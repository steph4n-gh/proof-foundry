/-!
# Proof Foundry state machine: executable Lean 4 specification and proofs

This file is a line-by-line executable model of `hub/state_machine.mjs`. It covers
`transitionClaim`, the King-of-the-Hill engine (`transitionRecord`, `replayRecordSubmissions`),
the seat-ownership reducers (`releaseSeatClaim`, `releaseClaimSeats`, `assignSeatClaim`),
`computeRecordTargets`, `computeTrustSeal`, and `isRungConquered`. It also contains universally
quantified theorems about the model. No theorem is bounded or sampled.

`formal/verify_state_machine_equiv.mjs` runs the compiled model (`pf_state_check`) and the real
JavaScript module on the same JSON inputs and checks that every output field matches.

## JavaScript value domain

JavaScript objects are dynamic, so the model types each field the reducers read or write:

* `JOpt α` distinguishes `undefined`, `null`, and a value, so pass-through fields round-trip
  exactly.
* `||`, `??`, and template-literal rendering are modelled explicitly (`jor`, `JOpt.nullish`,
  `render`), including the JavaScript falsiness of `""`.
* Opaque payloads that are copied wholesale (`checker`, `refutation`, `audit`, `epitaph`) keep
  their raw JSON text next to the typed view of the subfields the reducers inspect.

The differential domain, which the harness enforces when it generates inputs, is:

* lemma ids, seat ids, statuses, and event kinds are strings;
* scores are integers, decimal digit strings, `""`, or `null`;
* record replays contain only `record` and `record_bound` submissions;
* lemma ids are unique within a seat state;
* seat names, statement files, and map keys avoid `Object.prototype` names such as
  `constructor` and `__proto__`.

## `localeCompare` in the replay tie-break

`replayRecordSubmissions` breaks its last tie with `String.prototype.localeCompare`, which
uses ICU collation. That tie is reached only by submissions with equal git time, equal kind, and
equal numeric score. Two accepted submissions in that position share a canonical basename, so
their `_sub_file` keys are either equal, which leaves the stable input order in place, or one
key is `""`, which every collation sorts first. Refused submissions never change the state.
They can only shadow later submissions with the same key, and keys that are equal never reach
the collation step. Every total order with `""` as its least element therefore gives the same
result. The model uses code-point order.

The domain also excludes scores for which `Number(score)` is `NaN`. For those the JavaScript
comparator falls through to `localeCompare` and is not transitive, so the order V8's `sort`
produces depends on its algorithm. Such submissions are refused anyway.

## Theorems

| Requirement | Theorems |
| --- | --- |
| 1. Best record never worsens | `koth_monotone_best`, `koth_monotone_best_replay` |
| 2. Strongest bound never weakens | `koth_monotone_refuted`, `koth_monotone_refuted_replay` |
| 3. Anti-farming telescoping | `koth_anti_farming_ledger`, `koth_anti_farming_record_points`, `koth_anti_farming_bound_points`, `koth_anti_farming_record_points_replay` |
| 4. Contradiction is sticky | `koth_contradiction_sticky_step`, `koth_contradiction_sticky`, `koth_contradiction_reachable`, `koth_contradiction_replay` |
| 5. Order-independent contradiction | `koth_contradiction_order_independent` |
| 6. A closed hunt is exactly optimal | `koth_closed_exact_optimal`, `koth_closed_denies` |
| 7. Claim contradiction is sticky | `claim_contradiction_sticky_step`, `claim_contradiction_sticky` |
| 8. Proof and refutation contradict in either order | `claim_order_independent_contradiction` |
| 9. Barriers never overwrite verdicts | `barrier_never_overwrites_verdict` |
| 10. Seat–claim bijection | `seat_claim_bijection_release`, `seat_claim_bijection_releaseClaim`, `seat_claim_bijection_assign`, `seat_claim_bijection_preserved`, `Bij.iff`, `Bij.single_owner` |
| 11. Trust seal and conquest | `trust_seal_and_conquered_sound`, `trust_seal_contradiction_iff`, `conquered_false_of_bad_seal`, `conquered_record_default`, `conquered_replay_default` |

## Findings in `hub/state_machine.mjs`

1. **The points ledger reads inherited properties.** `transitionRecord` computes
   `(rs.points_by_seat[entry.seat] || 0) + points` on a plain object, so a `by_seat` that names an
   `Object.prototype` member (`constructor`, `toString`, `__proto__`, `valueOf`, …) starts from a
   function or object instead of `0` and the ledger concatenates strings. Two `min` records at 9
   then 7, with `start_target` 10 and `by_seat: "constructor"`, give
   `{"constructor": "function Object() { [native code] }22"}` instead of `{"constructor": 4}`.
   `missions.mjs` aggregates `recordPointsBySeat` the same way. `DONOR_SEAT_RE` blocks these names
   on donor PRs, but `allowMeta` PRs and internal seats skip that check. This model specifies
   own-property semantics (`pbsGet`), so the harness keeps such names out of the differential
   domain and prints the divergence for information.
2. **Stale-core receipts are still accepted.** `transitionRecord` requires the receipt's
   `core_hash` to be truthy, but it does not compare it with the current `coreHash`.
   `statement_hash` must match exactly. A record proved against an older judge core still earns
   points and can close the hunt. Only the `stale_core` freshness flag in `projectClaimView`
   reports it. The model and the theorems reproduce this behaviour.
3. **Replay mode can bypass the contradiction guard.** `transitionClaim` sends record events in
   `replay` mode straight to `transitionRecord`, before the `contradiction` guard. A record lemma
   with `status = "contradiction"` but `record_state.contradiction = false` can then reach
   `status = "checked"` through a direct `transitionClaim` call. `replayRecordSubmissions`
   restores the verdict in its final override, and `conquered_replay_default` proves that its
   outputs never show this state.
-/

namespace PF

/-! ## JavaScript value helpers -/

/-- A JavaScript slot: `undefined`, `null`, or a value. -/
inductive JOpt (α : Type) where
  | undef
  | null
  | val (a : α)
  deriving DecidableEq, Repr, Inhabited

/-- A string-valued JavaScript slot. -/
abbrev JStr := JOpt String

/-- `a ?? b`. -/
def JOpt.nullish {α : Type} (a b : JOpt α) : JOpt α :=
  match a with
  | .val _ => a
  | _ => b

/-- JavaScript truthiness of an object-valued slot (objects are always truthy). -/
def JOpt.present {α : Type} : JOpt α → Bool
  | .val _ => true
  | _ => false

/-- JavaScript truthiness of a string slot (`""` is falsy). -/
def jtruthy : JStr → Bool
  | .val s => s != ""
  | _ => false

/-- `a || b` on string slots. -/
def jor (a b : JStr) : JStr := if jtruthy a then a else b

/-- `` `${a}` `` template-literal rendering. -/
def render : JStr → String
  | .undef => "undefined"
  | .null => "null"
  | .val s => s

/-- `a || d` where `d` is a string literal. -/
def jorStr (a : JStr) (d : String) : String := if jtruthy a then render a else d

/-- `a || null` for a string slot, as an optional value. -/
def jorNull (a : JStr) : Option String :=
  match a with
  | .val s => if s != "" then some s else none
  | _ => none

/-- Lookup in an association list modelling a JS `Map` or plain object (first key wins). -/
def alookup {α : Type} (k : String) : List (String × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' = k then some v else alookup k rest

/-! ## Domain types -/

inductive Status where
  | conjecture
  | in_work
  | checked
  | refuted
  | dead
  | contradiction
  | other (s : String)
  deriving DecidableEq, Repr, Inhabited

def Status.name : Status → String
  | .conjecture => "conjecture"
  | .in_work => "in_work"
  | .checked => "checked"
  | .refuted => "refuted"
  | .dead => "dead"
  | .contradiction => "contradiction"
  | .other s => s

def Status.ofString (s : String) : Status :=
  if s = "conjecture" then .conjecture
  else if s = "in_work" then .in_work
  else if s = "checked" then .checked
  else if s = "refuted" then .refuted
  else if s = "dead" then .dead
  else if s = "contradiction" then .contradiction
  else .other s

/-- `openStatuses.has(status)`. -/
def Status.isOpen : Status → Bool
  | .conjecture => true
  | .in_work => true
  | _ => false

inductive EvKind where
  | claim
  | proof
  | refutation
  | rule_dead
  | audit
  | record
  | record_bound
  | other (s : String)
  deriving DecidableEq, Repr, Inhabited

def EvKind.name : EvKind → String
  | .claim => "claim"
  | .proof => "proof"
  | .refutation => "refutation"
  | .rule_dead => "rule_dead"
  | .audit => "audit"
  | .record => "record"
  | .record_bound => "record_bound"
  | .other s => s

def EvKind.ofString (s : String) : EvKind :=
  if s = "claim" then .claim
  else if s = "proof" then .proof
  else if s = "refutation" then .refutation
  else if s = "rule_dead" then .rule_dead
  else if s = "audit" then .audit
  else if s = "record" then .record
  else if s = "record_bound" then .record_bound
  else .other s

/-- `kind === "record" || kind === "record_bound"`. -/
def EvKind.isRecordEvent : EvKind → Bool
  | .record => true
  | .record_bound => true
  | _ => false

/-- Typed view of a `checker` receipt object. `raw` is its JSON text. -/
structure Checker where
  ok : Bool := false
  fileHash : JStr := .undef
  statementFrozen : Bool := false
  bySeat : JStr := .undef
  statementHash : JStr := .undef
  coreHash : JStr := .undef
  axioms : JOpt (List String) := .undef
  durationMs : JOpt Int := .undef
  raw : String := "{}"
  deriving DecidableEq, Repr, Inhabited

structure Refutation where
  fileHash : JStr := .undef
  raw : String := "{}"
  deriving DecidableEq, Repr, Inhabited

structure Audit where
  status : JStr := .undef
  fileHash : JStr := .undef
  raw : String := "{}"
  deriving DecidableEq, Repr, Inhabited

/-- A `record_state.best` / `record_state.refuted` receipt. -/
structure Receipt where
  score : Int
  seat : String
  file : String
  fileHash : JStr
  submission : String
  gitTs : Option Int
  atTime : Option String
  thm : String
  statementHash : JStr
  coreHash : JStr
  axioms : List String
  durationMs : Option Int
  inclusiveBound : Option Int
  deriving DecidableEq, Repr, Inhabited

inductive HistState where
  | accepted
  | ignored_non_improving
  | contradiction
  | stale_statement
  deriving DecidableEq, Repr, Inhabited

def HistState.name : HistState → String
  | .accepted => "accepted"
  | .ignored_non_improving => "ignored_non_improving"
  | .contradiction => "contradiction"
  | .stale_statement => "stale_statement"

/-- A `record_state.history` entry. `staleHashes` holds the extra stale-entry fields. -/
structure HistEntry where
  isRecord : Bool
  score : Int
  seat : String
  file : String
  fileHash : JStr
  submission : String
  points : Int
  gitTs : Option Int
  atTime : Option String
  staleHashes : Option (JStr × JStr)
  state : HistState
  deriving DecidableEq, Repr, Inhabited

structure RecordState where
  direction : String
  best : Option Receipt
  refuted : Option Receipt
  nextTarget : Option Int
  closed : Bool
  contradiction : Bool
  history : List HistEntry
  pointsBySeat : List (String × Int)
  deriving DecidableEq, Repr, Inhabited

/-- `lemma.record` hunt configuration, read-only. -/
structure RecordCfgIn where
  direction : JStr := .undef
  startTarget : Option Int := none
  boundFloor : Option Int := none
  scoreMax : Option Int := none
  allowBound : JOpt Bool := .undef
  fileStem : JStr := .undef
  claimsDir : JStr := .undef
  artifactExt : JStr := .undef
  theoremTemplate : JStr := .undef
  deriving DecidableEq, Repr, Inhabited

structure Lemma where
  id : String
  kind : JStr := .undef
  status : Status
  claimedBy : JStr := .undef
  updatedAt : JStr := .undef
  epitaph : JOpt String := .undef
  audit : JOpt Audit := .undef
  checker : JOpt Checker := .undef
  refutation : JOpt Refutation := .undef
  leanFile : JStr := .undef
  theoremName : JStr := .undef
  registeredStatement : JStr := .undef
  statement : JStr := .undef
  verifiedSignature : JStr := .undef
  statementFile : JStr := .undef
  record : JOpt RecordCfgIn := .undef
  recordState : JOpt RecordState := .undef
  deriving DecidableEq, Repr, Inhabited

/-- `event.score` as supplied in a submission. -/
inductive ScoreIn where
  | num (n : Int)
  | str (s : String)
  | null
  | undef
  deriving DecidableEq, Repr, Inhabited

structure Event where
  kind : EvKind
  atTime : JStr := .undef
  seat : JStr := .undef
  epitaph : JOpt String := .undef
  audit : JOpt Audit := .undef
  checker : JOpt Checker := .undef
  refutation : JOpt Refutation := .undef
  file : JStr := .undef
  thm : JStr := .undef
  signature : JStr := .undef
  score : ScoreIn := .undef
  subFile : JStr := .undef
  deriving DecidableEq, Repr, Inhabited

inductive Mode where
  | none
  | preflight
  | replay
  | other
  deriving DecidableEq, Repr, Inhabited

structure Ctx where
  mode : Mode := .none
  missionSlug : JStr := .undef
  gitTs : Option Int := none
  statementHash : JStr := .undef
  coreHash : JStr := .undef
  opposingScore : Option Int := none
  deriving DecidableEq, Repr, Inhabited

/-- `{ ok, lemma, reason }`. `reason` is `""` on success. -/
structure Result where
  ok : Bool
  lemma : Lemma
  reason : String
  deriving DecidableEq, Repr, Inhabited

/-! ## Numbers -/

def digitVal? (c : Char) : Option Int :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

def digitsVal? : List Char → Option Int
  | [] => none
  | [c] => digitVal? c
  | c :: rest =>
    match digitVal? c, digitsVal? rest with
    | some d, some v => some (d * 10 ^ rest.length + v)
    | _, _ => none

/-- `Number(s)` on the string domain (`""`, optional sign, decimal digits). `none` is `NaN`. -/
def jsNumberOfString (s : String) : Option Int :=
  if s = "" then some 0
  else match s.toList with
    | '-' :: ds => (digitsVal? ds).map (fun n => -n)
    | '+' :: ds => digitsVal? ds
    | ds => digitsVal? ds

/-- `Number(event.score)`; `none` is `NaN`. -/
def jsNumber : ScoreIn → Option Int
  | .num n => some n
  | .str s => jsNumberOfString s
  | .null => some 0
  | .undef => none

/-- `String(event.score)`. -/
def jsString : ScoreIn → String
  | .num n => toString n
  | .str s => s
  | .null => "null"
  | .undef => "undefined"

def maxSafe : Int := 9007199254740991

/-- The validity test at the top of `transitionRecord`, without the `checker.ok` conjunct. -/
def validScore (scoreMax : Int) (s : ScoreIn) : Option Int :=
  match jsNumber s with
  | some n =>
    if -maxSafe ≤ n ∧ n ≤ maxSafe ∧ 0 ≤ n ∧ n ≤ scoreMax ∧ toString n = jsString s then some n
    else none
  | none => none

/-! ## Record configuration and canonical targets -/

structure RecCfg where
  isMax : Bool
  startTarget : Int
  boundFloor : Int
  scoreMax : Int
  deriving DecidableEq, Repr, Inhabited

/-- `lemma.record || {}`. -/
def lemmaCfgIn (l : Lemma) : RecordCfgIn :=
  match l.record with
  | .val c => c
  | _ => {}

/-- `getRecordConfig`. -/
def getRecordConfig (l : Lemma) : RecCfg :=
  let c := lemmaCfgIn l
  { isMax := c.direction == .val "max"
    startTarget := c.startTarget.getD 0
    boundFloor := c.boundFloor.getD 0
    scoreMax := c.scoreMax.getD 100000 }

/-- `direction === "min" ? -1 : 1`. -/
def stepOf (isMax : Bool) : Int := if isMax then 1 else -1

def isRecordLemma (l : Lemma) : Bool := l.kind == .val "record"

/-- `lemma.record?.allow_bound === false`. -/
def allowBoundFalse (l : Lemma) : Bool :=
  match l.record with
  | .val c => c.allowBound == .val false
  | _ => false

structure Targets where
  tag : String
  artifactFile : String
  submissionBasename : String
  submissionFile : String
  theoremName : String
  deriving DecidableEq, Repr, Inhabited

/-- `computeRecordTargets(missionSlug, lemma, kind, score)`. -/
def computeRecordTargets (slug : JStr) (l : Lemma) (kind : EvKind) (score : Int) : Targets :=
  let tag := if kind = .record_bound then s!"not_s{score}" else s!"s{score}"
  let cfg := lemmaCfgIn l
  let stem := jorStr cfg.fileStem (l.id.replace "-" "_")
  let claimsDir := jorStr cfg.claimsDir s!"missions/{render slug}/lean/Claims"
  let ext := jorStr cfg.artifactExt ".lean"
  let tmpl := jorStr cfg.theoremTemplate s!"{stem}_\{tag}.record"
  let basename := s!"{l.id}.{kind.name}.s{score}.json"
  { tag
    artifactFile := s!"{claimsDir}/{stem}_{tag}{ext}"
    submissionBasename := basename
    submissionFile := s!"missions/{render slug}/submissions/{basename}"
    theoremName := tmpl.replace "{tag}" tag }

/-! ## Trust seal and rung conquest -/

inductive Seal where
  | contradiction
  | flagged
  | frozen
  | record
  | audited
  | provisional
  | refuted
  | dead
  | in_work
  | open_
  deriving DecidableEq, Repr, Inhabited

def Seal.name : Seal → String
  | .contradiction => "contradiction"
  | .flagged => "flagged"
  | .frozen => "frozen"
  | .record => "record"
  | .audited => "audited"
  | .provisional => "provisional"
  | .refuted => "refuted"
  | .dead => "dead"
  | .in_work => "in_work"
  | .open_ => "open"

/-- `lemma.record_state?.contradiction`. -/
def rsContra (l : Lemma) : Bool :=
  match l.recordState with
  | .val rs => rs.contradiction
  | _ => false

/-- `lemma.record_state?.closed`. -/
def rsClosed (l : Lemma) : Bool :=
  match l.recordState with
  | .val rs => rs.closed
  | _ => false

def checkerFileHash (l : Lemma) : JStr :=
  match l.checker with
  | .val c => c.fileHash
  | _ => .undef

def checkerOk (l : Lemma) : Bool :=
  match l.checker with
  | .val c => c.ok
  | _ => false

def checkerFrozen (l : Lemma) : Bool :=
  match l.checker with
  | .val c => c.statementFrozen
  | _ => false

def refutationFileHash (l : Lemma) : JStr :=
  match l.refutation with
  | .val r => r.fileHash
  | _ => .undef

def auditFileHash (l : Lemma) : JStr :=
  match l.audit with
  | .val a => a.fileHash
  | _ => .undef

def auditStatus (l : Lemma) : JStr :=
  match l.audit with
  | .val a => a.status
  | _ => .undef

/-- `computeTrustSeal(lemma)`. -/
def computeTrustSeal (l : Lemma) : Seal :=
  if l.status = .contradiction ∨ rsContra l = true then .contradiction
  else if isRecordLemma l then
    match l.recordState with
    | .val rs => if rs.closed then .frozen else if rs.best.isSome then .record else .open_
    | _ => .open_
  else
    let currentHash := jor (checkerFileHash l) (jor (refutationFileHash l) .null)
    let mismatch := jtruthy (auditFileHash l) && auditFileHash l != currentHash
    if auditStatus l = .val "flagged" ∧ mismatch = false then .flagged
    else if l.status = .checked then
      if checkerFrozen l then .frozen
      else if auditStatus l = .val "faithful" ∧ mismatch = false then .audited
      else .provisional
    else if l.status = .refuted then .refuted
    else if l.status = .dead then .dead
    else if l.status = .in_work then .in_work
    else .open_

/-- An objective requirement's `expect` value. `obj` keeps the `Number.isSafeInteger`
results for `record_at_most` and `record_at_least`. -/
inductive Expect where
  | str (s : String)
  | obj (atMost : Option Int) (atLeast : Option Int)
  | null
  deriving DecidableEq, Repr, Inhabited

/-- `isRungConquered(lemma, expect)`. -/
def isRungConquered (lo : Option Lemma) (ex : Expect) : Bool :=
  match lo with
  | none => false
  | some l =>
    let sl := computeTrustSeal l
    if sl = .flagged ∨ sl = .contradiction then false
    else if isRecordLemma l then
      match l.recordState with
      | .val rs =>
        if rs.contradiction then false
        else if ex = .str "record_any" then rs.best.isSome
        else match ex with
          | .obj (some n) _ =>
            rs.direction == "min" && (match rs.best with | some b => decide (b.score ≤ n) | none => false)
          | .obj none (some n) =>
            rs.direction == "max" && (match rs.best with | some b => decide (b.score ≥ n) | none => false)
          | _ => rs.closed
      | _ => false
    else if ex = .str "refutation" then l.status == .refuted
    else if ex = .str "either" then sl == .audited || sl == .frozen || l.status == .refuted
    else sl == .audited || sl == .frozen

/-! ## King-of-the-Hill core -/

/-- Points ledger read: `points_by_seat[seat] || 0`. -/
def pbsGet (l : List (String × Int)) (k : String) : Int := (alookup k l).getD 0

/-- Points ledger write: `{ ...points_by_seat, [seat]: v }`. -/
def pbsSet : List (String × Int) → String → Int → List (String × Int)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v => if k' = k then (k, v) :: rest else (k', v') :: pbsSet rest k v

def pbsAdd (l : List (String × Int)) (k : String) (p : Int) : List (String × Int) :=
  pbsSet l k (pbsGet l k + p)

/-- Total points across all seats. -/
def totalPoints (l : List (String × Int)) : Int := (l.map Prod.snd).sum

/-- `closed` as recomputed by `transitionRecord`. -/
def closedFor (st : Int) (best refuted : Option Receipt) : Bool :=
  match best with
  | some b =>
    (st == -1 && b.score == 0) ||
      (match refuted with
       | some r => r.score == b.score + st
       | none => false)
  | none => false

/-- `record ? step : -step`. -/
def kSgn (c : RecCfg) (isRec : Bool) : Int := if isRec then stepOf c.isMax else -stepOf c.isMax

/-- `rs[field]`. -/
def kCur (rs : RecordState) (isRec : Bool) : Option Receipt := if isRec then rs.best else rs.refuted

/-- `record ? startTarget : boundFloor`. -/
def kBase (c : RecCfg) (isRec : Bool) : Int := if isRec then c.startTarget else c.boundFloor

/-- `margin = (score - (rs[field]?.score ?? base)) * (record ? step : -step)`. -/
def kMargin (c : RecCfg) (rs : RecordState) (isRec : Bool) (score : Int) : Int :=
  (score - (match kCur rs isRec with | some r => r.score | none => kBase c isRec)) * kSgn c isRec

/-- `improves = rs[field] ? margin > 0 : margin >= 0`. -/
def kImproves (c : RecCfg) (rs : RecordState) (isRec : Bool) (score : Int) : Bool :=
  match kCur rs isRec with
  | some _ => decide (kMargin c rs isRec score > 0)
  | none => decide (kMargin c rs isRec score ≥ 0)

/-- `contradiction = opposingScore != null && (score - opposingScore) * (record ? step : -step) >= 0`. -/
def kContra (c : RecCfg) (isRec : Bool) (score : Int) (opp : Option Int) : Bool :=
  match opp with
  | some o => decide ((score - o) * kSgn c isRec ≥ 0)
  | none => false

/-- Points awarded by one step: `margin + (rs[field] ? 0 : 1)` on a non-contradicting improvement. -/
def kPoints (c : RecCfg) (rs : RecordState) (isRec : Bool) (score : Int) (opp : Option Int) : Int :=
  if kImproves c rs isRec score && !kContra c isRec score opp then
    kMargin c rs isRec score + (if (kCur rs isRec).isSome then 0 else 1)
  else 0

/-- The non-stale, non-contradicted branch of `transitionRecord`, from `const record = ...`
through `next.history = ...`. -/
def kothCore (c : RecCfg) (rs : RecordState) (isRec : Bool) (score : Int)
    (receipt : Receipt) (ent : HistEntry) (opp : Option Int) : RecordState :=
  let st := stepOf c.isMax
  let improves := kImproves c rs isRec score
  let contra := kContra c isRec score opp
  let pts := kPoints c rs isRec score opp
  let best' := if isRec && improves then some receipt else rs.best
  let refuted' :=
    if !isRec && improves then some { receipt with inclusiveBound := some (max 0 (score - st)) }
    else rs.refuted
  let pbs' :=
    if contra then [] else if improves then pbsAdd rs.pointsBySeat receipt.seat pts else rs.pointsBySeat
  let closed' := !contra && closedFor st best' refuted'
  let nt : Option Int :=
    if closed' || contra then none
    else match best' with
      | some b => some (b.score + st)
      | none => some c.startTarget
  let hs : HistState := if contra then .contradiction else if improves then .accepted else .ignored_non_improving
  { rs with
    contradiction := contra
    best := best'
    refuted := refuted'
    pointsBySeat := pbs'
    closed := closed'
    nextTarget := nt
    history := rs.history ++ [{ ent with points := pts, state := hs }] }

/-- The lemma returned by the main branch of `transitionRecord`. -/
def coreLemma (l : Lemma) (rs' : RecordState) : Lemma :=
  { l with
    status := if rs'.contradiction then .contradiction else if rs'.closed then .checked else l.status
    claimedBy := if rs'.contradiction || rs'.closed then .null else l.claimedBy
    recordState := .val rs' }

/-- The lemma returned by the stale-statement and already-contradicted branches. -/
def keepLemma (l : Lemma) (rs : RecordState) (h : HistEntry) : Lemma :=
  { l with recordState := .val { rs with history := rs.history ++ [h] } }

/-- `transitionRecord(lemma, event, ctx)`. -/
def transitionRecord (l : Lemma) (e : Event) (ctx : Ctx) : Result :=
  let c := getRecordConfig l
  let invalid : Result := ⟨false, l, "invalid record receipt"⟩
  match validScore c.scoreMax e.score, e.checker with
  | some score, .val chk =>
    if chk.ok then
      let t := computeRecordTargets ctx.missionSlug l e.kind score
      if (jtruthy e.subFile && e.subFile != .val t.submissionBasename) ||
          e.file != .val t.artifactFile || e.thm != .val t.theoremName then
        ⟨false, l, "non-canonical record receipt"⟩
      else
        match l.recordState with
        | .val rs =>
          let isRec := e.kind == .record
          let ent : HistEntry :=
            { isRecord := isRec, score, seat := jorStr chk.bySeat "unknown"
              file := t.artifactFile, fileHash := jor chk.fileHash .null
              submission := jorStr e.subFile "", points := 0, gitTs := ctx.gitTs
              atTime := jorNull e.atTime, staleHashes := none, state := .accepted }
          if !jtruthy ctx.statementHash || chk.statementHash != ctx.statementHash ||
              !jtruthy ctx.coreHash || !jtruthy chk.coreHash then
            ⟨true, keepLemma l rs { ent with
              staleHashes := some (chk.statementHash.nullish .null, chk.coreHash.nullish .null)
              state := .stale_statement }, ""⟩
          else if rs.contradiction then
            ⟨true, keepLemma l rs { ent with state := .contradiction }, ""⟩
          else
            let receipt : Receipt :=
              { score, seat := ent.seat, file := ent.file, fileHash := ent.fileHash
                submission := ent.submission, gitTs := ent.gitTs, atTime := ent.atTime
                thm := t.theoremName, statementHash := chk.statementHash
                coreHash := chk.coreHash
                axioms := (match chk.axioms with | .val a => a | _ => [])
                durationMs := (match chk.durationMs with | .val d => if d != 0 then some d else none | _ => none)
                inclusiveBound := none }
            ⟨true, coreLemma l (kothCore c rs isRec score receipt ent ctx.opposingScore), ""⟩
        | _ => ⟨false, l, "TypeError: record_state is missing"⟩
    else invalid
  | _, _ => invalid

/-! ## `transitionClaim` -/

def denyMsg (l : Lemma) (e : Event) (reason : String) : Result :=
  ⟨false, l, s!"Cannot apply {e.kind.name} to {l.id}: {reason}"⟩

def defaultReason (l : Lemma) : String := s!"status is \"{l.status.name}\""

def eventCheckerOk (e : Event) : Bool :=
  match e.checker with
  | .val c => c.ok
  | _ => false

def eventAuditFileHash (e : Event) : JStr :=
  match e.audit with
  | .val a => a.fileHash
  | _ => .undef

/-- Truthiness of `lemma.refutation`. -/
def hasRefutation (l : Lemma) : Bool := l.refutation.present

/-- The `proof` / `refutation` branch of `transitionClaim`. -/
def transitionVerdict (l : Lemma) (e : Event) (ctx : Ctx) : Result :=
  let proof := e.kind == .proof
  let conflicts : Bool :=
    if proof then l.status == .refuted || hasRefutation l
    else l.status == .checked || checkerOk l
  if ctx.mode = .preflight then
    if conflicts || (proof && l.status == .dead) then denyMsg l e (defaultReason l) else ⟨true, l, ""⟩
  else if (if proof then !eventCheckerOk e else !e.refutation.present) then
    denyMsg l e "missing verified receipt"
  else
    let existing : Bool := if proof then checkerOk l else hasRefutation l
    if ctx.mode = .replay && existing && !conflicts then ⟨true, l, ""⟩
    else
      let next : Lemma :=
        { l with
          status := if conflicts then .contradiction else if proof then .checked else .refuted
          claimedBy := .null
          updatedAt := e.atTime.nullish l.updatedAt }
      if ctx.mode = .replay && existing then ⟨true, next, ""⟩
      else if proof then
        ⟨true,
          { next with
            leanFile := jor e.file l.leanFile
            theoremName := jor e.thm l.theoremName
            registeredStatement := jor l.registeredStatement (jor l.statement (.val ""))
            verifiedSignature := if jtruthy e.signature then e.signature else l.verifiedSignature
            statement := if jtruthy e.signature then e.signature else l.statement
            checker := e.checker }, ""⟩
      else ⟨true, { next with refutation := e.refutation }, ""⟩

/-- `transitionClaim(lemma, event, ctx)`. -/
def transitionClaim (l : Lemma) (e : Event) (ctx : Ctx) : Result :=
  let isRec := isRecordLemma l
  let recordEvent := e.kind.isRecordEvent
  let contradiction := l.status == .contradiction || rsContra l
  if recordEvent && !isRec then denyMsg l e "claim is not a record hunt"
  else if e.kind = .record_bound ∧ allowBoundFalse l = true then denyMsg l e "bound proofs are not supported"
  else if recordEvent && ctx.mode == .replay then transitionRecord l e ctx
  else if contradiction && e.kind != .audit then denyMsg l e "status is \"contradiction\""
  else if e.kind = .claim then
    if !l.status.isOpen || rsClosed l then denyMsg l e (defaultReason l)
    else ⟨true, { l with status := .in_work, claimedBy := e.seat, updatedAt := e.atTime.nullish l.updatedAt }, ""⟩
  else if recordEvent then
    if rsClosed l || l.status == .checked then denyMsg l e "record hunt is closed" else ⟨true, l, ""⟩
  else if isRec then denyMsg l e "use record or record-bound for a record hunt"
  else if e.kind = .rule_dead then
    if l.status == .checked || l.status == .refuted then denyMsg l e (defaultReason l)
    else if !e.epitaph.present then denyMsg l e "missing epitaph"
    else ⟨true, { l with status := .dead, claimedBy := .null, epitaph := e.epitaph,
                         updatedAt := e.atTime.nullish l.updatedAt }, ""⟩
  else if e.kind = .audit then
    let hash := jor (checkerFileHash l) (refutationFileHash l)
    if !jtruthy hash || eventAuditFileHash e != hash then denyMsg l e "audit does not match the artifact hash"
    else ⟨true, { l with audit := e.audit }, ""⟩
  else if e.kind != .proof && e.kind != .refutation then denyMsg l e "unknown event"
  else transitionVerdict l e ctx

/-! ## Seats -/

structure Seat where
  id : String
  status : JStr := .undef
  current : JStr := .undef
  deriving DecidableEq, Repr, Inhabited

structure State where
  seats : List Seat
  lemmas : List Lemma
  deriving DecidableEq, Repr, Inhabited

/-- Apply `f` to the first element satisfying `p` (`arr.map(x => x === arr.find(p) ? f(x) : x)`). -/
def modifyFirst {α : Type} (p : α → Bool) (f : α → α) : List α → List α
  | [] => []
  | x :: xs => if p x then f x :: xs else x :: modifyFirst p f xs

/-- The lemma update inside `releaseSeatClaim`. `seats` is the already-released seat list. -/
def releaseLemma (seat : Seat) (sid : String) (seats : List Seat) (l : Lemma) : Lemma :=
  if seat.current ≠ .val l.id ∧ ¬(l.status = .in_work ∧ l.claimedBy = .val sid) then l
  else
    let other := seats.find? (fun s => s.current == .val l.id)
    { l with
      status := if l.status = .in_work ∧ other.isNone then .conjecture else l.status
      claimedBy := match other with | some o => .val o.id | none => .null }

def idleSeat (s : Seat) : Seat := { s with status := .val "idle", current := .null }

/-- `releaseSeatClaim(state, seatId)`. -/
def releaseSeatClaim (st : State) (sid : String) : Except String State :=
  match st.seats.find? (fun s => s.id == sid) with
  | none => .error s!"Unknown seat: {sid}"
  | some seat =>
    let seats := modifyFirst (fun s => s.id == sid) idleSeat st.seats
    .ok { st with seats, lemmas := st.lemmas.map (releaseLemma seat sid seats) }

/-- `releaseClaimSeats(state, lemmaId)`. It iterates over the original seat array. -/
def releaseClaimSeats (st : State) (lid : String) : Except String State :=
  st.seats.foldlM (fun acc seat => if seat.current = .val lid then releaseSeatClaim acc seat.id else pure acc) st

/-- `assignSeatClaim(state, seatId, lemmaId)`. -/
def assignSeatClaim (st : State) (sid lid : String) : Except String State :=
  match st.lemmas.find? (fun l => l.id == lid) with
  | none => .error s!"Unknown claim: {lid}"
  | some lemma =>
    let r := transitionClaim lemma { kind := .claim, seat := .val sid } {}
    if !r.ok then .error r.reason
    else do
      let s1 ← releaseSeatClaim st sid
      let released ← releaseClaimSeats s1 lid
      pure { released with
        seats := released.seats.map (fun s => if s.id = sid then { s with status := .val "working", current := .val lid } else s)
        lemmas := released.lemmas.map (fun l => if l.id = lid then r.lemma else l) }

/-! ## Record replay -/

structure Hashes where
  statementHashes : Option (List (String × String)) := none
  coreHash : JStr := .undef
  deriving DecidableEq, Repr, Inhabited

/-- `gitAddedTs.get(key)`. -/
def tsGet (ts : List (String × Int)) : JStr → Option Int
  | .val k => alookup k ts
  | _ => none

/-- `a._sub_file || ""`. -/
def subKey (e : Event) : String := jorStr e.subFile ""

/-- The `replayRecordSubmissions` comparator. A negative result puts `a` first. -/
def subCmp (ts : List (String × Int)) (st : Int) (a b : Event) : Int :=
  let ka := subKey a
  let kb := subKey b
  let ta := (alookup ka ts).getD maxSafe
  let tb := (alookup kb ts).getD maxSafe
  if ta - tb ≠ 0 then ta - tb
  else if a.kind ≠ b.kind then (if a.kind = .record then -1 else 1)
  else
    match jsNumber a.score, jsNumber b.score with
    | some x, some y =>
      if x - y ≠ 0 then (if a.kind = .record then st else -st) * (x - y)
      else if ka < kb then -1 else if ka = kb then 0 else 1
    | _, _ => if ka < kb then -1 else if ka = kb then 0 else 1

/-- Stable insertion: `x` goes after every element it does not strictly precede. -/
def insertStable {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertStable lt x ys

/-- A stable sort. Under a total preorder every stable sort returns the same list, so this is
the result of V8's `Array.prototype.sort`. -/
def sortStable {α : Type} (lt : α → α → Bool) (l : List α) : List α :=
  l.foldl (fun acc x => insertStable lt x acc) []

def sortSubs (ts : List (String × Int)) (st : Int) (subs : List Event) : List Event :=
  sortStable (fun a b => decide (subCmp ts st a b < 0)) subs

structure Loop where
  lemma : Lemma
  seen : List String
  strongRec : Option Int
  strongBnd : Option Int
  deriving DecidableEq, Repr, Inhabited

/-- Environment of one replay: everything the loop reads but does not change. -/
structure ReplayEnv where
  slug : JStr
  ts : List (String × Int)
  statementHash : JStr
  coreHash : JStr
  st : Int
  deriving DecidableEq, Repr, Inhabited

/-- `next.record_state.history.at(-1).state === "stale_statement"`. -/
def lastStale (l : Lemma) : Bool :=
  match l.recordState with
  | .val rs =>
    match rs.history.getLast? with
    | some h => h.state == .stale_statement
    | none => false
  | _ => false

def replayCtx (env : ReplayEnv) (lp : Loop) (sub : Event) : Ctx :=
  { mode := .replay
    missionSlug := env.slug
    gitTs := tsGet env.ts sub.subFile
    statementHash := env.statementHash
    coreHash := env.coreHash
    opposingScore := if sub.kind = .record then lp.strongBnd else lp.strongRec }

/-- One iteration of the `for (const sub of ordered)` loop. -/
def replayStep (env : ReplayEnv) (lp : Loop) (sub : Event) : Loop :=
  if jtruthy sub.subFile ∧ render sub.subFile ∈ lp.seen then lp
  else
    let seen := if jtruthy sub.subFile then render sub.subFile :: lp.seen else lp.seen
    let r := transitionClaim lp.lemma sub (replayCtx env lp sub)
    if !r.ok then { lp with seen }
    else if lastStale r.lemma then { lp with seen, lemma := r.lemma }
    else
      let score := (jsNumber sub.score).getD 0
      let isRec := sub.kind = .record
      let sgn := if isRec then env.st else -env.st
      let better (prev : Option Int) : Bool := match prev with
        | none => true
        | some p => decide ((score - p) * sgn > 0)
      if sub.kind = .record then
        { lemma := r.lemma, seen, strongRec := if better lp.strongRec then some score else lp.strongRec, strongBnd := lp.strongBnd }
      else if sub.kind = .record_bound then
        { lemma := r.lemma, seen, strongRec := lp.strongRec, strongBnd := if better lp.strongBnd then some score else lp.strongBnd }
      else { lp with seen, lemma := r.lemma }

def replayLoop (env : ReplayEnv) (lp : Loop) (subs : List Event) : Loop := subs.foldl (replayStep env) lp

/-- The empty hunt that `replayRecordSubmissions` starts from. -/
def emptyHunt (l : Lemma) : Lemma :=
  let c := getRecordConfig l
  { l with
    status := if l.status.isOpen then l.status else .conjecture
    recordState := .val
      { direction := if c.isMax then "max" else "min", best := none, refuted := none
        nextTarget := some c.startTarget, closed := false, contradiction := false
        history := [], pointsBySeat := [] } }

/-- `currentHashes.statementHashes?.[lemma.statement_file]`. -/
def statementHashFor (h : Hashes) (l : Lemma) : JStr :=
  match h.statementHashes with
  | some m => match alookup (render l.statementFile) m with
    | some v => .val v
    | none => .undef
  | none => .undef

def replayEnv (slug : JStr) (l : Lemma) (ts : List (String × Int)) (h : Hashes) : ReplayEnv :=
  { slug, ts, statementHash := statementHashFor h l, coreHash := h.coreHash
    st := stepOf (getRecordConfig l).isMax }

/-- The final `lemma.status === "contradiction"` override. -/
def finalizeReplay (orig fin : Lemma) : Lemma :=
  if orig.status = .contradiction ∧ rsContra fin = false then
    { fin with
      status := .contradiction
      claimedBy := .null
      recordState := match fin.recordState with
        | .val rs => .val { rs with contradiction := true, closed := false, nextTarget := none, pointsBySeat := [] }
        | o => o }
  else fin

/-- `replayRecordSubmissions(missionSlug, lemma, subs, { gitAddedTs, currentHashes })`. -/
def replayRecordSubmissions (slug : JStr) (l : Lemma) (subs : List Event)
    (ts : List (String × Int)) (h : Hashes) : Lemma :=
  let env := replayEnv slug l ts h
  let ordered := sortSubs ts env.st subs
  let fin := (replayLoop env ⟨emptyHunt l, [], none, none⟩ ordered).lemma
  finalizeReplay l fin

/-!
# Proofs

Every theorem below is universally quantified over the model's inputs and is checked by the
Lean kernel. `PFFormal.AxiomCheck` confirms that each one depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

set_option linter.unusedSimpArgs false

/-! ## Proofs: structural lemmas -/

/-- Every outcome of `transitionRecord`: refused, a history-only append, or the main branch. -/
inductive RecOutcome (l : Lemma) (e : Event) (opp : Option Int) : Result → Prop
  | refused (reason : String) : RecOutcome l e opp ⟨false, l, reason⟩
  | keep (rs : RecordState) (h : HistEntry) :
      l.recordState = .val rs → RecOutcome l e opp ⟨true, keepLemma l rs h, ""⟩
  | core (rs : RecordState) (score : Int) (receipt : Receipt) (ent : HistEntry) :
      l.recordState = .val rs → rs.contradiction = false → receipt.score = score →
      RecOutcome l e opp
        ⟨true, coreLemma l (kothCore (getRecordConfig l) rs (e.kind == .record) score receipt ent opp), ""⟩

theorem transitionRecord_outcome (l : Lemma) (e : Event) (ctx : Ctx) :
    RecOutcome l e ctx.opposingScore (transitionRecord l e ctx) := by
  unfold transitionRecord
  dsimp only
  split
  · split
    · split
      · exact .refused _
      · split
        · rename_i rs hrs
          split
          · exact .keep _ _ hrs
          · split
            · exact .keep _ _ hrs
            · rename_i hc
              exact .core _ _ _ _ hrs (by simpa using hc) rfl
        · exact .refused _
    · exact .refused _
  · exact .refused _

/-- The fields that no reducer writes. -/
structure Frame (l l' : Lemma) : Prop where
  record : l'.record = l.record
  id : l'.id = l.id
  kind : l'.kind = l.kind

theorem Frame.refl (l : Lemma) : Frame l l := ⟨rfl, rfl, rfl⟩

theorem Frame.trans {a b c : Lemma} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h2.record.trans h1.record, h2.id.trans h1.id, h2.kind.trans h1.kind⟩

theorem RecOutcome.frame {l e opp r} (h : RecOutcome l e opp r) : Frame l r.lemma := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem transitionVerdict_frame (l : Lemma) (e : Event) (ctx : Ctx) :
    (transitionVerdict l e ctx).lemma.recordState = l.recordState ∧ Frame l (transitionVerdict l e ctx).lemma := by
  unfold transitionVerdict denyMsg
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- `transitionClaim` either leaves the record state alone, or it is `transitionRecord`. -/
theorem transitionClaim_cases (l : Lemma) (e : Event) (ctx : Ctx) :
    ((transitionClaim l e ctx).lemma.recordState = l.recordState ∧ Frame l (transitionClaim l e ctx).lemma) ∨
    (e.kind.isRecordEvent = true ∧ ctx.mode = .replay ∧ isRecordLemma l = true ∧
     transitionClaim l e ctx = transitionRecord l e ctx) := by
  cases hk : e.kind <;>
    simp only [transitionClaim, hk, EvKind.isRecordEvent, Bool.false_and, Bool.true_and, reduceCtorEq,
      false_and, ↓reduceIte, Bool.false_eq_true, bne_self_eq_false, Bool.and_false, Bool.and_true,
      bne_iff_ne, ne_eq, not_false_eq_true, decide_true, decide_false, Bool.not_true, Bool.not_false, true_and,
      and_true, and_false]
  all_goals repeat' split
  all_goals first
    | exact .inl ⟨rfl, rfl, rfl, rfl⟩
    | exact .inl (transitionVerdict_frame l e ctx)
    | (right; simp_all)

theorem transitionClaim_frame (l : Lemma) (e : Event) (ctx : Ctx) : Frame l (transitionClaim l e ctx).lemma := by
  rcases transitionClaim_cases l e ctx with ⟨_, h⟩ | ⟨_, _, _, h⟩
  · exact h
  · rw [h]; exact (transitionRecord_outcome l e ctx).frame

theorem getRecordConfig_congr {l l' : Lemma} (h : Frame l l') : getRecordConfig l' = getRecordConfig l := by
  simp [getRecordConfig, lemmaCfgIn, h.record]

theorem isRecordLemma_congr {l l' : Lemma} (h : Frame l l') : isRecordLemma l' = isRecordLemma l := by
  simp [isRecordLemma, h.kind]

theorem allowBoundFalse_congr {l l' : Lemma} (h : Frame l l') : allowBoundFalse l' = allowBoundFalse l := by
  simp [allowBoundFalse, h.record]

theorem computeRecordTargets_congr {l l' : Lemma} (h : Frame l l') (slug : JStr) (k : EvKind) (s : Int) :
    computeRecordTargets slug l' k s = computeRecordTargets slug l k s := by
  simp [computeRecordTargets, lemmaCfgIn, h.record, h.id]

/-! ### Record-state invariants -/

/-- A record-state property preserved by every `transitionRecord` outcome under configuration `c`. -/
structure RsInvariant (c : RecCfg) (P : RecordState → Prop) : Prop where
  keep : ∀ rs h, P rs → P { rs with history := rs.history ++ [h] }
  core : ∀ rs isRec score receipt ent opp, P rs → rs.contradiction = false → receipt.score = score →
    P (kothCore c rs isRec score receipt ent opp)

/-- The lemma carries a record state satisfying `P`. -/
def HasRs (P : RecordState → Prop) (l : Lemma) : Prop := ∃ rs, l.recordState = .val rs ∧ P rs

theorem RecOutcome.preserves {c P} (hP : RsInvariant c P) {l e opp r} (ho : RecOutcome l e opp r)
    (hc : getRecordConfig l = c) (h : HasRs P l) : HasRs P r.lemma := by
  obtain ⟨rs0, h0, hp0⟩ := h
  cases ho with
  | refused => exact ⟨rs0, h0, hp0⟩
  | keep rs hh hrs =>
    rw [hrs] at h0; cases h0
    exact ⟨_, rfl, hP.keep _ _ hp0⟩
  | core rs score receipt ent hrs hcon hsc =>
    rw [hrs] at h0; cases h0
    exact ⟨_, rfl, hc ▸ hP.core _ _ _ _ _ _ hp0 hcon hsc⟩

theorem transitionRecord_preserves {c P} (hP : RsInvariant c P) (l : Lemma) (e : Event) (ctx : Ctx)
    (hc : getRecordConfig l = c) (h : HasRs P l) : HasRs P (transitionRecord l e ctx).lemma :=
  (transitionRecord_outcome l e ctx).preserves hP hc h

theorem transitionClaim_preserves {c P} (hP : RsInvariant c P) (l : Lemma) (e : Event) (ctx : Ctx)
    (hc : getRecordConfig l = c) (h : HasRs P l) : HasRs P (transitionClaim l e ctx).lemma := by
  rcases transitionClaim_cases l e ctx with ⟨hrs, _⟩ | ⟨_, _, _, heq⟩
  · obtain ⟨rs, h1, h2⟩ := h
    exact ⟨rs, hrs.trans h1, h2⟩
  · rw [heq]; exact transitionRecord_preserves hP l e ctx hc h

/-! ### The replay loop -/

theorem replayStep_lemma (env : ReplayEnv) (lp : Loop) (sub : Event) :
    (replayStep env lp sub).lemma = lp.lemma ∨
    (replayStep env lp sub).lemma = (transitionClaim lp.lemma sub (replayCtx env lp sub)).lemma := by
  unfold replayStep
  dsimp only
  repeat' split
  all_goals simp_all

theorem replayLoop_cons (env : ReplayEnv) (lp : Loop) (x : Event) (xs : List Event) :
    replayLoop env lp (x :: xs) = replayLoop env (replayStep env lp x) xs := rfl

theorem replayStep_frame (env : ReplayEnv) (lp : Loop) (sub : Event) :
    Frame lp.lemma (replayStep env lp sub).lemma := by
  rcases replayStep_lemma env lp sub with h | h <;> rw [h]
  · exact Frame.refl _
  · exact transitionClaim_frame _ _ _

theorem replayLoop_frame (env : ReplayEnv) (es : List Event) :
    ∀ lp, Frame lp.lemma (replayLoop env lp es).lemma := by
  induction es with
  | nil => intro lp; exact Frame.refl _
  | cons x xs ih =>
    intro lp
    rw [replayLoop_cons]
    exact (replayStep_frame env lp x).trans (ih _)

theorem replayStep_preserves {c P} (hP : RsInvariant c P) (env : ReplayEnv) (lp : Loop) (sub : Event)
    (hc : getRecordConfig lp.lemma = c) (h : HasRs P lp.lemma) : HasRs P (replayStep env lp sub).lemma := by
  rcases replayStep_lemma env lp sub with heq | heq <;> rw [heq]
  · exact h
  · exact transitionClaim_preserves hP _ _ _ hc h

theorem replayLoop_preserves {c P} (hP : RsInvariant c P) (env : ReplayEnv) (es : List Event) :
    ∀ lp, getRecordConfig lp.lemma = c → HasRs P lp.lemma → HasRs P (replayLoop env lp es).lemma := by
  induction es with
  | nil => intro lp _ h; exact h
  | cons x xs ih =>
    intro lp hc h
    rw [replayLoop_cons]
    exact ih _ ((getRecordConfig_congr (replayStep_frame env lp x)).trans hc)
      (replayStep_preserves hP env lp x hc h)

/-- The record state of the empty hunt. -/
def emptyRs (l : Lemma) : RecordState :=
  { direction := if (getRecordConfig l).isMax then "max" else "min", best := none, refuted := none
    nextTarget := some (getRecordConfig l).startTarget, closed := false, contradiction := false
    history := [], pointsBySeat := [] }

theorem emptyHunt_rs (l : Lemma) : (emptyHunt l).recordState = .val (emptyRs l) := rfl
theorem emptyHunt_frame (l : Lemma) : Frame l (emptyHunt l) := ⟨rfl, rfl, rfl⟩

theorem replayRecordSubmissions_eq (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int)) (h : Hashes) :
    replayRecordSubmissions slug l subs ts h =
      finalizeReplay l (replayLoop (replayEnv slug l ts h) ⟨emptyHunt l, [], none, none⟩
        (sortSubs ts (replayEnv slug l ts h).st subs)).lemma := rfl

/-- A replay-reachable property: it holds on the empty hunt, is an `RsInvariant`, and survives
the final `contradiction` override. -/
theorem replay_preserves {P} (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int)) (h : Hashes)
    (hP : RsInvariant (getRecordConfig l) P) (h0 : P (emptyRs l))
    (hfin : ∀ rs, P rs → P { rs with contradiction := true, closed := false, nextTarget := none, pointsBySeat := [] }) :
    HasRs P (replayRecordSubmissions slug l subs ts h) := by
  rw [replayRecordSubmissions_eq]
  have hl := replayLoop_preserves hP (replayEnv slug l ts h) (sortSubs ts (replayEnv slug l ts h).st subs)
    ⟨emptyHunt l, [], none, none⟩ rfl ⟨_, emptyHunt_rs l, h0⟩
  generalize (replayLoop _ _ _).lemma = fin at hl
  obtain ⟨rs, hrs, hp⟩ := hl
  unfold finalizeReplay
  split
  · exact ⟨_, by simp [hrs], hfin rs hp⟩
  · exact ⟨rs, hrs, hp⟩

theorem replay_frame (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int)) (h : Hashes) :
    Frame l (replayRecordSubmissions slug l subs ts h) := by
  rw [replayRecordSubmissions_eq]
  have := (emptyHunt_frame l).trans (replayLoop_frame (replayEnv slug l ts h) (sortSubs ts (replayEnv slug l ts h).st subs) ⟨emptyHunt l, [], none, none⟩)
  generalize (replayLoop _ _ _).lemma = fin at this
  unfold finalizeReplay
  split
  · exact ⟨this.record, this.id, this.kind⟩
  · exact this


/-! ## King-of-the-Hill: monotonicity -/

/-- `new` is at least as good a record as `old`: `≤` for `min`, `≥` for `max`. -/
def RecAtLeast (isMax : Bool) (new old : Int) : Prop := if isMax then old ≤ new else new ≤ old

/-- `new` is at least as strong a bound as `old`: `≥` for `min`, `≤` for `max`. -/
def BndAtLeast (isMax : Bool) (new old : Int) : Prop := if isMax then new ≤ old else old ≤ new

theorem kothCore_best (c rs isRec score receipt ent opp) :
    (kothCore c rs isRec score receipt ent opp).best =
      if isRec && kImproves c rs isRec score then some receipt else rs.best := rfl

theorem kothCore_refuted (c rs isRec score receipt ent opp) :
    (kothCore c rs isRec score receipt ent opp).refuted =
      if !isRec && kImproves c rs isRec score then
        some { receipt with inclusiveBound := some (max 0 (score - stepOf c.isMax)) }
      else rs.refuted := rfl

theorem kothCore_contradiction (c rs isRec score receipt ent opp) :
    (kothCore c rs isRec score receipt ent opp).contradiction = kContra c isRec score opp := rfl

theorem kothCore_pointsBySeat (c rs isRec score receipt ent opp) :
    (kothCore c rs isRec score receipt ent opp).pointsBySeat =
      if kContra c isRec score opp then []
      else if kImproves c rs isRec score then pbsAdd rs.pointsBySeat receipt.seat (kPoints c rs isRec score opp)
      else rs.pointsBySeat := rfl

theorem kothCore_closed (c rs isRec score receipt ent opp) :
    (kothCore c rs isRec score receipt ent opp).closed =
      (!kContra c isRec score opp &&
        closedFor (stepOf c.isMax) (kothCore c rs isRec score receipt ent opp).best
          (kothCore c rs isRec score receipt ent opp).refuted) := rfl

theorem kothCore_nextTarget (c rs isRec score receipt ent opp) :
    (kothCore c rs isRec score receipt ent opp).nextTarget =
      if (kothCore c rs isRec score receipt ent opp).closed || kContra c isRec score opp then none
      else match (kothCore c rs isRec score receipt ent opp).best with
        | some b => some (b.score + stepOf c.isMax)
        | none => some c.startTarget := rfl

/-- Invariant for theorem 1: the best record is at least as good as `b0`. -/
def BestAtLeast (c : RecCfg) (b0 : Int) (rs : RecordState) : Prop :=
  ∃ b, rs.best = some b ∧ RecAtLeast c.isMax b.score b0

theorem bestAtLeast_inv (c : RecCfg) (b0 : Int) : RsInvariant c (BestAtLeast c b0) where
  keep := fun _ _ h => h
  core := by
    intro rs isRec score receipt ent opp ⟨b, hb, hge⟩ _ hsc
    rw [BestAtLeast, kothCore_best]
    cases isRec
    · exact ⟨b, by simpa using hb, hge⟩
    · cases himp : kImproves c rs true score
      · exact ⟨b, by simpa using hb, hge⟩
      · refine ⟨receipt, by simp, ?_⟩
        simp only [kImproves, kMargin, kCur, kSgn, hb, ↓reduceIte, decide_eq_true_eq] at himp
        unfold RecAtLeast at hge ⊢
        cases hm : c.isMax <;> simp only [hm, stepOf, ↓reduceIte, Bool.false_eq_true] at himp hge ⊢ <;> omega

/-- Invariant for theorem 2: the strongest bound is at least as strong as `r0`. -/
def BoundAtLeast (c : RecCfg) (r0 : Int) (rs : RecordState) : Prop :=
  ∃ r, rs.refuted = some r ∧ BndAtLeast c.isMax r.score r0

theorem boundAtLeast_inv (c : RecCfg) (r0 : Int) : RsInvariant c (BoundAtLeast c r0) where
  keep := fun _ _ h => h
  core := by
    intro rs isRec score receipt ent opp ⟨r, hr, hge⟩ _ hsc
    rw [BoundAtLeast, kothCore_refuted]
    cases isRec
    · cases himp : kImproves c rs false score
      · exact ⟨r, by simpa using hr, hge⟩
      · refine ⟨{ receipt with inclusiveBound := some (max 0 (score - stepOf c.isMax)) }, by simp, ?_⟩
        simp only [kImproves, kMargin, kCur, kSgn, hr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at himp
        show BndAtLeast c.isMax receipt.score r0
        rw [hsc]
        unfold BndAtLeast at hge ⊢
        cases hm : c.isMax <;> simp only [hm, stepOf, ↓reduceIte, Bool.false_eq_true] at himp hge ⊢ <;> omega
    · exact ⟨r, by simpa using hr, hge⟩

/-- **Theorem 1 (step).** One `transitionRecord` step never worsens an existing best record. -/
theorem koth_monotone_best (l : Lemma) (e : Event) (ctx : Ctx) (rs : RecordState) (b : Receipt)
    (hrs : l.recordState = .val rs) (hb : rs.best = some b) :
    ∃ rs' b', (transitionRecord l e ctx).lemma.recordState = .val rs' ∧ rs'.best = some b' ∧
      RecAtLeast (getRecordConfig l).isMax b'.score b.score := by
  obtain ⟨rs', h1, b', h2, h3⟩ := transitionRecord_preserves (bestAtLeast_inv (getRecordConfig l) b.score) l e ctx rfl
    ⟨rs, hrs, b, hb, by unfold RecAtLeast; split <;> omega⟩
  exact ⟨rs', b', h1, h2, h3⟩

/-- **Theorem 1 (replay).** Over any list of submissions replayed from any state, the best record
never worsens. -/
theorem koth_monotone_best_replay (env : ReplayEnv) (es : List Event) (lp : Loop) (rs : RecordState) (b : Receipt)
    (hrs : lp.lemma.recordState = .val rs) (hb : rs.best = some b) :
    ∃ rs' b', (replayLoop env lp es).lemma.recordState = .val rs' ∧ rs'.best = some b' ∧
      RecAtLeast (getRecordConfig lp.lemma).isMax b'.score b.score := by
  obtain ⟨rs', h1, b', h2, h3⟩ := replayLoop_preserves (bestAtLeast_inv (getRecordConfig lp.lemma) b.score) env es lp rfl
    ⟨rs, hrs, b, hb, by unfold RecAtLeast; split <;> omega⟩
  exact ⟨rs', b', h1, h2, h3⟩

/-- **Theorem 2 (step).** One `transitionRecord` step never weakens an existing bound. -/
theorem koth_monotone_refuted (l : Lemma) (e : Event) (ctx : Ctx) (rs : RecordState) (r : Receipt)
    (hrs : l.recordState = .val rs) (hr : rs.refuted = some r) :
    ∃ rs' r', (transitionRecord l e ctx).lemma.recordState = .val rs' ∧ rs'.refuted = some r' ∧
      BndAtLeast (getRecordConfig l).isMax r'.score r.score := by
  obtain ⟨rs', h1, r', h2, h3⟩ := transitionRecord_preserves (boundAtLeast_inv (getRecordConfig l) r.score) l e ctx rfl
    ⟨rs, hrs, r, hr, by unfold BndAtLeast; split <;> omega⟩
  exact ⟨rs', r', h1, h2, h3⟩

/-- **Theorem 2 (replay).** Over any list of submissions replayed from any state, the strongest
bound never weakens. -/
theorem koth_monotone_refuted_replay (env : ReplayEnv) (es : List Event) (lp : Loop) (rs : RecordState) (r : Receipt)
    (hrs : lp.lemma.recordState = .val rs) (hr : rs.refuted = some r) :
    ∃ rs' r', (replayLoop env lp es).lemma.recordState = .val rs' ∧ rs'.refuted = some r' ∧
      BndAtLeast (getRecordConfig lp.lemma).isMax r'.score r.score := by
  obtain ⟨rs', h1, r', h2, h3⟩ := replayLoop_preserves (boundAtLeast_inv (getRecordConfig lp.lemma) r.score) env es lp rfl
    ⟨rs, hrs, r, hr, by unfold BndAtLeast; split <;> omega⟩
  exact ⟨rs', r', h1, h2, h3⟩

/-! ## King-of-the-Hill: anti-farming telescoping -/

theorem totalPoints_cons (k : String) (v : Int) (l : List (String × Int)) :
    totalPoints ((k, v) :: l) = v + totalPoints l := by simp [totalPoints]

theorem totalPoints_pbsSet (l : List (String × Int)) (k : String) (v : Int) :
    totalPoints (pbsSet l k v) = totalPoints l - pbsGet l k + v := by
  induction l with
  | nil => simp [pbsSet, pbsGet, alookup, totalPoints]
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k' = k
    · subst h; simp [pbsSet, pbsGet, alookup, totalPoints_cons]; omega
    · simp only [pbsSet, h, ↓reduceIte, totalPoints_cons, ih]
      simp only [pbsGet, alookup, h, ↓reduceIte]
      simp only [pbsGet] at ih
      omega

/-- Adding `p` points to one seat adds exactly `p` to the total. -/
theorem totalPoints_pbsAdd (l : List (String × Int)) (k : String) (p : Int) :
    totalPoints (pbsAdd l k p) = totalPoints l + p := by
  simp [pbsAdd, totalPoints_pbsSet]; omega

/-- Closed form of the points a record ledger has paid: `margin + 1` for the first record,
telescoped over every later improvement. -/
def recPts (c : RecCfg) : Option Receipt → Int
  | none => 0
  | some b => (b.score - c.startTarget) * stepOf c.isMax + 1

/-- Closed form of the points the bound ledger has paid. -/
def bndPts (c : RecCfg) : Option Receipt → Int
  | none => 0
  | some r => (r.score - c.boundFloor) * (-stepOf c.isMax) + 1

/-- The anti-farming ledger identity for a hunt that is not contradicted. -/
def PtsInv (c : RecCfg) (rs : RecordState) : Prop :=
  rs.contradiction = false → totalPoints rs.pointsBySeat = recPts c rs.best + bndPts c rs.refuted

theorem ptsInv_inv (c : RecCfg) : RsInvariant c (PtsInv c) where
  keep := fun _ _ h => h
  core := by
    intro rs isRec score receipt ent opp hinv hcon hsc hfin
    have hk : kContra c isRec score opp = false := by simpa [kothCore_contradiction] using hfin
    have htot := hinv hcon
    rw [kothCore_pointsBySeat, kothCore_best, kothCore_refuted, hk]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases himp : kImproves c rs isRec score
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false]; exact htot
    · simp only [↓reduceIte, totalPoints_pbsAdd, htot, kPoints, himp, hk, Bool.not_false, Bool.and_self]
      cases isRec
      · cases hr : rs.refuted <;>
          simp only [kImproves, kMargin, kCur, kSgn, kBase, hr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
            Option.isSome_none, Option.isSome_some, recPts, bndPts, hsc, Bool.not_false, Bool.and_true,
            Bool.not_true, Bool.false_and] at himp ⊢ <;>
          cases hm : c.isMax <;> simp only [hm, stepOf, ↓reduceIte, Bool.false_eq_true] <;> omega
      · cases hb : rs.best <;>
          simp only [kImproves, kMargin, kCur, kSgn, kBase, hb, ↓reduceIte, decide_eq_true_eq,
            Option.isSome_none, Option.isSome_some, recPts, bndPts, hsc, Bool.true_and, Bool.not_true,
            Bool.false_and, Bool.false_eq_true] at himp ⊢ <;>
          cases hm : c.isMax <;> simp only [hm, stepOf, ↓reduceIte, Bool.false_eq_true] <;> omega

theorem emptyRs_ptsInv (l : Lemma) : PtsInv (getRecordConfig l) (emptyRs l) := by
  intro _; simp [emptyRs, totalPoints, recPts, bndPts]

/-- **Theorem 3 (general ledger).** For any submission list replayed from the empty hunt, if the
hunt is not contradicted then the points paid to all seats sum to
`recPts best + bndPts refuted`, whatever the seats, scores, order and duplicates. -/
theorem koth_anti_farming_ledger (env : ReplayEnv) (l : Lemma) (es : List Event) :
    HasRs (PtsInv (getRecordConfig l)) (replayLoop env ⟨emptyHunt l, [], none, none⟩ es).lemma :=
  replayLoop_preserves (ptsInv_inv _) env es _ rfl ⟨_, emptyHunt_rs l, emptyRs_ptsInv l⟩


/-! ### Telescoping for record-only and bound-only replays -/

theorem replayStep_strongBnd_of_record (env : ReplayEnv) (lp : Loop) (sub : Event) (hk : sub.kind = .record) :
    (replayStep env lp sub).strongBnd = lp.strongBnd := by
  unfold replayStep; dsimp only
  repeat' split
  all_goals simp_all

theorem replayStep_strongRec_of_bound (env : ReplayEnv) (lp : Loop) (sub : Event) (hk : sub.kind = .record_bound) :
    (replayStep env lp sub).strongRec = lp.strongRec := by
  unfold replayStep; dsimp only
  repeat' split
  all_goals simp_all

theorem replayCtx_opp_record (env : ReplayEnv) (lp : Loop) (sub : Event) (hk : sub.kind = .record) :
    (replayCtx env lp sub).opposingScore = lp.strongBnd := by simp [replayCtx, hk]

theorem replayCtx_opp_bound (env : ReplayEnv) (lp : Loop) (sub : Event) (hk : sub.kind = .record_bound) :
    (replayCtx env lp sub).opposingScore = lp.strongRec := by simp [replayCtx, hk]

/-- A `transitionClaim` step with no opposing score never introduces a contradiction, and a
record (resp. bound) never touches `refuted` (resp. `best`). -/
theorem transitionClaim_no_opp (l : Lemma) (e : Event) (ctx : Ctx) (hopp : ctx.opposingScore = none)
    (P : RecordState → Prop)
    (hkeep : ∀ rs h, P rs → P { rs with history := rs.history ++ [h] })
    (hcore : ∀ rs score receipt ent, P rs → rs.contradiction = false →
      P (kothCore (getRecordConfig l) rs (e.kind == .record) score receipt ent none))
    (h : HasRs P l) : HasRs P (transitionClaim l e ctx).lemma := by
  obtain ⟨rs0, h0, hp0⟩ := h
  rcases transitionClaim_cases l e ctx with ⟨hrs, _⟩ | ⟨_, _, _, heq⟩
  · exact ⟨rs0, hrs.trans h0, hp0⟩
  · rw [heq]
    have ho := transitionRecord_outcome l e ctx
    rw [hopp] at ho
    generalize transitionRecord l e ctx = r at ho ⊢
    cases ho with
    | refused => exact ⟨rs0, h0, hp0⟩
    | keep rs hh hrs => rw [hrs] at h0; cases h0; exact ⟨_, rfl, hkeep _ _ hp0⟩
    | core rs score receipt ent hrs hcon _ => rw [hrs] at h0; cases h0; exact ⟨_, rfl, hcore _ _ _ _ hp0 hcon⟩

/-- Clean record-only state: no bound seen, not contradicted, no `refuted`. -/
def RecOnly (lp : Loop) : Prop :=
  lp.strongBnd = none ∧ HasRs (fun rs => rs.contradiction = false ∧ rs.refuted = none) lp.lemma

theorem replayStep_recOnly (env : ReplayEnv) (lp : Loop) (sub : Event) (hk : sub.kind = .record)
    (h : RecOnly lp) : RecOnly (replayStep env lp sub) := by
  refine ⟨(replayStep_strongBnd_of_record env lp sub hk).trans h.1, ?_⟩
  rcases replayStep_lemma env lp sub with heq | heq <;> rw [heq]
  · exact h.2
  · refine transitionClaim_no_opp _ _ _ ((replayCtx_opp_record env lp sub hk).trans h.1) _
      (fun _ _ hp => hp) ?_ h.2
    intro rs score receipt ent _ _
    simp [kothCore_contradiction, kothCore_refuted, kContra, hk, *]

/-- Clean bound-only state: no record seen, not contradicted, no `best`. -/
def BndOnly (lp : Loop) : Prop :=
  lp.strongRec = none ∧ HasRs (fun rs => rs.contradiction = false ∧ rs.best = none) lp.lemma

theorem replayStep_bndOnly (env : ReplayEnv) (lp : Loop) (sub : Event) (hk : sub.kind = .record_bound)
    (h : BndOnly lp) : BndOnly (replayStep env lp sub) := by
  refine ⟨(replayStep_strongRec_of_bound env lp sub hk).trans h.1, ?_⟩
  rcases replayStep_lemma env lp sub with heq | heq <;> rw [heq]
  · exact h.2
  · refine transitionClaim_no_opp _ _ _ ((replayCtx_opp_bound env lp sub hk).trans h.1) _
      (fun _ _ hp => hp) ?_ h.2
    intro rs score receipt ent _ _
    simp [kothCore_contradiction, kothCore_best, kContra, hk, *]

theorem replayLoop_induct (env : ReplayEnv) (Q : Loop → Prop) (R : Event → Prop)
    (hstep : ∀ lp sub, R sub → Q lp → Q (replayStep env lp sub)) :
    ∀ es lp, (∀ e ∈ es, R e) → Q lp → Q (replayLoop env lp es) := by
  intro es
  induction es with
  | nil => intro lp _ h; exact h
  | cons x xs ih =>
    intro lp hes h
    rw [replayLoop_cons]
    exact ih _ (fun e he => hes e (List.mem_cons_of_mem _ he)) (hstep _ _ (hes x (List.mem_cons_self ..)) h)

theorem hasRs_and {P Q : RecordState → Prop} {l : Lemma} (hp : HasRs P l) (hq : HasRs Q l) :
    HasRs (fun rs => P rs ∧ Q rs) l := by
  obtain ⟨rs, h1, h2⟩ := hp
  obtain ⟨rs', h1', h2'⟩ := hq
  rw [h1] at h1'; cases h1'
  exact ⟨rs, h1, h2, h2'⟩

/-- **Theorem 3 (`koth_anti_farming_record_points`).** Replay any finite list of `record`
submissions from the empty hunt. The hunt is never contradicted, and the points across all seats
sum to `0` if there is no best record, or to `(best - startTarget) * step + 1` otherwise,
which is the first-record `margin + 1` telescoped over every later improvement. Duplicates,
non-improving scores, stale receipts, and seat churn do not change the sum. -/
theorem koth_anti_farming_record_points (env : ReplayEnv) (l : Lemma) (es : List Event)
    (hes : ∀ e ∈ es, e.kind = .record) :
    ∃ rs, (replayLoop env ⟨emptyHunt l, [], none, none⟩ es).lemma.recordState = .val rs ∧
      rs.contradiction = false ∧ rs.refuted = none ∧
      totalPoints rs.pointsBySeat =
        match rs.best with
        | none => 0
        | some b => (b.score - (getRecordConfig l).startTarget) * stepOf (getRecordConfig l).isMax + 1 := by
  have h1 := replayLoop_induct env RecOnly (fun e => e.kind = .record)
    (fun lp sub hk h => replayStep_recOnly env lp sub hk h) es ⟨emptyHunt l, [], none, none⟩ hes ⟨rfl, emptyRs l, emptyHunt_rs l, rfl, rfl⟩
  obtain ⟨rs, hrs, ⟨hc, hr⟩, hp⟩ := hasRs_and h1.2 (koth_anti_farming_ledger env l es)
  refine ⟨rs, hrs, hc, hr, ?_⟩
  rw [hp hc, hr]
  cases rs.best <;> simp [recPts, bndPts]

/-- **Theorem 3' (`koth_anti_farming_bound_points`).** The same identity for `record_bound`
submissions: `0` with no bound, otherwise `(refuted - boundFloor) * (-step) + 1`. -/
theorem koth_anti_farming_bound_points (env : ReplayEnv) (l : Lemma) (es : List Event)
    (hes : ∀ e ∈ es, e.kind = .record_bound) :
    ∃ rs, (replayLoop env ⟨emptyHunt l, [], none, none⟩ es).lemma.recordState = .val rs ∧
      rs.contradiction = false ∧ rs.best = none ∧
      totalPoints rs.pointsBySeat =
        match rs.refuted with
        | none => 0
        | some r => (r.score - (getRecordConfig l).boundFloor) * (-stepOf (getRecordConfig l).isMax) + 1 := by
  have h1 := replayLoop_induct env BndOnly (fun e => e.kind = .record_bound)
    (fun lp sub hk h => replayStep_bndOnly env lp sub hk h) es ⟨emptyHunt l, [], none, none⟩ hes ⟨rfl, emptyRs l, emptyHunt_rs l, rfl, rfl⟩
  obtain ⟨rs, hrs, ⟨hc, hb⟩, hp⟩ := hasRs_and h1.2 (koth_anti_farming_ledger env l es)
  refine ⟨rs, hrs, hc, hb, ?_⟩
  rw [hp hc, hb]
  cases rs.refuted <;> simp [recPts, bndPts]

theorem mem_insertStable {α : Type} (lt : α → α → Bool) (x y : α) (l : List α) :
    x ∈ insertStable lt y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [insertStable]
  | cons z zs ih =>
    unfold insertStable
    split
    · simp
    · simp only [List.mem_cons, ih]
      exact or_left_comm

theorem mem_foldl_insertStable {α : Type} (lt : α → α → Bool) (l : List α) :
    ∀ (acc : List α) x, x ∈ l.foldl (fun acc y => insertStable lt y acc) acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    intro acc x
    simp only [List.foldl_cons, ih, mem_insertStable, List.mem_cons]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]

/-- The replay sort is a permutation: it neither drops nor invents submissions. -/
theorem mem_sortSubs (ts : List (String × Int)) (st : Int) (subs : List Event) (x : Event) :
    x ∈ sortSubs ts st subs ↔ x ∈ subs := by
  simp [sortSubs, sortStable, mem_foldl_insertStable]

/-- **Theorem 3 for `replayRecordSubmissions`.** The full replay of record-only submissions,
including the sort and the final override, pays `0` for a hunt whose input status was
`contradiction`, and otherwise exactly the telescoped margin. -/
theorem koth_anti_farming_record_points_replay (slug : JStr) (l : Lemma) (subs : List Event)
    (ts : List (String × Int)) (h : Hashes) (hs : ∀ e ∈ subs, e.kind = .record) :
    ∃ rs, (replayRecordSubmissions slug l subs ts h).recordState = .val rs ∧ rs.refuted = none ∧
      totalPoints rs.pointsBySeat =
        if l.status = .contradiction then 0
        else match rs.best with
          | none => 0
          | some b => (b.score - (getRecordConfig l).startTarget) * stepOf (getRecordConfig l).isMax + 1 := by
  rw [replayRecordSubmissions_eq]
  obtain ⟨rs, hrs, hc, hr, hp⟩ := koth_anti_farming_record_points (replayEnv slug l ts h) l
    (sortSubs ts (replayEnv slug l ts h).st subs) (fun e he => hs e ((mem_sortSubs _ _ _ _).1 he))
  generalize (replayLoop _ _ _).lemma = fin at hrs
  unfold finalizeReplay
  by_cases hst : l.status = .contradiction
  · simp [hst, rsContra, hrs, hc, hr, totalPoints]
  · simp [hst, hrs, hr, hp]

/-! ## King-of-the-Hill: contradiction is sticky -/

/-- A contradicted hunt: flagged, not closed, no target, empty ledger. -/
def Sticky (rs : RecordState) : Prop :=
  rs.contradiction = true ∧ rs.closed = false ∧ rs.nextTarget = none ∧ rs.pointsBySeat = []

theorem sticky_inv (c : RecCfg) : RsInvariant c Sticky where
  keep := fun _ _ h => h
  core := by intro rs _ _ _ _ _ h hc _; rw [h.1] at hc; cases hc

/-- `transitionClaim` on a contradicted claim, outside the record replay path. Every
non-`audit` event is refused and leaves the lemma unchanged. An `audit` can only rewrite
`lemma.audit`. -/
theorem transitionClaim_contradicted (l : Lemma) (e : Event) (ctx : Ctx)
    (hc : l.status = .contradiction ∨ rsContra l = true)
    (hk : e.kind.isRecordEvent = true → ctx.mode = .replay → isRecordLemma l = true → False) :
    (e.kind ≠ .audit → (transitionClaim l e ctx).ok = false ∧ (transitionClaim l e ctx).lemma = l) ∧
    ((transitionClaim l e ctx).lemma = l ∨ (transitionClaim l e ctx).lemma = { l with audit := e.audit }) := by
  have hcb : (l.status == Status.contradiction || rsContra l) = true := by
    rcases hc with h | h <;> simp [h]
  cases hkd : e.kind <;>
    simp only [hkd, EvKind.isRecordEvent, forall_const, true_implies] at hk <;>
    simp only [transitionClaim, hkd, hcb, EvKind.isRecordEvent, Bool.false_and, Bool.true_and, reduceCtorEq,
      false_and, ↓reduceIte, Bool.false_eq_true, bne_self_eq_false, Bool.and_false, Bool.and_true,
      bne_iff_ne, ne_eq, not_false_eq_true, decide_true, decide_false, Bool.not_true, Bool.not_false, true_and,
      and_true, and_false, Bool.true_or, denyMsg, not_true_eq_false, false_implies]
  all_goals repeat' split
  all_goals first
    | (simp; done)
    | (simp_all; done)
    | (exfalso; simp_all)

/-- On the record replay path `transitionClaim` is `transitionRecord`, unless bounds are disabled. -/
theorem transitionClaim_replay_record (l : Lemma) (e : Event) (ctx : Ctx) (hk : e.kind.isRecordEvent = true)
    (hm : ctx.mode = .replay) (hl : isRecordLemma l = true) :
    transitionClaim l e ctx = transitionRecord l e ctx ∨
    (transitionClaim l e ctx).ok = false ∧ (transitionClaim l e ctx).lemma = l := by
  cases hkd : e.kind <;> simp only [hkd, EvKind.isRecordEvent, Bool.false_eq_true] at hk <;>
    simp only [transitionClaim, hkd, hl, hm, EvKind.isRecordEvent, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, reduceCtorEq, false_and, Bool.true_and, beq_self_eq_true, true_and, denyMsg]
  · exact .inl trivial
  · by_cases hab : allowBoundFalse l = true
    · exact .inr (by simp [hab])
    · exact .inl (by simp [hab])

/-- **Theorem 4 (step).** On a contradicted hunt, any event in any mode keeps
`contradiction = true`, `closed = false`, `next_target = none` and an empty ledger. It never
changes `status` or `claimed_by`. -/
theorem koth_contradiction_sticky_step (l : Lemma) (e : Event) (ctx : Ctx) (h : HasRs Sticky l) :
    HasRs Sticky (transitionClaim l e ctx).lemma ∧
    (transitionClaim l e ctx).lemma.status = l.status ∧
    (transitionClaim l e ctx).lemma.claimedBy = l.claimedBy := by
  refine ⟨transitionClaim_preserves (sticky_inv _) l e ctx rfl h, ?_⟩
  obtain ⟨rs, hrs, hst⟩ := h
  have hrc : rsContra l = true := by simp [rsContra, hrs, hst.1]
  by_cases hk : e.kind.isRecordEvent = true ∧ ctx.mode = .replay ∧ isRecordLemma l = true
  · obtain ⟨hk1, hk2, hk3⟩ := hk
    rcases transitionClaim_replay_record l e ctx hk1 hk2 hk3 with heq | heq
    · rw [heq]
      have ho := transitionRecord_outcome l e ctx
      generalize transitionRecord l e ctx = r at ho ⊢
      cases ho with
      | refused => exact ⟨rfl, rfl⟩
      | keep => exact ⟨rfl, rfl⟩
      | core rs' _ _ _ hrs' hcon _ => rw [hrs] at hrs'; cases hrs'; rw [hst.1] at hcon; cases hcon
    · rw [heq.2]; exact ⟨rfl, rfl⟩
  · have := (transitionClaim_contradicted l e ctx (.inr hrc) (fun a b c => hk ⟨a, b, c⟩)).2
    rcases this with h1 | h1 <;> rw [h1] <;> exact ⟨rfl, rfl⟩

/-- **Theorem 4 (replay).** Once a hunt is contradicted, any further list of submissions
leaves it contradicted, not closed, with no next target and zero points, and never changes
`status` or `claimed_by`. -/
theorem koth_contradiction_sticky (env : ReplayEnv) (es : List Event) :
    ∀ lp, HasRs Sticky lp.lemma →
      HasRs Sticky (replayLoop env lp es).lemma ∧
      (replayLoop env lp es).lemma.status = lp.lemma.status ∧
      (replayLoop env lp es).lemma.claimedBy = lp.lemma.claimedBy ∧
      ∀ rs, (replayLoop env lp es).lemma.recordState = .val rs → totalPoints rs.pointsBySeat = 0 := by
  induction es with
  | nil =>
    intro lp h
    refine ⟨h, rfl, rfl, ?_⟩
    obtain ⟨rs, hrs, hs⟩ := h
    intro rs' hrs'
    change lp.lemma.recordState = _ at hrs'
    rw [hrs] at hrs'; cases hrs'; simp [hs.2.2.2, totalPoints]
  | cons x xs ih =>
    intro lp h
    rw [replayLoop_cons]
    have hstep : HasRs Sticky (replayStep env lp x).lemma ∧ (replayStep env lp x).lemma.status = lp.lemma.status ∧
        (replayStep env lp x).lemma.claimedBy = lp.lemma.claimedBy := by
      rcases replayStep_lemma env lp x with heq | heq <;> rw [heq]
      · exact ⟨h, rfl, rfl⟩
      · exact koth_contradiction_sticky_step _ _ _ h
    obtain ⟨h1, h2, h3, h4⟩ := ih _ hstep.1
    exact ⟨h1, h2.trans hstep.2.1, h3.trans hstep.2.2, h4⟩

/-- Every reachable contradicted hunt is `Sticky`. -/
def ContraInv (rs : RecordState) : Prop := rs.contradiction = true → Sticky rs

theorem contraInv_inv (c : RecCfg) : RsInvariant c ContraInv where
  keep := fun _ _ h => h
  core := by
    intro rs isRec score receipt ent opp _ _ _ hc
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [kothCore_closed]; simp [kothCore_contradiction] at hc; simp [hc]
    · rw [kothCore_nextTarget]; simp [kothCore_contradiction] at hc; simp [hc]
    · rw [kothCore_pointsBySeat]; simp [kothCore_contradiction] at hc; simp [hc]

/-- **Theorem 4 (reachability).** In every replay from the empty hunt, every prefix that reaches
a contradiction is `Sticky`, so `koth_contradiction_sticky` applies to it. -/
theorem koth_contradiction_reachable (env : ReplayEnv) (l : Lemma) (es : List Event) :
    HasRs ContraInv (replayLoop env ⟨emptyHunt l, [], none, none⟩ es).lemma :=
  replayLoop_preserves (contraInv_inv (getRecordConfig l)) env es _ rfl
    ⟨_, emptyHunt_rs l, fun h => by simp [emptyRs] at h⟩

/-- The final output of `replayRecordSubmissions` satisfies `ContraInv`. -/
theorem koth_contradiction_replay (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int)) (h : Hashes) :
    HasRs ContraInv (replayRecordSubmissions slug l subs ts h) :=
  replay_preserves slug l subs ts h (contraInv_inv _) (fun h => by simp [emptyRs] at h)
    (fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩)

/-! ## King-of-the-Hill: closed hunts are exactly optimal -/

/-- A closed hunt is not contradicted and has no next target. Its best record is `0` in a
`min` hunt, or it is matched by a bound exactly one step beyond it. -/
def ClosedInv (c : RecCfg) (rs : RecordState) : Prop :=
  rs.closed = true → rs.contradiction = false ∧ rs.nextTarget = none ∧
    ∃ b, rs.best = some b ∧
      ((c.isMax = false ∧ b.score = 0) ∨ ∃ r, rs.refuted = some r ∧ r.score = b.score + stepOf c.isMax)

theorem closedFor_spec (st : Int) (best refuted : Option Receipt) (h : closedFor st best refuted = true) :
    ∃ b, best = some b ∧ ((st = -1 ∧ b.score = 0) ∨ ∃ r, refuted = some r ∧ r.score = b.score + st) := by
  unfold closedFor at h
  cases best with
  | none => simp at h
  | some b =>
    refine ⟨b, rfl, ?_⟩
    cases refuted with
    | none => simp at h; exact .inl h
    | some r =>
      simp at h
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨r, rfl, h⟩

theorem closedInv_inv (c : RecCfg) : RsInvariant c (ClosedInv c) where
  keep := fun _ _ h => h
  core := by
    intro rs isRec score receipt ent opp _ _ _ hcl
    have hcl' := hcl
    rw [kothCore_closed] at hcl'
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcl'
    obtain ⟨hk, hcf⟩ := hcl'
    refine ⟨by rw [kothCore_contradiction]; exact hk, by rw [kothCore_nextTarget, hcl]; simp, ?_⟩
    obtain ⟨b, hb, hor⟩ := closedFor_spec _ _ _ hcf
    refine ⟨b, hb, ?_⟩
    rcases hor with ⟨hst, h0⟩ | hr
    · left; refine ⟨?_, h0⟩; cases hm : c.isMax <;> simp_all [stepOf]
    · exact .inr hr

/-- **Theorem 6.** Every `replayRecordSubmissions` output that is `closed` is not contradicted
and has no next target. Its best record `b` is `0` in a `min` hunt, or the hunt holds a
verified bound at exactly `b + step`. -/
theorem koth_closed_exact_optimal (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int)) (h : Hashes) :
    HasRs (ClosedInv (getRecordConfig l)) (replayRecordSubmissions slug l subs ts h) :=
  replay_preserves slug l subs ts h (closedInv_inv _) (fun h => by simp [emptyRs] at h)
    (fun _ _ h => by simp at h)

/-- **Theorem 6 (preflight).** A closed hunt refuses `claim` in every mode, and refuses
`record` and `record_bound` outside replay. -/
theorem koth_closed_denies (l : Lemma) (e : Event) (ctx : Ctx) (hcl : rsClosed l = true)
    (hk : e.kind = .claim ∨ ((e.kind = .record ∨ e.kind = .record_bound) ∧ ctx.mode ≠ .replay)) :
    (transitionClaim l e ctx).ok = false ∧ (transitionClaim l e ctx).lemma = l := by
  have hcases : e.kind.isRecordEvent = false ∨ ctx.mode ≠ .replay := by
    rcases hk with hk | ⟨hk | hk, hm⟩
    · exact .inl (by simp [hk, EvKind.isRecordEvent])
    · exact .inr hm
    · exact .inr hm
  have hm' : (e.kind.isRecordEvent && ctx.mode == Mode.replay) = false := by
    rcases hcases with h | h <;> simp [h]
  unfold transitionClaim denyMsg
  simp only [hm', hcl, Bool.false_eq_true, ↓reduceIte, Bool.or_true, Bool.true_or]
  rcases hk with hk | ⟨hk | hk, _⟩ <;> simp only [hk, EvKind.isRecordEvent, Bool.false_and, Bool.true_and,
    reduceCtorEq, false_and, ↓reduceIte, Bool.false_eq_true, Bool.or_true, Bool.true_or]
  all_goals repeat' split
  all_goals simp_all

/-! ## Standard claims -/

/-- **Theorem 7 (`claim_contradiction_sticky`, step).** On a standard claim with
`status = contradiction`, every non-`audit` event in every mode is refused and leaves the claim
unchanged. An `audit` never changes `status`. -/
theorem claim_contradiction_sticky_step (l : Lemma) (e : Event) (ctx : Ctx)
    (hstd : isRecordLemma l = false) (hc : l.status = .contradiction) :
    (e.kind ≠ .audit → (transitionClaim l e ctx).ok = false ∧ (transitionClaim l e ctx).lemma = l) ∧
    (transitionClaim l e ctx).lemma.status = .contradiction := by
  have hcb : (l.status == Status.contradiction || rsContra l) = true := by simp [hc]
  cases hkd : e.kind <;>
    simp only [transitionClaim, hkd, hcb, hstd, hc, EvKind.isRecordEvent, Bool.false_and, Bool.true_and, reduceCtorEq,
      false_and, ↓reduceIte, Bool.false_eq_true, bne_self_eq_false, Bool.and_false, Bool.and_true,
      bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false, true_and, and_true, Bool.true_or, denyMsg,
      not_true_eq_false, false_implies, Bool.not_true, imp_self, implies_true]
  all_goals repeat' split
  all_goals simp_all

/-- **Theorem 7 (`claim_contradiction_sticky`).** Fold any list of `(event, ctx)` steps over a
standard claim with `status = contradiction`: the status never leaves `contradiction`. -/
theorem claim_contradiction_sticky (steps : List (Event × Ctx)) :
    ∀ l : Lemma, isRecordLemma l = false → l.status = .contradiction →
      (steps.foldl (fun cur s => (transitionClaim cur s.1 s.2).lemma) l).status = .contradiction := by
  induction steps with
  | nil => intro l _ hc; exact hc
  | cons s rest ih =>
    intro l hstd hc
    simp only [List.foldl_cons]
    refine ih _ ?_ (claim_contradiction_sticky_step l s.1 s.2 hstd hc).2
    rw [isRecordLemma_congr (transitionClaim_frame _ _ _)]; exact hstd

/-- A verified `proof` event. -/
def VerifiedProof (e : Event) : Prop := e.kind = .proof ∧ eventCheckerOk e = true

/-- A verified `refutation` event. -/
def VerifiedRefutation (e : Event) : Prop := e.kind = .refutation ∧ e.refutation.present = true

/-- Shared assumptions: a standard claim that is not contradicted, outside preflight. -/
structure Writable (l : Lemma) (ctx : Ctx) : Prop where
  std : isRecordLemma l = false
  notContra : l.status ≠ .contradiction
  rsOk : rsContra l = false
  mode : ctx.mode ≠ .preflight

theorem transitionClaim_verdict (l : Lemma) (e : Event) (ctx : Ctx) (hw : Writable l ctx)
    (hk : e.kind = .proof ∨ e.kind = .refutation) :
    transitionClaim l e ctx = transitionVerdict l e ctx := by
  have hcb : (l.status == Status.contradiction || rsContra l) = false := by
    simp [hw.rsOk, hw.notContra]
  rcases hk with hk | hk <;>
    simp only [transitionClaim, hk, hcb, hw.std, EvKind.isRecordEvent, Bool.false_and, reduceCtorEq, ↓reduceIte,
      Bool.false_eq_true, false_and, bne_self_eq_false, Bool.and_false, Bool.true_and, Bool.and_self, Bool.not_true]

/-- After a verified proof, a standard claim is `checked`-like (verified checker or `checked`
status) or already contradicted with no owner. -/
theorem after_proof (l : Lemma) (p : Event) (ctx : Ctx) (hw : Writable l ctx) (hp : VerifiedProof p) :
    let l1 := (transitionClaim l p ctx).lemma
    isRecordLemma l1 = false ∧ rsContra l1 = false ∧
    ((l1.status = .contradiction ∧ l1.claimedBy = .null) ∨
     (l1.status ≠ .contradiction ∧ (checkerOk l1 = true ∨ l1.status = .checked))) := by
  intro l1
  have hfr := transitionClaim_frame l p ctx
  refine ⟨(isRecordLemma_congr hfr).trans hw.std, ?_, ?_⟩
  · rcases transitionClaim_cases l p ctx with ⟨hrs, _⟩ | ⟨hk, _⟩
    · simp only [l1, rsContra, hrs]; exact hw.rsOk
    · simp [hp.1, EvKind.isRecordEvent] at hk
  · simp only [l1, transitionClaim_verdict l p ctx hw (.inl hp.1)]
    unfold transitionVerdict denyMsg
    have hm := hw.mode
    have hnc := hw.notContra
    have hok := hp.2
    simp only [hp.1, beq_self_eq_true, ↓reduceIte, hm, Bool.not_true, Bool.true_and, Bool.false_eq_true]
    simp only [eventCheckerOk] at hok
    repeat' split
    all_goals simp_all [checkerOk, eventCheckerOk]

/-- After a verified refutation, a standard claim is `refuted`-like or already contradicted
with no owner. -/
theorem after_refutation (l : Lemma) (r : Event) (ctx : Ctx) (hw : Writable l ctx) (hr : VerifiedRefutation r) :
    let l1 := (transitionClaim l r ctx).lemma
    isRecordLemma l1 = false ∧ rsContra l1 = false ∧
    ((l1.status = .contradiction ∧ l1.claimedBy = .null) ∨
     (l1.status ≠ .contradiction ∧ (hasRefutation l1 = true ∨ l1.status = .refuted))) := by
  intro l1
  have hfr := transitionClaim_frame l r ctx
  refine ⟨(isRecordLemma_congr hfr).trans hw.std, ?_, ?_⟩
  · rcases transitionClaim_cases l r ctx with ⟨hrs, _⟩ | ⟨hk, _⟩
    · simp only [l1, rsContra, hrs]; exact hw.rsOk
    · simp [hr.1, EvKind.isRecordEvent] at hk
  · simp only [l1, transitionClaim_verdict l r ctx hw (.inr hr.1)]
    unfold transitionVerdict denyMsg
    have hm := hw.mode
    have hnc := hw.notContra
    have hok := hr.2
    simp only [hr.1, reduceCtorEq, beq_iff_eq, ↓reduceIte, hm, Bool.false_eq_true]
    repeat' split
    all_goals simp_all [hasRefutation, JOpt.present]

/-- The opposite verdict on a claim holding one verdict is a contradiction with no owner. -/
theorem second_verdict (l : Lemma) (e : Event) (ctx : Ctx) (hmode : ctx.mode ≠ .preflight)
    (hstd : isRecordLemma l = false) (hrc : rsContra l = false)
    (he : e.kind = .proof ∨ e.kind = .refutation)
    (h : (l.status = .contradiction ∧ l.claimedBy = .null) ∨
         (l.status ≠ .contradiction ∧
          ((VerifiedRefutation e ∧ (checkerOk l = true ∨ l.status = .checked)) ∨
           (VerifiedProof e ∧ (hasRefutation l = true ∨ l.status = .refuted))))) :
    (transitionClaim l e ctx).lemma.status = .contradiction ∧ (transitionClaim l e ctx).lemma.claimedBy = .null := by
  rcases h with ⟨hc, hcb⟩ | ⟨hnc, hcase⟩
  · have hk : e.kind ≠ .audit := by rcases he with h | h <;> simp [h]
    rw [((claim_contradiction_sticky_step l e ctx hstd hc).1 hk).2]
    exact ⟨hc, hcb⟩
  · have hw : Writable l ctx := ⟨hstd, hnc, hrc, hmode⟩
    rw [transitionClaim_verdict l e ctx hw he]
    unfold transitionVerdict denyMsg
    rcases hcase with ⟨⟨hk, hv⟩, hcon⟩ | ⟨⟨hk, hv⟩, hcon⟩
    · simp only [hk, reduceCtorEq, beq_iff_eq, ↓reduceIte, hmode, Bool.false_eq_true, hv, Bool.not_true]
      have hconf : (l.status == Status.checked || checkerOk l) = true := by
        rcases hcon with h | h <;> simp [h]
      simp only [hconf, Bool.not_true, Bool.and_false, ↓reduceIte, Bool.false_eq_true]
      repeat' split
      all_goals simp_all
    · simp only [hk, beq_self_eq_true, ↓reduceIte, hmode, Bool.false_eq_true, Bool.not_true]
      simp only [VerifiedProof, eventCheckerOk] at hv
      have hconf : (l.status == Status.refuted || hasRefutation l) = true := by
        rcases hcon with h | h <;> simp [h]
      simp only [hconf, Bool.not_true, Bool.and_false, ↓reduceIte, Bool.false_eq_true]
      repeat' split
      all_goals simp_all [eventCheckerOk]

/-- **Theorem 8 (`claim_order_independent_contradiction`).** For a standard claim that is not
contradicted, a verified proof followed by a verified refutation, and the reverse order, both
end in `status = contradiction` with `claimed_by = null`. This holds in writeback (`ctx = {}`),
replay, and any other non-preflight mode, whatever the claim's earlier status, receipts and
owner. -/
theorem claim_order_independent_contradiction (l : Lemma) (p r : Event) (ctx : Ctx)
    (hstd : isRecordLemma l = false) (hnc : l.status ≠ .contradiction) (hrc : rsContra l = false)
    (hmode : ctx.mode ≠ .preflight) (hp : VerifiedProof p) (hr : VerifiedRefutation r) :
    let pr := (transitionClaim (transitionClaim l p ctx).lemma r ctx).lemma
    let rp := (transitionClaim (transitionClaim l r ctx).lemma p ctx).lemma
    pr.status = .contradiction ∧ pr.claimedBy = .null ∧ rp.status = .contradiction ∧ rp.claimedBy = .null := by
  intro pr rp
  have hw : Writable l ctx := ⟨hstd, hnc, hrc, hmode⟩
  obtain ⟨s1, r1, c1⟩ := after_proof l p ctx hw hp
  obtain ⟨s2, r2, c2⟩ := after_refutation l r ctx hw hr
  have h1 := second_verdict _ r ctx hmode s1 r1 (.inr hr.1) (by
    rcases c1 with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, .inl ⟨hr, h2⟩⟩)
  have h2 := second_verdict _ p ctx hmode s2 r2 (.inl hp.1) (by
    rcases c2 with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, .inr ⟨hp, h2⟩⟩)
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- **Theorem 9 (`barrier_never_overwrites_verdict`).** `rule_dead` is refused, and the claim
left unchanged, whenever `status ∈ {checked, refuted, contradiction}`. This holds in every mode,
for standard claims and record hunts. -/
theorem barrier_never_overwrites_verdict (l : Lemma) (e : Event) (ctx : Ctx) (hk : e.kind = .rule_dead)
    (hs : l.status = .checked ∨ l.status = .refuted ∨ l.status = .contradiction) :
    (transitionClaim l e ctx).ok = false ∧ (transitionClaim l e ctx).lemma = l := by
  simp only [transitionClaim, hk, EvKind.isRecordEvent, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq, false_and, denyMsg]
  repeat' split
  all_goals simp_all

/-! ## Trust seal and rung conquest -/

/-- **Theorem 11a.** `computeTrustSeal` is `contradiction` exactly when the claim's status is
`contradiction` or its record state is contradicted. -/
theorem trust_seal_contradiction_iff (l : Lemma) :
    computeTrustSeal l = .contradiction ↔ (l.status = .contradiction ∨ rsContra l = true) := by
  constructor
  · intro h
    by_cases hc : l.status = .contradiction ∨ rsContra l = true
    · exact hc
    · exfalso
      revert h
      unfold computeTrustSeal
      dsimp only
      simp only [hc, ↓reduceIte]
      repeat' split
      all_goals simp
  · intro h; simp [computeTrustSeal, h]

/-- **Theorem 11b.** A rung whose seal is `contradiction` or `flagged` is never conquered, for
any `expect`. -/
theorem conquered_false_of_bad_seal (l : Lemma) (ex : Expect)
    (h : computeTrustSeal l = .contradiction ∨ computeTrustSeal l = .flagged) :
    isRungConquered (some l) ex = false := by
  unfold isRungConquered
  rcases h with h | h <;> simp [h]

/-- A missing lemma is never conquered. -/
theorem conquered_none (ex : Expect) : isRungConquered none ex = false := rfl

/-- Record hunts are never `flagged`. -/
theorem record_seal_not_flagged (l : Lemma) (hl : isRecordLemma l = true) : computeTrustSeal l ≠ .flagged := by
  unfold computeTrustSeal
  dsimp only
  simp only [hl, ↓reduceIte]
  repeat' split
  all_goals simp

/-- **Theorem 11c.** For a record hunt under the default `expect` (`"proof"`), and equally
`"record_closed"` or `null`, the rung is conquered exactly when the hunt is closed, its record
state is not contradicted, and its status is not `contradiction`. -/
theorem conquered_record_default (l : Lemma) (rs : RecordState) (hl : isRecordLemma l = true)
    (hrs : l.recordState = .val rs) (ex : Expect) (hex : ex = .str "proof" ∨ ex = .str "record_closed" ∨ ex = .null) :
    isRungConquered (some l) ex = (rs.closed && !rs.contradiction && l.status != .contradiction) := by
  have hnf := record_seal_not_flagged l hl
  unfold isRungConquered
  simp only [hnf, false_or, hl, ↓reduceIte, hrs]
  by_cases hsc : computeTrustSeal l = .contradiction
  · have := (trust_seal_contradiction_iff l).1 hsc
    simp only [rsContra, hrs] at this
    rcases this with h | h <;> simp [hsc, h]
  · have := mt (trust_seal_contradiction_iff l).2 hsc
    simp only [rsContra, hrs, not_or] at this
    obtain ⟨h1, h2⟩ := this
    rcases hex with rfl | rfl | rfl <;> simp [hsc, h1, h2]

/-- `status = contradiction` implies a contradicted record state. -/
def StatusInv (l : Lemma) : Prop := l.status = .contradiction → rsContra l = true

/-- On a record hunt, every `transitionClaim` outcome outside the record replay path keeps the
status or sets it to `in_work`. -/
theorem transitionClaim_record_status (l : Lemma) (e : Event) (ctx : Ctx) (hl : isRecordLemma l = true) :
    (transitionClaim l e ctx).lemma.status = l.status ∨ (transitionClaim l e ctx).lemma.status = .in_work ∨
    transitionClaim l e ctx = transitionRecord l e ctx := by
  cases hkd : e.kind <;>
    simp only [transitionClaim, hkd, hl, EvKind.isRecordEvent, Bool.false_and, Bool.true_and, reduceCtorEq,
      false_and, ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.and_false, denyMsg]
  all_goals repeat' split
  all_goals simp_all

theorem transitionClaim_statusInv (l : Lemma) (e : Event) (ctx : Ctx) (hl : isRecordLemma l = true)
    (h : StatusInv l) : StatusInv (transitionClaim l e ctx).lemma := by
  rcases transitionClaim_record_status l e ctx hl with hs | hs | heq
  · intro hc
    rcases transitionClaim_cases l e ctx with ⟨hrs, _⟩ | ⟨_, _, _, heq⟩
    · simp only [rsContra, hrs]; exact h (hs ▸ hc)
    · have ho := transitionRecord_outcome l e ctx
      rw [heq] at hc hs ⊢
      generalize transitionRecord l e ctx = r at ho hc hs ⊢
      cases ho with
      | refused => exact h hc
      | keep rs hh hrs => have := h (by simpa [keepLemma] using hc); simpa [rsContra, keepLemma, hrs] using this
      | core rs score receipt ent hrs hcon _ =>
        have := h (by simpa using hs.symm.trans hc)
        simp [rsContra, hrs, hcon] at this
  · intro hc; rw [hs] at hc; cases hc
  · rw [heq]
    intro hc
    have ho := transitionRecord_outcome l e ctx
    generalize transitionRecord l e ctx = r at ho hc ⊢
    cases ho with
    | refused => exact h hc
    | keep rs hh hrs => have := h (by simpa [keepLemma] using hc); simpa [rsContra, keepLemma, hrs] using this
    | core rs score receipt ent hrs hcon _ =>
      simp only [coreLemma] at hc ⊢
      simp only [rsContra]
      split at hc
      · assumption
      · split at hc
        · cases hc
        · have := h hc; simp [rsContra, hrs, hcon] at this

theorem replayLoop_statusInv (env : ReplayEnv) (es : List Event) :
    ∀ lp, isRecordLemma lp.lemma = true → StatusInv lp.lemma → StatusInv (replayLoop env lp es).lemma := by
  induction es with
  | nil => intro lp _ h; exact h
  | cons x xs ih =>
    intro lp hl h
    rw [replayLoop_cons]
    apply ih
    · rw [isRecordLemma_congr (replayStep_frame env lp x)]; exact hl
    · rcases replayStep_lemma env lp x with heq | heq <;> rw [heq]
      · exact h
      · exact transitionClaim_statusInv _ _ _ hl h

/-- **Theorem 11d.** Every record hunt produced by `replayRecordSubmissions` is conquered under
the default `expect` exactly when it is closed and not contradicted. -/
theorem conquered_replay_default (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int))
    (h : Hashes) (hl : isRecordLemma l = true) :
    ∃ rs, (replayRecordSubmissions slug l subs ts h).recordState = .val rs ∧
      (isRungConquered (some (replayRecordSubmissions slug l subs ts h)) (.str "proof") = true ↔
        rs.closed = true ∧ rs.contradiction = false) := by
  have htriv : RsInvariant (getRecordConfig l) (fun _ => True) := ⟨fun _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ => trivial⟩
  have hsi : StatusInv (replayRecordSubmissions slug l subs ts h) := by
    rw [replayRecordSubmissions_eq]
    have hloop := replayLoop_statusInv (replayEnv slug l ts h) (sortSubs ts (replayEnv slug l ts h).st subs)
      ⟨emptyHunt l, [], none, none⟩ hl (by
        intro hc
        simp only [emptyHunt] at hc
        split at hc
        · rename_i ho; rw [hc] at ho; simp [Status.isOpen] at ho
        · cases hc)
    have hrs0 := replayLoop_preserves htriv (replayEnv slug l ts h) (sortSubs ts (replayEnv slug l ts h).st subs)
      ⟨emptyHunt l, [], none, none⟩ rfl ⟨_, emptyHunt_rs l, trivial⟩
    generalize (replayLoop _ _ _).lemma = fin at hloop hrs0
    obtain ⟨rsf, hrsf, _⟩ := hrs0
    unfold finalizeReplay
    split
    · intro _; simp [rsContra, hrsf]
    · exact hloop
  obtain ⟨rs, hrs, _⟩ := replay_preserves slug l subs ts h htriv trivial (fun _ _ => trivial)
  refine ⟨rs, hrs, ?_⟩
  have hl' : isRecordLemma (replayRecordSubmissions slug l subs ts h) = true := by
    rw [isRecordLemma_congr (replay_frame slug l subs ts h)]; exact hl
  rw [conquered_record_default _ rs hl' hrs _ (.inl rfl)]
  have : (replayRecordSubmissions slug l subs ts h).status = .contradiction → rs.contradiction = true := by
    intro hc; have := hsi hc; simpa [rsContra, hrs] using this
  by_cases hc : (replayRecordSubmissions slug l subs ts h).status = .contradiction
  · have := this hc; simp [hc, this]
  · cases rs.closed <;> cases rs.contradiction <;> simp [hc]

/-! ## King-of-the-Hill: order-independent contradiction -/

/-- The submission is valid, canonical and fresh: `transitionRecord` takes its main branch under
the replay environment `env`, with score `score`. -/
def Accepts (env : ReplayEnv) (l : Lemma) (e : Event) (score : Int) : Prop :=
  validScore (getRecordConfig l).scoreMax e.score = some score ∧
  ∃ chk, e.checker = .val chk ∧ chk.ok = true ∧
    ((jtruthy e.subFile && e.subFile != .val (computeRecordTargets env.slug l e.kind score).submissionBasename) ||
      e.file != .val (computeRecordTargets env.slug l e.kind score).artifactFile ||
      e.thm != .val (computeRecordTargets env.slug l e.kind score).theoremName) = false ∧
    jtruthy env.statementHash = true ∧ chk.statementHash = env.statementHash ∧
    jtruthy env.coreHash = true ∧ jtruthy chk.coreHash = true

theorem Accepts.congr {env : ReplayEnv} {l l' : Lemma} {e : Event} {score : Int} (hf : Frame l l')
    (h : Accepts env l e score) : Accepts env l' e score := by
  unfold Accepts at *
  simp only [getRecordConfig_congr hf, computeRecordTargets_congr hf]
  exact h

theorem validScore_jsNumber {m : Int} {s : ScoreIn} {n : Int} (h : validScore m s = some n) : jsNumber s = some n := by
  unfold validScore at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem transitionRecord_accept (env : ReplayEnv) (l : Lemma) (e : Event) (ctx : Ctx) (score : Int) (rs : RecordState)
    (hslug : ctx.missionSlug = env.slug) (hsh : ctx.statementHash = env.statementHash) (hch : ctx.coreHash = env.coreHash)
    (hacc : Accepts env l e score) (hrs : l.recordState = .val rs) (hc : rs.contradiction = false) :
    ∃ receipt ent, receipt.score = score ∧
      transitionRecord l e ctx =
        ⟨true, coreLemma l (kothCore (getRecordConfig l) rs (e.kind == .record) score receipt ent ctx.opposingScore), ""⟩ := by
  obtain ⟨hv, chk, hchk, hok, hcanon, h1, h2, h3, h4⟩ := hacc
  unfold transitionRecord
  simp only [hv, hchk, hok, ↓reduceIte, hslug, hcanon, Bool.false_eq_true, hrs, hsh, hch, h1, h2, h3, h4, hc,
    Bool.not_true, bne_self_eq_false, Bool.or_false, Bool.false_or]
  exact ⟨_, _, rfl, rfl⟩

theorem transitionClaim_replay_record_eq (l : Lemma) (e : Event) (ctx : Ctx) (hk : e.kind.isRecordEvent = true)
    (hm : ctx.mode = .replay) (hl : isRecordLemma l = true) (hab : allowBoundFalse l = false) :
    transitionClaim l e ctx = transitionRecord l e ctx := by
  rcases transitionClaim_replay_record l e ctx hk hm hl with h | ⟨_, _⟩
  · exact h
  · cases hkd : e.kind <;> simp only [hkd, EvKind.isRecordEvent, Bool.false_eq_true] at hk <;>
      simp [transitionClaim, hkd, hl, hm, hab, EvKind.isRecordEvent]

theorem lastStale_coreLemma (l : Lemma) (c : RecCfg) (rs : RecordState) (isRec : Bool) (score : Int)
    (receipt : Receipt) (ent : HistEntry) (opp : Option Int) :
    lastStale (coreLemma l (kothCore c rs isRec score receipt ent opp)) = false := by
  simp only [lastStale, coreLemma, kothCore, List.getLast?_append, List.getLast?_singleton, Option.some_or]
  split <;> (try split) <;> simp

/-- One replay step on an accepted submission. -/
theorem replayStep_accept (env : ReplayEnv) (lp : Loop) (sub : Event) (score : Int) (rs : RecordState)
    (hnew : ¬(jtruthy sub.subFile = true ∧ render sub.subFile ∈ lp.seen))
    (hk : sub.kind = .record ∨ sub.kind = .record_bound)
    (hl : isRecordLemma lp.lemma = true) (hab : allowBoundFalse lp.lemma = false)
    (hacc : Accepts env lp.lemma sub score) (hrs : lp.lemma.recordState = .val rs) (hc : rs.contradiction = false) :
    ∃ receipt ent, receipt.score = score ∧
      (replayStep env lp sub).lemma =
        coreLemma lp.lemma (kothCore (getRecordConfig lp.lemma) rs (sub.kind == .record) score receipt ent
          (if sub.kind = .record then lp.strongBnd else lp.strongRec)) ∧
      (replayStep env lp sub).seen = (if jtruthy sub.subFile then render sub.subFile :: lp.seen else lp.seen) ∧
      (sub.kind = .record → lp.strongRec = none →
        (replayStep env lp sub).strongRec = some score ∧ (replayStep env lp sub).strongBnd = lp.strongBnd) ∧
      (sub.kind = .record_bound → lp.strongBnd = none →
        (replayStep env lp sub).strongBnd = some score ∧ (replayStep env lp sub).strongRec = lp.strongRec) := by
  have hrk : sub.kind.isRecordEvent = true := by rcases hk with h | h <;> simp [h, EvKind.isRecordEvent]
  have htc := transitionClaim_replay_record_eq lp.lemma sub (replayCtx env lp sub) hrk rfl hl hab
  obtain ⟨receipt, ent, hsc, htr⟩ := transitionRecord_accept env lp.lemma sub (replayCtx env lp sub) score rs
    rfl rfl rfl hacc hrs hc
  have hnum := validScore_jsNumber hacc.1
  refine ⟨receipt, ent, hsc, ?_⟩
  unfold replayStep
  simp only [hnew, ↓reduceIte, htc, htr, Bool.not_true, Bool.false_eq_true, lastStale_coreLemma, hnum,
    Option.getD_some]
  rcases hk with hk | hk <;> simp [hk, replayCtx] <;> intro h1 <;> simp [h1]

theorem sortSubs_pair (ts : List (String × Int)) (st : Int) (a b : Event) :
    sortSubs ts st [a, b] = [a, b] ∨ sortSubs ts st [a, b] = [b, a] := by
  simp only [sortSubs, sortStable, List.foldl_cons, List.foldl_nil, insertStable]
  split
  · exact .inr rfl
  · exact .inl rfl

theorem canonical_subFile {sf : JStr} {B : String} {rest : Bool}
    (h : ((jtruthy sf && sf != .val B) || rest) = false) (ht : jtruthy sf = true) : render sf = B := by
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_imp, ht, true_implies, bne_eq_false_iff_eq] at h
  rw [h.1]; rfl

theorem basename_ne (slug : JStr) (l : Lemma) (r b : Int) :
    (computeRecordTargets slug l .record r).submissionBasename ≠
      (computeRecordTargets slug l .record_bound b).submissionBasename := by
  simp only [computeRecordTargets, EvKind.name]
  intro h
  have := congrArg String.toList h
  have e1 : ∀ s : String, toString s = s := fun _ => rfl
  simp only [String.toList_append, e1, List.append_assoc, List.append_cancel_left_eq] at this
  simp at this

/-- Two accepted submissions of opposite kinds, replayed in the order `x` then `y`, where
`y`'s score crosses `x`'s. -/
theorem replay_two_crossing (env : ReplayEnv) (l : Lemma) (x y : Event) (sx sy : Int)
    (hl : isRecordLemma l = true) (hab : allowBoundFalse l = false)
    (hkx : x.kind = .record ∨ x.kind = .record_bound) (hky : y.kind = .record ∨ y.kind = .record_bound)
    (hxy : x.kind ≠ y.kind)
    (hx : Accepts env l x sx) (hy : Accepts env l y sy)
    (hdist : jtruthy x.subFile = true → jtruthy y.subFile = true → render x.subFile ≠ render y.subFile)
    (hcross : kContra (getRecordConfig l) (y.kind == .record) sy (some sx) = true) :
    ∃ rs, (replayLoop env ⟨emptyHunt l, [], none, none⟩ [x, y]).lemma.recordState = .val rs ∧ Sticky rs ∧
      (replayLoop env ⟨emptyHunt l, [], none, none⟩ [x, y]).lemma.status = .contradiction ∧
      (replayLoop env ⟨emptyHunt l, [], none, none⟩ [x, y]).lemma.claimedBy = .null := by
  have hf0 := emptyHunt_frame l
  rw [show replayLoop env ⟨emptyHunt l, [], none, none⟩ [x, y] =
    replayStep env (replayStep env ⟨emptyHunt l, [], none, none⟩ x) y from rfl]
  obtain ⟨rc1, en1, _, hl1, hseen1, hsR, hsB⟩ := replayStep_accept env ⟨emptyHunt l, [], none, none⟩ x sx (emptyRs l)
    (by simp) hkx hl hab (hx.congr hf0) (emptyHunt_rs l) rfl
  have hf1 : Frame l (replayStep env ⟨emptyHunt l, [], none, none⟩ x).lemma :=
    hf0.trans (replayStep_frame env ⟨emptyHunt l, [], none, none⟩ x)
  have hopp1 : (if x.kind = .record then (none : Option Int) else none) = none := by split <;> rfl
  simp only [hopp1] at hl1
  have hc1 : (kothCore (getRecordConfig (emptyHunt l)) (emptyRs l) (x.kind == .record) sx rc1 en1 none).contradiction
      = false := by simp [kothCore_contradiction, kContra]
  generalize kothCore (getRecordConfig (emptyHunt l)) (emptyRs l) (x.kind == .record) sx rc1 en1 none = rs1 at hl1 hc1
  generalize replayStep env ⟨emptyHunt l, [], none, none⟩ x = lp1 at hl1 hseen1 hsR hsB hf1 ⊢
  have hrs1v : lp1.lemma.recordState = .val rs1 := by rw [hl1]; rfl
  have hopp2 : (if y.kind = .record then lp1.strongBnd else lp1.strongRec) = some sx := by
    rcases hkx with hk | hk <;> rcases hky with hk' | hk'
    · exact absurd (hk.trans hk'.symm) hxy
    · simp [hk', (hsR hk rfl).1]
    · simp [hk', (hsB hk rfl).1]
    · exact absurd (hk.trans hk'.symm) hxy
  have hnew2 : ¬(jtruthy y.subFile = true ∧ render y.subFile ∈ lp1.seen) := by
    rw [hseen1]
    rintro ⟨hty, hmem⟩
    split at hmem
    · rename_i htx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      exact hdist htx hty hmem.symm
    · simp at hmem
  obtain ⟨rc2, en2, hsc2, hl2, _, _, _⟩ := replayStep_accept env lp1 y sy rs1 hnew2 hky
    ((isRecordLemma_congr hf1).trans hl) ((allowBoundFalse_congr hf1).trans hab) (hy.congr hf1) hrs1v hc1
  rw [hopp2, getRecordConfig_congr hf1] at hl2
  have hc2 : (kothCore (getRecordConfig l) rs1 (y.kind == .record) sy rc2 en2 (some sx)).contradiction = true := by
    rw [kothCore_contradiction]; exact hcross
  have hst2 := (contraInv_inv (getRecordConfig l)).core rs1 (y.kind == .record) sy rc2 en2 (some sx)
    (fun h => by rw [hc1] at h; cases h) hc1 hsc2 hc2
  rw [hl2]
  exact ⟨_, rfl, hst2, by simp [coreLemma, hc2], by simp [coreLemma, hc2]⟩

/-- **Theorem 5 (`koth_contradiction_order_independent`).** Take a valid, canonical, fresh
`record` at score `r` and `record_bound` at score `b` that cross (`min`: `r ≤ b`, `max`:
`r ≥ b`). Replaying `[rec, bnd]` or `[bnd, rec]`, under any git timestamps, ends in
`contradiction = true`, `closed = false`, zero points, `status = contradiction` and
`claimed_by = null`. -/
theorem koth_contradiction_order_independent (slug : JStr) (l : Lemma) (ts : List (String × Int)) (h : Hashes)
    (rec bnd : Event) (r b : Int)
    (hl : isRecordLemma l = true) (hab : allowBoundFalse l = false)
    (hrk : rec.kind = .record) (hbk : bnd.kind = .record_bound)
    (hr : Accepts (replayEnv slug l ts h) l rec r) (hb : Accepts (replayEnv slug l ts h) l bnd b)
    (hcross : if (getRecordConfig l).isMax then b ≤ r else r ≤ b) :
    ∀ subs, (subs = [rec, bnd] ∨ subs = [bnd, rec]) →
      ∃ rs, (replayRecordSubmissions slug l subs ts h).recordState = .val rs ∧
        rs.contradiction = true ∧ rs.closed = false ∧ totalPoints rs.pointsBySeat = 0 ∧
        (replayRecordSubmissions slug l subs ts h).status = .contradiction ∧
        (replayRecordSubmissions slug l subs ts h).claimedBy = .null := by
  have hdist : jtruthy rec.subFile = true → jtruthy bnd.subFile = true → render rec.subFile ≠ render bnd.subFile := by
    intro h1 h2
    rw [canonical_subFile (by have := hr.2; obtain ⟨_, _, _, hc, _⟩ := this; rw [Bool.or_assoc] at hc; exact hc) h1,
      canonical_subFile (by have := hb.2; obtain ⟨_, _, _, hc, _⟩ := this; rw [Bool.or_assoc] at hc; exact hc) h2,
      hrk, hbk]
    exact basename_ne _ _ _ _
  have hRB := replay_two_crossing (replayEnv slug l ts h) l rec bnd r b hl hab (.inl hrk) (.inr hbk)
    (by rw [hrk, hbk]; simp) hr hb hdist (by
      simp only [kContra, hbk, kSgn, reduceCtorEq, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
      cases hm : (getRecordConfig l).isMax <;> simp only [hm, stepOf, ↓reduceIte, Bool.false_eq_true] at hcross ⊢ <;> omega)
  have hBR := replay_two_crossing (replayEnv slug l ts h) l bnd rec b r hl hab (.inr hbk) (.inl hrk)
    (by rw [hrk, hbk]; simp) hb hr (fun a c d => hdist c a d.symm) (by
      simp only [kContra, hrk, kSgn, beq_self_eq_true, ↓reduceIte, decide_eq_true_eq]
      cases hm : (getRecordConfig l).isMax <;> simp only [hm, stepOf, ↓reduceIte, Bool.false_eq_true] at hcross ⊢ <;> omega)
  intro subs hsubs
  have key : ∀ fin : Lemma, (∃ rs, fin.recordState = .val rs ∧ Sticky rs ∧ fin.status = .contradiction ∧
      fin.claimedBy = .null) →
      ∃ rs, (finalizeReplay l fin).recordState = .val rs ∧
        rs.contradiction = true ∧ rs.closed = false ∧ totalPoints rs.pointsBySeat = 0 ∧
        (finalizeReplay l fin).status = .contradiction ∧ (finalizeReplay l fin).claimedBy = .null := by
    rintro fin ⟨rs, hrs, hst, hs, hcb⟩
    have hfin : finalizeReplay l fin = fin := by unfold finalizeReplay; simp [rsContra, hrs, hst.1]
    rw [hfin]
    exact ⟨rs, hrs, hst.1, hst.2.1, by simp [hst.2.2.2, totalPoints], hs, hcb⟩
  rw [replayRecordSubmissions_eq]
  rcases hsubs with rfl | rfl
  · rcases sortSubs_pair ts (replayEnv slug l ts h).st rec bnd with hs | hs <;> rw [hs]
    · exact key _ hRB
    · exact key _ hBR
  · rcases sortSubs_pair ts (replayEnv slug l ts h).st bnd rec with hs | hs <;> rw [hs]
    · exact key _ hBR
    · exact key _ hRB

/-! ## Seat ownership: the seat–claim bijection -/

/-- Seat–claim bijection over any number of seats and claims. Ids are unique, every seat pointer
names a claim owned by that seat, and every owner names a seat that points back. -/
structure Bij (st : State) : Prop where
  seatsNodup : (st.seats.map (·.id)).Nodup
  lemmasNodup : (st.lemmas.map (·.id)).Nodup
  seatToLemma : ∀ s ∈ st.seats, ∀ c, s.current = .val c → ∃ l ∈ st.lemmas, l.id = c ∧ l.claimedBy = .val s.id
  lemmaToSeat : ∀ l ∈ st.lemmas, ∀ sid, l.claimedBy = .val sid → ∃ s ∈ st.seats, s.id = sid ∧ s.current = .val l.id

theorem nodup_map_inj {α β : Type} {f : α → β} : ∀ {xs : List α}, (xs.map f).Nodup →
    ∀ {a b}, a ∈ xs → b ∈ xs → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: xs, hnd, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hnd⟩ := hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (List.mem_map.2 ⟨b, hb, hab.symm⟩) hx
    · exact absurd (List.mem_map.2 ⟨a, ha, hab⟩) hx
    · exact nodup_map_inj hnd ha hb hab

/-- **Theorem 10 (`seat_claim_bijection`).** Under `Bij`, a seat points at a claim exactly when
that claim is owned by that seat. -/
theorem Bij.iff {st : State} (hb : Bij st) : ∀ s ∈ st.seats, ∀ l ∈ st.lemmas,
    s.current = .val l.id ↔ l.claimedBy = .val s.id := by
  intro s hs l hl
  constructor
  · intro hc
    obtain ⟨l', hl', hid, hcb⟩ := hb.seatToLemma s hs _ hc
    rw [nodup_map_inj hb.lemmasNodup hl hl' hid.symm]; exact hcb
  · intro hc
    obtain ⟨s', hs', hid, hcur⟩ := hb.lemmaToSeat l hl _ hc
    rw [nodup_map_inj hb.seatsNodup hs hs' hid.symm]; exact hcur

/-- **Theorem 10 (`single_owner`).** Under `Bij`, no two seats point at the same claim. -/
theorem Bij.single_owner {st : State} (hb : Bij st) {s1 s2 : Seat} (h1 : s1 ∈ st.seats) (h2 : s2 ∈ st.seats)
    {c : String} (hc1 : s1.current = .val c) (hc2 : s2.current = .val c) : s1 = s2 := by
  obtain ⟨l1, hl1, hid1, hcb1⟩ := hb.seatToLemma s1 h1 c hc1
  obtain ⟨l2, hl2, hid2, hcb2⟩ := hb.seatToLemma s2 h2 c hc2
  have := nodup_map_inj hb.lemmasNodup hl1 hl2 (hid1.trans hid2.symm)
  subst this
  rw [hcb1] at hcb2
  exact nodup_map_inj hb.seatsNodup h1 h2 (JOpt.val.inj hcb2)

theorem modifyFirst_eq_map {sid : String} {f : Seat → Seat} :
    ∀ {xs : List Seat}, (xs.map (·.id)).Nodup →
      modifyFirst (fun s => s.id == sid) f xs = xs.map (fun s => if s.id = sid then f s else s)
  | [], _ => rfl
  | x :: xs, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [modifyFirst, List.map_cons]
    by_cases hx : x.id = sid
    · simp only [hx, beq_self_eq_true, ↓reduceIte, List.cons.injEq, true_and]
      refine (List.map_id xs).symm.trans (List.map_congr_left ?_)
      intro a ha
      have : a.id ≠ sid := fun h => hnd.1 (List.mem_map.2 ⟨a, ha, h.trans hx.symm⟩)
      simp [this]
    · simp only [hx, ↓reduceIte, beq_iff_eq, List.cons.injEq, true_and]
      exact modifyFirst_eq_map hnd.2

/-- The seat map applied by `releaseSeatClaim st sid`. -/
def releaseSeats (sid : String) (seats : List Seat) : List Seat :=
  seats.map (fun s => if s.id = sid then idleSeat s else s)

theorem releaseSeats_ids (sid : String) (seats : List Seat) :
    (releaseSeats sid seats).map (·.id) = seats.map (·.id) := by
  simp only [releaseSeats, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  split <;> rfl

theorem releaseLemma_id (seat : Seat) (sid : String) (seats : List Seat) (l : Lemma) :
    (releaseLemma seat sid seats l).id = l.id := by
  unfold releaseLemma; split <;> rfl

/-- Shape of a successful `releaseSeatClaim`. -/
theorem releaseSeatClaim_ok {st st' : State} {sid : String} (hnd : (st.seats.map (·.id)).Nodup)
    (h : releaseSeatClaim st sid = .ok st') :
    ∃ seat, seat ∈ st.seats ∧ seat.id = sid ∧
      st'.seats = releaseSeats sid st.seats ∧
      st'.lemmas = st.lemmas.map (releaseLemma seat sid (releaseSeats sid st.seats)) := by
  unfold releaseSeatClaim at h
  split at h
  · cases h
  · rename_i seat hseat
    cases h
    refine ⟨seat, List.mem_of_find?_eq_some hseat, by simpa using List.find?_some hseat, ?_, ?_⟩
    · exact modifyFirst_eq_map hnd
    · simp only [modifyFirst_eq_map hnd]; rfl

theorem mem_releaseSeats {sid : String} {seats : List Seat} {s' : Seat} (h : s' ∈ releaseSeats sid seats) :
    ∃ s ∈ seats, s'.id = s.id ∧ ((s.id = sid ∧ s'.current = .null) ∨ (s.id ≠ sid ∧ s' = s)) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
  refine ⟨s, hs, ?_⟩
  by_cases hid : s.id = sid
  · simp [hid, idleSeat]
  · simp [hid]

theorem self_mem_releaseSeats {sid : String} {seats : List Seat} {s : Seat} (hs : s ∈ seats) (hid : s.id ≠ sid) :
    s ∈ releaseSeats sid seats :=
  List.mem_map.2 ⟨s, hs, by simp [hid]⟩

/-- **Theorem 10 (`releaseSeatClaim`).** Releasing a seat preserves the bijection. -/
theorem seat_claim_bijection_release {st st' : State} {sid : String} (hb : Bij st)
    (h : releaseSeatClaim st sid = .ok st') : Bij st' := by
  obtain ⟨seat, hseat, hsid, hseats, hlemmas⟩ := releaseSeatClaim_ok hb.seatsNodup h
  have hids : st'.seats.map (·.id) = st.seats.map (·.id) := by rw [hseats, releaseSeats_ids]
  refine ⟨hids ▸ hb.seatsNodup, ?_, ?_, ?_⟩
  · rw [hlemmas, List.map_map]
    have : ((·.id) ∘ releaseLemma seat sid (releaseSeats sid st.seats)) = (·.id) := by
      funext l; exact releaseLemma_id _ _ _ l
    rw [this]; exact hb.lemmasNodup
  · intro s' hs' c hc
    rw [hseats] at hs'
    obtain ⟨s, hs, hidss, hcase⟩ := mem_releaseSeats hs'
    rcases hcase with ⟨_, hnull⟩ | ⟨hne, rfl⟩
    · rw [hnull] at hc; cases hc
    · obtain ⟨l, hl, hlid, hlcb⟩ := hb.seatToLemma s' hs c hc
      refine ⟨_, by rw [hlemmas]; exact List.mem_map.2 ⟨l, hl, rfl⟩, by rw [releaseLemma_id]; exact hlid, ?_⟩
      unfold releaseLemma
      split
      · exact hlcb
      · have hmem : s' ∈ releaseSeats sid st.seats := self_mem_releaseSeats hs hne
        have hsome : (List.find? (fun s => s.current == JOpt.val l.id) (releaseSeats sid st.seats)).isSome := by
          rw [List.find?_isSome]; exact ⟨s', hmem, by simp [hc, hlid]⟩
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hsome
        simp only [ho]
        have hoc : o.current = .val l.id := by simpa using List.find?_some ho
        obtain ⟨o0, ho0, hoid, hocase⟩ := mem_releaseSeats (List.mem_of_find?_eq_some ho)
        rcases hocase with ⟨_, hnull⟩ | ⟨_, rfl⟩
        · rw [hnull] at hoc; cases hoc
        · rw [hb.single_owner ho0 hs (hoc.trans (by rw [hlid])) hc]
  · intro l' hl' x hx
    rw [hlemmas] at hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    rw [releaseLemma_id]
    unfold releaseLemma at hx
    split at hx
    · rename_i hcond
      obtain ⟨s, hs, hsx, hcur⟩ := hb.lemmaToSeat l hl x hx
      have hne : s.id ≠ sid := by
        intro heq
        have := nodup_map_inj hb.seatsNodup hs hseat (heq.trans hsid.symm)
        subst this
        exact hcond.1 hcur
      exact ⟨s, by rw [hseats]; exact self_mem_releaseSeats hs hne, hsx, hcur⟩
    · simp only at hx
      split at hx
      · rename_i o ho
        cases hx
        exact ⟨o, by rw [hseats]; exact List.mem_of_find?_eq_some ho, rfl, by simpa using List.find?_some ho⟩
      · cases hx


theorem releaseSeatClaim_ids {st st' : State} {sid : String} (hb : Bij st) (h : releaseSeatClaim st sid = .ok st') :
    st'.seats.map (·.id) = st.seats.map (·.id) ∧ st'.lemmas.map (·.id) = st.lemmas.map (·.id) := by
  obtain ⟨seat, _, _, hseats, hlemmas⟩ := releaseSeatClaim_ok hb.seatsNodup h
  refine ⟨by rw [hseats, releaseSeats_ids], ?_⟩
  rw [hlemmas, List.map_map]
  apply List.map_congr_left
  intro l _; exact releaseLemma_id _ _ _ l

theorem releaseSeatClaim_seat_mem {st st' : State} {sid : String} (hb : Bij st) (h : releaseSeatClaim st sid = .ok st') :
    ∀ s' ∈ st'.seats, ∃ s ∈ st.seats, s'.id = s.id ∧ ((s.id = sid ∧ s'.current = .null) ∨ (s.id ≠ sid ∧ s' = s)) := by
  obtain ⟨seat, _, _, hseats, _⟩ := releaseSeatClaim_ok hb.seatsNodup h
  intro s' hs'; rw [hseats] at hs'; exact mem_releaseSeats hs'

theorem foldlM_except_induct {α β ε : Type} (f : β → α → Except ε β) (Q : List α → β → Prop)
    (hstep : ∀ x xs b b', Q (x :: xs) b → f b x = .ok b' → Q xs b') :
    ∀ (xs : List α) (b r : β), Q xs b → xs.foldlM f b = .ok r → Q [] r := by
  intro xs
  induction xs with
  | nil =>
    intro b r hq h
    simp only [List.foldlM_nil] at h
    cases h; exact hq
  | cons x xs ih =>
    intro b r hq h
    rw [List.foldlM_cons] at h
    cases hfx : f b x with
    | error e => rw [hfx] at h; cases h
    | ok b' =>
      rw [hfx] at h
      exact ih b' r (hstep x xs b b' hq hfx) h

/-- Everything `releaseClaimSeats` guarantees. -/
structure ReleasedClaim (st0 : State) (lid : String) (st : State) : Prop where
  bij : Bij st
  seatIds : st.seats.map (·.id) = st0.seats.map (·.id)
  lemmaIds : st.lemmas.map (·.id) = st0.lemmas.map (·.id)
  noPtr : ∀ s ∈ st.seats, s.current ≠ .val lid
  keepsFree : ∀ sid, (∀ s ∈ st0.seats, s.id = sid → s.current = .null) → ∀ s ∈ st.seats, s.id = sid → s.current = .null

theorem releaseClaimSeats_spec {st st' : State} {lid : String} (hb : Bij st)
    (h : releaseClaimSeats st lid = .ok st') : ReleasedClaim st lid st' := by
  let Q : List Seat → State → Prop := fun R acc =>
    Bij acc ∧ acc.seats.map (·.id) = st.seats.map (·.id) ∧ acc.lemmas.map (·.id) = st.lemmas.map (·.id) ∧
    (∀ s ∈ acc.seats, s.current = .val lid → ∃ y ∈ R, y.id = s.id ∧ y.current = .val lid) ∧
    (∀ sid, (∀ s ∈ st.seats, s.id = sid → s.current = .null) → ∀ s ∈ acc.seats, s.id = sid → s.current = .null)
  have hfin := foldlM_except_induct _ Q (by
    intro x xs acc acc' ⟨hbj, hsi, hli, hptr, hfree⟩ hstep
    split at hstep
    · rename_i hx
      have hb' := seat_claim_bijection_release hbj hstep
      obtain ⟨hs1, hl1⟩ := releaseSeatClaim_ids hbj hstep
      have hmem := releaseSeatClaim_seat_mem hbj hstep
      refine ⟨hb', hs1.trans hsi, hl1.trans hli, ?_, ?_⟩
      · intro s' hs' hc'
        obtain ⟨s, hs, hid, hcase⟩ := hmem s' hs'
        rcases hcase with ⟨_, hnull⟩ | ⟨hne, rfl⟩
        · rw [hnull] at hc'; cases hc'
        · obtain ⟨y, hy, hyid, hyc⟩ := hptr s' hs hc'
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact absurd hyid.symm hne
          · exact ⟨y, hy, hyid, hyc⟩
      · intro sid hsid s' hs' hsid'
        obtain ⟨s, hs, hid, hcase⟩ := hmem s' hs'
        rcases hcase with ⟨_, hnull⟩ | ⟨_, rfl⟩
        · exact hnull
        · exact hfree sid hsid s' hs hsid'
    · rename_i hx
      cases hstep
      refine ⟨hbj, hsi, hli, ?_, hfree⟩
      intro s hs hc
      obtain ⟨y, hy, hyid, hyc⟩ := hptr s hs hc
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact absurd hyc hx
      · exact ⟨y, hy, hyid, hyc⟩) st.seats st st'
    ⟨hb, rfl, rfl, fun s hs hc => ⟨s, hs, rfl, hc⟩, fun _ _ s hs hid => by simp_all⟩ h
  obtain ⟨hbj, hsi, hli, hptr, hfree⟩ := hfin
  refine ⟨hbj, hsi, hli, ?_, hfree⟩
  intro s hs hc
  obtain ⟨y, hy, _⟩ := hptr s hs hc
  cases hy

/-- **Theorem 10 (`releaseClaimSeats`).** Releasing every seat on a claim preserves the
bijection, and afterwards no seat points at that claim. -/
theorem seat_claim_bijection_releaseClaim {st st' : State} {lid : String} (hb : Bij st)
    (h : releaseClaimSeats st lid = .ok st') : Bij st' ∧ ∀ s ∈ st'.seats, s.current ≠ .val lid :=
  let r := releaseClaimSeats_spec hb h
  ⟨r.bij, r.noPtr⟩

theorem transitionClaim_claim_ok (l : Lemma) (sid : String)
    (hok : (transitionClaim l { kind := .claim, seat := .val sid } {}).ok = true) :
    (transitionClaim l { kind := .claim, seat := .val sid } {}).lemma.id = l.id ∧
    (transitionClaim l { kind := .claim, seat := .val sid } {}).lemma.claimedBy = .val sid := by
  revert hok
  simp only [transitionClaim, EvKind.isRecordEvent, Bool.false_and, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
    false_and, denyMsg]
  repeat' split
  all_goals simp_all

theorem mem_ids {xs : List Seat} {x : String} : x ∈ xs.map (·.id) ↔ ∃ s ∈ xs, s.id = x := by
  simp [List.mem_map]

theorem mem_lemma_ids {xs : List Lemma} {x : String} : x ∈ xs.map (·.id) ↔ ∃ l ∈ xs, l.id = x := by
  simp [List.mem_map]

/-- **Theorem 10 (`assignSeatClaim`).** A successful assignment preserves the bijection, and
afterwards seat `sid` points at claim `lid`, which `sid` owns. -/
theorem seat_claim_bijection_assign {st st' : State} {sid lid : String} (hb : Bij st)
    (h : assignSeatClaim st sid lid = .ok st') :
    Bij st' ∧ (∃ s ∈ st'.seats, s.id = sid ∧ s.current = .val lid) ∧
      ∃ l ∈ st'.lemmas, l.id = lid ∧ l.claimedBy = .val sid := by
  unfold assignSeatClaim at h
  split at h
  · cases h
  rename_i lemma hlem
  have hlemmem := List.mem_of_find?_eq_some hlem
  have hlemid : lemma.id = lid := by simpa using List.find?_some hlem
  dsimp only at h
  split at h
  · cases h
  rename_i hok
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hok
  obtain ⟨hrid, hrcb⟩ := transitionClaim_claim_ok lemma sid hok
  generalize transitionClaim lemma { kind := .claim, seat := .val sid } {} = r at h hrid hrcb
  cases hs1 : releaseSeatClaim st sid with
  | error e => simp [hs1, bind, Except.bind] at h
  | ok s1 =>
  cases hrel : releaseClaimSeats s1 lid with
  | error e => simp [hs1, hrel, bind, Except.bind] at h
  | ok released =>
  simp only [hs1, hrel, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨seat, hseat, hsid, hseats1, _⟩ := releaseSeatClaim_ok hb.seatsNodup hs1
  have hb1 := seat_claim_bijection_release hb hs1
  obtain ⟨hsi1, hli1⟩ := releaseSeatClaim_ids hb hs1
  have hfree1 : ∀ s ∈ s1.seats, s.id = sid → s.current = .null := by
    intro s hs hid
    rw [hseats1] at hs
    obtain ⟨s0, _, hid0, hcase⟩ := mem_releaseSeats hs
    rcases hcase with ⟨_, hnull⟩ | ⟨hne, rfl⟩
    · exact hnull
    · exact absurd hid hne
  have R := releaseClaimSeats_spec hb1 hrel
  have hfree := R.keepsFree sid hfree1
  have hbR := R.bij
  -- Ids in `released` match the original state.
  have hsidR : ∃ s ∈ released.seats, s.id = sid := by
    rw [← mem_ids, R.seatIds, hsi1, mem_ids]; exact ⟨seat, hseat, hsid⟩
  have hlidR : ∃ l ∈ released.lemmas, l.id = lid := by
    rw [← mem_lemma_ids, R.lemmaIds, hli1, mem_lemma_ids]; exact ⟨lemma, hlemmem, hlemid⟩
  have hrid' : r.lemma.id = lid := hrid.trans hlemid
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [List.map_map]
    have : ((·.id) ∘ fun s : Seat => if s.id = sid then { s with status := .val "working", current := .val lid } else s) =
        (·.id) := by funext s; simp only [Function.comp]; split <;> rfl
    rw [this]; exact hbR.seatsNodup
  · rw [List.map_map]
    have : ((·.id) ∘ fun l : Lemma => if l.id = lid then r.lemma else l) = (·.id) := by
      funext l; simp only [Function.comp]; split <;> simp_all
    rw [this]; exact hbR.lemmasNodup
  · intro s'' hs'' c hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs''
    by_cases hid : s.id = sid
    · simp only [hid, ↓reduceIte] at hc ⊢
      cases hc
      obtain ⟨l, hl, hlid⟩ := hlidR
      exact ⟨r.lemma, List.mem_map.2 ⟨l, hl, by simp [hlid]⟩, hrid', hrcb⟩
    · simp only [hid, ↓reduceIte] at hc ⊢
      obtain ⟨l, hl, hlid, hlcb⟩ := hbR.seatToLemma s hs c hc
      have hne : l.id ≠ lid := by intro heq; exact R.noPtr s hs (hc.trans (by rw [← hlid, heq]))
      exact ⟨l, List.mem_map.2 ⟨l, hl, by simp [hne]⟩, hlid, hlcb⟩
  · intro l'' hl'' x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl''
    by_cases hid : l.id = lid
    · simp only [hid, ↓reduceIte] at hx ⊢
      rw [hrcb] at hx; cases hx
      obtain ⟨s, hs, hsid'⟩ := hsidR
      exact ⟨_, List.mem_map.2 ⟨s, hs, rfl⟩, by simp [hsid'], by simp [hsid', hrid']⟩
    · simp only [hid, ↓reduceIte] at hx ⊢
      obtain ⟨s, hs, hsx, hcur⟩ := hbR.lemmaToSeat l hl x hx
      have hne : s.id ≠ sid := by intro heq; rw [hfree s hs heq] at hcur; cases hcur
      exact ⟨s, List.mem_map.2 ⟨s, hs, by simp [hne]⟩, hsx, hcur⟩
  · obtain ⟨s, hs, hsid'⟩ := hsidR
    exact ⟨_, List.mem_map.2 ⟨s, hs, rfl⟩, by simp [hsid'], by simp [hsid']⟩
  · obtain ⟨l, hl, hlid⟩ := hlidR
    exact ⟨r.lemma, List.mem_map.2 ⟨l, hl, by simp [hlid]⟩, hrid', hrcb⟩

/-- A seat-ownership operation, as `fleet` issues them. -/
inductive SeatOp where
  | assign (sid lid : String)
  | release (sid : String)
  | releaseClaim (lid : String)

def SeatOp.run : SeatOp → State → Except String State
  | .assign sid lid, st => assignSeatClaim st sid lid
  | .release sid, st => releaseSeatClaim st sid
  | .releaseClaim lid, st => releaseClaimSeats st lid

/-- Apply operations in order. A thrown error leaves the state unchanged, as the CLI does. -/
def runSeatOps (ops : List SeatOp) (st : State) : State :=
  ops.foldl (fun st op => match op.run st with | .ok st' => st' | .error _ => st) st

/-- **Theorem 10 (`seat_claim_bijection_preserved`).** Start from any bijective seat–claim
assignment, with any number of seats and claims. Every sequence of `assignSeatClaim`,
`releaseSeatClaim` and `releaseClaimSeats` calls, including calls that throw, preserves the
bijection `seat.current_lemma = c ↔ claim.claimed_by = seat` and leaves at most one seat on
each claim. -/
theorem seat_claim_bijection_preserved (ops : List SeatOp) :
    ∀ st, Bij st → Bij (runSeatOps ops st) ∧
      (∀ s ∈ (runSeatOps ops st).seats, ∀ l ∈ (runSeatOps ops st).lemmas, s.current = .val l.id ↔ l.claimedBy = .val s.id) ∧
      (∀ s1 ∈ (runSeatOps ops st).seats, ∀ s2 ∈ (runSeatOps ops st).seats, ∀ c, s1.current = .val c → s2.current = .val c → s1 = s2) := by
  induction ops with
  | nil => intro st hb; exact ⟨hb, hb.iff, fun _ h1 _ h2 _ hc1 hc2 => hb.single_owner h1 h2 hc1 hc2⟩
  | cons op ops ih =>
    intro st hb
    apply ih
    show Bij (match op.run st with | .ok st' => st' | .error _ => st)
    cases hr : op.run st with
    | error => exact hb
    | ok st' =>
      cases op with
      | assign sid lid => exact (seat_claim_bijection_assign hb hr).1
      | release sid => exact seat_claim_bijection_release hb hr
      | releaseClaim lid => exact (seat_claim_bijection_releaseClaim hb hr).1

/-! ## Summary theorem for the trust seal -/

/-- **Theorem 11 (`trust_seal_and_conquered_sound`).**
1. `computeTrustSeal` returns `contradiction` whenever `status = contradiction` or
   `record_state.contradiction` holds, and only then.
2. `isRungConquered` is `false` for every `expect` when the seal is `contradiction` or `flagged`.
3. For any record hunt state, the default `expect` (`"proof"`) is conquered exactly when
   `closed ∧ ¬contradiction ∧ status ≠ contradiction`.
4. For every hunt produced by `replayRecordSubmissions`, this reduces to
   `rs.closed ∧ ¬rs.contradiction`. -/
theorem trust_seal_and_conquered_sound :
    (∀ l : Lemma, computeTrustSeal l = .contradiction ↔ (l.status = .contradiction ∨ rsContra l = true)) ∧
    (∀ (l : Lemma) (ex : Expect), (computeTrustSeal l = .contradiction ∨ computeTrustSeal l = .flagged) →
      isRungConquered (some l) ex = false) ∧
    (∀ (l : Lemma) (rs : RecordState), isRecordLemma l = true → l.recordState = .val rs →
      isRungConquered (some l) (.str "proof") = (rs.closed && !rs.contradiction && l.status != .contradiction)) ∧
    (∀ (slug : JStr) (l : Lemma) (subs : List Event) (ts : List (String × Int)) (h : Hashes),
      isRecordLemma l = true →
      ∃ rs, (replayRecordSubmissions slug l subs ts h).recordState = .val rs ∧
        (isRungConquered (some (replayRecordSubmissions slug l subs ts h)) (.str "proof") = true ↔
          rs.closed = true ∧ rs.contradiction = false)) :=
  ⟨trust_seal_contradiction_iff, conquered_false_of_bad_seal,
    fun l rs hl hrs => conquered_record_default l rs hl hrs _ (.inl rfl), conquered_replay_default⟩

end PF
