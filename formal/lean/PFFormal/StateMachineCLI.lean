import Lean.Data.Json
import PFFormal.StateMachine

/-!
# `pf_state_check`: batch driver for the Lean state-machine model

Reads `{"cases": [...]}` from stdin and writes `{"results": [...]}` to stdout. Each case
receives the same JSON objects that `formal/verify_state_machine_equiv.mjs` passes to
`hub/state_machine.mjs`.

| `op`         | input                                                   | output                          |
| ------------ | ------------------------------------------------------- | ------------------------------- |
| `replay`     | `slug`, `lemma`, `subs`, `gitAddedTs` pairs, `currentHashes` | `lemma` overlay            |
| `claimTrace` | `lemma`, `steps: [{event, ctx}]`                        | per step `ok`, `reason`, overlay |
| `seatTrace`  | `state`, `steps: [{fn, seat, lemma}]`                   | per step `ok`/`error`, overlay  |
| `seal`       | `lemma` (or `null`), `expects`                          | `seal`, `conquered`             |
| `targets`    | `slug`, `lemma`, `kind`, `score`                        | `computeRecordTargets` fields   |

An overlay holds every field the reducers can write. `_undef` lists the fields whose value is
`undefined`. The harness applies the overlay to the input object, then compares the whole
result with the JavaScript output.
-/

open Lean PF

abbrev P := Except String

def fld (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

/-- JavaScript truthiness of a JSON value. -/
def jsTruthy : Option Json → Bool
  | none => false
  | some .null => false
  | some (.bool b) => b
  | some (.num n) => n.mantissa != 0
  | some (.str s) => s != ""
  | some _ => true

def pJStr (j : Json) (k : String) : P JStr :=
  match fld j k with
  | none => pure .undef
  | some .null => pure .null
  | some (.str s) => pure (.val s)
  | some v => throw s!"field {k}: expected string, got {v.compress}"

def pStr (j : Json) (k : String) : P String :=
  match fld j k with
  | some (.str s) => pure s
  | _ => throw s!"field {k}: expected string"

def pInt (j : Json) (k : String) : P Int :=
  match fld j k with
  | some v => match v.getInt? with
    | .ok n => pure n
    | .error _ => throw s!"field {k}: expected integer"
  | none => throw s!"field {k}: missing integer"

/-- Absent or `null` becomes `none`. -/
def pOptInt (j : Json) (k : String) : P (Option Int) :=
  match fld j k with
  | none => pure none
  | some .null => pure none
  | some v => match v.getInt? with
    | .ok n => pure (some n)
    | .error _ => throw s!"field {k}: expected integer or null"

def pJInt (j : Json) (k : String) : P (JOpt Int) :=
  match fld j k with
  | none => pure .undef
  | some .null => pure .null
  | some v => match v.getInt? with
    | .ok n => pure (.val n)
    | .error _ => throw s!"field {k}: expected integer"

def pBool (j : Json) (k : String) : P Bool :=
  match fld j k with
  | some (.bool b) => pure b
  | _ => throw s!"field {k}: expected boolean"

def pStrList (v : Json) : P (List String) := do
  let arr ← v.getArr?
  arr.toList.mapM fun x => match x with
    | .str s => pure s
    | _ => throw "expected string array"

/-- An object-valued slot: absent, `null`, or a parsed object. -/
def pJObj {α : Type} (j : Json) (k : String) (f : Json → P α) : P (JOpt α) :=
  match fld j k with
  | none => pure .undef
  | some .null => pure .null
  | some v@(.obj _) => do pure (.val (← f v))
  | some v => throw s!"field {k}: expected object or null, got {v.compress}"

def pChecker (v : Json) : P Checker := do
  let axioms ← match fld v "axioms" with
    | none => pure .undef
    | some .null => pure .null
    | some a => do pure (.val (← pStrList a))
  pure {
    ok := jsTruthy (fld v "ok")
    fileHash := ← pJStr v "file_hash"
    statementFrozen := jsTruthy (fld v "statement_frozen")
    bySeat := ← pJStr v "by_seat"
    statementHash := ← pJStr v "statement_hash"
    coreHash := ← pJStr v "core_hash"
    axioms
    durationMs := ← pJInt v "duration_ms"
    raw := v.compress }

def pRefutation (v : Json) : P Refutation := do
  pure { fileHash := ← pJStr v "file_hash", raw := v.compress }

def pAudit (v : Json) : P Audit := do
  pure { status := ← pJStr v "status", fileHash := ← pJStr v "file_hash", raw := v.compress }

def pRaw (v : Json) : P String := pure v.compress

def pOptStr (j : Json) (k : String) : P (Option String) :=
  match fld j k with
  | none => pure none
  | some .null => pure none
  | some (.str s) => pure (some s)
  | _ => throw s!"field {k}: expected string or null"

def pReceipt (v : Json) : P Receipt := do
  pure {
    score := ← pInt v "score"
    seat := ← pStr v "seat"
    file := ← pStr v "file"
    fileHash := ← pJStr v "file_hash"
    submission := ← pStr v "submission"
    gitTs := ← pOptInt v "git_ts"
    atTime := ← pOptStr v "at"
    thm := ← pStr v "theorem"
    statementHash := ← pJStr v "statement_hash"
    coreHash := ← pJStr v "core_hash"
    axioms := ← match fld v "axioms" with
      | some a => pStrList a
      | none => throw "receipt.axioms missing"
    durationMs := ← pOptInt v "duration_ms"
    inclusiveBound := ← pOptInt v "inclusive_bound" }

def pHistState (s : String) : P HistState :=
  if s = "accepted" then pure .accepted
  else if s = "ignored_non_improving" then pure .ignored_non_improving
  else if s = "contradiction" then pure .contradiction
  else if s = "stale_statement" then pure .stale_statement
  else if s = "stale_core" then pure .stale_core
  else throw s!"unknown history state {s}"

def pHist (v : Json) : P HistEntry := do
  let kind ← pStr v "kind"
  let stale ← match fld v "statement_hash", fld v "core_hash" with
    | none, none => pure none
    | _, _ => do pure (some (← pJStr v "statement_hash", ← pJStr v "core_hash"))
  pure {
    isRecord := kind == "record"
    score := ← pInt v "score"
    seat := ← pStr v "seat"
    file := ← pStr v "file"
    fileHash := ← pJStr v "file_hash"
    submission := ← pStr v "submission"
    points := ← pInt v "points"
    gitTs := ← pOptInt v "git_ts"
    atTime := ← pOptStr v "at"
    staleHashes := stale
    state := ← pHistState (← pStr v "state") }

def pOptReceipt (v : Json) (k : String) : P (Option Receipt) :=
  match fld v k with
  | none => pure none
  | some .null => pure none
  | some r => do pure (some (← pReceipt r))

def pObjPairs {α : Type} (v : Json) (f : Json → P α) : P (List (String × α)) := do
  let o ← v.getObj?
  o.toList.mapM fun (k, x) => do pure (k, ← f x)

def pRecordState (v : Json) : P RecordState := do
  pure {
    direction := ← pStr v "direction"
    best := ← pOptReceipt v "best"
    refuted := ← pOptReceipt v "refuted"
    nextTarget := ← pOptInt v "next_target"
    closed := ← pBool v "closed"
    contradiction := ← pBool v "contradiction"
    history := ← match fld v "history" with
      | some h => do (← h.getArr?).toList.mapM pHist
      | none => throw "record_state.history missing"
    pointsBySeat := ← match fld v "points_by_seat" with
      | some p => pObjPairs p (fun x => x.getInt?)
      | none => throw "record_state.points_by_seat missing" }

def pRecordCfg (v : Json) : P RecordCfgIn := do
  pure {
    direction := ← pJStr v "direction"
    startTarget := ← pOptInt v "start_target"
    boundFloor := ← pOptInt v "bound_floor"
    scoreMax := ← pOptInt v "score_max"
    allowBound := ← match fld v "allow_bound" with
      | none => pure .undef
      | some .null => pure .null
      | some (.bool b) => pure (.val b)
      | _ => throw "allow_bound: expected boolean"
    fileStem := ← pJStr v "file_stem"
    claimsDir := ← pJStr v "claims_dir"
    artifactExt := ← pJStr v "artifact_ext"
    theoremTemplate := ← pJStr v "theorem_template" }

def pLemma (v : Json) : P Lemma := do
  pure {
    id := ← pStr v "id"
    kind := ← pJStr v "kind"
    status := Status.ofString (← pStr v "status")
    freshness := ← pJStr v "freshness"
    claimedBy := ← pJStr v "claimed_by"
    updatedAt := ← pJStr v "updated_at"
    epitaph := ← pJObj v "epitaph" pRaw
    audit := ← pJObj v "audit" pAudit
    checker := ← pJObj v "checker" pChecker
    refutation := ← pJObj v "refutation" pRefutation
    leanFile := ← pJStr v "lean_file"
    theoremName := ← pJStr v "theorem_name"
    registeredStatement := ← pJStr v "registered_statement"
    statement := ← pJStr v "statement"
    verifiedSignature := ← pJStr v "verified_signature"
    statementFile := ← pJStr v "statement_file"
    record := ← pJObj v "record" pRecordCfg
    recordState := ← pJObj v "record_state" pRecordState }

def pScore (v : Json) : P ScoreIn :=
  match fld v "score" with
  | none => pure .undef
  | some .null => pure .null
  | some (.str s) => pure (.str s)
  | some n => match n.getInt? with
    | .ok i => pure (.num i)
    | .error _ => throw s!"score: unsupported value {n.compress}"

def pEvent (v : Json) : P Event := do
  pure {
    kind := EvKind.ofString (← pStr v "kind")
    atTime := ← pJStr v "at"
    seat := ← pJStr v "seat"
    epitaph := ← pJObj v "epitaph" pRaw
    audit := ← pJObj v "audit" pAudit
    checker := ← pJObj v "checker" pChecker
    refutation := ← pJObj v "refutation" pRefutation
    file := ← pJStr v "file"
    thm := ← pJStr v "theorem"
    signature := ← pJStr v "signature"
    score := ← pScore v
    subFile := ← pJStr v "_sub_file" }

def pCtx (v : Option Json) : P Ctx :=
  match v with
  | none => pure {}
  | some .null => pure {}
  | some c => do
    let mode ← match fld c "mode" with
      | none => pure Mode.none
      | some .null => pure Mode.none
      | some (.str "preflight") => pure Mode.preflight
      | some (.str "replay") => pure Mode.replay
      | some _ => pure Mode.other
    pure {
      mode
      missionSlug := ← pJStr c "missionSlug"
      gitTs := ← pOptInt c "gitTs"
      statementHash := ← pJStr c "statementHash"
      coreHash := ← pJStr c "coreHash"
      opposingScore := ← pOptInt c "opposingScore" }

def pSeat (v : Json) : P Seat := do
  pure { id := ← pStr v "id", status := ← pJStr v "status", current := ← pJStr v "current_lemma" }

def pState (v : Json) : P State := do
  pure {
    seats := ← match fld v "seats" with
      | some s => do (← s.getArr?).toList.mapM pSeat
      | none => throw "state.seats missing"
    lemmas := ← match fld v "lemmas" with
      | some s => do (← s.getArr?).toList.mapM pLemma
      | none => throw "state.lemmas missing" }

def pExpect (v : Json) : Expect :=
  match v with
  | .str "__undefined__" => .str "proof"
  | .str s => .str s
  | .obj _ =>
    let safe (k : String) : Option Int :=
      match fld v k with
      | some n => match n.getInt? with
        | .ok i => if -maxSafe ≤ i ∧ i ≤ maxSafe then some i else none
        | .error _ => none
      | none => none
    .obj (safe "record_at_most") (safe "record_at_least")
  | .arr _ => .obj none none
  | _ => .null

/-! ## Serialisation -/

def jInt (n : Int) : Json := toJson n
def jOptInt : Option Int → Json
  | some n => jInt n
  | none => .null
def jOptStr : Option String → Json
  | some s => .str s
  | none => .null
def jStrList (l : List String) : Json := .arr (l.map Json.str).toArray

/-- A `JStr` field: `none` means `undefined`. -/
def jJStr : JStr → Option Json
  | .undef => none
  | .null => some .null
  | .val s => some (.str s)

def rawJson (s : String) : Json := (Json.parse s).toOption.getD .null

def jJObj {α : Type} (f : α → Json) : JOpt α → Option Json
  | .undef => none
  | .null => some .null
  | .val a => some (f a)

/-- Build an object, dropping `undefined` fields. -/
def objOpt (kvs : List (String × Option Json)) : Json :=
  Json.mkObj (kvs.filterMap fun (k, v) => v.map (k, ·))

def jReceipt (r : Receipt) : Json :=
  objOpt [
    ("score", some (jInt r.score)), ("seat", some (.str r.seat)), ("file", some (.str r.file)),
    ("file_hash", jJStr r.fileHash), ("submission", some (.str r.submission)),
    ("git_ts", some (jOptInt r.gitTs)), ("at", some (jOptStr r.atTime)),
    ("theorem", some (.str r.thm)), ("statement_hash", jJStr r.statementHash),
    ("core_hash", jJStr r.coreHash), ("axioms", some (jStrList r.axioms)),
    ("duration_ms", some (jOptInt r.durationMs)),
    ("inclusive_bound", r.inclusiveBound.map jInt)]

def jHist (h : HistEntry) : Json :=
  objOpt ([
    ("kind", some (.str (if h.isRecord then "record" else "record_bound"))),
    ("score", some (jInt h.score)), ("seat", some (.str h.seat)), ("file", some (.str h.file)),
    ("file_hash", jJStr h.fileHash), ("submission", some (.str h.submission)),
    ("points", some (jInt h.points)), ("git_ts", some (jOptInt h.gitTs)),
    ("at", some (jOptStr h.atTime)), ("state", some (.str h.state.name))] ++
    match h.staleHashes with
    | some (s, c) => [("statement_hash", jJStr s), ("core_hash", jJStr c)]
    | none => [])

def jRecordState (rs : RecordState) : Json :=
  Json.mkObj [
    ("direction", .str rs.direction),
    ("best", match rs.best with | some b => jReceipt b | none => .null),
    ("refuted", match rs.refuted with | some b => jReceipt b | none => .null),
    ("next_target", jOptInt rs.nextTarget),
    ("closed", .bool rs.closed), ("contradiction", .bool rs.contradiction),
    ("history", .arr (rs.history.map jHist).toArray),
    ("points_by_seat", Json.mkObj (rs.pointsBySeat.map fun (k, v) => (k, jInt v)))]

/-- Overlay with every field a reducer can write, plus `_undef` for the `undefined` ones. -/
def overlay (kvs : List (String × Option Json)) : Json :=
  let undefs := kvs.filterMap fun (k, v) => if v.isNone then some (Json.str k) else none
  Json.mkObj ((kvs.filterMap fun (k, v) => v.map (k, ·)) ++ [("_undef", .arr undefs.toArray)])

def lemmaOverlay (l : Lemma) : Json :=
  overlay [
    ("status", some (.str l.status.name)),
    ("claimed_by", jJStr l.claimedBy),
    ("updated_at", jJStr l.updatedAt),
    ("epitaph", jJObj rawJson l.epitaph),
    ("audit", jJObj (fun a => rawJson a.raw) l.audit),
    ("checker", jJObj (fun c => rawJson c.raw) l.checker),
    ("refutation", jJObj (fun r => rawJson r.raw) l.refutation),
    ("lean_file", jJStr l.leanFile),
    ("theorem_name", jJStr l.theoremName),
    ("registered_statement", jJStr l.registeredStatement),
    ("statement", jJStr l.statement),
    ("verified_signature", jJStr l.verifiedSignature),
    ("record_state", jJObj jRecordState l.recordState)]

def seatOverlay (s : Seat) : Json :=
  overlay [("status", jJStr s.status), ("current_lemma", jJStr s.current)]

def stateOverlay (st : State) : Json :=
  Json.mkObj [
    ("seats", .arr (st.seats.map seatOverlay).toArray),
    ("lemmas", .arr (st.lemmas.map lemmaOverlay).toArray)]

def jResult (r : Result) : Json :=
  Json.mkObj [
    ("ok", .bool r.ok),
    ("reason", if r.ok then .null else .str r.reason),
    ("lemma", lemmaOverlay r.lemma)]

/-! ## Case dispatch -/

def pPairs (v : Json) : P (List (String × Int)) := do
  (← v.getArr?).toList.mapM fun p => do
    let a ← p.getArr?
    match a.toList with
    | [.str k, n] => do pure (k, ← n.getInt?)
    | _ => throw "gitAddedTs: expected [key, int] pairs"

def pHashes (v : Json) : P Hashes := do
  pure {
    statementHashes := ← match fld v "statementHashes" with
      | none => pure none
      | some .null => pure none
      | some o => do pure (some (← pObjPairs o fun x => match x with
          | .str s => pure s
          | _ => throw "statementHashes: expected strings"))
    coreHash := ← pJStr v "coreHash" }

def runSeatStep (st : State) (step : Json) : P (State × Json) := do
  let fn ← pStr step "fn"
  let r : Except String State ←
    if fn = "assign" then pure (assignSeatClaim st (← pStr step "seat") (← pStr step "lemma"))
    else if fn = "release" then pure (releaseSeatClaim st (← pStr step "seat"))
    else if fn = "releaseClaim" then pure (releaseClaimSeats st (← pStr step "lemma"))
    else throw s!"unknown seat fn {fn}"
  match r with
  | .ok st' => pure (st', Json.mkObj [("ok", .bool true), ("state", stateOverlay st')])
  | .error msg => pure (st, Json.mkObj [("ok", .bool false), ("error", .str msg)])

def runCase (c : Json) : P Json := do
  let op ← pStr c "op"
  if op = "replay" then
    let l ← pLemma (← (fld c "lemma").elim (throw "lemma missing") pure)
    let subs ← (← ((fld c "subs").elim (throw "subs missing") pure)).getArr?
    let subs ← subs.toList.mapM pEvent
    let ts ← pPairs (← (fld c "gitAddedTs").elim (throw "gitAddedTs missing") pure)
    let h ← pHashes (← (fld c "currentHashes").elim (throw "currentHashes missing") pure)
    pure (Json.mkObj [("lemma", lemmaOverlay (replayRecordSubmissions (← pJStr c "slug") l subs ts h))])
  else if op = "claimTrace" then
    let l ← pLemma (← (fld c "lemma").elim (throw "lemma missing") pure)
    let steps ← (← ((fld c "steps").elim (throw "steps missing") pure)).getArr?
    let (_, outs) ← steps.toList.foldlM (init := (l, #[])) fun (cur, acc) s => do
      let e ← pEvent (← (fld s "event").elim (throw "event missing") pure)
      let ctx ← pCtx (fld s "ctx")
      let r := transitionClaim cur e ctx
      pure (r.lemma, acc.push (jResult r))
    pure (Json.mkObj [("steps", .arr outs)])
  else if op = "seatTrace" then
    let st ← pState (← (fld c "state").elim (throw "state missing") pure)
    let steps ← (← ((fld c "steps").elim (throw "steps missing") pure)).getArr?
    let (_, outs) ← steps.toList.foldlM (init := (st, #[])) fun (cur, acc) s => do
      let (st', out) ← runSeatStep cur s
      pure (st', acc.push out)
    pure (Json.mkObj [("steps", .arr outs)])
  else if op = "seal" then
    let lo ← match fld c "lemma" with
      | none => pure none
      | some .null => pure none
      | some v => do pure (some (← pLemma v))
    let expects ← (← ((fld c "expects").elim (throw "expects missing") pure)).getArr?
    pure (Json.mkObj [
      ("seal", match lo with | some l => .str (computeTrustSeal l).name | none => .null),
      ("conquered", .arr (expects.map fun e => .bool (isRungConquered lo (pExpect e))))])
  else if op = "targets" then
    let l ← pLemma (← (fld c "lemma").elim (throw "lemma missing") pure)
    let t := computeRecordTargets (← pJStr c "slug") l (EvKind.ofString (← pStr c "kind")) (← pInt c "score")
    pure (Json.mkObj [
      ("tag", .str t.tag), ("artifactFile", .str t.artifactFile),
      ("submissionBasename", .str t.submissionBasename), ("submissionFile", .str t.submissionFile),
      ("theoremName", .str t.theoremName)])
  else throw s!"unknown op {op}"

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error e =>
    IO.eprintln s!"pf_state_check: invalid JSON input: {e}"
    pure 2
  | .ok j =>
    let cases : Array Json ← match fld j "cases" with
      | some (.arr a) => pure a
      | _ => do IO.eprintln "pf_state_check: expected {\"cases\": [...]}"; return 2
    let results := cases.map fun c => match runCase c with
      | .ok r => r
      | .error e => Json.mkObj [("error", .str e)]
    IO.println (Json.mkObj [("results", .arr results)]).compress
    pure 0
