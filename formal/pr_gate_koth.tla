--------------------------- MODULE pr_gate_koth ---------------------------
EXTENDS Naturals

CONSTANTS CheckFrozenStatement, CheckDonorFiles, CheckScoreOnCurrentBase,
          BlockContradictionAutoMerge, RequireCurrentBase, RequireAuthorizedHead

PRs == 1..2
Record(n) == <<"record", n>>
Bound(n) == <<"record_bound", n>>
Frozen == <<"frozen_stmt_mutation", 0>>
Bad == {<<"mode_120000", 0>>, <<"path_escape", 0>>}
Inputs(p) == {Record(7), Record(6), Record(5), Record(4), Bound(5), Bound(7), Frozen} \cup Bad
ChartInputs(p) == IF p = 1 THEN {Record(6)} ELSE {Bound(7)}

InitialMain == [tip |-> 0, best |-> 8, refuted |-> 4]
EmptyRun == [phase |-> "open", payload |-> <<"none", 0>>, base |-> InitialMain,
             head |-> "event", judged |-> "none"]
EndRun(phase) == [EmptyRun EXCEPT !.phase = phase]

VARIABLES runs, main, last, frozenIntact
vars == <<runs, main, last, frozenIntact>>

Init == /\ runs = [p \in PRs |-> EmptyRun]
        /\ main = InitialMain /\ frozenIntact = TRUE
        /\ last = [before |-> InitialMain, payload |-> EmptyRun.payload,
                   head |-> "none", judged |-> "none"]

Improves(x, b) == IF x[1] = "record" THEN x[2] < b.best ELSE x[2] > b.refuted
Crosses(x, b) == IF x[1] = "record" THEN x[2] <= b.refuted ELSE x[2] >= b.best
Closed(b) == b.refuted + 1 = b.best
Breakthrough(x) == x[1] = "record" /\ x[2] < 6

\* validateRecordImprovement is shared by the artifact judge and the data-only decision.
\* Literature best is 6; there is no literature lower bound. Crossings fail the judge,
\* while a valid breakthrough passes the judge but needs a maintainer at decision.
Verdict(x, current) ==
  LET b == IF CheckScoreOnCurrentBase THEN current ELSE InitialMain IN
  CASE Closed(b) -> "review"
    [] ~Improves(x, b) -> "stopped"
    [] Crosses(x, b) /\ BlockContradictionAutoMerge -> "review"
    [] OTHER -> IF Breakthrough(x) THEN "breakthrough" ELSE "eligible"

\* Each of two donors can start immediately, or submit after the other lands.
\* Capture the immutable PR base at classification; 'event' denotes this PR's own SHA.
Classify(p) ==
  /\ runs[p].phase = "open"
  /\ \E x \in Inputs(p):
       LET phase == CASE x = Frozen -> IF CheckFrozenStatement THEN "stopped" ELSE "infra"
                      [] x \in Bad /\ CheckDonorFiles -> "infra"
                      [] OTHER -> "judge"
       IN runs' = [runs EXCEPT ![p] = IF @.head # "event" THEN EndRun("stopped")
                    ELSE [@ EXCEPT !.phase = phase, !.payload = x, !.base = main]]
  /\ UNCHANGED <<main, last, frozenIntact>>

\* Fork infra cannot enter the donor lane. Even maintainer adoption + passing infra CI
\* must not save an edit to a frozen statement; this branch witnesses the freeze mutation.
InfraGate(p) ==
  /\ runs[p].phase = "infra"
  /\ \E adoptedByMaintainer \in BOOLEAN:
       LET editsStatement == adoptedByMaintainer /\ runs[p].payload = Frozen IN
       /\ frozenIntact' = (frozenIntact /\ ~editsStatement)
       /\ runs' = [runs EXCEPT ![p] = EndRun(IF editsStatement THEN "adopted" ELSE "stopped")]
  /\ UNCHANGED <<main, last>>

MoveHead(p) ==
  /\ runs[p].phase \in {"open", "judge", "decide", "eligible", "enabled"} /\ runs[p].head = "event"
  /\ runs' = [runs EXCEPT ![p].head = "changed"]
  /\ UNCHANGED <<main, last, frozenIntact>>

Judge(p) ==
  /\ runs[p].phase = "judge"
  /\ \E artifactVerified \in BOOLEAN:
       LET r == runs[p]
           v == Verdict(r.payload, r.base)
       IN runs' = [runs EXCEPT ![p] =
            IF ~artifactVerified \/ r.head # "event" THEN EndRun("stopped")
            ELSE IF v \in {"review", "stopped"} THEN EndRun(v)
            ELSE [r EXCEPT !.phase = "decide", !.judged = r.head]]
  /\ UNCHANGED <<main, last, frozenIntact>>

Decide(p) ==
  /\ runs[p].phase = "decide"
  /\ LET r == runs[p]
         v == Verdict(r.payload, main)
     IN runs' = [runs EXCEPT ![p] =
          IF r.head # "event" THEN EndRun("stopped")
          ELSE CASE v = "eligible" -> [r EXCEPT !.phase = "eligible"]
                 [] v = "stopped" -> EndRun("stopped")
                 [] OTHER -> EndRun("review")]
  /\ UNCHANGED <<main, last, frozenIntact>>

EnableAutoMerge(p) ==
  /\ runs[p].phase = "eligible"
  /\ runs' = [runs EXCEPT ![p] = IF @.head = "event" THEN [@ EXCEPT !.phase = "enabled"]
                                  ELSE EndRun("stopped")]
  /\ UNCHANGED <<main, last, frozenIntact>>

\* Server-side conditions, not a second call to Verdict. Two PRs never share a tip ID.
Merge(p) ==
  /\ runs[p].phase = "enabled"
  /\ LET r == runs[p]
         x == r.payload
         canLand == (~RequireAuthorizedHead \/ r.head = "event") /\ (~RequireCurrentBase \/ r.base.tip = main.tip)
     IN /\ runs' = [runs EXCEPT ![p] = EndRun(IF canLand THEN "merged" ELSE "stopped")]
        /\ IF canLand THEN
                /\ last' = [before |-> main, payload |-> x, head |-> r.head, judged |-> r.judged]
                /\ main' = [tip |-> p, best |-> IF x[1] = "record" THEN x[2] ELSE main.best,
                            refuted |-> IF x[1] = "record_bound" THEN x[2] ELSE main.refuted]
           ELSE UNCHANGED <<main, last>>
  /\ UNCHANGED frozenIntact

Done == (\A p \in PRs: runs[p].phase \in {"stopped", "review", "merged", "adopted"}) /\ UNCHANGED vars
Next == (\E p \in PRs: Classify(p) \/ InfraGate(p) \/ MoveHead(p) \/ Judge(p) \/ Decide(p)
                       \/ EnableAutoMerge(p) \/ Merge(p)) \/ Done

NeverMutateFrozenStatement == frozenIntact
NeverAcceptBadModeOrPath == last.payload \notin Bad /\
    (\A p \in PRs: runs[p].payload \in Bad => runs[p].phase = "infra")
NeverMergeDuplicateOrWorseScore == main.tip # 0 => Improves(last.payload, last.before)
NeverAutoMergeContradictionCrossing == main.tip # 0 => ~Crosses(last.payload, last.before)
NeverAutoMergeBreakthrough == main.tip # 0 => ~Breakthrough(last.payload)
NeverMergeUnjudgedCommit == main.tip # 0 => last.head = last.judged /\ last.judged = "event"
MainBestMonotone == main.best <= last.before.best /\ main.refuted >= last.before.refuted
=============================================================================
