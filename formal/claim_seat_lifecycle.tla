----------------------- MODULE claim_seat_lifecycle -----------------------
EXTENDS FiniteSets, Naturals

Seats == {"A", "B"}
Target == "target"
Claims == {Target, "other"}
None == "none"
Verdicts == {"checked", "refuted", "contradiction"}

VARIABLES owner, current, status, receipts, wasContradiction, barrierFrom
vars == <<owner, current, status, receipts, wasContradiction, barrierFrom>>

Init ==
    /\ owner = [c \in Claims |-> None]
    /\ current = [s \in Seats |-> None]
    /\ status = "open" /\ receipts = {}
    /\ wasContradiction = FALSE /\ barrierFrom = None

\* Monitors record the state before an event, independently of its effect.
Observe(isBarrier) ==
    /\ wasContradiction' = (wasContradiction \/ status = "contradiction")
    /\ barrierFrom' = IF isBarrier THEN status ELSE None

Assign(s, c) ==
    /\ status # "contradiction"
    /\ c # Target \/ status = "open"
    /\ owner[c] # s
    /\ owner' = [k \in Claims |->
          IF k = c THEN s ELSE IF owner[k] = s THEN None ELSE owner[k]]
    /\ current' = [k \in Seats |->
          IF k = s THEN c ELSE IF current[k] = c THEN None ELSE current[k]]
    /\ Observe(FALSE)
    /\ UNCHANGED <<status, receipts>>

ReleaseTarget ==
    /\ owner' = [owner EXCEPT ![Target] = None]
    /\ current' = [s \in Seats |-> IF current[s] = Target THEN None ELSE current[s]]

\* The work queue may deliver either kind first and may redeliver it.
JudgeProof ==
    /\ status' = IF status \in {"refuted", "contradiction"}
                 THEN "contradiction" ELSE "checked"
    /\ receipts' = receipts \cup {"proof"}
    /\ Observe(FALSE)
    /\ ReleaseTarget

JudgeRefutation ==
    /\ status' = IF status \in {"checked", "contradiction"}
                 THEN "contradiction" ELSE "refuted"
    /\ receipts' = receipts \cup {"refutation"}
    /\ Observe(FALSE)
    /\ ReleaseTarget

Barrier ==
    /\ status' = IF status \in Verdicts THEN status ELSE "dead"
    /\ Observe(TRUE)
    /\ ReleaseTarget
    /\ UNCHANGED receipts

\* Contradiction is a terminal verdict. Continue to check later deliveries.
Done == status = "contradiction" /\ UNCHANGED vars

Next == (\E s \in Seats, c \in Claims : Assign(s, c))
        \/ JudgeProof \/ JudgeRefutation \/ Barrier \/ Done

ContradictionIsSticky == wasContradiction => status = "contradiction"
SingleSeatPerClaim ==
    \A c \in Claims : Cardinality({s \in Seats : current[s] = c}) <= 1
SeatClaimBijection ==
    /\ owner \in [Claims -> (Seats \cup {None})]
    /\ current \in [Seats -> (Claims \cup {None})]
    /\ \A s \in Seats, c \in Claims : (owner[c] = s) <=> (current[s] = c)
ClosedClaimReleased == status # "open" => owner[Target] = None
BarrierNeverOverwritesVerdict == barrierFrom \in Verdicts => status = barrierFrom
OrderIndependentContradiction ==
    receipts = {"proof", "refutation"} => status = "contradiction"
=============================================================================
