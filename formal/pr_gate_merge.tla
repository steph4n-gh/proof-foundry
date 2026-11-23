-------------------------- MODULE pr_gate_merge --------------------------
EXTENDS Naturals

CONSTANTS PinJudgeInputs, RequireCurrentBase, RequireAuthorizedHead

VARIABLES kind, phase, head, main, donorSHA, okSHA, mergedSHA
vars == <<kind, phase, head, main, donorSHA, okSHA, mergedSHA>>

EventHead == "H0"
EventBase == "B0"
Finished == phase \in {"merged", "stopped"}

Init ==
    /\ kind \in {"bounty", "record"}
    /\ phase = "classify"
    /\ head = EventHead /\ main = EventBase
    /\ donorSHA = "none" /\ okSHA = "none" /\ mergedSHA = "none"

MoveHead ==
    /\ ~Finished
    /\ head' = IF head = EventHead THEN "H1" ELSE EventHead
    /\ UNCHANGED <<kind, phase, main, donorSHA, okSHA, mergedSHA>>

AdvanceMain ==
    /\ ~Finished /\ main = EventBase
    /\ main' \in (IF kind = "bounty" THEN {"unrelated", "claimed"}
                  ELSE {"unrelated", "tied", "beaten"})
    /\ UNCHANGED <<kind, phase, head, donorSHA, okSHA, mergedSHA>>

\* A successful job records the object it actually inspected.
FetchedExpectedHead == ~PinJudgeInputs \/ head = EventHead

ClassifyDonor ==
    /\ phase = "classify"
    /\ FetchedExpectedHead
    /\ donorSHA' = head /\ phase' = "judge"
    /\ UNCHANGED <<kind, head, main, okSHA, mergedSHA>>

JudgeOK ==
    /\ phase = "judge"
    /\ FetchedExpectedHead
    /\ okSHA' = head /\ phase' = "decide"
    /\ UNCHANGED <<kind, head, main, donorSHA, mergedSHA>>

FailCheck ==
    /\ phase \in {"classify", "judge"}
    /\ phase' = "stopped"
    /\ UNCHANGED <<kind, head, main, donorSHA, okSHA, mergedSHA>>

\* Minimize a concrete score of 7 against an incumbent of 8, 7, or 6.
Improves(base) == 7 < (CASE base = "tied" -> 7 [] base = "beaten" -> 6 [] OTHER -> 8)
Eligible(base) == IF kind = "bounty" THEN base # "claimed" ELSE Improves(base)

Decide ==
    /\ phase = "decide"
    /\ phase' = IF head = EventHead /\ Eligible(main) THEN "eligible" ELSE "stopped"
    /\ UNCHANGED <<kind, head, main, donorSHA, okSHA, mergedSHA>>

EnableAutoMerge ==
    /\ phase = "eligible"
    /\ phase' = IF head = EventHead THEN "enabled" ELSE "stopped"
    /\ UNCHANGED <<kind, head, main, donorSHA, okSHA, mergedSHA>>

\* Model a merge of the authorized head. Strict up-to-date checks are a
\* separate server-side condition. H0 descends from B0 only.
CanLand == /\ ~RequireAuthorizedHead \/ head = EventHead
           /\ ~RequireCurrentBase \/ main = EventBase

Merge ==
    /\ phase = "enabled"
    /\ phase' = IF CanLand THEN "merged" ELSE "stopped"
    /\ mergedSHA' = IF CanLand THEN head ELSE "none"
    /\ UNCHANGED <<kind, head, main, donorSHA, okSHA>>

Done == Finished /\ UNCHANGED vars

Next == MoveHead \/ AdvanceMain \/ ClassifyDonor \/ JudgeOK \/ FailCheck
        \/ Decide \/ EnableAutoMerge \/ Merge \/ Done

NeverMergeUnjudgedCommit ==
    phase = "merged" => (mergedSHA = donorSHA /\ mergedSHA = okSHA)

\* 'main' is the previous main tip at the instant of landing.
NeverMergeStaleClaim == phase = "merged" => Eligible(main)
=============================================================================
