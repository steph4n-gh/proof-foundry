# P = NP ? · Local T3 Code Fleet Playbook

**One rule:** No claim counts as a proof unless the Lean 4.36.0 kernel verifies it (`zero sorry`, standard axioms only: `propext`, `Classical.choice`, `Quot.sound`).

## Commands (run from `/Volumes/Storage/pnpenis2`)

```bash
# Inspect current board & seats
node hub/cli.mjs status

# Claim a lemma (lights up the live dashboard + Proof Map halo!)
node hub/cli.mjs claim --lemma L-clb-001 --seat seat-clb-1 --whisper "Proving XOR is not monotone"

# Broadcast a live whisper while thinking or proving
node hub/cli.mjs whisper --seat seat-clb-1 --lemma L-clb-001 --text "Formalizing witness inputs (true,false) <= (true,true)"

# Send an inter-seat dispatch (shows up in Live Fleet topology + Comms feed!)
node hub/cli.mjs msg --from seat-redteam-1 --to seat-alg-1 --lemma L-alg-002 --kind challenge --text "Counterexample found!"

# Submit a Lean 4 proof to the Judge (runs `lake env lean` + `#print axioms` audit)
node hub/cli.mjs verify --lemma L-clb-001 --seat seat-clb-1 --file lean/PnP/Lemmas/L_clb_001.lean --theorem PnP.Lemmas.L_clb_001.xor2_no_monotone_circuit

# Submit a Lean 4 counterexample refutation (Red Team!)
node hub/cli.mjs refute --lemma L-alg-002 --seat seat-redteam-1 --file lean/PnP/Lemmas/L_alg_002_refute.lean --theorem PnP.Lemmas.L_alg_002_refute.counterexample --summary "Explicit 3-var CNF falsifies the conjecture"

# Rule an approach dead against a complexity barrier (Barrier Desk!)
node hub/cli.mjs rule-dead --lemma L-bar-001 --seat seat-barrier-1 --wall "Relativization (Baker-Gill-Solovay, 1975)" --reason "Step-counting diagonalization holds relative to all oracles, contradicting oracle A with P^A = NP^A."

# State a brand new conjecture on the board
node hub/cli.mjs lemma-add --id L-clb-005 --program circuit_lower_bounds --title "..." --statement "..." --theorem "PnP.Lemmas.L_clb_005.thm" --deps "L-clb-001" --seat seat-clb-1 --aims p_neq_np --rung 5

# Update seat status when finished
node hub/cli.mjs seat-state --seat seat-clb-1 --status idle --whisper "Wave 1 targets cleared; awaiting Wave 2"
```

## File Isolation Rule for Parallel Seats
- **NEVER edit `lean/PnP/Core.lean`** during a parallel wave (it is shared read-only).
- Put each proof in its own dedicated file `lean/PnP/Lemmas/<LemmaId>.lean` (e.g. `lean/PnP/Lemmas/L_clb_001.lean`) with `import PnP.Core`.
- You may import another checked lemma ONLY if you write self-contained helpers or after checking it compiles under `lake env lean`. Self-contained proofs that only `import PnP.Core` compile fastest (~1s) and never conflict!
