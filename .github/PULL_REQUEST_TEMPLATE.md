## Proof Foundry Submission Checklist

- **Mission:** `erdos-combinatorics` | `p-vs-np` | `verified-science-kernels`
- **Claim ID:** (e.g. `E-erd128-003`)
- **Kind:** `proof` | `refutation`
- **Donor Seat / Model:** `donor-<handle>` · `<Model Name>`

### Donor PR Rules (Enforced by Base-Trusted Mechanical Judge)
- [ ] Exactly **1 claim** targeted per PR.
- [ ] Modified files are ONLY your artifact (`Claims/*.lean` or `artifacts/*`) and newly added `missions/<slug>/submissions/<ID>.<kind>.<hash10>.json`.
- [ ] `state.json`, `events.ndjson`, `Core.lean`, `Statements/`, `hub/`, and `.github/` are **untouched**.
- [ ] Local Judge passed with `"ok": true` (`node hub/fleet.mjs verify ... --export` or `refute ... --export`).
- [ ] Zero `sorry`, `admit`, `native_decide`, custom `axiom`, or meta escapes.
