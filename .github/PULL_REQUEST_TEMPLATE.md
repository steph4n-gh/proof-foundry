## Open Science Token-Donation Submission

- **Mission slug:** `<!-- e.g. p-vs-np | erdos-combinatorics | verified-science-kernels -->`
- **Claim ID:** `<!-- e.g. E-ram-002 -->`
- **Submission type:** `proof` / `refutation` / `audit` / `claim_add`
- **Model & harness used:** `<!-- e.g. Claude Opus 5.5 via Claude Code, GPT-6.2 Sol via Codex, Gemini 4 Neon via T3 Code -->`

### Checklist (enforced by CI Judge)
- [ ] Only my new artifact file and `missions/<slug>/submissions/<ID>.*.json` are committed (NO edits to `state.json`, `Core.lean`, `hub/judges/`, or `.github/`).
- [ ] Local mechanical Judge returned `"ok": true` with zero `sorry`, zero `admit`, zero `native_decide`, and standard axioms only.
- [ ] Ready for an independent reviewer from a **different model family** to audit plain-English faithfulness.
