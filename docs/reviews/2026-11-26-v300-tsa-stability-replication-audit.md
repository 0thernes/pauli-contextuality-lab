# Audit Record: `v3.0.0` Explicit Stability Axiom Audit, Expanded Batteries Linter, RFC 3161 TSA/OTS, SWHID, and Clean-Clone Replication (`2026-11-26`)

- **Repository:** `0thernes/pauli-contextuality-lab`
- **Target release:** `v3.0.0`
- **Date:** 2026-11-26
- **Auditor:** Automated verification pass under human direction (`Alexander S. Donahue`, ORCID `0009-0006-8168-9648`)
- **Human line-by-line Lean review status:** `false` (unchanged — see `formalization.yaml` and `docs/submission-packet.md`)

## Scope Verified

1. **Expanded Lean 4.35.0 Explicit Axiom Audit & Batteries Linter:**
   - Added explicit `#print axioms` declarations for all 6 quantitative third-moment stability theorems in `HoggarBound.Stability` (`moment_entry_le`, `shifted_square_sum`, `cubic_residual_identity`, `cubic_deficit_controls_top`, `spectrum_distance_identity`, `exists_near_extremal_spectrum`) into `lean/VerifyAll.lean` and refreshed `results/lean-axioms-all.log` (`166` explicit `#print axioms` + `2,206` exhaustively audited theorems strictly within `[propext, Classical.choice, Quot.sound]`).
   - Expanded Batteries `runLinter` in `.github/workflows/lean-verify.yml` and `scripts/dev.sh` to `HoggarBound.Bound HoggarBound.Stability ContextualityTensor Evidence` — all 4 modules pass with 0 linter errors.
   - Left heavy standalone finite-certificate modules (`HoggarBound.C3Certificate`, `C3Spectra`, `Saturated*`) out of `VerifyAll.lean` so CI stays fast and green while still scanning all 59 non-`Challenge` `.lean` files for zero forbidden tokens.
2. **Cryptographic Timestamps (Playbook v1.3 #26):**
   - Sealed `data/MANIFEST.sha256` (`09a086b27907bc06fbbf6269a71c036ae3598e4aca4eb9f653e5ed531d6bc599`) with DigiCert RFC 3161 TSA (`data/MANIFEST.sha256.tsr`, 5,996 bytes) and 3-calendar Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots`, 721 bytes).
   - Verified cross-platform + Linux OpenSSL X.509 DigiCert CA chain (`Verification: OK`) via `scripts/stamp_timestamps.py --verify` in `.github/workflows/ci.yml`, `scripts/dev.sh reproduce`, and `tests/test_repo_integrity.py`.
3. **Permanent Software Heritage SWHID & Submission Packet:**
   - Embedded permanent `visit_status: full` SWHID `swh:1:snp:0d84f85d8dc6b9c703784c655998864acee6c98d` across `CITATION.cff`, `formalization.yaml`, `README.md`, and `docs/threat-model.md`.
   - Added draft-labeled `docs/submission-packet.md` (Palomar Registry payload, human line-by-line fidelity checklist, specialist correspondence notes).
4. **All 4 Manuscripts Recompiled (`0.00 pt` Overfull):**
   - Recompiled `unified-contextuality.pdf`, `c3-spectral-counterexample.pdf`, `contextuality-tensor.pdf`, and `whitepaper.pdf` with Tectonic (`0` overfull hboxes, `0.00 pt`).
5. **Automated Clean-Clone Replication (`B44`):**
   - Executed fresh `git clone --depth 1` into an isolated temporary workspace on `Z:\` (`_tmp_clean_rep_pauli`, deleted after completion), running the full exact verification, pytest, Node, audit, blueprint, and site suite; recorded honestly in `REPLICATION.md` as author-automated (external human replication remains open).

## Remaining Honest Open Items

- External independent human replication and human line-by-line review sign-off (`human_line_by_line_review_recorded: false`).
- External scholarly submissions (Palomar Registry, Zenodo/HAL DOI, arXiv, specialist correspondence) remain drafts in `docs/submission-packet.md` awaiting author action.
