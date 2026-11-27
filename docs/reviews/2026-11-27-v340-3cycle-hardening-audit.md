# 3-Cycle Forensic Hardening Audit (`v3.4.0`, 2026-11-27)

- **Repository:** `0thernes/pauli-contextuality-lab` (`v3.3.0` (`53e9875`) → **`v3.4.0`**)
- **Standards audited against:** Build Standard for LLMs `v1.2.0` (`repo.yaml`, `scripts/Audit-Repo.ps1`, `scripts/audit-repo.sh`) and Defensible Independent AI Research Playbook `v1.3` (`H48` literal-count reporting)
- **Author / Director:** Alexander S. Donahue (ORCID `0009-0006-8168-9648`)
- **Methodology:** Three literal sequential hardening cycles — **Cycle 1** (Full Proof, Verifier, Sanitizer, Citation, Axiom & Build-Standard Gauntlet), **Cycle 2** (Adversarial Repo-Wide Stale-Count, Lean-Token, HTML/PDF & Metadata Re-Audit), and **Cycle 3** (Audit-Record Closure & Clean Zero-Edit Final Verification Run). Every defect count below is literal; no synthetic pass inflation is used.

---

## Scope Delivered in `v3.4.0` (on top of published `v3.3.0`)

1. **Track 2 100% Formalization (`lean/ContextualityTensor/GeneralTheory.lean`, Eqs. 1–16, Targets 19–24):**
   - `heterogeneous_endpoint_reduction` (Theorem 2 / Eq. 7), `mixed_square_pentagram_minimum` (Eq. 12), `general_seed_epsilon_tends_to_one` (Theorem 5 / Eq. 13), `arbitrary_k_square_pauli_realization` & `arbitrary_k_pentagram_pauli_realization` (Eq. 5 on `HoggarBound.Pauli`), and `noisyScore_closed_form`, `square_noise_threshold_iff`, `pentagram_noise_threshold_iff`, `noisy_normalized_score_tends_to_zero` (Eqs. 14–16).
   - Live CI tamper-injection negative gate in `.github/workflows/lean-verify.yml` + `7/7` isolated AST source-code mutation suite in `tests/test_mutation_and_fuzz.py`.
2. **Track 1 Theorems 23–25 (Saniga November 2026 Correspondence, Targets 25–30):**
   - **Theorem 23 (`lean/HoggarBound/TrialityResiduals.lean`):** All four triality-induced 315-line deletions of $Q^+(7,2)$ (`1,260` residual contexts): exact degrees `0` (`dw52_residual_exact_zero`), universal `210` over every 9-solid spread (`SolidSpread.spread_residual_ge_210` + `m1_spread_residual_exact_210`), universal `252` over all 120 $Q(6,2)$'s (`q62_residual_ge_252` + `q62_residual_exact_252`), and `252` on the triality-dual 9-point ovoid deletion $Q^+(7,2) \setminus O$ (`ovoid_residual_exact_252`, strictly beating spectral floor `204` by `+48`).
   - **Theorem 24 (`lean/HoggarBound/PGRigidity.lean`, pure algebra, zero `decide +kernel`):** Rank-two + scalar decomposition `opA_realPoints_pgCssSign_decomp`, all-$N$ ($N \ge 4$) skew-trace no-go bound `pg_rigidity_lower_bound_all_N`, and `pg_rigidity_n8` forcing $\ge 166{,}115{,}415$ on $W(15,2)$, strictly above our C11 ASan/UBSan (`w15_verify.c`) verified witness `161,360,335` (`data/witness/n8_f_l4_opt.txt`, margin `4,755,080`) alongside `38,088,999` on $Q^+(15,2)$ (`data/witness/n8_h_l4_opt.txt`).
   - **Theorem 25 (`lean/HoggarBound/DesarguesQuasiQuadric.lean`):** All-$N$ universal `[DHOP]` fiber-flip two-character hyperplane law (`fiberFlip_hyperplane_card` & `fiberFlip_n4_71_63`: `71/63` across all `32,768` 4-qubit sets), Desargues $(10_3)$ 5-frame $E$ (`desargues_five_frame_and_10_3`), exact ovoid context parabola $L(S_T)=1575-256k+32k^2$ (`ovoid_context_parabola`, min `1,063` at $k=4$, collinear negative control `967`), decoupling/non-saturation of $S_B^+$ (`sb_aug_structural_properties`), and sharp pairwise-line-disjoint Mermin–Peres brackets (`k95_bounds_53_55`, `k103_bounds_87_107`, `sb4flip_bounds_112_123`, `sb_aug_bounds_121_127`).
   - **Scholarly attribution & correspondence integration:** Verbatim private-communication excerpt of M. Saniga et al. on six-qubit polar-disjoint $PG(5,2)$ hexagons (`unified-contextuality.{tex,md,html,pdf}`, Section 7.2.1 & Figure 2b `two-hexagons.png`), Acknowledgments to M. Saniga, Tsotchke repository URLs (`[Ts1]`–`[Ts4]`), and Track 2 private-communication credit to M. Saniga & A. Muller.

---

## Cycle 1 — Full Verification & Sanitizer Gauntlet (Defects Caught & Fixed)

| # | Class | Artifact | Literal Finding | Fix & Verification |
|---|---|---|---|---|
| 1 | `error` | `README.md`, `CLAIMS.md` | Track 2 independent-readout noise thresholds were misstated in prose as `22.48%`/`16.56%` (`6^{-1/3}`, `5^{-1/4}`) instead of the Lean-proved `6.32%`/`5.99%` (`(1-(2/3)^{1/3})/2`, `(1-(3/5)^{1/4})/2`). | Corrected both files to exact Lean formulas & percentages; added permanent regression guard in `tests/test_repo_integrity.py` forbidding `22.48%`, `16.56%`, `6^{-1/3}`, `5^{-1/4}`. |
| 2 | `conflict` | `LIMITATIONS.md` | Item `L15` contradicted `v3.2.0` by stating vertex-case membership `IsCaseC1`–`IsCaseC15` was outside Lean. | Reconciled `L15` accurately: `IsCaseC1`–`IsCaseC15` are kernel-proved in `ConjectureECases.lean`; only Jonah `[J3, Theorem B4]` single-orbit transitivity remains outside Lean. |
| 3 | `bug` | `scripts/build_blueprint.py` | Hardcoded `"12-target"` in Blueprint header HTML instead of reading live target count from `lean/comparator.json`. | Replaced with dynamic `{bridge_targets}-target` (now `30-target`); verified `32 nodes / 251 Lean decls`. |
| 4 | `error` | `papers/spectral-bounds/unified-citation.bib` | Stale `version = {3.1.0}` and old date while `VERSION` was `3.3.0`. | Synced to `3.3.0` / `2026-11-27`; added automated BibTeX version parity check in `tests/test_repo_integrity.py`. |
| 5 | `issue` | `lean/HoggarBound/{PGRigidity,TrialityResiduals}.lean` | Batteries `runLinter` reported 1 unused `[DecidableEq n]` parameter in `PGRigidity.lean` and 3 missing docstrings in `TrialityResiduals.lean`. | Removed unused parameter and added docstrings; all 3 new modules pass all 15 Batteries linters with `0` errors (`18` CI-linted modules total). |
| 6 | `bug` | `papers/spectral-bounds/unified-contextuality.tex` | Including raw `figures/two-hexagons.pdf` triggered a XeTeX `pdf_link_obj()` crash; Table 2 col 4 overflowed `2.93 pt` on `357886635`; `[Ts1]`–`[Ts3]` 40-char SHAs overflowed `17–85 pt`; LaTeX `figure` counter collided with existing Figures 1–4. | Losslessly extracted native `2068×960` image stream to `figures/two-hexagons.png` (works in XeTeX, HTML, and Markdown); widened Table 2 col 4 (`0.0926 → 0.1126`); added `\allowbreak` inside SHA `\texttt{}`; labeled Figure `2b` matching existing figure style. Recompiled to **`0` overfull hboxes (`0.00 pt`), `0` undefined refs**. |
| 7 | `conflict` | `papers/spectral-bounds/unified-contextuality.{tex,md,html}` | Retained pre-`v1.8.0` prose `"were not rerun"` and `"All 17 rows"` (now 19 rows with $W(15,2)$ and $Q^+(15,2)$). | Updated all three formats to 100% parity (`19 rows`, $N=4\text{--}8$ interval percentages `75, 81, 91, 96, 95%`, `1.98%` gap on $Q^+(15,2)$). |

---

## Cycle 2 — Adversarial Re-Audit (Defects Caught & Fixed)

| # | Class | Artifact | Literal Finding | Fix & Verification |
|---|---|---|---|---|
| 8 | `conflict` | `docs/threat-model.md` | Still cited pre-Theorem-23–25 `v3.3.0` draft counts (`24 targets`, `10` non-vacuity, `8` refutations, `65` non-Challenge files, `217` explicit, `2,452` theorems, `14 C11`). | Synced to literal `v3.3.0` counts (`30 targets`, `13` non-vacuity, `11` refutations, `67` non-Challenge files, `255` explicit, `2,798` theorems, `15 C11`). |
| 9 | `conflict` | `ERRATA.md`, `ROADMAP.md`, `REPLICATION.md` | `ERRATA.md` `v3.3.0` row and `ROADMAP.md` lacked Theorems 23–25 and updated counts; `REPLICATION.md` lacked a `v3.3.0` author-run entry; superseded draft `2026-11-27-v330-3cycle-track2-general-theory-audit.md` remained in `docs/reviews/`. | Updated `ERRATA.md`, `ROADMAP.md`, `REPLICATION.md`; replaced draft review file with this consolidated audit record. |
| 10 | `issue` | Local PowerShell invocation of `scripts/Audit-Repo.ps1` | Invoking Windows PowerShell 5.1 from a bracketed workspace path without `-Path` fell back to `WindowsPowerShell\v1.0`. | Verified `pwsh -NoProfile -File scripts/Audit-Repo.ps1 -Path <repo>` and WSL `bash scripts/audit-repo.sh .` both score **`100.0% (68/68)`, Core `100.0% (30/30)`**. |

Cycle 2 repo-wide scans confirmed: **0** occurrences of `22.48%`/`16.56%`, **0** `sorry`/`admit`/`native_decide` across all 67 non-Challenge `.lean` files, **0** raw ASCII `---` in visible prose of `unified-contextuality.html`, and **0** overfull hboxes across all 4 compiled PDFs.

---

## Cycle 3 — Final Clean Verification Run (Zero Subsequent Edits)

Executed after all Cycle 1–2 edits and `scripts/generate_llms_full.py` regeneration:

- **Lean 4.35.0 (`VerifyAll.lean`):** `255` explicit `#print axioms` + `2,798` exhaustively audited kernel theorem constants (`1,464` authored / `1,434` non-Challenge across `68` `.lean` files; `0` disallowed axioms; strictly `[propext, Classical.choice, Quot.sound]`).
- **Batteries `runLinter`:** `18` clean modules, `0` errors.
- **Six-kernel comparator (`lean/comparator.json`):** `30` isolated targets (`Challenge.lean` vs `Solution.lean`).
- **Unified verifier (`scripts/verify_all.py`):** PASS (`10` track verifiers + `data/MANIFEST.sha256` `24 files` + `third_party/SHA256SUMS.json` `15 files`).
- **Test suites:** `pytest -v tests/` (`56 passed, 13 subtests passed`, including `6/6` C3 + `7/7` AST source-code mutants); `node --test tests/test_web_models.mjs` (`2/2`).
- **Audits & timestamps:** `arithmetic_audit.py` (`75` Python files), `check_citations.py --online` (`21` arXiv, `23` DOIs, `20` BibTeX, `0` issues), `check_readme_axioms.py --require-exhaustive` (`255` explicit / `2,798` exhaustive / `31` README headlines), `stamp_timestamps.py --verify` (DigiCert RFC 3161 TSA + 3-calendar OpenTimestamps on `e363723f...`), `ruff` (`0` errors), `mypy` (`0` errors).
- **Blueprint, Pages & Build Standard:** `build_blueprint.py` (`32` nodes / `251` Lean decls), `build_site.py` (`0` broken links), `Audit-Repo.ps1` & `audit-repo.sh` (`100.0%`, `68/68`, Core `30/30`).
- **C11 Sanitizers (WSL GCC 13.3):** `bash scripts/dev.sh sanitizers` — **all `15` C11 engines pass under ASan/UBSan** (`0` repo compiler warnings).

---

## Honest Residual Boundaries Preserved

- **Not externally peer reviewed;** `human_line_by_line_review_recorded: false` in `formalization.yaml`.
- **Outside Lean 4 kernel:** 42-orbit $W(5,2)$ C census (`w52_census_verify.c`), 540.3M-form $N=9$ rank-8 cyclic-symmetry census (`n9_rank8_search.c`), Jonah `[J3, Theorem B4]` single-orbit transitivity transfer, concrete C11/Python $N=8$ witness recounts (`161,360,335` on $W(15,2)$ and `38,088,999` on $Q^+(15,2)$), closing residual integer gaps inside the Theorem 25 brackets on $K_{95}, K_{103}, S_B^{(4)}, S_B^+$, Track 3 physical experimental assumptions, and browser/Moonlab simulations.
