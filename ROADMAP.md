# Roadmap

This roadmap follows the release discipline in the Defensible Independent AI Research Playbook v1.3: each milestone ships only after the previous milestone passes mechanical and editorial checks.

## Completed in `v2.3.0`–`v3.1.0` (2026-11-24 – 2026-11-26)

- Unified four scattered Pauli/Hoggar/Mermin repositories (`hoggar-bound-lab`, `hoggar-bound`, `contextuality-tensor-lab`, `contextuality-evidence-lab`) into one Lean 4.35.0 + Mathlib v4.35.0 workspace with deduplicated `third_party/` stack.
- Adopted open licensing (`Apache-2.0` code + `CC-BY-4.0` papers/docs) and accurate independent-researcher attribution (`Alexander S. Donahue`, ORCID `0009-0006-8168-9648`), removing premature LLC claims.
- Integrated `TwoQubit.lean`, `Witness.lean` (`d(W(5,2)) = 63`, `d(Q^-(5,2)) = 9`, Mermin-Peres, doily), and `HoggarBound.Stability` (quantitative third-moment stability, 6 theorems) into unified `VerifyAll.lean` alongside the full `HoggarBound`, `ContextualityTensor`, and `Evidence` libraries (`166` explicit `#print axioms` + `2,206` exhaustively audited theorems; 10 clean Batteries linter modules in CI).
- Upgraded to Build Standard v1.2.0 (`100.0%`, `68/68`, 10 finding classes, JSON Schema-validated `repo.yaml`, SHA-256-verified `gitleaks` + `osv-scanner`) and Playbook v1.3: `Challenge.lean` / `Solution.lean` / `comparator.json`, adversarial false-variant Lean rejection tests, verbatim `#print axioms` CI sync, 27-node/162-declaration Lean Blueprint with SRI, 14-engine C11 ASan/UBSan, Hypothesis property tests, mutation/fuzz tests, Crossref retraction-aware citation audit, arithmetic audit, DigiCert RFC 3161 TSA + 3-calendar OpenTimestamps (`data/MANIFEST.sha256.{tsr,ots}`, OpenSSL X.509 verified in CI), permanent Software Heritage SWHID (`swh:1:snp:54b1005a1e5ebde0c4dd89892c1bff4c3e6845ba`), draft-labeled `docs/submission-packet.md`, automated clean-clone replication receipt, `ERRATA.md`, 1,900-problem Mega-Atlas cross-reference, CRediT/COI disclosures across all 4 manuscripts (`0.00 pt` overfull hboxes), GFM Markdown table pipe-escaping guards, and SLSA release attestations.

## Next Milestones (Strict Release Order)

1. **External mathematician correspondence & review (Saniga / Muller / Holweck / Giorgetti / Kelleher):** Review and dispatch the drafts in `docs/submission-packet.md`; log all mathematical feedback and errata transparently.
2. **Independent clean-machine human replication:** Obtain at least one external human clean-clone build (`lake exe cache get && lake build`, `lake comparator --paranoid`, `just reproduce`) and record it in `REPLICATION.md` alongside our automated clean-clone check.
3. **Human line-by-line statement fidelity sign-off:** Review every row of `docs/statement-fidelity.md` using the checklist in `docs/submission-packet.md` and flip `human_line_by_line_review_recorded: true` in `formalization.yaml` only once actually completed.
4. **External archival identifiers & registry submission:**
   - Software Heritage archival save completed (`swh:1:snp:54b1005a1e5ebde0c4dd89892c1bff4c3e6845ba`; refreshed on each tagged release).
   - Zenodo concept DOI (only after explicit author verification of Zenodo's April 2026 generative-AI depositor policy) or **OSF Preprints** DOI fallback (Playbook v1.3 H13; HAL requires a formal affiliation and cannot delete accepted deposits).
   - Palomar Registry submission (after migrating remaining non-`Evidence` `.lean` files and `Challenge.lean`/`Solution.lean` to Lean 4.35 `module` headers; draft payload in `docs/submission-packet.md`).
   - Update ORCID `0009-0006-8168-9648` via minted DOI (not self-assertion).
5. **Lean community & journal venues:**
   - Extract small, self-contained helper lemmas (finite-field quadratic forms, symplectic transvections, exact integer moment inequalities) for hand-reviewed Mathlib PRs under `Apache-2.0` (following Mathlib's human-written PR/Zulip prose rules).
   - Prepare peer-reviewed journal submissions (*Quantum*, *Journal of Formalized Reasoning*, or *J. Phys. A*) and arXiv `quant-ph` once an active category endorser reviews the manuscript.
   - Only after all steps above are settled: optional discoverability mirror on `ai.viXra.org` linking back to the canonical DOI, ORCID, GitHub repo, and Blueprint.
