# Roadmap

This roadmap follows the release discipline in the Defensible Independent AI Research Playbook v1.3: each milestone ships only after the previous milestone passes mechanical and editorial checks.

## Completed in `v2.3.0`–`v2.9.0` (2026-11-24 – 2026-11-25)

- Unified four scattered Pauli/Hoggar/Mermin repositories (`hoggar-bound-lab`, `hoggar-bound`, `contextuality-tensor-lab`, `contextuality-evidence-lab`) into one Lean 4.35.0 + Mathlib v4.35.0 workspace with deduplicated `third_party/` stack.
- Adopted open licensing (`Apache-2.0` code + `CC-BY-4.0` papers/docs) and accurate independent-researcher attribution (`Alexander S. Donahue`, ORCID `0009-0006-8168-9648`), removing premature LLC claims.
- Integrated `TwoQubit.lean` and `Witness.lean` (`d(W(5,2)) = 63`, `d(Q^-(5,2)) = 9`, Mermin-Peres, doily) alongside the full `HoggarBound`, `ContextualityTensor`, and `Evidence` libraries.
- Upgraded to Build Standard v1.2.0 (90 items, 10 finding classes, JSON Schema-validated `repo.yaml`, SHA-256-verified `gitleaks` + `osv-scanner`) and Playbook v1.3: `Challenge.lean` / `Solution.lean` / `comparator.json`, adversarial false-variant Lean rejection tests, Batteries linter, verbatim `#print axioms` CI sync, 27-node/162-declaration Lean Blueprint with SRI, 14-engine C11 ASan/UBSan, Hypothesis property tests, mutation/fuzz tests, Crossref retraction-aware citation audit, arithmetic audit, `ERRATA.md`, 1,900-problem Mega-Atlas cross-reference, CRediT/COI disclosures across all 4 manuscripts, and SLSA release attestations.

## Next Milestones (Strict Release Order)

1. **External mathematician correspondence & review (Saniga / Muller / Holweck / Giorgetti / Kelleher):** Share the clean unified repository, Track 1 unified preprint, and Track 2 Muller-Saniga Section 6 preprint; log all mathematical feedback and errata transparently.
2. **Independent clean-machine human replication:** Obtain at least one external clean-clone build (`lake exe cache get && lake build`, `lake comparator --paranoid`, `just reproduce`) and record it in `REPLICATION.md`.
3. **Human line-by-line statement fidelity sign-off:** Review every row of `docs/statement-fidelity.md` and flip `human_line_by_line_review_recorded: true` in `formalization.yaml` only once actually completed.
4. **Archival identifiers & registry submission:**
   - Software Heritage archival save (`swh:1:snp:...` / `swh:1:rel:...`).
   - Zenodo concept DOI (only after explicit author verification of Zenodo's April 2026 generative-AI depositor policy) or HAL/OSF identifier.
   - Palomar Registry submission (40-char commit SHA passing `lake comparator --paranoid`).
   - Update ORCID `0009-0006-8168-9648` via minted DOI (not self-assertion).
5. **Lean community & journal venues:**
   - Extract small, self-contained helper lemmas (finite-field quadratic forms, symplectic transvections, exact integer moment inequalities) for hand-reviewed Mathlib PRs under `Apache-2.0` (following Mathlib's human-written PR/Zulip prose rules).
   - Prepare peer-reviewed journal submissions (*Quantum*, *Journal of Formalized Reasoning*, or *J. Phys. A*) and arXiv `quant-ph` once an active category endorser reviews the manuscript.
   - Only after all steps above are settled: optional discoverability mirror on `ai.viXra.org` linking back to the canonical DOI, ORCID, GitHub repo, and Blueprint.
