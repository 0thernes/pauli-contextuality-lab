# Run Log (`docs/run-log.md`)

Chronological audit trail of verification, formal proof, and consolidation runs (Build Standard item B40).

| Date | Version | Scope & Commands | Result |
|---|---|---|---|
| 2026-11-24 | `2.0.0` | Unified 3-track consolidation (`hoggar-bound-lab` v1.9.0 + `hoggar-bound` v1.0.0 + `contextuality-tensor-lab` v0.1.0 + `contextuality-evidence-lab` v1.0.0) into `pauli-contextuality-lab` | Consolidated |
| 2026-11-24 | `2.0.0` | `pytest -v tests/` (36 tests + 6 mutation subtests, Hypothesis + fuzz + adversarial binding + integrity) | 36/36 PASS |
| 2026-11-24 | `2.0.0` | `node --test tests/test_web_models.mjs` (Track 2 4-qubit enumeration + Track 3 exact BigInt stopping) | 2/2 PASS |
| 2026-11-24 | `2.0.0` | `python scripts/verify_all.py` (Track 1: 97+15+10+32+9 exact checks; Track 2: 262,144 assignments + 5 negative controls; Track 3: 18,000 trial replays + 512 assignments; `data/MANIFEST.sha256` 21 files; `third_party/SHA256SUMS.json` 15 files) | ALL PASS |
| 2026-11-24 | `2.0.0` | `scripts/arithmetic_audit.py` (66 files), `scripts/check_citations.py` (13 files, 20 arXiv IDs, 23 DOIs, 0 placeholders), `scripts/build_blueprint.py` (13 nodes, 48 Lean decl refs), `scripts/build_site.py` | ALL PASS |
| 2026-11-24 | `2.0.0` | Unified Lean 4.35.0 build (`HoggarBound`, `ContextualityTensor`, `Evidence`, `Solution`), `VerifyAll.lean` axiom audit, `scripts/check_readme_axioms.py`, and `Audit-Repo.ps1` | Verified |
