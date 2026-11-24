# Consolidation & Ten-Pass Gold Standard Audit (`v2.0.0`, 2026-11-24)

This review documents the consolidation of four standalone Pauli contextuality repositories (`0thernes/hoggar-bound-lab`, `0thernes/hoggar-bound`, `0thernes/contextuality-tensor-lab`, `0thernes/contextuality-evidence-lab`) into `0thernes/pauli-contextuality-lab`, audited against **Build Standard for LLMs v1.1.0** (90 items) and the **Defensible Independent AI Research Playbook v1.1** (10-pass protocol). Every finding is classified using the six-class taxonomy (`bug`, `error`, `issue`, `problem`, `dilemma`, `conflict`).

## Consolidation Inventory & Decisions

| Legacy Source | Disposition | Rationale |
|---|---|---|
| `0thernes/hoggar-bound-lab` (`v1.9.0`) | Consolidated → Track 1 (`tracks/spectral-bounds/`, `lean/HoggarBound/`, `papers/spectral-bounds/`) + GitHub archived (read-only redirect) | Eliminates 30-file root clutter and legacy frozen-audit lock while preserving full v1.9.0 Lean formalizations and links. |
| `0thernes/hoggar-bound` (`v1.0.0`) | Unique Lean modules (`Witness.lean`, `TwoQubit.lean`), C search (`legacy-search/`), ILP check (`ilp_qminus.py`), and `revtex-v1/` merged into Track 1 + GitHub archived | Eliminates stale Nov 9 duplicate repo while keeping kernel-checked `d(W(5,2))=63`, `d(Q^-(5,2))=9`, and Mermin-Peres/doily theorems. |
| `0thernes/contextuality-tensor-lab` (`v0.1.0`) | Consolidated → Track 2 (`tracks/disjoint-mermin/`, `lean/ContextualityTensor/`, `papers/disjoint-mermin/`) + GitHub archived | Shares identical Lean 4.35.0 / Mathlib `56a005855ea1` pin & `third_party/` stack; directly addresses Muller & Saniga (`arXiv:2609.19862v1`). |
| `0thernes/contextuality-evidence-lab` (`v1.0.0`) | Consolidated → Track 3 (`tracks/sequential-evidence/`, `lean/Evidence/`, `papers/sequential-evidence/`) + GitHub archived | Shares identical Lean 4.35.0 / Mathlib `56a005855ea1` pin & `third_party/` stack; unified hash-bound verification. |
| `0thernes/kochen-specker-extremal-lab` | Kept separate and upgraded to `v1.1.0` Gold Standard (Apache-2.0/CC-BY-4.0, 6-kernel Comparator) | Preserves zero-Mathlib, <30s minimal formal trust base for ray-pool SAT/DRUP proofs. |

## Ten-Pass Review Disposition

| Pass | Lens | Findings & Resolution |
|---|---|---|
| **1** | Claims ledger & scope | **`[issue]` Fixed:** Unified `CLAIMS.md` tags all 13 claim families (`C01`–`C13`) with explicit falsifiers; `LIMITATIONS.md` states real-vs-metaphor and non-peer-reviewed status. |
| **2** | Statement fidelity | **`[issue]` Fixed:** Unified `docs/statement-fidelity.md` covers all three tracks; `lean/Challenge.lean` <-> `lean/Solution.lean` isolates 12 headline targets across Tracks 1–3; `NonVacuity.lean` certifies 10 non-vacuity witnesses. |
| **3** | Formal trust base | **`[issue]` Fixed:** Single Lean 4.35.0 + Mathlib `56a005855ea1` workspace compiles all three libraries plus ported `Witness.lean` & `TwoQubit.lean`; `VerifyAll.lean` audits axioms strictly within `[propext, Classical.choice, Quot.sound]`; verbatim lines synced to `README.md` (`check_readme_axioms.py`); 6-kernel `lake comparator --paranoid` configured in `.github/workflows/lean-verify.yml`. |
| **4** | Novelty & literature | **`[issue]` Fixed:** Explicit attribution in `NOTICE`, `LIMITATIONS.md`, and `papers/README.md` distinguishing peer-reviewed papers (Muller/Saniga/Holweck/Giorgetti/Kelleher, Okumura) from unreviewed preprints (Jonah Zenodo notes, Cieśliński, Li–Gupta–Ganesh). |
| **5** | Citation integrity | **`[issue]` Fixed:** `scripts/check_citations.py` validated 13 manuscript files, 20 arXiv IDs, 23 DOIs, 0 placeholders. |
| **6** | Numerics, C11 & tests | **`[bug]` Fixed:** Track 3 `run_experiment.py` updated to resolve deduplicated root `third_party/` and refresh `web/experiment.json`; 36/36 pytest (Hypothesis, mutation, 300-payload fuzz, integrity) + 2/2 Node + 7/7 exact verifiers pass; `scripts/arithmetic_audit.py` explicitly labels all 66 Python files. |
| **7** | Reproduction & Blueprint | **`[conflict]` Fixed:** Single unified `.github/workflows/pages.yml` builds `scripts/build_blueprint.py` (13 nodes, 48 Lean decl refs) under `/blueprint/` alongside all 3 web labs and papers — zero competing Pages workflows. |
| **8** | Provenance & attestations | **`[issue]` Fixed:** `data/MANIFEST.sha256` (21 files), `third_party/SHA256SUMS.json` (15 files), tag-triggered `SHA256SUMS` + Sigstore SLSA attestations (`actions/attest-build-provenance`). |
| **9** | Ethics, legal & licensing | **`[problem]` & `[conflict]` Fixed:** Removed unformed `0thernes LLC` claims; standardized to `Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)`; re-licensed code to `Apache-2.0` + papers/docs to `CC-BY-4.0`; added explicit CRediT & AI-contribution disclosure. |
| **10** | External human scrutiny | **`[issue]` Open (transparently logged):** No external human mathematician has yet completed independent replication or signed off on `docs/statement-fidelity.md`; tracked in `REPLICATION.md`, `formalization.yaml`, and `ROADMAP.md` ahead of correspondence with M. Saniga, A. Muller, F. Holweck, C. Kelleher, and A. Giorgetti. |
