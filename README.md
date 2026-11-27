# Pauli Contextuality Lab

Machine-checked Lean 4.35.0 proofs, exact integer/rational verifiers, research preprints, and reproducible interactive labs unifying three Pauli contextuality research tracks: spectral bounds and Jonah's Conjecture E, exact disjoint Mermin configuration degrees, and finite-horizon sequential contextuality certificates.

[![CI](https://github.com/0thernes/pauli-contextuality-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/pauli-contextuality-lab/actions/workflows/ci.yml)
[![Lean 4.35.0 Verification](https://github.com/0thernes/pauli-contextuality-lab/actions/workflows/lean-verify.yml/badge.svg)](https://github.com/0thernes/pauli-contextuality-lab/actions/workflows/lean-verify.yml)
[![Pages & Blueprint](https://github.com/0thernes/pauli-contextuality-lab/actions/workflows/pages.yml/badge.svg)](https://0thernes.github.io/pauli-contextuality-lab/)
[![License: Apache-2.0 / CC-BY-4.0](https://img.shields.io/badge/license-Apache--2.0%20%2F%20CC--BY--4.0-green)](LICENSE)
[![Version 3.1.0](https://img.shields.io/badge/version-3.1.0-informational)](CHANGELOG.md)

![Pauli Contextuality Lab overview](docs/media/social-preview.svg)

**Status:** Active research preprints (`v3.1.0`, 26 November 2026) — **NOT externally peer reviewed**; AI-assisted under human direction ([LIMITATIONS.md](LIMITATIONS.md)).  
**Author:** Alexander S. Donahue, independent researcher ([ORCID 0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`).  
**Live Portal & Blueprint:** [Pauli Contextuality Lab](https://0thernes.github.io/pauli-contextuality-lab/) · [Lean 4 Dependency Blueprint](https://0thernes.github.io/pauli-contextuality-lab/blueprint/) · [Papers](papers/README.md) · [Claims Ledger](CLAIMS.md) · [Statement Fidelity](docs/statement-fidelity.md) · [Errata & Withdrawal](ERRATA.md) · [Mega-Atlas Audit](docs/mega-atlas-cross-reference.md) · [Replication Protocol](REPLICATION.md) · [Submission Packet (Draft)](docs/submission-packet.md)  
**Archival & Timestamp Provenance:** Software Heritage [`swh:1:snp:54b1005a1e5ebde0c4dd89892c1bff4c3e6845ba`](https://archive.softwareheritage.org/swh:1:snp:54b1005a1e5ebde0c4dd89892c1bff4c3e6845ba) · DigiCert RFC 3161 TSA (`data/MANIFEST.sha256.tsr`) · Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots`)

> **Consolidation note:** This repository consolidates four earlier standalone Pauli repositories (`0thernes/hoggar-bound-lab`, `0thernes/hoggar-bound`, `0thernes/contextuality-tensor-lab`, and `0thernes/contextuality-evidence-lab`, all archived read-only with redirects) into one Lean 4.35.0 + Mathlib `v4.35.0` workspace with a single deduplicated `third_party/` stack and open `Apache-2.0` / `CC-BY-4.0` licensing. The zero-Mathlib ray-pool Kochen–Specker repository remains separate at [`0thernes/kochen-specker-extremal-lab`](https://github.com/0thernes/kochen-specker-extremal-lab) to preserve its minimal Mathlib-free trust base.

---

## Five-Second Formal Proof Check (`#print axioms`)

The theorems in the 43 modules imported by `lean/VerifyAll.lean` (the libraries `HoggarBound`, `ContextualityTensor`, `Evidence` and `lean/Solution.lean`) compile with **no `sorry`, no `admit`, no `native_decide` and no custom axioms**; the only `sorry` tokens are the 12 intended specification stubs in `lean/Challenge.lean`. These theorems are kernel-checked by Lean (`lake build`, `#print axioms`). The 12 comparator targets listed in `lean/comparator.json`, with their dependency closure, were also accepted by **6 independent kernels** (`lean-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`, `lean-default`) via `lake comparator --paranoid` in CI; other theorems, including the Track 2 limit theorems and the small degrees 63 and 9, are checked by the standard Lean kernel only. Nine Track 1 modules (`Saturated`, `SaturatedFive`, `SaturatedPhaseFive`, `SaturatedPhaseSeven`, `C3Certificate`, `C3Spectra`, `C3Theorem`, `FlatData`, `PhaseData`) are not compiled by CI at this release ([LIMITATIONS.md](LIMITATIONS.md)). Exact verbatim output from `cd lean && lake env lean VerifyAll.lean` ([full log: 166 explicit `#print axioms` plus an exhaustive check of 2,206 kernel theorem constants, auxiliary constants included](results/lean-axioms-all.log), checked in CI by `scripts/check_readme_axioms.py`):

```text
'HoggarBound.hoggar_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.hoggar_bound_quaternionic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.mermin_peres' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.degree_three_qubit' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.degree_three_qubit_elliptic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.saturation_tfae' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.exists_near_extremal_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.C3ExactOptima.corollary16_exact_binary_optima' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.ConjectureE.jonah_conjecture_e_all_nine_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.ExactDegreesN4N5.w72_ge_1455' depends on axioms: [propext, Classical.choice, Quot.sound]
'HoggarBound.ExactDegreesN4N5.q9plus_ge_6444' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextualityTensor.square_minimum_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextualityTensor.pentagram_minimum_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextualityTensor.global_actual_square_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextualityTensor.global_actual_pentagram_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Evidence.sharp_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Evidence.BetTree.finite_hitting_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Evidence.concrete_classical_false_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Three Unified Research Tracks

| Track | Path & Lean Library | Headline Results | Preprint & Interactive Lab |
|---|---|---|---|
| **1 · Spectral Bounds & Conjecture E** | [`tracks/spectral-bounds/`](tracks/spectral-bounds/README.md) · `lean/HoggarBound/` | Formalizes Jonah's universal and Kramers spectral floors (prior work, `doi:10.5281/zenodo.23538829`; here for arbitrary supports) and five-way saturation equivalences; known small degrees formalized ($d(Q^+(3,2))=1$, $d(W(5,2))=63$, $d(Q^-(5,2))=9$); infinite family of non-closed pure-CCZ sets $\lvert\Psi_{3m}\rangle$ attaining the floor (all $m \ge 1$, contextual for $m \ge 2$; degree $2{,}016$ at $m = 2$); kernel-checked lower bounds $d(W(7,2)) \ge 1455$ and $d(Q^+(9,2)) \ge 6444$ (Jonah, `doi:10.5281/zenodo.23510634`, earlier claimed the exact values $1575$ and $6975$, computer-assisted); for **Jonah's Conjecture E**, strict-law failure for one explicit representative of each of the 9 vertex cases, all $N \ge 4$ (C1 and C6 were already proved by Jonah; that each representative is in its case, and coverage of whole cases via his Theorem B4, are outside Lean); exact binary completion optima **368 and 344** for one four-qubit C3 sign pair via integer SDP-dual certificates. | [Unified PDF](papers/spectral-bounds/unified-contextuality.pdf) · [C3 Lab](https://0thernes.github.io/pauli-contextuality-lab/c3-lab/) · [Explorer](https://0thernes.github.io/pauli-contextuality-lab/independent-review/) |
| **2 · Disjoint Mermin Configurations** | [`tracks/disjoint-mermin/`](tracks/disjoint-mermin/README.md) · `lean/ContextualityTensor/` | Exact contextuality degrees $d_k = (7^k - 5^k)/2$ ($k$ disjoint Peres–Mermin squares) and $(6^k - 4^k)/2$ ($k$ Mermin pentagrams) for the explicit union-context family, with $2d_k/L_k \to 1$. This answers the stacking-limit question in **Section 6 of Muller & Saniga (`arXiv:2609.19862v1`, unreviewed preprint)** for disjoint squares and pentagrams only. The identification of the Lean seed contexts with the source's $HS(kG)$ rests on enumeration and the source's Sec. 4.2, not on Lean; the limit theorems are checked by the standard Lean kernel, not by the six-kernel comparator. | [Paper PDF](papers/disjoint-mermin/contextuality-tensor.pdf) · [4-Qubit Lab](https://0thernes.github.io/pauli-contextuality-lab/disjoint-mermin/) |
| **3 · Sequential Contextuality Evidence** | [`tracks/sequential-evidence/`](tracks/sequential-evidence/README.md) · `lean/Evidence/` | Formalizes two elementary bounds ([`PRIOR_ART.md`](papers/sequential-evidence/PRIOR_ART.md)): the Peres–Mermin setting-bias floor $\min_c p(c)$ and a finite betting-tree hitting bound $\le z/T$ (a finite form of Ville's inequality). Miscalibration example: **97.24%** naive vs **0.89%** bias-aware false rejection at nominal 1% (exact-rational Python computation; Lean proves a false-positive probability above 4.3% for a 36-round tree). | [Paper PDF](papers/sequential-evidence/whitepaper.pdf) · [Evidence Lab](https://0thernes.github.io/pauli-contextuality-lab/sequential-evidence/) |

---

## Quickstart

From a clean clone (Python 3.11–3.13, Node 22+, optional Lean 4 `elan` & GCC/Clang):

```bash
git clone https://github.com/0thernes/pauli-contextuality-lab.git
cd pauli-contextuality-lab
python -m pip install -r requirements.txt

# 1. Exact verification across all 3 tracks + dataset & third_party SHA-256 checksums
python scripts/verify_all.py

# 2. Automated Python (exact, Hypothesis property, mutation/fuzz, integrity) & Node suites
python -m pytest -v tests/
node --test tests/test_web_models.mjs

# 3. Audits, timestamp check, Blueprint declaration check & unified Pages build
python scripts/arithmetic_audit.py
python scripts/check_citations.py
python scripts/check_readme_axioms.py
python scripts/stamp_timestamps.py --verify
python scripts/build_blueprint.py
python scripts/build_site.py
```

Expected headline output: `ALL TRACK VERIFICATIONS PASSED.`, `52 passed` in pytest, `2 pass` in Node, and `PASS: Blueprint validated 27 nodes (162 Lean decls with exact GitHub #L links)`.

### Full Lean 4.35.0 Verification & 6-Kernel Comparator

```bash
cd lean
lake exe cache get
lake build HoggarBound ContextualityTensor Evidence Solution VerifyAll
lake env lean VerifyAll.lean
lake comparator --config comparator.json --paranoid
```

---

## Usage Examples

- **One-word task runner (`justfile` / `scripts/dev.sh`):**
  ```bash
  just test          # Run all Python + Node tests
  just verify-lean   # Build all 3 Lean libraries + VerifyAll + 6-kernel comparator
  just sanitizers    # Compile & run C11 engines under ASan/UBSan (Linux/macOS)
  just blueprint     # Check every \lean{...} declaration and rebuild dependency graph
  just reproduce     # Clean-clone full exact reproduction
  just audit         # Score repo against Build Standard for LLMs v1.2.0 (90 items)
  ```
- **Failure / negative-control example:** Running Track 2 verification under Python `-O` deliberately fails rather than silently skipping `assert` checks (`python -O -c "import sys; sys.path.insert(0, 'tracks/disjoint-mermin/src'); import certificates"` exits non-zero with `RuntimeError`). Similarly, mutating any single entry in `data/c3_exact_optima_certs.json` or `tracks/sequential-evidence/results/stack_trials.json` is rejected by `tests/test_mutation_and_fuzz.py` and `tests/test_sequential_evidence.py`.

---

## Architecture & Key Documents

| Path | Purpose |
|---|---|
| `lean/` | Unified Lean 4.35.0 + Mathlib `v4.35.0` package (`HoggarBound`, `ContextualityTensor`, `Evidence`, `Challenge`, `Solution`, `VerifyAll`) |
| `tracks/` | Self-contained code, C11 engines, exact Python verifiers, interactive web labs, and JSON receipts for Tracks 1–3 |
| `papers/` | Preprint PDFs, LaTeX sources, BibTeX, and external-reviewer correspondence guide ([papers/README.md](papers/README.md)) |
| `data/` & `third_party/` | SHA-256-pinned witness/flat datasets (`data/MANIFEST.sha256`, sealed by `data/MANIFEST.sha256.{tsr,ots}`) and single deduplicated Tsotchke stack (`third_party/SHA256SUMS.json`) |
| `docs/` | [Architecture](docs/architecture.md), [ADRs](docs/adr/), [Statement Fidelity](docs/statement-fidelity.md), [Threat Model](docs/threat-model.md), [FAQ](docs/faq.md), [Glossary](docs/glossary.md), [10-Pass Audit](docs/reviews/2026-11-24-consolidation-and-ten-pass-audit.md) |

---

## Limitations & Licensing

- **Epistemic boundary:** See [CLAIMS.md](CLAIMS.md) and [LIMITATIONS.md](LIMITATIONS.md). Nothing here is externally peer reviewed or measured on physical quantum hardware; human line-by-line statement fidelity sign-off remains open. Both external sources of the questions answered here (Muller & Saniga; Jonah) are unreviewed preprints.
- **Statement audit (2026-11-26):** Claim wording in this README, `CLAIMS.md`, `LIMITATIONS.md` and `docs/` was corrected to match an independent statement audit ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)); open items are listed in [ERRATA.md](ERRATA.md).
- **Dual open license:** All source code (`lean/`, `tracks/`, `scripts/`, `tests/`, `.github/`) is licensed under **[Apache-2.0](LICENSE)**. All manuscripts, figures, blueprints, and documentation (`papers/`, `docs/`, `blueprint/`, `README.md`) are licensed under **[CC-BY-4.0](LICENSE-DOCS)**. Vendored components under `third_party/` retain their original MIT licenses ([NOTICE](NOTICE)).
