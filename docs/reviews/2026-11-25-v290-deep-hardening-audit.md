# Deep Forensic Hardening Audit (`v2.9.0` — Second-Round 3-Cycle Verification)

**Date:** 2026-11-25  
**Target:** `pauli-contextuality-lab` (`v2.8.0` → `v2.9.0`), cross-checked alongside sibling `kochen-specker-extremal-lab` (`v1.8.0` → `v1.9.0`) and `0thernes/unsolved-problems-mega-atlas` (`commit f838db1d7`, `1,900` problems).  
**Standards:** Build Standard for LLMs `v1.2.0` (`90` items, `10` finding classes) & Defensible Independent AI Research Playbook `v1.3` (`43` checklist items, `H01`–`H48`).

> **Epistemic-honesty note (Playbook v1.3 H48):** This document reports only the exact cycles, automated checks, and findings actually executed and verified in this audit — zero inflated pass multipliers.

## Cycle 1 — Full-Tree Security, Static Analysis, Provenance & Lean Module Map

| Finding Class | Location | Concrete Defect Found | Resolution & Guard |
|---|---|---|---|
| `hole` | `tracks/disjoint-mermin/scripts/build_paper.py:127` | Floating `https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js` missing `integrity="sha384-..."` and `crossorigin="anonymous"`; stale `Version 0.1.0` in LaTeX preamble. | Replaced with pinned MathJax `3.2.2` + `sha384` SRI + `crossorigin="anonymous"`, synced LaTeX preamble (`\usepackage{xurl}`, `Version 2.9.0`), and added permanent repo-wide test `test_all_cdn_scripts_have_sri_and_crossorigin` in `tests/test_repo_integrity.py`. |
| `hole` | `tracks/disjoint-mermin/scripts/check_release.py:22` | `urlopen(url)` flagged by `ruff S310` without explicit `https://`/`http://` scheme guard. | Added explicit scheme validation before `urlopen` and bumped `RELEASE_TAG = 'v2.9.0'`. |
| `issue` | `tracks/spectral-bounds/scripts/` (10 files) | `14` `ruff F401/F841/F541` findings across 10 non-SHA256-pinned Track 1 scripts (plus Windows `add_dll_directory` handle left unclosed in `stack_audit.py`). | Cleaned all 14 findings and explicitly closed `dll_search` in `stack_audit.py`; intentionally preserved SHA-256-pinned Track 2/3 `run_stack.py` byte-identical to `stack_report.json` provenance receipts. |
| `hole` | `lean/README.md` | Did not spell out how the 60 `.lean` files partition between `VerifyAll.lean` (45 transitive modules including Lean 4.35 `public import` modules in `Evidence`), `Challenge.lean` (1 spec), and standalone heavy finite-certificate verification modules (14 files). | Added explicit 60-module coverage table in `lean/README.md` confirming all 59 non-`Challenge` `.lean` files are scanned for zero forbidden tokens. |

## Cycle 2 — Zero-Overflow LaTeX Typesetting (`0.00 pt`), PDF Metadata & Live CI Receipts

| Finding Class | Location | Concrete Defect Found | Resolution & Verification |
|---|---|---|---|
| `issue` | `papers/spectral-bounds/unified-contextuality.tex` (Tables 1 & 2) | 4 residual sub-5 pt overfull hboxes (`1.87 pt`, `3.57 pt`, `4.56 pt`, `2.90 pt`). | Rebalanced Table 1 and Table 2 column fractions (summing strictly to `1.0000`) → **`0` overfull hboxes (`0.00 pt` max)**. |
| `issue` | `papers/disjoint-mermin/contextuality-tensor.tex` (Ref. 2) | 1 residual sub-1 pt overfull hbox (`0.96 pt`) on Reference 2 DOI line. | Added `\usepackage{xurl}` → **`0` overfull hboxes (`0.00 pt` max)**. |
| `issue` | `papers/spectral-bounds/unified-contextuality.{tex,md,html}` | Section 9.4 cited older `v2.7.2` Actions run IDs (`45693255547`, `45693255565`). | Updated to verified `v2.8.0` CI runs (`45722562212` 6-kernel Lean, `45722562213` 3-OS & 14-engine ASan/UBSan). |
| `blindspot` | PDF `/Info` inspection across all 4 PDFs | Verified decompressed PDF `/Info` dictionaries contain UTF-16BE `/Title` and `/Author = Alexander S. Donahue` across all 4 manuscripts. | Confirmed 4/4 PDFs carry exact `/Title` and `/Author` metadata with 0 missing glyphs and 0 undefined references. |

## Cycle 3 — Convergence Sweep & Release Verification

- **Mega-Atlas re-check (`0thernes/unsolved-problems-mega-atlas` at `f838db1d7`):** Still `1,900` problems; honest status remains `0 / 1,900` grand problems completely solved (bounded Pauli subcases settled in Lean 4.35.0 under `QM-011`).
- **Local Verification:** Full `pytest` (including new CDN SRI test), `node --test`, `ruff`, `mypy`, `scripts/verify_all.py`, `scripts/check_readme_axioms.py`, `scripts/arithmetic_audit.py`, `scripts/check_citations.py --online`, `scripts/build_blueprint.py`, `scripts/build_site.py`, WSL C11 14-engine ASan/UBSan (`scripts/dev.sh sanitizers`), `Audit-Repo.ps1` (`100.0%`, `68/68`, Core `30/30`), and WSL `audit-repo.sh` (`100.0%`).
