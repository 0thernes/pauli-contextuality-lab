# Replication Protocol (`REPLICATION.md`)

This document gives the exact, clean-clone commands to reproduce every automated test, exact verifier, C11 sanitizer check, Lean 4.35.0 proof, 6-kernel comparator replay, Blueprint build, and GitHub Pages assembly.

## 1. Prerequisites

- **Git**
- **Python 3.11–3.13** (`pip install -r requirements.txt`)
- **Node.js 22+** (for browser-model unit tests and Moonlab WASM checks)
- **GCC or Clang** (C11, optional `-fsanitize=address,undefined` on Linux/macOS)
- **Lean 4 (`elan`)** — automatically selects `leanprover/lean4:v4.35.0` from `lean/lean-toolchain`
- **Bubblewrap (`bwrap`)** on Linux for sandboxed `lake comparator --paranoid`

## 2. Clean-Clone Replication Commands

```bash
git clone https://github.com/0thernes/pauli-contextuality-lab.git
cd pauli-contextuality-lab

# 1. Python & Node verification suites + exact verifiers + audits + Blueprint + site
python -m pip install -r requirements.txt
python scripts/verify_all.py
python -m pytest -v tests/
node --test tests/test_web_models.mjs
python scripts/arithmetic_audit.py
python scripts/check_citations.py
python scripts/check_readme_axioms.py
python scripts/build_blueprint.py
python scripts/build_site.py

# 2. C11 engines with AddressSanitizer + UndefinedBehaviorSanitizer (Linux/macOS)
bash scripts/dev.sh sanitizers

# 3. Full Lean 4.35.0 build, exhaustive axiom audit & 6-kernel comparator
cd lean
lake exe cache get
lake build HoggarBound ContextualityTensor Evidence Solution
lake env lean VerifyAll.lean
lake comparator --config comparator.json --paranoid
```

## 3. Replication Log

External independent replications are welcomed — open an issue or email `0_0@0thernes.art` with your OS, tool versions, commit SHA, and command output to add a row below.

| Date | Replicator | Environment | Scope Verified | Result |
|---|---|---|---|---|
| 2026-11-24 | Alexander S. Donahue (author / local & CI) | Windows 11 + Ubuntu 24.04 GitHub Actions, Python 3.12/3.13, Node 22, Lean 4.35.0 | Unified 3-track Lean build, `VerifyAll.lean`, `verify_all.py`, `pytest`, Node tests, Blueprint, site, Build Standard v1.1.0 audit | Pass (author-run; independent external replication still open) |
| 2026-11-25 | Alexander S. Donahue (author / local & CI) | Windows 11 + WSL2 + Ubuntu 24.04/macOS/Windows CI, Python 3.12, Node 22, Lean 4.35.0 | `v2.9.0` Build Standard v1.2.0 (`100.0%`, `68/68`), Playbook v1.3 checks (adversarial false-variant Lean tests, Crossref retraction audit, 14-engine C11 ASan/UBSan, 6-kernel `lake comparator --paranoid`) | Pass (author-run; independent external replication still open) |
