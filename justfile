# Task runner for pauli-contextuality-lab (Build Standard v1.2.0, item A31)
set shell := ["bash", "-euo", "pipefail", "-c"]

# List available recipes
default:
    @just --list

# Install pinned Python dependencies and fetch Mathlib cache
setup:
    bash scripts/dev.sh setup

# Build all Lean 4.35.0 libraries and compile C11 engines with -Wall -Wextra
build:
    bash scripts/dev.sh build

# Run unified Python (pytest) and Node.js test suites across all 3 tracks
test:
    bash scripts/dev.sh test

# Report-only linters & type checks (ruff, mypy, C warnings, Batteries runLinter)
lint:
    python3 -m ruff check scripts/ tests/ || true
    python3 -m mypy --ignore-missing-imports scripts/ || true
    bash scripts/dev.sh lint

# Compile and execute C11 verifiers with AddressSanitizer + UndefinedBehaviorSanitizer
sanitizers:
    bash scripts/dev.sh sanitizers

# Build Lean libraries, audit axioms (VerifyAll.lean), scan forbidden tokens, run lake comparator --paranoid
verify-lean:
    bash scripts/dev.sh verify-lean

# Validate Lean declarations in blueprint/src/content.tex and build the dependency graph
blueprint:
    bash scripts/dev.sh blueprint

# Assemble the unified GitHub Pages site (portal + 3 web labs + Blueprint + papers)
site:
    bash scripts/dev.sh site

# Clean-clone end-to-end reproduction of exact verifiers, audits, blueprint, and site
reproduce:
    bash scripts/dev.sh reproduce

# Score repository against Build Standard for LLMs v1.2.0 (90 items)
audit:
    bash scripts/audit-repo.sh .

# Tag and push a semantic version release straight to main
release version:
    bash scripts/dev.sh release "{{version}}"
