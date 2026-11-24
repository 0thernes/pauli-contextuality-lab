#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PY="${PYTHON:-python3}"
command -v "$PY" >/dev/null 2>&1 || PY="python"

cmd="${1:-help}"
shift || true

case "$cmd" in
  setup)
    "$PY" -m pip install --upgrade pip
    "$PY" -m pip install -r requirements.txt
    if command -v lake >/dev/null 2>&1; then
      (cd lean && lake exe cache get)
    fi
    ;;

  build)
    if command -v cc >/dev/null 2>&1; then
      mkdir -p build/bin
      QR=third_party/quantum_rng/src/quantum_rng
      cc -O2 -std=gnu11 -Wall -Wextra tracks/spectral-bounds/src/hoggar.c "$QR/quantum_rng.c" -I"$QR" -lm -o build/bin/hoggar
      cc -O2 -std=gnu11 -Wall -Wextra -pthread tracks/spectral-bounds/src/w52_census_verify.c -lm -o build/bin/w52_census_verify
      cc -O2 -std=gnu11 -Wall -Wextra -pthread tracks/spectral-bounds/src/third_level.c -lm -o build/bin/third_level
    else
      echo "WARN: cc not found; skipping C11 build"
    fi
    if command -v lake >/dev/null 2>&1; then
      (cd lean && lake build HoggarBound ContextualityTensor Evidence)
    else
      echo "WARN: lake not found; skipping Lean build"
    fi
    ;;

  test)
    "$PY" -m pytest -v tests/
    if command -v node >/dev/null 2>&1; then
      node --test tests/test_web_models.mjs
    fi
    ;;

  lint)
    "$PY" -m ruff check scripts/ tests/ tracks/ || true
    "$PY" -m mypy --ignore-missing-imports scripts/check_citations.py scripts/check_readme_axioms.py scripts/arithmetic_audit.py scripts/build_blueprint.py || true
    if command -v lake >/dev/null 2>&1; then
      (cd lean && lake exe runLinter ContextualityTensor Evidence || true)
    fi
    ;;

  sanitizers)
    mkdir -p build/san
    QR=third_party/quantum_rng/src/quantum_rng
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/hoggar.c "$QR/quantum_rng.c" -I"$QR" -lm -o build/san/hoggar_san
    ./build/san/hoggar_san table 4 >/dev/null
    ./build/san/hoggar_san verify 3 f data/witness/n3_f.txt >/dev/null
    ./build/san/hoggar_san verify 4 h data/witness/n4_h.txt >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -pthread \
      tracks/spectral-bounds/src/w52_census_verify.c -lm -o build/san/w52_san
    echo "ASan/UBSan checks passed."
    ;;

  verify-lean)
    (cd lean && lake build HoggarBound ContextualityTensor Evidence Solution)
    (cd lean && lake env lean VerifyAll.lean)
    if grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b|implemented_by|@\[extern' lean/HoggarBound lean/ContextualityTensor lean/Evidence lean/Solution.lean | grep -vE '^[^:]+:[0-9]+:\s*(--|/-)'; then
      echo "ERROR: forbidden Lean token found!" >&2
      exit 1
    fi
    (cd lean && lake comparator --config comparator.json --paranoid)
    ;;

  blueprint)
    "$PY" scripts/build_blueprint.py
    ;;

  site)
    "$PY" scripts/build_blueprint.py
    "$PY" scripts/build_site.py
    ;;

  reproduce)
    "$PY" scripts/verify_all.py
    "$PY" -m pytest -v tests/
    "$PY" scripts/arithmetic_audit.py
    "$PY" scripts/check_citations.py
    "$PY" scripts/check_readme_axioms.py
    "$PY" scripts/build_blueprint.py
    "$PY" scripts/build_site.py
    ;;

  release)
    ver="${1:?Usage: dev.sh release X.Y.Z}"
    printf '%s\n' "$ver" > VERSION
    git add VERSION
    git commit -m "release: v$ver"
    git tag -a "v$ver" -m "Release v$ver"
    git push origin main --follow-tags
    ;;

  *)
    echo "Usage: scripts/dev.sh {setup|build|test|lint|sanitizers|verify-lean|blueprint|site|reproduce|release}"
    exit 2
    ;;
esac
