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
    "$PY" -m ruff check scripts/ tests/ || true
    "$PY" -m ruff check --select E9,F821,F822,F823,B tracks/ || true
    "$PY" -m mypy --ignore-missing-imports scripts/ || true
    if command -v lake >/dev/null 2>&1; then
      (cd lean && lake exe runLinter HoggarBound.Bound HoggarBound.Stability ContextualityTensor Evidence || true)
    fi
    ;;

  sanitizers)
    mkdir -p build/san
    QR=third_party/quantum_rng/src/quantum_rng
    QG=(-Ithird_party/qgtl/include -Ithird_party/qgtl/stub third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c)
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/hoggar.c "$QR/quantum_rng.c" -I"$QR" -lm -o build/san/hoggar_san
    ./build/san/hoggar_san table 4 >/dev/null
    ./build/san/hoggar_san exhaust2 >/dev/null
    ./build/san/hoggar_san lines 2 f >/dev/null
    ./build/san/hoggar_san falsify 2 f 42 5 50 >/dev/null
    ./build/san/hoggar_san verify 4 f data/witness/n4_f.txt >/dev/null
    ./build/san/hoggar_san verify 4 h data/witness/n4_h.txt >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -pthread \
      tracks/spectral-bounds/src/w52_census_verify.c -lm -o build/san/w52_san
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -pthread \
      tracks/spectral-bounds/src/third_level.c -lm -o build/san/third_level_san
    ./build/san/third_level_san >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/orbits7.c -o build/san/orbits7_san
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/legacy-search/wcheck.c -o build/san/wcheck_san
    ./build/san/wcheck_san data/witness/n4_f.txt data/witness/n4_h.txt >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/legacy-search/exhaust.c -o build/san/exhaust_san
    ./build/san/exhaust_san 2 f >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/legacy-search/tabu.c -lm -o build/san/tabu_san
    ./build/san/tabu_san 2 f 42 0.05 build/san/tabu_out.txt >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      "${QG[@]}" tracks/spectral-bounds/src/qgt_hoggar.c -lm -o build/san/qgt_hoggar_san
    ./build/san/qgt_hoggar_san data/witness/n3_f_hoggar_moonlab.txt data/witness/n4_h_hoggar_moonlab.txt >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      "${QG[@]}" tracks/spectral-bounds/src/qgt_flat.c -lm -o build/san/qgt_flat_san
    ./build/san/qgt_flat_san --no-seven >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/disjoint-mermin/src/stack_qrng.c "$QR/quantum_rng.c" -I"$QR" -lm -o build/san/dm_qrng_san
    ./build/san/dm_qrng_san 20261109 64 >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/family7.c -o build/san/family7_san
    ./build/san/family7_san 0 2 >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/sample7.c -o build/san/sample7_san
    ./build/san/sample7_san 0 3 200 42 >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/n9_rank8_search.c -o build/san/n9_rank8_san
    ./build/san/n9_rank8_san --smoke >/dev/null
    cc -O1 -g -std=gnu11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer \
      tracks/spectral-bounds/src/qrng_stream.c "$QR/quantum_rng.c" -I"$QR" -lm -o build/san/qrng_stream_san
    ./build/san/qrng_stream_san 42 64 >/dev/null
    echo "All 14 C11 ASan/UBSan checks passed."
    ;;

  verify-lean)
    (cd lean && lake build HoggarBound ContextualityTensor Evidence Solution VerifyAll)
    (cd lean && lake env lean VerifyAll.lean)
    "$PY" -m pytest -v -k test_no_forbidden_lean_tokens_in_proof_modules tests/test_repo_integrity.py
    (cd lean && lake env leanchecker --fresh Evidence || true)
    (cd lean && lake env leanchecker --fresh ContextualityTensor || true)
    (cd lean && lake env leanchecker --fresh Solution || true)
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
    "$PY" scripts/stamp_timestamps.py --verify
    "$PY" scripts/build_blueprint.py
    "$PY" scripts/build_site.py
    ;;

  release)
    ver="${1:?Usage: dev.sh release X.Y.Z}"
    [[ "$ver" =~ ^[0-9]+\.[0-9]+\.[0-9]+([-+][0-9A-Za-z.-]+)?$ ]] || { echo "Usage: dev.sh release X.Y.Z" >&2; exit 2; }
    if git rev-parse "v$ver" >/dev/null 2>&1; then echo "tag v$ver already exists" >&2; exit 2; fi
    grep -Eq "^## \[$ver\]" CHANGELOG.md || { echo "CHANGELOG.md has no '## [$ver]' section" >&2; exit 2; }
    printf '%s\n' "$ver" > VERSION
    for f in VERSION CITATION.cff CHANGELOG.md; do [ -f "$f" ] && git add "$f"; done
    git commit -m "release: v$ver" || true
    git tag -a "v$ver" -m "Release v$ver"
    git push origin main --follow-tags
    ;;

  *)
    echo "Usage: scripts/dev.sh {setup|build|test|lint|sanitizers|verify-lean|blueprint|site|reproduce|release}"
    exit 2
    ;;
esac
