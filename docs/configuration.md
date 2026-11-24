# Environment and Configuration

No secrets, API keys, or cloud credentials are required to build, test, or reproduce any result in `pauli-contextuality-lab`.

## Optional Environment Variables

| Variable | Default | Purpose |
|---|---|---|
| `PYTHON` | `python3` (fallback `python`) | Python interpreter used by `scripts/dev.sh` |
| `ESHKOL_RUN` | *(unset; optional)* | Path to Eshkol runtime for optional Track 1/2/3 Eshkol cross-checks |
| `LAB_URL` | `http://127.0.0.1:8837` | Local server URL when running optional Playwright browser UI tests |
| `BROWSER_CHANNEL` | *(Playwright default)* | Browser channel override (e.g. `msedge`) for UI tests |

## Toolchains & Pinned Versions

- **Lean 4:** Pinned in `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`) and `lean/lake-manifest.json`.
- **Python:** Python 3.11–3.13 with pinned packages in `requirements.txt`.
- **C11:** Any C11 compiler (`gcc` or `clang`) with `-std=c11 -lm` (optional `-fsanitize=address,undefined`).
- **Node.js:** Node 22+ for Moonlab WASM execution and browser-model unit tests.
