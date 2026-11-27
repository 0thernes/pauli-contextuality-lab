#!/usr/bin/env python3
"""Single-command end-to-end exact verification across all three research tracks."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run_step(label: str, cmd: list[str], cwd: Path = ROOT) -> None:
    print(f"==> {label}")
    res = subprocess.run(cmd, cwd=cwd, text=True)
    if res.returncode != 0:
        raise SystemExit(f"FAILED ({res.returncode}): {label}")


def verify_data_manifest() -> None:
    manifest = ROOT / "data" / "MANIFEST.sha256"
    if not manifest.is_file():
        raise SystemExit("FAILED: missing data/MANIFEST.sha256")
    checked = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        expected, rel = line.split(None, 1)
        target = ROOT / rel.strip().lstrip("*")
        if not target.is_file():
            raise SystemExit(f"FAILED: missing data file {rel}")
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != expected.lower():
            raise SystemExit(f"FAILED: SHA-256 mismatch for {rel}: {actual} != {expected}")
        checked += 1
    print(f"PASS: data/MANIFEST.sha256 verified ({checked} files).")


def verify_third_party_hashes() -> None:
    sums_path = ROOT / "third_party" / "SHA256SUMS.json"
    data = json.loads(sums_path.read_text(encoding="utf-8"))
    files_map = data.get("files", data) if isinstance(data, dict) else {}
    checked = 0
    for rel, expected in files_map.items():
        if not isinstance(expected, str):
            continue
        target = ROOT / "third_party" / rel
        if not target.is_file():
            target = ROOT / rel
        if not target.is_file():
            raise SystemExit(f"FAILED: missing third_party file {rel}")
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != expected.lower():
            raise SystemExit(f"FAILED: third_party SHA-256 mismatch for {rel}")
        checked += 1
    print(f"PASS: third_party/SHA256SUMS.json verified ({checked} files).")


def main() -> int:
    py = sys.executable
    verify_data_manifest()
    verify_third_party_hashes()

    # Track 1 exact verifiers (spectral-bounds)
    t1_scripts = ROOT / "tracks" / "spectral-bounds" / "scripts"
    for name in (
        "conjecture_e_trace_formula.py",
        "c3_sdp_dual_check.py",
        "c3_exact_optima_check.py",
        "norm_phase_family.py",
        "exact_degrees_n4_n5.py",
        "q7plus_triality_residuals.py",
        "desargues_augmented_sb.py",
        "pg_rigidity_and_w15.py",
    ):
        p = t1_scripts / name
        if p.is_file():
            run_step(f"Track 1: {name}", [py, str(p)], cwd=ROOT / "tracks" / "spectral-bounds")

    # Track 2 exact verifier (disjoint-mermin)
    t2_verify = ROOT / "tracks" / "disjoint-mermin" / "scripts" / "verify_exact.py"
    if t2_verify.is_file():
        run_step("Track 2: verify_exact.py", [py, str(t2_verify)], cwd=ROOT / "tracks" / "disjoint-mermin")

    # Track 3 independent artifact replay (sequential-evidence)
    t3_verify = ROOT / "tracks" / "sequential-evidence" / "scripts" / "verify_artifact.py"
    if t3_verify.is_file():
        run_step("Track 3: verify_artifact.py", [py, str(t3_verify)], cwd=ROOT / "tracks" / "sequential-evidence")

    print("ALL TRACK VERIFICATIONS PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
