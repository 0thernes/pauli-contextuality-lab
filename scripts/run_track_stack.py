#!/usr/bin/env python3
"""Run any track's native Tsotchke stack runner (Moonlab, QGTL, quantum_rng, Eshkol)
in an isolated staging directory that binds the shared monorepo `third_party/` and
`data/` trees alongside the unmodified, SHA-256-fingerprinted track sources.

Usage:
    python scripts/run_track_stack.py disjoint-mermin [--dry-run] [-- ...]
    python scripts/run_track_stack.py sequential-evidence [--dry-run] [-- ...]
    python scripts/run_track_stack.py spectral-bounds [--dry-run] [-- ...]
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

TRACK_ENTRYPOINTS: dict[str, str] = {
    "disjoint-mermin": "scripts/run_stack.py",
    "sequential-evidence": "scripts/run_stack.py",
    "spectral-bounds": "scripts/stack_audit.py",
}


def stage_track(track: str, dest: Path) -> Path:
    track_dir = ROOT / "tracks" / track
    if not track_dir.is_dir():
        raise FileNotFoundError(f"Unknown track directory: {track_dir}")
    for sub in ("scripts", "src", "results"):
        src_sub = track_dir / sub
        if src_sub.is_dir():
            shutil.copytree(src_sub, dest / sub)
    shutil.copytree(ROOT / "third_party", dest / "third_party")
    if track == "spectral-bounds":
        shutil.copytree(ROOT / "data", dest / "data")
    return dest / TRACK_ENTRYPOINTS[track]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("track", choices=sorted(TRACK_ENTRYPOINTS))
    parser.add_argument("--dry-run", action="store_true", help="Stage isolated workspace, verify entrypoints, and exit.")
    args, extra = parser.parse_known_args(argv)
    if extra and extra[0] == "--":
        extra = extra[1:]

    with tempfile.TemporaryDirectory(prefix=f"pcl_stack_{args.track}_") as tmp:
        stage = Path(tmp)
        entry = stage_track(args.track, stage)
        if not entry.is_file():
            print(f"ERROR: missing staged entrypoint {entry}", file=sys.stderr)
            return 1
        if not (stage / "third_party" / "SHA256SUMS.json").is_file():
            print("ERROR: staged third_party/SHA256SUMS.json missing", file=sys.stderr)
            return 1
        if args.dry_run:
            print(f"PASS: staged {args.track} -> {entry.relative_to(stage)} with shared third_party/ intact")
            return 0
        res = subprocess.run([sys.executable, str(entry), *extra], cwd=stage)
        return res.returncode


if __name__ == "__main__":
    raise SystemExit(main())
