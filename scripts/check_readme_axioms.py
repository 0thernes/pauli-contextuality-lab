#!/usr/bin/env python3
"""Verify that README.md's verbatim #print axioms block matches results/lean-axioms-all.log
and that every audited theorem uses strictly standard axioms.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_LINE_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]$")
NO_AXIOM_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")


def parse_log(text: str) -> dict[str, set[str]]:
    # Unwrap Lean pretty-printed multi-line axiom lists
    unwrapped = re.sub(r",\n\s+", ", ", text.replace("\r\n", "\n"))
    found: dict[str, set[str]] = {}
    for raw in unwrapped.splitlines():
        line = raw.strip()
        m = AXIOM_LINE_RE.match(line)
        if m:
            axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
            found[m.group(1)] = axioms
            continue
        m2 = NO_AXIOM_RE.match(line)
        if m2:
            found[m2.group(1)] = set()
    return found


def main() -> int:
    log_path = ROOT / "results" / "lean-axioms-all.log"
    readme_path = ROOT / "README.md"
    if not log_path.is_file():
        print(f"ERROR: missing {log_path}", file=sys.stderr)
        return 1
    if not readme_path.is_file():
        print(f"ERROR: missing {readme_path}", file=sys.stderr)
        return 1

    log_decls = parse_log(log_path.read_text(encoding="utf-8"))
    if not log_decls:
        print("ERROR: no #print axioms lines parsed from results/lean-axioms-all.log", file=sys.stderr)
        return 1

    bad_axioms = {name: sorted(ax - ALLOWED) for name, ax in log_decls.items() if not (ax <= ALLOWED)}
    if bad_axioms:
        print(f"ERROR: non-standard axioms detected: {bad_axioms}", file=sys.stderr)
        return 1

    readme_decls = parse_log(readme_path.read_text(encoding="utf-8"))
    if not readme_decls:
        print("ERROR: README.md has no verbatim #print axioms lines", file=sys.stderr)
        return 1

    mismatches = []
    for name, ax in readme_decls.items():
        if name not in log_decls:
            mismatches.append(f"README cites '{name}' which is absent from results/lean-axioms-all.log")
        elif log_decls[name] != ax:
            mismatches.append(f"Axiom mismatch for '{name}': README={sorted(ax)} vs log={sorted(log_decls[name])}")

    if mismatches:
        for msg in mismatches:
            print("ERROR:", msg, file=sys.stderr)
        return 1

    print(
        f"PASS: {len(log_decls)} Lean declarations audited strictly within {sorted(ALLOWED)}; "
        f"{len(readme_decls)} headline declarations verified verbatim in README.md."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
