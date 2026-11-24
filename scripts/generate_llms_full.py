#!/usr/bin/env python3
"""Generate llms-full.txt from AGENTS.md, CLAIMS.md, LIMITATIONS.md, and docs/build-standard.md."""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARTS = [
    ("AGENTS.md", ROOT / "AGENTS.md"),
    ("CLAIMS.md", ROOT / "CLAIMS.md"),
    ("LIMITATIONS.md", ROOT / "LIMITATIONS.md"),
    ("formalization.yaml", ROOT / "formalization.yaml"),
    ("docs/statement-fidelity.md", ROOT / "docs" / "statement-fidelity.md"),
]


def main() -> int:
    chunks = [
        ("# Pauli Contextuality Lab — Generated Bulk Context (`llms-full.txt`)\n\n"
         "> Generated automatically by `scripts/generate_llms_full.py`. Do not hand-edit.\n")
    ]
    for title, path in PARTS:
        if path.is_file():
            chunks.append(f"\n---\n\n## File: `{title}`\n\n" + path.read_text(encoding="utf-8").strip() + "\n")
    out = ROOT / "llms-full.txt"
    out.write_text("\n".join(chunks), encoding="utf-8", newline="\n")
    print(f"PASS: wrote {out} ({out.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
