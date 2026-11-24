#!/usr/bin/env python3
"""Validate DOI, arXiv, Zenodo, and BibTeX citation identifiers across all manuscripts.

Static structural check runs offline in CI; pass --online to perform HTTP HEAD checks.
"""
from __future__ import annotations

import argparse
import json
import re
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"

ARXIV_RE = re.compile(r"arXiv:([0-9]{4}\.[0-9]{4,5}(?:v[0-9]+)?|[a-z-]+/[0-9]{7})", re.I)
DOI_RE = re.compile(r"\b(10\.[0-9]{4,9}/[-._;()/:A-Za-z0-9]+)")
PLACEHOLDER_RE = re.compile(r"(TODO\(cite\)|FIXME_DOI|10\.0000/|arXiv:0000\.00000)", re.I)


def scan_papers() -> dict:
    arxiv_ids: set[str] = set()
    dois: set[str] = set()
    placeholders: list[dict] = []
    files_scanned = 0

    for path in sorted(PAPERS_DIR.rglob("*")):
        if not path.is_file() or path.suffix.lower() not in {".md", ".tex", ".bib"}:
            continue
        files_scanned += 1
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = path.relative_to(ROOT).as_posix()
        for m in ARXIV_RE.finditer(text):
            arxiv_ids.add(m.group(1))
        for m in DOI_RE.finditer(text):
            cleaned = m.group(1).rstrip(".,;)]}")
            dois.add(cleaned)
        for m in PLACEHOLDER_RE.finditer(text):
            placeholders.append({"file": rel, "match": m.group(0)})

    return {
        "files_scanned": files_scanned,
        "arxiv_ids": sorted(arxiv_ids),
        "dois": sorted(dois),
        "placeholders": placeholders,
    }


def check_online(urls: list[str]) -> list[dict]:
    results = []
    for url in urls:
        req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "pauli-contextuality-lab-audit/2.0"})
        try:
            with urllib.request.urlopen(req, timeout=10) as resp:
                results.append({"url": url, "status": resp.status, "ok": 200 <= resp.status < 400})
        except Exception as exc:
            results.append({"url": url, "status": None, "ok": False, "error": str(exc)})
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="Verify DOI/arXiv URLs live over HTTPS")
    args = parser.parse_args()

    scan = scan_papers()
    online_checks = []
    if args.online:
        urls = [f"https://arxiv.org/abs/{aid}" for aid in scan["arxiv_ids"]] + [
            f"https://doi.org/{doi}" for doi in scan["dois"]
        ]
        online_checks = check_online(urls)

    ok = len(scan["placeholders"]) == 0 and scan["files_scanned"] > 0
    report = {
        "status": "pass" if ok else "fail",
        "files_scanned": scan["files_scanned"],
        "arxiv_count": len(scan["arxiv_ids"]),
        "doi_count": len(scan["dois"]),
        "placeholder_hits": scan["placeholders"],
        "arxiv_ids": scan["arxiv_ids"],
        "dois": scan["dois"],
        "online_checks": online_checks,
    }
    out = ROOT / "results" / "citation-audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(
        f"Citation audit ({report['status']}): {scan['files_scanned']} files, "
        f"{len(scan['arxiv_ids'])} arXiv IDs, {len(scan['dois'])} DOIs, "
        f"{len(scan['placeholders'])} placeholders."
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
