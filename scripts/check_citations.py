#!/usr/bin/env python3
"""Validate DOI, arXiv, Zenodo, and BibTeX citation identifiers across all manuscripts.

Offline check runs in CI: scans .md/.tex/.bib files for placeholder identifiers,
validates BibTeX entry syntax and duplicate keys, and emits results/citation-audit.json.
Pass --online to perform live HTTPS checks plus Crossref retraction-status auditing
(Defensible Independent AI Research Playbook v1.3, Checklist #15 and #16).
"""
from __future__ import annotations

import argparse
import json
import re
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"

ARXIV_RE = re.compile(r"arXiv:([0-9]{4}\.[0-9]{4,5}(?:v[0-9]+)?|[a-z-]+/[0-9]{7})", re.I)
DOI_RE = re.compile(r"\b(10\.[0-9]{4,9}/[-._;()/:A-Za-z0-9]+)")
PLACEHOLDER_RE = re.compile(r"(TODO\(cite\)|FIXME_DOI|10\.0000/|arXiv:0000\.00000)", re.I)
BIB_ENTRY_RE = re.compile(r"@([A-Za-z]+)\s*\{\s*([^,\s]+)\s*,")


def audit_bibtex_files() -> dict:
    bib_files: list[str] = []
    duplicate_keys: list[dict] = []
    unbalanced_files: list[str] = []
    total_entries = 0

    for path in sorted(PAPERS_DIR.rglob("*.bib")):
        if not path.is_file():
            continue
        rel = path.relative_to(ROOT).as_posix()
        bib_files.append(rel)
        text = path.read_text(encoding="utf-8", errors="replace")
        # Brace balance check
        depth = 0
        ok_braces = True
        for ch in text:
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth < 0:
                    ok_braces = False
                    break
        if not ok_braces or depth != 0:
            unbalanced_files.append(rel)

        seen: set[str] = set()
        for m in BIB_ENTRY_RE.finditer(text):
            etype = m.group(1).lower()
            if etype in {"string", "preamble", "comment"}:
                continue
            key = m.group(2)
            total_entries += 1
            if key in seen:
                duplicate_keys.append({"file": rel, "key": key})
            seen.add(key)

    return {
        "bib_files": bib_files,
        "total_entries": total_entries,
        "duplicate_keys": duplicate_keys,
        "unbalanced_files": unbalanced_files,
    }


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
        "bibtex": audit_bibtex_files(),
    }


def check_online(arxiv_ids: list[str], dois: list[str]) -> list[dict]:
    results = []
    for aid in arxiv_ids:
        url = f"https://arxiv.org/abs/{aid}"
        req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "pauli-contextuality-lab-audit/2.8"})  # noqa: S310
        try:
            with urllib.request.urlopen(req, timeout=12) as resp:  # noqa: S310
                results.append({"url": url, "status": resp.status, "ok": 200 <= resp.status < 400})
        except Exception as exc:
            results.append({"url": url, "status": None, "ok": False, "error": str(exc)})
    for doi in dois:
        # Use official Handle REST API (doi.org/api/handles/) to avoid publisher bot-403 false negatives
        url = f"https://doi.org/api/handles/{urllib.parse.quote(doi, safe='/')}"
        req = urllib.request.Request(url, headers={"User-Agent": "pauli-contextuality-lab-audit/2.8"})  # noqa: S310
        try:
            with urllib.request.urlopen(req, timeout=12) as resp:  # noqa: S310
                body = json.loads(resp.read().decode("utf-8"))
                ok = resp.status == 200 and body.get("responseCode") == 1
                results.append({"url": f"https://doi.org/{doi}", "status": resp.status, "handle_code": body.get("responseCode"), "ok": ok})
        except Exception as exc:
            results.append({"url": f"https://doi.org/{doi}", "status": None, "ok": False, "error": str(exc)})
    return results


def check_crossref_retractions(dois: list[str]) -> list[dict]:
    """Query Crossref Works API (with polite spacing & 429 retry) for retraction notices on journal DOIs."""
    findings = []
    for doi in dois:
        if doi.lower().startswith(("10.5281/zenodo.", "10.48550/arxiv.")):
            findings.append({"doi": doi, "source": "datacite_preprint", "retracted": False, "status": "skipped_non_crossref"})
            continue
        url = f"https://api.crossref.org/works/{urllib.parse.quote(doi, safe='')}"
        req = urllib.request.Request(
            url,
            headers={"User-Agent": "pauli-contextuality-lab-audit/2.8 (mailto:0_0@0thernes.art)"},
        )  # noqa: S310
        last_err: Exception | None = None
        payload = None
        for attempt in range(3):
            if attempt > 0:
                time.sleep(1.5 * attempt)
            else:
                time.sleep(0.35)
            try:
                with urllib.request.urlopen(req, timeout=12) as resp:  # noqa: S310
                    payload = json.loads(resp.read().decode("utf-8"))
                break
            except urllib.error.HTTPError as exc:
                last_err = exc
                if exc.code != 429:
                    break
            except Exception as exc:
                last_err = exc
                break
        if payload is None:
            findings.append({"doi": doi, "source": "crossref", "retracted": None, "status": "lookup_error", "error": str(last_err)})
            continue
        msg = payload.get("message", {})
        updates = msg.get("update-to", []) or []
        updated_by = msg.get("updated-by", []) or []
        relations = msg.get("relation", {}) or {}
        retracted = any(
            "retract" in str(item.get("type", "")).lower() or "retract" in str(item.get("label", "")).lower()
            for item in (*updates, *updated_by)
        ) or "is-retracted-by" in relations
        findings.append(
            {
                "doi": doi,
                "source": "crossref",
                "retracted": retracted,
                "title": (msg.get("title") or [""])[0],
                "status": "checked",
            }
        )
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="Verify DOI/arXiv URLs and Crossref retraction metadata over HTTPS")
    args = parser.parse_args()

    scan = scan_papers()
    online_checks = []
    retraction_checks = []
    if args.online:
        online_checks = check_online(scan["arxiv_ids"], scan["dois"])
        retraction_checks = check_crossref_retractions(scan["dois"])

    bib = scan["bibtex"]
    any_retracted = any(r.get("retracted") is True for r in retraction_checks)
    ok = (
        len(scan["placeholders"]) == 0
        and scan["files_scanned"] > 0
        and len(bib["duplicate_keys"]) == 0
        and len(bib["unbalanced_files"]) == 0
        and not any_retracted
    )
    report = {
        "status": "pass" if ok else "fail",
        "files_scanned": scan["files_scanned"],
        "arxiv_count": len(scan["arxiv_ids"]),
        "doi_count": len(scan["dois"]),
        "placeholder_hits": scan["placeholders"],
        "bibtex": bib,
        "arxiv_ids": scan["arxiv_ids"],
        "dois": scan["dois"],
        "online_checks": online_checks,
        "crossref_retraction_checks": retraction_checks,
    }
    out = ROOT / "results" / "citation-audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(
        f"Citation audit ({report['status']}): {scan['files_scanned']} files, "
        f"{len(scan['arxiv_ids'])} arXiv IDs, {len(scan['dois'])} DOIs, "
        f"{bib['total_entries']} BibTeX entries ({len(bib['duplicate_keys'])} dup, {len(bib['unbalanced_files'])} unbalanced), "
        f"{len(scan['placeholders'])} placeholders."
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
