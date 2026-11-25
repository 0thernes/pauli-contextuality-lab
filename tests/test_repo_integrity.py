"""Repository-wide integrity, version consistency, license, link, CRLF, provenance, and Lean hygiene checks."""
from __future__ import annotations

import hashlib
import json
import os
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def strip_lean_comments(src: str) -> str:
    """Remove nested /- ... -/ block comments, -- line comments, and string literals from Lean source."""
    out: list[str] = []
    i, n, depth, in_str = 0, len(src), 0, False
    while i < n:
        if depth > 0:
            if src[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif src[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        elif in_str:
            if src[i] == "\\" and i + 1 < n:
                i += 2
            elif src[i] == '"':
                in_str = False
                i += 1
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        else:
            if src[i : i + 2] == "/-":
                depth = 1
                i += 2
            elif src[i : i + 2] == "--":
                while i < n and src[i] != "\n":
                    i += 1
            elif src[i] == '"':
                in_str = True
                i += 1
            else:
                out.append(src[i])
                i += 1
    return "".join(out)


def path_exists_case_exact(root: Path, target: Path) -> bool:
    """Return True iff target exists and every path component under root matches exact disk casing."""
    if not target.exists():
        return False
    norm_target = Path(os.path.normpath(str(target)))
    norm_root = Path(os.path.normpath(str(root)))
    try:
        rel_parts = norm_target.relative_to(norm_root).parts
    except ValueError:
        return True
    cur = norm_root
    for part in rel_parts:
        names = {entry.name for entry in cur.iterdir()}
        if part not in names:
            return False
        cur = cur / part
    return True


class RepoIntegrityTests(unittest.TestCase):
    def test_single_version_source_consistency(self) -> None:
        version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
        self.assertRegex(version, r"^\d+\.\d+\.\d+$")
        changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
        self.assertRegex(changelog, re.compile(rf"^## \[?v?{re.escape(version)}\]?", re.M))
        citation = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
        self.assertRegex(citation, re.compile(rf'^version:\s*"{re.escape(version)}"$', re.M))
        formal = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
        self.assertRegex(formal, re.compile(rf'^version:\s*"{re.escape(version)}"$', re.M))
        lakefile = (ROOT / "lean" / "lakefile.toml").read_text(encoding="utf-8")
        self.assertRegex(lakefile, re.compile(rf'^version\s*=\s*"{re.escape(version)}"$', re.M))
        readme = (ROOT / "README.md").read_text(encoding="utf-8")
        self.assertIn(f"v{version}", readme)
        self.assertIn(f"Version {version}", readme)
        meta = json.loads((ROOT / "papers" / "spectral-bounds" / "unified-metadata.json").read_text(encoding="utf-8"))
        self.assertEqual(meta["version"], version)
        self.assertTrue(meta["source_release"].endswith(f"/v{version}"))

    def test_all_root_doc_repo_paths_exist(self) -> None:
        path_pat = re.compile(r"`((?:lean|tracks|papers|scripts|tests|docs|data|third_party|results|blueprint)/[A-Za-z0-9_./-]+)`")
        missing: list[tuple[str, str]] = []
        for rel in ("README.md", "CLAIMS.md", "LIMITATIONS.md", "REPLICATION.md", "docs/statement-fidelity.md", "AGENTS.md"):
            txt = (ROOT / rel).read_text(encoding="utf-8")
            for m in path_pat.finditer(txt):
                cand = m.group(1).rstrip("/.")
                if any(ch in cand for ch in ("*", "<", "{", "..")):
                    continue
                if not path_exists_case_exact(ROOT, ROOT / cand):
                    missing.append((rel, cand))
        self.assertEqual(missing, [], f"Dead repo paths referenced in root docs: {missing}")

    def test_all_local_markdown_links_resolve_case_exact(self) -> None:
        skip = {".git", ".lake", ".venv", "node_modules", "third_party", "build", "archive"}
        md_link_re = re.compile(r"\[[^\]]*\]\(([^)#\s]+)")
        broken: list[tuple[str, str]] = []
        for md in sorted(ROOT.rglob("*.md")):
            if any(part in skip for part in md.parts) or md.name == "build-standard.md":
                continue
            txt = re.sub(r"```.*?```", "", md.read_text(encoding="utf-8", errors="replace"), flags=re.S)
            for m in md_link_re.finditer(txt):
                target = m.group(1)
                if target.startswith(("http://", "https://", "mailto:", "data:", "javascript:")):
                    continue
                cand = md.parent / target
                if not path_exists_case_exact(ROOT, cand):
                    broken.append((md.relative_to(ROOT).as_posix(), target))
        self.assertEqual(broken, [], f"Broken or wrong-case local Markdown links: {broken}")

    def test_all_doc_lean_decl_refs_exist(self) -> None:
        decl_re = re.compile(
            r"^\s*(?:private\s+|noncomputable\s+|protected\s+)*(?:theorem|lemma|def|structure|abbrev|inductive|instance)\s+([A-Za-z0-9_.']+)",
            re.M,
        )
        ns_re = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)", re.M)
        known: set[str] = set()
        for lf in (ROOT / "lean").rglob("*.lean"):
            if ".lake" in lf.parts:
                continue
            t = lf.read_text(encoding="utf-8", errors="replace")
            nss = ns_re.findall(t)
            for m in decl_re.finditer(t):
                short = m.group(1)
                known.add(short)
                for ns in nss:
                    known.add(f"{ns}.{short}")
        ref_re = re.compile(r"`((?:HoggarBound|ContextualityTensor|Evidence|PauliContextualityLab)\.[A-Za-z0-9_.']+)`")
        missing: list[tuple[str, str]] = []
        for rel in ("README.md", "CLAIMS.md", "docs/statement-fidelity.md"):
            t = (ROOT / rel).read_text(encoding="utf-8")
            for m in ref_re.finditer(t):
                d = m.group(1)
                if d not in known and d.split(".")[-1] not in known:
                    missing.append((rel, d))
        self.assertEqual(missing, [], f"Unresolved Lean decl refs in docs: {missing}")

    def test_no_legacy_llc_or_verification_licence_in_active_papers_and_docs(self) -> None:
        pat = re.compile(r"0thernes\s+LLC|verification\s+licen[cs]e", re.I)
        active = [
            "README.md", "CLAIMS.md", "LIMITATIONS.md", "REPLICATION.md", "LEGAL.md",
            "papers/README.md",
            "papers/spectral-bounds/unified-contextuality.tex",
            "papers/spectral-bounds/unified-contextuality.md",
            "papers/spectral-bounds/unified-contextuality.html",
            "papers/spectral-bounds/c3-spectral-counterexample.tex",
            "papers/spectral-bounds/unified-citation.bib",
            "papers/spectral-bounds/unified-metadata.json",
            "papers/disjoint-mermin/contextuality-tensor.tex",
            "papers/disjoint-mermin/contextuality-tensor.md",
            "papers/disjoint-mermin/contextuality-tensor.bib",
            "papers/disjoint-mermin/STATUS.md",
            "papers/disjoint-mermin/ARXIV-SOURCE.md",
            "papers/sequential-evidence/whitepaper.tex",
            "papers/sequential-evidence/whitepaper.md",
        ]
        hits = [r for r in active if (ROOT / r).is_file() and pat.search((ROOT / r).read_text(encoding="utf-8"))]
        self.assertEqual(hits, [], f"Legacy LLC or verification-licence found in active docs/papers: {hits}")

    def test_no_crlf_in_code_and_lean_sources(self) -> None:
        skip = {".git", ".lake", ".venv", "node_modules", "third_party", "build"}
        crlf: list[str] = []
        for p in sorted(ROOT.rglob("*")):
            if not p.is_file() or any(part in skip for part in p.parts):
                continue
            if p.suffix.lower() in {".lean", ".py", ".c", ".h", ".sh", ".yml", ".yaml", ".toml", ".js", ".mjs", ".css", ".html"}:
                if b"\r\n" in p.read_bytes():
                    crlf.append(p.relative_to(ROOT).as_posix())
        self.assertEqual(crlf, [], f"CRLF line endings found in source/config files: {crlf}")

    def test_open_dual_license_and_independent_affiliation(self) -> None:
        lic = (ROOT / "LICENSE").read_text(encoding="utf-8")
        self.assertIn("Apache License", lic)
        self.assertIn("Version 2.0", lic)
        self.assertNotIn("0thernes LLC", lic)
        docs_lic = (ROOT / "LICENSE-DOCS").read_text(encoding="utf-8")
        self.assertIn("CC-BY-4.0", docs_lic)
        citation = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
        self.assertNotIn("0thernes LLC", citation)
        self.assertIn("0009-0006-8168-9648", citation)

    def test_data_manifest_sha256(self) -> None:
        manifest = ROOT / "data" / "MANIFEST.sha256"
        self.assertTrue(manifest.is_file())
        count = 0
        for line in manifest.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            expected, rel = line.split(None, 1)
            target = ROOT / rel.strip().lstrip("*")
            self.assertTrue(target.is_file(), f"Missing data file: {rel}")
            actual = hashlib.sha256(target.read_bytes()).hexdigest()
            self.assertEqual(actual, expected.lower(), f"Hash mismatch: {rel}")
            count += 1
        self.assertGreaterEqual(count, 20)

    def test_third_party_sha256sums(self) -> None:
        sums = json.loads((ROOT / "third_party" / "SHA256SUMS.json").read_text(encoding="utf-8"))
        files_map = sums.get("files", sums)
        checked = 0
        for rel, expected in files_map.items():
            if not isinstance(expected, str):
                continue
            p = ROOT / "third_party" / rel
            if not p.is_file():
                p = ROOT / rel
            self.assertTrue(p.is_file(), f"Missing vendored file: {rel}")
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(), expected.lower())
            checked += 1
        self.assertGreaterEqual(checked, 10)

    def test_no_forbidden_lean_tokens_in_proof_modules(self) -> None:
        forbidden = re.compile(r"\b(sorry|admit|native_decide|unsafe)\b|^\s*(?:private\s+|protected\s+)?axiom\b|implemented_by|@\[extern")
        roots = [
            ROOT / "lean" / "HoggarBound",
            ROOT / "lean" / "ContextualityTensor",
            ROOT / "lean" / "Evidence",
            ROOT / "lean" / "Solution.lean",
            ROOT / "lean" / "HoggarBound.lean",
            ROOT / "lean" / "ContextualityTensor.lean",
            ROOT / "lean" / "Evidence.lean",
        ]
        hits: list[str] = []
        for item in roots:
            files = [item] if item.is_file() else sorted(item.rglob("*.lean"))
            for f in files:
                cleaned = strip_lean_comments(f.read_text(encoding="utf-8"))
                for lineno, line in enumerate(cleaned.splitlines(), 1):
                    if forbidden.search(line):
                        hits.append(f"{f.relative_to(ROOT)}:{lineno}: {line.strip()}")
        self.assertEqual(hits, [], f"Forbidden Lean tokens found: {hits}")

    def test_no_template_placeholders(self) -> None:
        pat = re.compile(r"\{\{(PROJECT_NAME|DESCRIPTION|OWNER|YEAR|DATE)\}\}")
        for rel in ("README.md", "AGENTS.md", "CONTRIBUTING.md", "SECURITY.md", "SUPPORT.md", "CODE_OF_CONDUCT.md"):
            p = ROOT / rel
            if p.is_file():
                self.assertIsNone(pat.search(p.read_text(encoding="utf-8")), f"Placeholder left in {rel}")

    def test_no_malformed_or_double_replaced_paper_urls(self) -> None:
        bad: list[str] = []
        for p in sorted((ROOT / "papers").rglob("*")):
            if not p.is_file() or p.suffix.lower() not in {".html", ".md", ".tex"}:
                continue
            txt = p.read_text(encoding="utf-8", errors="replace")
            if re.search(r"consolidated from[^\n]*consolidated from", txt):
                bad.append(f"{p.relative_to(ROOT)}: double consolidated-from string")
            if re.search(r'href="[^"]*\s+[^"]*"', txt):
                bad.append(f"{p.relative_to(ROOT)}: whitespace inside href URL")
            if re.search(r"https://github\.com/0thernes/pauli-contextuality-lab/actions/runs/(?:42|44)\d+", txt):
                bad.append(f"{p.relative_to(ROOT)}: historical hoggar-bound-lab run ID pointing to pauli-contextuality-lab (404)")
            if p.suffix.lower() == ".tex" and r"-\/-\/-" in txt:
                bad.append(f"{p.relative_to(ROOT)}: pandoc-mangled em-dash -\\/-\\/-")
            if p.suffix.lower() == ".html":
                vis = re.sub(r"<(script|style|pre|code)\b[^>]*>.*?</\1>", "", txt, flags=re.DOTALL | re.IGNORECASE)
                vis = re.sub(r"<!--.*?-->", "", vis, flags=re.DOTALL)
                if "---" in vis:
                    bad.append(f"{p.relative_to(ROOT)}: raw ASCII --- in visible HTML prose")
        self.assertEqual(bad, [], f"Malformed paper URLs/headers/typography: {bad}")

    def test_track_scripts_resolve_shared_monorepo_roots(self) -> None:
        import subprocess
        import sys
        py_scripts = [
            "tracks/spectral-bounds/scripts/stack_audit.py",
            "tracks/spectral-bounds/scripts/phase_seven_lean.py",
            "tracks/spectral-bounds/scripts/flat_states.py",
            "tracks/spectral-bounds/scripts/phase_states.py",
            "tracks/spectral-bounds/scripts/frontier_c3_axioms.py",
            "tracks/spectral-bounds/scripts/frontier_c3_certificate_audit.py",
            "tracks/spectral-bounds/scripts/analysis.py",
            "tracks/sequential-evidence/scripts/make_figures.py",
        ]
        for rel in py_scripts:
            txt = (ROOT / rel).read_text(encoding="utf-8")
            self.assertIn("REPO_ROOT", txt, f"{rel} missing REPO_ROOT monorepo resolution")
        mjs_drivers = [
            "tracks/spectral-bounds/src/moonlab_experiment.mjs",
            "tracks/spectral-bounds/src/moonlab_saturated.mjs",
        ]
        for rel in mjs_drivers:
            txt = (ROOT / rel).read_text(encoding="utf-8")
            self.assertIn("repoRoot", txt, f"{rel} missing repoRoot monorepo resolution")
        for rel, needle in (
            ("tracks/spectral-bounds/scripts/run_falsify.sh", "../../data"),
            ("tracks/spectral-bounds/src/qgt_flat.c", "../../data/flat/"),
            ("tracks/spectral-bounds/src/qgt_hoggar.c", "../../data/witness/"),
        ):
            txt = (ROOT / rel).read_text(encoding="utf-8")
            self.assertIn(needle, txt, f"{rel} missing monorepo fallback {needle}")
        # Verify isolated monorepo stack runner stages shared third_party/ cleanly for all 3 tracks
        # while keeping SHA-256-fingerprinted Track 2 & 3 stack drivers byte-identical to receipts.
        for track in ("disjoint-mermin", "sequential-evidence", "spectral-bounds"):
            res = subprocess.run(
                [sys.executable, str(ROOT / "scripts" / "run_track_stack.py"), track, "--dry-run"],
                cwd=ROOT,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 0, f"run_track_stack --dry-run failed for {track}: {res.stderr}")
            self.assertIn("PASS: staged", res.stdout)

    def test_blueprint_generates_exact_github_line_links(self) -> None:
        import subprocess
        import sys
        res = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "build_blueprint.py")],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("PASS: Blueprint validated 27 nodes (162 Lean decls", res.stdout)
        bp = json.loads((ROOT / "build" / "site" / "blueprint" / "blueprint.json").read_text(encoding="utf-8"))
        self.assertEqual(len(bp), 27)
        bp_html = (ROOT / "build" / "site" / "blueprint" / "index.html").read_text(encoding="utf-8")
        self.assertIn('integrity="sha384-', bp_html)
        self.assertIn('crossorigin="anonymous"', bp_html)
        total = 0
        for node in bp:
            self.assertEqual(len(node["lean"]), len(node["lean_links"]))
            for link in node["lean_links"]:
                self.assertRegex(link["url"], r"^https://github\.com/0thernes/pauli-contextuality-lab/blob/main/lean/.+\.lean#L\d+$")
                self.assertTrue((ROOT / link["file"]).is_file(), f"Missing file {link['file']}")
                total += 1
        self.assertEqual(total, 162)

    def test_phase_seven_and_c3_audit_paths_live(self) -> None:
        import subprocess
        import sys
        res = subprocess.run(
            [sys.executable, str(ROOT / "tracks" / "spectral-bounds" / "scripts" / "frontier_c3_certificate_audit.py")],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0, f"frontier_c3_certificate_audit failed: {res.stderr}\n{res.stdout}")
        self.assertIn('"status": "pass"', res.stdout)

    def test_independent_review_theorem_links_exact(self) -> None:
        explorer = (ROOT / "tracks" / "spectral-bounds" / "web" / "independent-review" / "explorer.js").read_text(encoding="utf-8")
        pairs = re.findall(r"(\w+):\s*'([A-Za-z0-9_]+\.lean)#L(\d+)'", explorer)
        self.assertGreaterEqual(len(pairs), 5, "Expected >=5 Lean theorem source links in independent-review/explorer.js")
        for thm, fname, lineno_s in pairs:
            lean_file = ROOT / "lean" / "HoggarBound" / fname
            self.assertTrue(lean_file.is_file(), f"Missing Lean file {lean_file}")
            lines = lean_file.read_text(encoding="utf-8").splitlines()
            lineno = int(lineno_s)
            self.assertTrue(1 <= lineno <= len(lines), f"Line {lineno} out of bounds in {fname}")
            self.assertRegex(
                lines[lineno - 1],
                rf"^\s*(?:theorem|lemma|def)\s+{re.escape(thm)}\b",
                f"{fname}#L{lineno} does not declare {thm}: {lines[lineno - 1]!r}",
            )


if __name__ == "__main__":
    unittest.main()
