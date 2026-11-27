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
            "README.md", "CLAIMS.md", "LIMITATIONS.md", "REPLICATION.md", "ERRATA.md", "NOTICE",
            "CITATION.cff", "formalization.yaml", "repo.yaml", "AGENTS.md",
            "docs/mega-atlas-cross-reference.md", "docs/statement-fidelity.md", "docs/threat-model.md",
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
        forbidden = re.compile(
            r"\b(sorry|admit|native_decide|unsafe)\b|"
            r"^\s*(?:(?:private|protected|noncomputable|scoped|local)\s+)*axiom\b|"
            r"implemented_by|@\[extern"
        )
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
                if ".lake" in f.parts:
                    continue
                cleaned = strip_lean_comments(f.read_text(encoding="utf-8"))
                for lineno, line in enumerate(cleaned.splitlines(), 1):
                    if forbidden.search(line):
                        hits.append(f"{f.relative_to(ROOT)}:{lineno}: {line.strip()}")
        self.assertEqual(hits, [], f"Forbidden Lean tokens found: {hits}")

    def test_build_standard_v12_manifest_and_ten_finding_classes(self) -> None:
        import yaml

        schema = json.loads((ROOT / "repo-standard.schema.json").read_text(encoding="utf-8"))
        self.assertEqual(schema["$id"], "urn:0thernes:build-standard:repo-manifest-schema:1.2.0")
        manifest = yaml.safe_load((ROOT / "repo.yaml").read_text(encoding="utf-8"))
        self.assertEqual(manifest["standard"], "1.2.0")
        allowed_stacks = set(schema["properties"]["stack"]["items"]["enum"])
        for entry in manifest["stack"]:
            self.assertIn(entry, allowed_stacks, f"Invalid stack value in repo.yaml: {entry!r}")
        allowed_types = set(schema["properties"]["project_type"]["enum"])
        self.assertIn(manifest["project_type"], allowed_types)
        try:
            import jsonschema

            jsonschema.validate(instance=manifest, schema=schema)
        except ImportError:
            pass

        ten_classes = [
            "bug", "error", "issue", "problem", "concern",
            "dilemma", "conflict", "gap", "hole", "blindspot",
        ]
        labels_txt = (ROOT / ".github" / "labels.tsv").read_text(encoding="utf-8")
        bug_form_txt = (ROOT / ".github" / "ISSUE_TEMPLATE" / "bug.yml").read_text(encoding="utf-8")
        glossary_txt = (ROOT / "docs" / "glossary.md").read_text(encoding="utf-8")
        for cls in ten_classes:
            self.assertRegex(labels_txt, re.compile(rf"^{cls}\t", re.M), f"Missing label '{cls}' in .github/labels.tsv")
            self.assertIn(f'"{cls}:', bug_form_txt, f"Missing finding class '{cls}' in .github/ISSUE_TEMPLATE/bug.yml")
            self.assertIn(f"**{cls}**", glossary_txt, f"Missing finding class '{cls}' in docs/glossary.md")

    def test_playbook_v13_errata_mega_atlas_and_native_axiom_rejection(self) -> None:
        import importlib.util

        errata = (ROOT / "ERRATA.md").read_text(encoding="utf-8")
        self.assertIn("Withdrawal Plan", errata)
        self.assertIn("version-specific DOI", errata)
        mega = (ROOT / "docs" / "mega-atlas-cross-reference.md").read_text(encoding="utf-8")
        self.assertIn("0 / 1,900", mega)
        self.assertIn("QM-011", mega)

        # Verify check_readme_axioms.py rejects Lean 4.35 _native.*, ofReduceBool, trustCompiler, sorryAx
        spec = importlib.util.spec_from_file_location("check_readme_axioms", ROOT / "scripts" / "check_readme_axioms.py")
        assert spec is not None and spec.loader is not None
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        sample = (
            "'A.clean' does not depend on any axioms\n"
            "'A.wrapped' depends on axioms: [propext,\n"
            "  Classical.choice, Quot.sound]\n"
            "'A.bad_native' depends on axioms: [propext, A.bad_native._native.native_decide.ax_1]\n"
            "'A.bad_bool' depends on axioms: [Lean.ofReduceBool]\n"
            "'A.bad_sorry' depends on axioms: [sorryAx]\n"
        )
        parsed = mod.parse_log(sample)
        self.assertEqual(parsed["A.clean"], set())
        self.assertEqual(parsed["A.wrapped"], {"propext", "Classical.choice", "Quot.sound"})
        self.assertFalse(parsed["A.bad_native"] <= mod.ALLOWED)
        self.assertFalse(parsed["A.bad_bool"] <= mod.ALLOWED)
        self.assertFalse(parsed["A.bad_sorry"] <= mod.ALLOWED)

        # Verify Palomar size caps on Challenge.lean and all Lean modules (Playbook v1.3 H14)
        ch = ROOT / "lean" / "Challenge.lean"
        self.assertLessEqual(len(ch.read_text(encoding="utf-8").splitlines()), 1000)
        self.assertLessEqual(ch.stat().st_size, 102400)
        for lf in (ROOT / "lean").rglob("*.lean"):
            if ".lake" in lf.parts:
                continue
            self.assertFalse(lf.is_symlink(), f"Lean file must not be a symlink: {lf}")
            self.assertLessEqual(len(lf.read_text(encoding="utf-8").splitlines()), 10000)

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
        self.assertEqual(
            bad, [], f"Malformed paper URLs/headers/typography: {bad}"
        )

    def test_unified_metadata_paths_and_abstract_parity(self) -> None:
        meta_path = ROOT / "papers" / "spectral-bounds" / "unified-metadata.json"
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        for key in ("canonical_source", "author_declarations_record", "distribution_record"):
            val = meta.get(key)
            self.assertIsInstance(val, str, f"Missing string field {key} in unified-metadata.json")
            self.assertTrue(
                path_exists_case_exact(ROOT, ROOT / val),
                f"Dead repo path in unified-metadata.json[{key}]: {val}",
            )
        ver_recs = meta.get("verification_records", [])
        self.assertGreaterEqual(len(ver_recs), 3)
        for rec in ver_recs:
            self.assertTrue(
                path_exists_case_exact(ROOT, ROOT / rec),
                f"Dead repo path in unified-metadata.json[verification_records]: {rec}",
            )
        self.assertNotIn("ETHICS.md", meta_path.read_text(encoding="utf-8"))
        self.assertNotRegex(meta["abstract"], r"\$`[^`]+`\$")
        for rel in (
            "papers/spectral-bounds/unified-metadata.json",
            "papers/spectral-bounds/unified-abstract.txt",
            "papers/spectral-bounds/unified-contextuality.md",
            "papers/spectral-bounds/unified-contextuality.tex",
            "papers/spectral-bounds/unified-contextuality.html",
        ):
            txt = (ROOT / rel).read_text(encoding="utf-8")
            self.assertNotIn(
                "110 newly audited declarations plus retained audits",
                txt,
                f"Stale 110-declaration abstract phrasing found in {rel}",
            )
            self.assertIn(
                "2,452 exhaustively audited",
                txt,
                f"Missing synchronized 2,452-theorem count in {rel}",
            )

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
        self.assertIn("PASS: Blueprint validated 29 nodes (213 Lean decls", res.stdout)
        bp = json.loads((ROOT / "build" / "site" / "blueprint" / "blueprint.json").read_text(encoding="utf-8"))
        self.assertEqual(len(bp), 29)
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
        self.assertEqual(total, 213)

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

    def test_all_cdn_scripts_have_sri_and_crossorigin(self) -> None:
        skip = {".git", ".lake", ".venv", "node_modules", "third_party", "build", ".mypy_cache"}
        cdn_re = re.compile(r"<script[^>]+src=[\"'](https?://[^\"']*(?:cdn\.|jsdelivr|cdnjs|unpkg)[^\"']*)[\"'][^>]*>", re.I)
        missing_sri: list[str] = []
        for ext in ("*.html", "*.py", "*.js", "*.mjs"):
            for fp in sorted(ROOT.rglob(ext)):
                if any(part in skip for part in fp.parts):
                    continue
                txt = fp.read_text(encoding="utf-8", errors="ignore")
                for m in cdn_re.finditer(txt):
                    tag = m.group(0)
                    if 'integrity="sha384-' not in tag or 'crossorigin="anonymous"' not in tag:
                        missing_sri.append(f"{fp.relative_to(ROOT).as_posix()}: {m.group(1)}")
        self.assertEqual(missing_sri, [], f"External CDN <script> missing sha384 SRI or crossorigin: {missing_sri}")

    def test_rfc3161_opentimestamps_swhid_and_submission_packet(self) -> None:
        import importlib.util

        spec = importlib.util.spec_from_file_location("stamp_timestamps", ROOT / "scripts" / "stamp_timestamps.py")
        assert spec is not None and spec.loader is not None
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        self.assertEqual(mod.verify_timestamps(), 0, "RFC 3161 TSA or OpenTimestamps proof verification failed")
        self.assertTrue((ROOT / "data" / "MANIFEST.sha256.tsr").is_file())
        self.assertTrue((ROOT / "data" / "MANIFEST.sha256.ots").is_file())
        self.assertIn("swh:1:snp:cf9ae7bd108e9556e79d4c0c81c8de92632b91c1", (ROOT / "CITATION.cff").read_text(encoding="utf-8"))
        self.assertIn("swh:1:snp:cf9ae7bd108e9556e79d4c0c81c8de92632b91c1", (ROOT / "formalization.yaml").read_text(encoding="utf-8"))
        packet = ROOT / "docs" / "submission-packet.md"
        self.assertTrue(packet.is_file(), "Missing docs/submission-packet.md")
        self.assertIn("DRAFT", packet.read_text(encoding="utf-8").upper())

        # Guard against unescaped `|` breaking GitHub Markdown tables across active docs
        bad_tables: list[str] = []
        for md_rel in ("README.md", "CLAIMS.md", "LIMITATIONS.md", "ERRATA.md", "REPLICATION.md", "docs/statement-fidelity.md", "docs/mega-atlas-cross-reference.md", "docs/threat-model.md"):
            lines = (ROOT / md_rel).read_text(encoding="utf-8").splitlines()
            in_code = False
            i = 0
            while i < len(lines):
                if lines[i].lstrip().startswith("```"):
                    in_code = not in_code
                    i += 1
                    continue
                if not in_code and i + 1 < len(lines) and "|" in lines[i] and re.match(r"^\s*\|?\s*:?-{2,}:?\s*(\|\s*:?-{2,}:?\s*)+\|?\s*$", lines[i + 1]):
                    def _cols(s: str) -> int:
                        s = re.sub(r"\\\|", "PIPE", s.strip())
                        if s.startswith("|"):
                            s = s[1:]
                        if s.endswith("|"):
                            s = s[:-1]
                        return len(s.split("|"))
                    exp = _cols(lines[i + 1])
                    if _cols(lines[i]) != exp:
                        bad_tables.append(f"{md_rel}:{i + 1}")
                    j = i + 2
                    while j < len(lines) and "|" in lines[j] and lines[j].strip():
                        if _cols(lines[j]) != exp:
                            bad_tables.append(f"{md_rel}:{j + 1}")
                        j += 1
                    i = j
                else:
                    i += 1
        self.assertEqual(bad_tables, [], f"Broken Markdown table column counts (unescaped |): {bad_tables}")


if __name__ == "__main__":
    unittest.main()
