"""Repository-wide integrity, version consistency, license, provenance, and Lean hygiene checks."""
from __future__ import annotations

import hashlib
import json
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


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
        forbidden = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*axiom\b|implemented_by|@\[extern")
        roots = [
            ROOT / "lean" / "HoggarBound",
            ROOT / "lean" / "ContextualityTensor",
            ROOT / "lean" / "Evidence",
            ROOT / "lean" / "Solution.lean",
            ROOT / "lean" / "HoggarBound.lean",
            ROOT / "lean" / "ContextualityTensor.lean",
            ROOT / "lean" / "Evidence.lean",
        ]
        hits = []
        for item in roots:
            files = [item] if item.is_file() else sorted(item.rglob("*.lean"))
            for f in files:
                in_block = False
                for lineno, raw in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
                    s = raw.strip()
                    if s.startswith("/-"):
                        in_block = True
                    if in_block:
                        if "-/" in s:
                            in_block = False
                        continue
                    code = raw.split("--", 1)[0]
                    if forbidden.search(code):
                        hits.append(f"{f.relative_to(ROOT)}:{lineno}: {code.strip()}")
        self.assertEqual(hits, [], f"Forbidden Lean tokens found: {hits}")

    def test_no_template_placeholders(self) -> None:
        pat = re.compile(r"\{\{(PROJECT_NAME|DESCRIPTION|OWNER|YEAR|DATE)\}\}")
        for rel in ("README.md", "AGENTS.md", "CONTRIBUTING.md", "SECURITY.md", "SUPPORT.md", "CODE_OF_CONDUCT.md"):
            p = ROOT / rel
            if p.is_file():
                self.assertIsNone(pat.search(p.read_text(encoding="utf-8")), f"Placeholder left in {rel}")


if __name__ == "__main__":
    unittest.main()
