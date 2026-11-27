# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Exact verification, negative-control, and mutation tests for Theorems 23-25
(Q+(7,2) triality residuals, all-N PG(N-1,2) rigidity & W(15,2), and Desargues / S_B^+).
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "tracks" / "spectral-bounds" / "scripts"
RESULTS = ROOT / "tracks" / "spectral-bounds" / "results"
WITNESS = ROOT / "data" / "witness"


class SanigaTheorems23To25Tests(unittest.TestCase):
    def test_theorem_23_q7plus_triality_residuals_exact(self) -> None:
        res = subprocess.run(
            [sys.executable, str(SCRIPTS / "q7plus_triality_residuals.py")],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("Case (0) Q+(7,2) \\ DW(5,2): 135 pts, 1,260 lines, exact d = 0", res.stdout)
        self.assertIn("Case (a) Q+(7,2) \\ Spread(M1): 5,040 transversal grids", res.stdout)
        self.assertIn("Case (a) Q+(7,2) \\ Spread(M2): 5,040 transversal grids", res.stdout)
        self.assertIn("Case (a*) Q+(7,2) \\ Ovoid: 126 pts, 1,260 lines, 280 intact Q-(5,2)s", res.stdout)
        self.assertIn("Case (b) Q+(7,2) \\ Q(6,2): exact integer minpoly (Lam-21)(Lam-9)(Lam+3)=0", res.stdout)

        data = json.loads((RESULTS / "q7plus_triality_residuals.json").read_text(encoding="utf-8"))
        self.assertEqual(data["status"], "pass")
        self.assertEqual(data["case_0_dw52_deleted"]["exact_degree"], 0)
        self.assertEqual(data["case_a_spread_deleted"]["exact_degree"], 210)
        self.assertEqual(data["case_a_dual_ovoid_deleted"]["exact_degree"], 252)
        self.assertEqual(data["case_b_q62_deleted"]["exact_degree"], 252)
        self.assertEqual(data["case_b_q62_deleted"]["total_unique_optimal_sets"], 240)
        self.assertEqual(data["case_b_q62_deleted"]["eigenvalue_multiplicities"], {"21": 2, "9": 14, "-3": 56})

    def test_theorem_25_desargues_and_augmented_sb_exact(self) -> None:
        res = subprocess.run(
            [sys.executable, str(SCRIPTS / "desargues_augmented_sb.py")],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("PASS  Desargues (10_3)", res.stdout)
        self.assertIn("PASS  Universal [DHOP] fiber-flip theorem", res.stdout)
        self.assertIn("PASS  Ovoid context parabola L(S_k) = 1575 - 256k + 32k^2", res.stdout)
        self.assertIn("PASS  Negative control: collinear 3-flip", res.stdout)

        data = json.loads((RESULTS / "desargues_augmented_sb.json").read_text(encoding="utf-8"))
        self.assertEqual(data["status"], "pass")
        self.assertEqual(data["desargues_10_3"]["desargues_lines"], 10)
        self.assertEqual(data["ovoid_context_parabola"]["values_by_k"], {
            "0": 1575, "1": 1351, "2": 1191, "3": 1095, "4": 1063, "5": 1095
        })
        aug = data["augmented_sb_variants"]
        self.assertEqual(aug["contexts_linking_red8_to_SB_minus_Q7p"], 0)
        self.assertEqual(aug["tangent_hyperplane_IZZZ_in_K103"], "71/71")
        self.assertTrue(aug["SB_4flip"]["breaks_floor_saturation"])
        self.assertEqual(aug["K95"]["disjoint_grid_lb"], 53)
        self.assertEqual(aug["K103"]["disjoint_grid_lb"], 87)
        self.assertEqual(aug["SB_4flip"]["disjoint_grid_lb"], 112)
        self.assertEqual(aug["SB_aug_143"]["disjoint_grid_lb"], 121)
        self.assertEqual(aug["SB_aug_143"]["hyperplane_profile"]["out_S"], {"67": 112})
        self.assertFalse(aug["SB_aug_143"]["is_square"])

    def test_theorem_24_pg_rigidity_w15_and_negative_mutation(self) -> None:
        res = subprocess.run(
            [sys.executable, str(SCRIPTS / "pg_rigidity_and_w15.py")],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("PASS  SymPy exact PG(N-1,2) rigidity theorem", res.stdout)
        self.assertIn("PASS  Strict W(15,2) separation: 161,360,335 < 166,115,415", res.stdout)

        data = json.loads((RESULTS / "pg_rigidity_and_w15.json").read_text(encoding="utf-8"))
        self.assertEqual(data["status"], "pass")
        sep = data["w15_strict_separation_below_pg72_lb"]
        self.assertEqual(sep["pg72_centered_lower_bound"], 166115415)
        self.assertEqual(sep["verified_w15_witness"], 161360335)
        self.assertEqual(sep["strict_margin"], 4755080)

        # Negative / mutation test: tampering with claimed violation count in n4_f.txt must raise AssertionError
        sys.path.insert(0, str(SCRIPTS))
        import pg_rigidity_and_w15 as pg  # type: ignore[import-not-found]

        orig = (WITNESS / "n4_f.txt").read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory(prefix="pauli_mut_") as td:
            mut = Path(td) / "n4_f_bad.txt"
            mut.write_text(orig.replace("4 f 1575", "4 f 1574"), encoding="utf-8", newline="\n")
            with self.assertRaises(AssertionError):
                pg.verify_witness_exact_int(mut)


if __name__ == "__main__":
    unittest.main()
