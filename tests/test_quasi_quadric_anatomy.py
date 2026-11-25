"""Exact verification tests for classical witness isomorphisms (Q1-Q3) and the
hyperbolic quasi-quadric S_B (135 observables, 1,095 contexts, 75 violated contexts, Q4).
"""
from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tracks" / "spectral-bounds" / "scripts" / "quasi_quadric_and_witness_anatomy.py"
EXP_DIR = ROOT / "tracks" / "spectral-bounds" / "results" / "hyperbolic-quasi-quadric-135"
PAULI4_RE = re.compile(r"^[IXYZ]{4}$")


class QuasiQuadricAndWitnessAnatomyTests(unittest.TestCase):
    def test_exact_anatomy_script_and_qontextium_exports(self) -> None:
        res = subprocess.run(
            [sys.executable, str(SCRIPT)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("PASS  Q1 Q-(7,2) 315", res.stdout)
        self.assertIn("PASS  Q2 W(7,2) 1575", res.stdout)
        self.assertIn("PASS  Q3 Q+(9,2) 6975", res.stdout)
        self.assertIn("PASS  Q4 S_B hyperbolic quasi-quadric", res.stdout)

        # Verify Qontextium --import assignment files (exact P1,P2,P3 syntax, no header, LF only)
        qa_all = (EXP_DIR / "qa_hyperbolic_quasi_quadric_135_contexts.txt").read_bytes()
        qa_viol = (EXP_DIR / "qa_hyperbolic_quasi_quadric_135_violated_75.txt").read_bytes()
        self.assertNotIn(b"\r\n", qa_all)
        self.assertNotIn(b"\r\n", qa_viol)

        all_rows = qa_all.decode("utf-8").splitlines()
        viol_rows = qa_viol.decode("utf-8").splitlines()
        self.assertEqual(len(all_rows), 1095)
        self.assertEqual(len(viol_rows), 75)
        for row in all_rows + viol_rows:
            parts = row.split(",")
            self.assertEqual(len(parts), 3, f"Bad Qontextium row: {row!r}")
            for p in parts:
                self.assertRegex(p, PAULI4_RE)

        # Verify CSV files have exact row counts and unambiguous diagonal PG(3,2) vs abstract-doily labels
        with (EXP_DIR / "contexts_1095.csv").open(encoding="utf-8") as fh:
            ctx_rows = list(csv.DictReader(fh))
        self.assertEqual(len(ctx_rows), 1095)
        self.assertEqual(sum(1 for r in ctx_rows if r["violated"] == "1"), 75)
        self.assertEqual(sum(1 for r in ctx_rows if r["diag_subspace_role"] == "DIAG_ABSTRACT_DOILY_VIOL"), 15)
        self.assertEqual(sum(1 for r in ctx_rows if r["diag_subspace_role"] == "DIAG_PG32_NONDOILY_SAT"), 20)

        with (EXP_DIR / "violated_75.csv").open(encoding="utf-8") as fh:
            v_rows = list(csv.DictReader(fh))
        self.assertEqual(len(v_rows), 75)
        self.assertEqual(sum(1 for r in v_rows if r["group"] == "diagonal_abstract_doily"), 15)
        self.assertEqual(sum(1 for r in v_rows if r["group"] == "external_generator_star"), 60)

        # Verify JSON bundle invariants and Sp(2N,2) isomorphism flags
        bundle = json.loads((EXP_DIR / "hyperbolic_quasi_quadric_135.json").read_text(encoding="utf-8"))
        self.assertEqual(bundle["status"], "pass")
        self.assertTrue(bundle["q1_q7minus_315"]["sp8_2_isomorphism"]["isomorphic_in_Sp_2N_2"])
        self.assertEqual(bundle["q1_q7minus_315"]["sp8_2_isomorphism"]["exact_violated_lines_matched"], 315)
        self.assertTrue(bundle["q2_w72_1575"]["sp8_2_isomorphism"]["isomorphic_in_Sp_2N_2"])
        self.assertEqual(bundle["q2_w72_1575"]["sp8_2_isomorphism"]["exact_violated_lines_matched"], 1575)
        self.assertTrue(bundle["q3_q9plus_6975"]["sp10_2_isomorphism"]["isomorphic_in_Sp_2N_2"])
        self.assertEqual(bundle["q3_q9plus_6975"]["sp10_2_isomorphism"]["exact_violated_lines_matched"], 6975)
        q4 = bundle["q4_hyperbolic_quasi_quadric_135"]
        self.assertEqual(q4["observables"], 135)
        self.assertEqual(q4["regular_commutation_degree"], 70)
        self.assertEqual(q4["ambient_contexts"], 1095)
        self.assertEqual(q4["violated_contexts"], 75)
        cd = q4["diagonal_abstract_doily"]
        self.assertTrue(cd["ambient_subspace_is_maximal_totally_isotropic_PG32"])
        self.assertFalse(cd["is_symplectic_four_qubit_doily"])
        self.assertTrue(cd["all_105_pairs_commute"])
        self.assertTrue(cd["all_35_ambient_lines_positive"])
        self.assertTrue(cd["prop6_512_odd_imaginary_states_share_exact_15_doily_lines"])
        self.assertTrue(q4["ovoid_relation_to_Q7plus"]["pairwise_noncollinear_in_abstract_doily"])
        self.assertTrue(q4["ovoid_relation_to_Q7plus"]["hits_every_abstract_doily_line_once"])
        self.assertTrue(q4["remaining_60_violated_lines"]["all_15_generators_maximal_totally_isotropic_PG32"])


if __name__ == "__main__":
    unittest.main()
