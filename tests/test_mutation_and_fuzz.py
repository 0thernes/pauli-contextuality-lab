#!/usr/bin/env python3
"""Mutation-killing (B13) and parser-fuzzing (B15) verification suite.

1. Mutation tests: injects deliberate single-value mutations into in-memory copies of
   `data/c3_exact_optima_certs.json` and `data/q7minus_42_certs.json` and asserts that
   the exact verifier invariants kill 100% of mutants.
2. Fuzz harness (`fuzz_parse_target`, compatible with `atheris` when installed, and exercised
   over 300 deterministic adversarial payloads during normal test runs).
"""
from __future__ import annotations

import copy
import json
import random
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def validate_c3_cert_structure(cert: dict) -> bool:
    """Strict structural & arithmetic validator for a single C3 MET-SDP integer certificate."""
    required = {"Q", "mu", "K", "d", "cuts", "L"}
    if not isinstance(cert, dict) or not required <= set(cert.keys()):
        return False
    Q, mu, K = cert["Q"], cert["mu"], cert["K"]
    d, cuts, L = cert["d"], cert["cuts"], cert["L"]
    if not (isinstance(Q, int) and Q > 0 and isinstance(K, int) and K > 0 and isinstance(mu, int)):
        return False
    if not (isinstance(d, list) and len(d) == 64 and all(isinstance(x, int) for x in d)):
        return False
    if sum(d) != 0:
        return False
    if not (isinstance(cuts, list) and len(cuts) > 0):
        return False
    for cut in cuts:
        if not (isinstance(cut, list) and len(cut) == 7 and all(isinstance(x, int) for x in cut)):
            return False
        i, j, k, s1, s2, s3, w = cut
        if not (0 <= i < j < k < 64):
            return False
        if s1 not in (-1, 1) or s2 not in (-1, 1) or s3 not in (-1, 1):
            return False
        if s1 * s2 * s3 != -1 or w < 0:
            return False
    if not (isinstance(L, list) and len(L) == 64):
        return False
    for r, row in enumerate(L):
        if not (isinstance(row, list) and len(row) == r + 1 and all(isinstance(x, int) for x in row)):
            return False
    return True


def fuzz_parse_target(raw: bytes) -> None:
    """Atheris-compatible fuzz target: malformed bytes must never raise unhandled exceptions."""
    try:
        text = raw.decode("utf-8", errors="strict")
        obj = json.loads(text)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError, RecursionError):
        return
    if isinstance(obj, dict):
        validate_c3_cert_structure(obj)


class TestMutationAndFuzz(unittest.TestCase):
    """Verify certificate validators kill mutants and survive malformed fuzz inputs."""

    def setUp(self) -> None:
        self.certs = json.loads(
            (ROOT / "data" / "c3_exact_optima_certs.json").read_text(encoding="utf-8")
        )

    def test_baseline_certificates_valid(self) -> None:
        self.assertTrue(validate_c3_cert_structure(self.certs["sigmaA_368"]))
        self.assertTrue(validate_c3_cert_structure(self.certs["sigmaB_344"]))

    def test_mutation_killing_c3_certificates(self) -> None:
        """Mutation testing (B13): every single-defect mutant must be rejected."""
        mutants = []

        # Mutant 1: break zero-sum diagonal shift
        m1 = copy.deepcopy(self.certs["sigmaA_368"])
        m1["d"][0] += 1
        mutants.append(("nonzero_d_sum", m1))

        # Mutant 2: flip frustrated-triangle parity s1*s2*s3 from -1 to +1
        m2 = copy.deepcopy(self.certs["sigmaA_368"])
        m2["cuts"][0][3] *= -1
        mutants.append(("non_frustrated_triangle", m2))

        # Mutant 3: negative cut weight
        m3 = copy.deepcopy(self.certs["sigmaB_344"])
        m3["cuts"][0][6] = -1
        mutants.append(("negative_cut_weight", m3))

        # Mutant 4: out-of-range vertex index
        m4 = copy.deepcopy(self.certs["sigmaB_344"])
        m4["cuts"][0][2] = 64
        mutants.append(("index_out_of_bounds", m4))

        # Mutant 5: non-positive scale K
        m5 = copy.deepcopy(self.certs["sigmaA_368"])
        m5["K"] = 0
        mutants.append(("zero_gram_scale", m5))

        # Mutant 6: truncated triangular Cholesky row
        m6 = copy.deepcopy(self.certs["sigmaA_368"])
        m6["L"][10] = m6["L"][10][:-1]
        mutants.append(("truncated_cholesky_row", m6))

        killed = 0
        for label, mutant in mutants:
            with self.subTest(mutant=label):
                self.assertFalse(validate_c3_cert_structure(mutant))
                killed += 1
        self.assertEqual(killed, len(mutants))

    def test_deterministic_fuzz_corpus(self) -> None:
        """Fuzzing (B15): 300 adversarial byte payloads must never crash the parser."""
        rng = random.Random(20261124)
        edge_cases = [
            b"",
            b"{}",
            b"[]",
            b'{"Q":1,"mu":0,"K":1,"d":[],"cuts":[],"L":[]}',
            b'{"Q":"bad","mu":null,"K":-1,"d":[0],"cuts":[[0,0,0,1,1,1,1]],"L":[[]]}',
            b"\xff\xfe\x00\x01",
            b"{" * 200,
        ]
        for payload in edge_cases:
            fuzz_parse_target(payload)
        for _ in range(300):
            length = rng.randint(0, 256)
            payload = bytes(rng.getrandbits(8) for _ in range(length))
            fuzz_parse_target(payload)

    def test_ast_source_code_mutation_killing(self) -> None:
        """Isolated AST source-code mutation testing (Build Standard B13):
        mutate real operators in in-memory AST copies of core verification modules
        (`certificates.py`, `evidence.py`, `check_readme_axioms.py`) and assert 100% kill rate."""
        import ast
        import types
        from fractions import Fraction

        def load_mutated(
            path: Path,
            fn_name: str,
            target_op: type,
            replacement_op: type,
            class_name: str | None = None,
        ) -> types.ModuleType:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
            mutated = False

            class OpMutator(ast.NodeTransformer):
                def visit_Compare(self, node: ast.Compare) -> ast.AST:
                    nonlocal mutated
                    if not mutated:
                        new_ops = []
                        for op in node.ops:
                            if not mutated and isinstance(op, target_op):
                                new_ops.append(replacement_op())
                                mutated = True
                            else:
                                new_ops.append(op)
                        node.ops = new_ops
                    return self.generic_visit(node)

                def visit_BinOp(self, node: ast.BinOp) -> ast.AST:
                    nonlocal mutated
                    if not mutated and isinstance(node.op, target_op):
                        node.op = replacement_op()
                        mutated = True
                    return self.generic_visit(node)

            target_node = None
            if class_name is None:
                for node in ast.walk(tree):
                    if isinstance(node, ast.FunctionDef) and node.name == fn_name:
                        target_node = node
                        break
            else:
                for node in ast.walk(tree):
                    if isinstance(node, ast.ClassDef) and node.name == class_name:
                        for child in node.body:
                            if isinstance(child, ast.FunctionDef) and child.name == fn_name:
                                target_node = child
                                break
            self.assertIsNotNone(target_node, f"Missing {class_name}.{fn_name} in {path.name}")
            OpMutator().visit(target_node)
            self.assertTrue(mutated, f"AST mutant not applied to {path.name}:{fn_name}")
            ast.fix_missing_locations(tree)
            mod = types.ModuleType(f"_mut_{path.stem}_{fn_name}")
            mod.__file__ = str(path)
            exec(compile(tree, str(path), "exec"), mod.__dict__)
            return mod

        cert_py = ROOT / "tracks" / "disjoint-mermin" / "src" / "certificates.py"
        ev_py = ROOT / "tracks" / "sequential-evidence" / "src" / "evidence.py"
        ax_py = ROOT / "scripts" / "check_readme_axioms.py"

        mutants = [
            # Mutant 1: invert Pauli commutation check == -> != in certificates.commute
            ("certificates.commute: == -> !=", cert_py, "commute", None, ast.Eq, ast.NotEq,
             lambda m: m.commute("XI", "IX") is True and m.commute("XI", "ZI") is False),
            # Mutant 2: corrupt exact degree subtraction (contexts - bound) -> + in certificates.exact_family
            ("certificates.exact_family: - -> +", cert_py, "exact_family", None, ast.Sub, ast.Add,
             lambda m: m.exact_family("square", 2)["contexts"] == 48 and m.exact_family("square", 2)["degree"] == 12),
            # Mutant 3: corrupt independent-readout noise formula (1 - 2*p) -> (1 + 2*p) in certificates.noisy_quantum_score
            ("certificates.noisy_quantum_score: - -> +", cert_py, "noisy_quantum_score", None, ast.Sub, ast.Add,
             lambda m: m.noisy_quantum_score("square", 1, Fraction(1, 20)) == Fraction(1000 + 6 * 729, 1000) - 1),
            # Mutant 4: invert Bet null-mean safety check > -> < in evidence.Bet.__init__
            ("evidence.Bet.__init__: > -> <", ev_py, "__init__", "Bet", ast.Gt, ast.Lt,
             lambda m: self._unsafe_bet_rejected(m)),
            # Mutant 5: corrupt sharp classical bound 1 - min(p) -> 1 + min(p) in evidence.sharp_classical_bound
            ("evidence.sharp_classical_bound: - -> +", ev_py, "sharp_classical_bound", None, ast.Sub, ast.Add,
             lambda m: m.sharp_classical_bound([Fraction(1, 6)] * 6) == Fraction(5, 6)),
            # Mutant 6: corrupt Bet.null_mean weighted sum + -> - in evidence.Bet.null_mean
            ("evidence.Bet.null_mean: + -> -", ev_py, "null_mean", "Bet", ast.Add, ast.Sub,
             lambda m: m.Bet(beta=Fraction(1, 6), q=Fraction(19, 20)).null_mean() == 1),
            # Mutant 7: invert allowed-axiom subset check <= -> > in check_readme_axioms.main
            ("check_readme_axioms.main: <= -> >", ax_py, "main", None, ast.LtE, ast.Gt,
             lambda m: (lambda bad_ax: bad_ax <= m.ALLOWED)({"propext"}) and
             not ({"propext", "sorryAx"} <= m.ALLOWED) and
             m.parse_log("'Foo' depends on axioms: [propext]")["Foo"] == {"propext"} and
             # Actually run mutated main() with clean args via sys.argv patch
             self._run_mutated_axiom_main(m) == 0),
        ]
        killed = 0
        for label, path, fn_name, cls_name, old_op, new_op, invariant in mutants:
            with self.subTest(ast_mutant=label):
                mod = load_mutated(path, fn_name, old_op, new_op, class_name=cls_name)
                try:
                    ok = bool(invariant(mod))
                except Exception:
                    ok = False
                self.assertFalse(ok, f"AST source mutant survived: {label}")
                killed += 1
        self.assertEqual(killed, len(mutants))

    @staticmethod
    def _unsafe_bet_rejected(mod: object) -> bool:
        from fractions import Fraction
        try:
            mod.Bet(beta=Fraction(1, 6), q=Fraction(19, 20), success_factor=2, failure_factor=1)  # type: ignore[attr-defined]
            return False
        except ValueError:
            return True

    @staticmethod
    def _run_mutated_axiom_main(mod: object) -> int:
        old_argv = sys.argv
        try:
            sys.argv = ["check_readme_axioms.py", "--require-exhaustive"]
            return int(mod.main())  # type: ignore[attr-defined]
        finally:
            sys.argv = old_argv


if __name__ == "__main__":
    if "--atheris" in sys.argv:  # pragma: no cover
        import atheris  # type: ignore

        atheris.Setup([a for a in sys.argv if a != "--atheris"], fuzz_parse_target)
        atheris.Fuzz()
    else:
        unittest.main()
