"""Track 2 tests: exact contextuality degrees for disjoint Mermin configurations.

Includes literal Gaussian-integer matrix checks (zero floats) and negative controls.
"""
import copy
import itertools
import subprocess
import sys
import unittest
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

TRACK_ROOT = Path(__file__).resolve().parents[1] / "tracks" / "disjoint-mermin"
sys.path.insert(0, str(TRACK_ROOT / "src"))
import certificates as production  # noqa: E402

ZERO, ONE, MINUS, IMAG, NIMAG = (0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)
LITERAL = {
    "I": ((ONE, ZERO), (ZERO, ONE)),
    "X": ((ZERO, ONE), (ONE, ZERO)),
    "Y": ((ZERO, NIMAG), (IMAG, ZERO)),
    "Z": ((ONE, ZERO), (ZERO, MINUS)),
}


def _add(a, b):
    return a[0] + b[0], a[1] + b[1]


def _mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def _dot_entry(a, b, i, j, n):
    acc = ZERO
    for k in range(n):
        acc = _add(acc, _mul(a[i][k], b[k][j]))
    return acc


def _matmul(a, b):
    n = len(a)
    return tuple(
        tuple(_dot_entry(a, b, i, j, n) for j in range(n))
        for i in range(n)
    )


def _tensor(a, b):
    return tuple(tuple(_mul(x, y) for x in ar for y in br) for ar in a for br in b)


@lru_cache(None)
def _operator(word):
    matrix = ((ONE,),)
    for letter in word:
        matrix = _tensor(matrix, LITERAL[letter])
    return matrix


def _identity(n, sign=1):
    return tuple(tuple((sign, 0) if i == j else ZERO for j in range(n)) for i in range(n))


def _literal_graph(config):
    ops = [_operator(w) for w in config["observables"]]
    adjacent = [set() for _ in ops]
    for i, a in enumerate(ops):
        for j in range(i):
            if _matmul(a, ops[j]) != _matmul(ops[j], a):
                adjacent[i].add(j)
                adjacent[j].add(i)
    return adjacent


def _independently_enumerated_support(config):
    graph = _literal_graph(config)
    found = set()

    def visit(selected, available):
        if selected and all(len(neighbors.intersection(selected)) % 2 == 0 for neighbors in graph):
            found.add(frozenset(selected))
        while available:
            vertex = min(available)
            available.remove(vertex)
            visit(selected | {vertex}, available - graph[vertex])

    visit(set(), set(range(len(graph))))
    return found


class DisjointMerminTests(unittest.TestCase):
    def test_zero_copies_and_closed_forms(self):
        self.assertEqual(production.exact_family("square", 0)["contexts"], 0)
        self.assertIsNone(production.exact_family("square", 0)["epsilon"])
        self.assertEqual(production.spectrum([]), {0: 1})
        for k in range(1, 6):
            sq = production.exact_family("square", k)
            self.assertEqual(sq["degree"], (7**k - 5**k) // 2)
            self.assertEqual(sq["contexts"], 7**k - 1)
            pent = production.exact_family("pentagram", k)
            self.assertEqual(pent["degree"], (6**k - 4**k) // 2)
            self.assertEqual(pent["contexts"], 6**k - 1)

    def test_phase_sensitive_multiplication(self):
        self.assertEqual(production.multiply("XX", "ZZ"), (2, "YY"))
        self.assertEqual(production.multiply("XZ", "ZX"), (0, "YY"))
        self.assertNotEqual(production.multiply("X", "Y"), production.multiply("Y", "X"))

    def test_score_negative_endpoint(self):
        sq, pent = production.all_scores(production.SQUARE), production.all_scores(production.PENTAGRAM)
        self.assertEqual(max(abs(s + 1) for s in sq), max(sq) + 1)
        self.assertEqual(max(abs(s + 1) for s in pent), max(pent) + 1)
        self.assertEqual(min(pent) + 1, -4)

    def test_mixed_contexts(self):
        cfg = production.compose([production.SQUARE, production.PENTAGRAM])
        self.assertEqual(len(cfg["observables"]), 19)
        self.assertEqual(len(cfg["contexts"]), 41)
        self.assertTrue(production.validate(cfg))
        self.assertEqual(max(production.spectrum([production.SQUARE, production.PENTAGRAM])), 19)

    def test_exact_noise_endpoints(self):
        for kind in production.SEEDS:
            for k in (1, 2, 3):
                self.assertEqual(production.noisy_quantum_score(kind, k, 0), production.exact_family(kind, k)["contexts"])
                self.assertEqual(production.noisy_quantum_score(kind, k, Fraction(1, 2)), 0)

    def test_literal_pauli_contexts(self):
        for config in [
            production.SQUARE,
            production.PENTAGRAM,
            production.compose([production.SQUARE, production.SQUARE]),
        ]:
            ops = [_operator(w) for w in config["observables"]]
            for context, sign in zip(config["contexts"], config["signs"], strict=True):
                result = _identity(2 ** config["qubits"])
                for i in context:
                    for j in context:
                        self.assertEqual(_matmul(ops[i], ops[j]), _matmul(ops[j], ops[i]))
                    result = _matmul(result, ops[i])
                self.assertEqual(result, _identity(len(result), sign))

    def test_full_support_independent_matrix_and_set_route(self):
        for config in [
            production.SQUARE,
            production.PENTAGRAM,
            production.compose([production.SQUARE, production.SQUARE]),
        ]:
            found = _independently_enumerated_support(config)
            self.assertEqual(found, {frozenset(c) for c in config["contexts"]})

    def test_direct_seed_assignment_counts(self):
        expected = [{4: 96, 0: 320, -4: 96}, {3: 320, -1: 640, -5: 64}]
        for seed, wanted in zip([production.SQUARE, production.PENTAGRAM], expected, strict=True):
            histogram = Counter()
            for assignment in itertools.product([-1, 1], repeat=len(seed["observables"])):
                score = 0
                for context, sign in zip(seed["contexts"], seed["signs"], strict=True):
                    value = sign
                    for v in context:
                        value *= assignment[v]
                    score += value
                histogram[score] += 1
            self.assertEqual(histogram, wanted)
            self.assertEqual(histogram, Counter(production.all_scores(seed)))

    def test_noise_against_enumerated_error_patterns(self):
        p = Fraction(1, 20)
        for seed in [production.SQUARE, production.PENTAGRAM]:
            config = production.compose([seed, seed])
            by_size = Counter(map(len, config["contexts"]))
            score = 0
            for r, count in by_size.items():
                mean = 0
                for errors in itertools.product([False, True], repeat=r):
                    flips = sum(errors)
                    probability = p**flips * (1 - p) ** (r - flips)
                    mean += (-1 if flips % 2 else 1) * probability
                score += count * mean
            self.assertEqual(score, production.noisy_quantum_score(seed["name"], 2, p))

    def test_validation_negative_controls(self):
        bad = copy.deepcopy(production.SQUARE)
        bad["contexts"].append(bad["contexts"][0])
        bad["signs"].append(bad["signs"][0])
        with self.assertRaisesRegex(AssertionError, "duplicate context"):
            production.validate(bad)
        bad = copy.deepcopy(production.SQUARE)
        bad["signs"][0] *= -1
        with self.assertRaisesRegex(AssertionError, "quantum context sign"):
            production.validate(bad)
        with self.assertRaises(ValueError):
            production.noisy_quantum_score("nonexistent-family", 1, Fraction(0))

    def test_optimized_python_is_rejected(self):
        result = subprocess.run(
            [sys.executable, "-O", "-c", "import certificates"],
            cwd=str(TRACK_ROOT / "src"),
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("RuntimeError", result.stderr)


if __name__ == "__main__":
    unittest.main()
