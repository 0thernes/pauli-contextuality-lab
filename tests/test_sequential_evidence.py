"""Track 3 tests: exact sequential contextuality evidence and adversarial artifact binding."""
import json
import random
import shutil
import sys
import tempfile
import unittest
from fractions import Fraction as F
from itertools import product
from pathlib import Path

TRACK_ROOT = Path(__file__).resolve().parents[1] / "tracks" / "sequential-evidence"
sys.path.insert(0, str(TRACK_ROOT / "src"))
sys.path.insert(0, str(TRACK_ROOT / "scripts"))

from evidence import (  # noqa: E402
    Bet,
    enumerate_square,
    exact_hitting_probability,
    outcomes,
    replay,
    sharp_classical_bound,
    validate_distribution,
)
from run_experiment import load_native_trials  # noqa: E402


class SequentialEvidenceTests(unittest.TestCase):
    def test_parity_structure(self):
        report = enumerate_square()
        self.assertEqual(report["failure_histogram"], {1: 96, 3: 320, 5: 96})
        for context, witness in report["singleton_witnesses"].items():
            self.assertEqual(outcomes(witness), tuple(i != context for i in range(6)))

    def test_sharp_bound_for_heterogeneous_distributions(self):
        rng = random.Random(43)
        for _ in range(25):
            counts = [rng.randrange(20) for _ in range(6)]
            p = tuple(F(c, sum(counts)) for c in counts)
            self.assertEqual(sharp_classical_bound(p), 1 - min(p))

    def test_every_adversarial_assignment_and_simplex_vertex(self):
        bet = Bet()
        for vertex in range(6):
            p = [bet.beta] * 6
            p[vertex] += 1 - 6 * bet.beta
            for assignment in range(512):
                mean = sum(pi * bet.factor(win) for pi, win in zip(p, outcomes(assignment)))
                self.assertLessEqual(mean, 1)

    def test_exceptional_mixture_budget(self):
        bet = Bet(delta=F(1, 5), q=F(29, 30))
        self.assertEqual(bet.bound, F(14, 15))
        self.assertEqual(bet.null_mean(), 1)
        mean = F(4, 5) * (F(11, 12) * bet.a + F(1, 12) * bet.b) + F(1, 5) * bet.a
        self.assertEqual(mean, 1)

    def test_absorption_dp_against_independent_path_enumeration(self):
        bet = Bet(beta=F(1, 6), q=F(19, 20))
        p, horizon, threshold = F(5, 6), 9, F(3, 2)
        hit = F(0)
        for path in product((False, True), repeat=horizon):
            wealth, ever = F(1), False
            for win in path:
                wealth *= bet.factor(win)
                ever |= wealth >= threshold
            if ever:
                s = sum(path)
                hit += p**s * (1 - p) ** (horizon - s)
        self.assertEqual(exact_hitting_probability(bet, p, horizon, threshold), hit)

    def test_exact_counterexample_to_miscalibration(self):
        naive = Bet(beta=F(1, 6))
        self.assertGreater(naive.a**36, 100)
        self.assertGreater(F(11, 12) ** 36, F(1, 100))
        self.assertLess(Bet().a**36, 100)

    def test_finite_optional_stopping_bound(self):
        for bet in (Bet(), Bet(beta=F(1, 6))):
            probability = exact_hitting_probability(bet, bet.bound, 200, 20)
            self.assertLessEqual(probability, F(1, 20))

    def test_reject_unsafe_contracts(self):
        for kwargs in (
            {"success_factor": F(6, 5)},
            {"failure_factor": -1},
            {"beta": 0},
            {"beta": F(1, 5)},
            {"q": F(1, 2)},
            {"delta": 1},
        ):
            with self.assertRaises(ValueError):
                Bet(**kwargs)
        with self.assertRaises(ValueError):
            validate_distribution((F(11, 60),) * 5 + (F(1, 12),), F(1, 6))
        with self.assertRaises(ValueError):
            replay([{"success": 1}], Bet())


class ArtifactBindingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = json.loads((TRACK_ROOT / "results/stack_report.json").read_text(encoding="utf-8"))

    def fixture(self, root):
        (root / "results").mkdir()
        shutil.copy2(TRACK_ROOT / "results/stack_report.json", root / "results/stack_report.json")
        for name in self.report["artifacts_sha256"]:
            shutil.copy2(TRACK_ROOT / "results" / name, root / "results" / name)
        for name in self.report["source_sha256"]:
            src_path = TRACK_ROOT / name
            if not src_path.exists() and name.startswith("third_party/"):
                src_path = TRACK_ROOT.parents[1] / name
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_path, target)

    def test_current_artifact_and_stale_failure_rejected(self):
        self.assertEqual(len(load_native_trials()), 6000)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            report = dict(self.report, status="fail")
            (root / "results/stack_report.json").write_text(json.dumps(report), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "successful execution"):
                load_native_trials(root)

    def test_changed_transcript_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            path = root / "results/stack_trials.json"
            data = json.loads(path.read_text(encoding="utf-8"))
            data[0]["success"] = not data[0]["success"]
            path.write_text(json.dumps(data), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "fingerprint mismatch"):
                load_native_trials(root)

    def test_changed_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            with (root / "src/stack_moonlab.mjs").open("a", encoding="utf-8") as out:
                out.write("\n// changed after the run\n")
            with self.assertRaisesRegex(ValueError, "source changed"):
                load_native_trials(root)


if __name__ == "__main__":
    unittest.main()
