import assert from 'node:assert/strict';
import test from 'node:test';

import {
  contexts,
  observables,
  evaluate,
  family,
  normalizedMargin,
  verifySigns,
  exhaustive,
} from '../tracks/disjoint-mermin/web/lab.mjs';

import {
  enumerate as enumerateSquare,
  wins as squareWins,
  exactReplay,
} from '../tracks/sequential-evidence/web/model.mjs';

test('Track 2 web model: 4-qubit disjoint Mermin square exact enumeration & mutation rejection', () => {
  assert.equal(observables.length, 18);
  assert.equal(new Set(observables).size, 18);
  assert.equal(contexts.length, 48);
  assert.equal(contexts.filter((c) => c.indices.length === 3).length, 12);
  assert.equal(contexts.filter((c) => c.indices.length === 6).length, 36);
  assert.ok(verifySigns().every((x) => x.valid));

  // Negative control: flipping a single context sign must be detected
  const mutated = contexts.map((x) => ({ ...x }));
  mutated[47].sign *= -1;
  assert.deepEqual(
    verifySigns(mutated)
      .filter((x) => !x.valid)
      .map((x) => x.index),
    [47],
  );

  assert.equal(evaluate(0).score, 24);
  assert.equal(evaluate(0).violations, 12);
  for (let m = 0; m < 512; m++) {
    const r = evaluate(m | (m << 9));
    assert.equal(r.score, (1 + r.localScores[0]) * (1 + r.localScores[1]) - 1);
  }
  const exact = exhaustive();
  assert.equal(exact.assignments, 262144);
  assert.equal(exact.best, 24);
  assert.equal(exact.minimumViolations, 12);
  assert.equal(exact.minimizers, 9216);
  assert.equal(family('square', 2).d, 12n);
  assert.equal(family('pentagram', 2).d, 10n);
  for (const kind of ['square', 'pentagram']) {
    for (const k of [1, 2, 7, 24, 1000]) {
      const f = family(kind, k);
      assert.equal(f.L - f.B, 2n * f.d);
      assert.ok(Math.abs(normalizedMargin(kind, k, 0) - f.gap) < 1e-12);
      assert.ok(normalizedMargin(kind, k, f.threshold + 0.001) <= 0);
    }
  }
  assert.throws(() => family('square', 0));
  assert.throws(() => family('invalid', 2));
});

test('Track 3 web model: Peres-Mermin parity histogram & exact BigInt stopping replay', () => {
  assert.deepEqual(enumerateSquare(), { 1: 96, 3: 320, 5: 96 });
  assert.deepEqual(squareWins(0), [true, true, true, true, true, false]);
  assert.equal(exactReplay(Array(36).fill(true), 57n, 50n, 3n, 10n), 36);
  assert.equal(exactReplay(Array(36).fill(true), 57n, 55n, 3n, 5n), null);
  assert.equal(exactReplay(Array(600).fill(true), 57n, 55n, 3n, 5n), 129);
});
