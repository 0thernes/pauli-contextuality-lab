#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Exact pure-integer & rational verification of the four-way Q+(7,2) triality residuals
(Theorem 23, motivated by Metod Saniga's 26 Nov 2026 correspondence).

Deletes four structurally distinct 315-line subsystems from Q+(7,2) (135 pts, 1,575 lines),
leaving 1,260 residual contexts in every case, and certifies exact contextuality degrees
with ZERO floating-point arithmetic:
  (0) Q+(7,2) \\ DW(5,2)       (135 pts, 1,260 lines): exact d = 0
  (a) Q+(7,2) \\ Spread(9 PG3) (135 pts, 1,260 lines): exact d = 210
      - Proved via 5,040 = 7! transversal Mermin-Peres grids covering every line uniformly
        with multiplicity 24 (5,040 / 24 = 210) on BOTH solid systems M1 and M2.
      - Attained by 36 = C(9,2) copies of DW(5,2) hitting every grid in exactly 1 line.
  (a*) Q+(7,2) \\ Ovoid(9 pts) (126 pts, 1,260 lines): exact d = 252
      - Triality dual of (a): proved via 280 intact Q-(5,2) elliptic quadrics (d = 9)
        covering every line uniformly with multiplicity 10 (280 * 9 / 10 = 252), strictly
        beating the Theorem 1 spectral floor (204).
      - Attained by all 240 copies of DW(5,2) (6-regular on 126 points).
  (b) Q+(7,2) \\ Q(6,2)        (135 pts, 1,260 lines): exact d = 252
      - Proved via Case C4 Jordan-multiplication operator Lambda_sigma on the 72 outside
        points: exact integer minimal polynomial (Lambda - 21 I)(Lambda - 9 I)(Lambda + 3 I) = 0
        plus exact integer traces certifies spec(Lambda_sigma) = {21^2, 9^14, (-3)^56}.
      - Exact rational Gaussian elimination over Q proves the 2D top eigenspace ker(Lambda - 21 I)
        contains exactly 2 projective +-1 vectors -> 120 * 2 = 240 unique optimal sets.

Also enumerates all 240 copies of DW(5,2) via O+(8,2) orthogonal transvections and verifies
their exact intersection spectra against the spread, Q(6,2), and ovoid, plus negative controls.
"""
from __future__ import annotations

import itertools
import json
import sys
from collections import Counter, deque
from fractions import Fraction
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve()
REPO_ROOT = HERE.parents[3]
WITNESS_N4_H = REPO_ROOT / "data" / "witness" / "n4_h.txt"
OUT_JSON = REPO_ROOT / "tracks" / "spectral-bounds" / "results" / "q7plus_triality_residuals.json"

N = 4
MASK = (1 << N) - 1


def symp(u: int, v: int) -> int:
    return (bin((u & MASK) & (v >> N)).count("1") ^ bin((u >> N) & (v & MASK)).count("1")) & 1


def y_count(u: int) -> int:
    return bin((u & MASK) & (u >> N)).count("1")


def q0(u: int) -> int:
    return y_count(u) & 1


def line_sign(u: int, v: int) -> int:
    ux, uz, vx, vz = u & MASK, u >> N, v & MASK, v >> N
    ph = (
        bin(ux & uz).count("1")
        + bin(vx & vz).count("1")
        - bin((ux ^ vx) & (uz ^ vz)).count("1")
        + 2 * bin(uz & vx).count("1")
    ) % 4
    if ph not in (0, 2):
        raise ValueError(f"Non-commuting pair ({u}, {v})")
    return 1 if ph == 0 else -1


def fmt_pauli(u: int) -> str:
    x, z = u & MASK, u >> N
    return "".join("IXZY"[((x >> i) & 1) + 2 * ((z >> i) & 1)] for i in range(N))


def build_lines(pts: list[int]) -> list[tuple[int, int, int, int]]:
    spts = sorted(pts)
    pset = set(spts)
    lines: list[tuple[int, int, int, int]] = []
    for i, u in enumerate(spts):
        for j in range(i + 1, len(spts)):
            v = spts[j]
            w = u ^ v
            if w > v and w in pset and symp(u, v) == 0:
                lines.append((u, v, w, line_sign(u, v)))
    return lines


def build_q7plus_solids() -> tuple[list[int], list[tuple[int, int, int, int]], list[frozenset[int]], list[frozenset[int]]]:
    q7p = [u for u in range(1, 256) if q0(u) == 0]
    if len(q7p) != 135:
        raise AssertionError(f"Expected 135 points in Q+(7,2), got {len(q7p)}")
    q7p_lines = build_lines(q7p)
    if len(q7p_lines) != 1575:
        raise AssertionError(f"Expected 1575 lines in Q+(7,2), got {len(q7p_lines)}")

    adj: dict[int, set[int]] = {u: set() for u in q7p}
    for u, v, w, _ in q7p_lines:
        adj[u].update((v, w))
        adj[v].update((u, w))
        adj[w].update((u, v))

    solids_set: set[frozenset[int]] = set()
    for u in q7p:
        nu = [v for v in adj[u] if v > u]
        for v in nu:
            w = u ^ v
            common = adj[u] & adj[v]
            for x in common:
                if x <= v or x == w:
                    continue
                common2 = common & adj[x]
                for y in common2:
                    if y <= x or y in (u ^ x, v ^ x, w ^ x):
                        continue
                    pts = {
                        a ^ b ^ c ^ d
                        for a in (0, u)
                        for b in (0, v)
                        for c in (0, x)
                        for d in (0, y)
                    } - {0}
                    if len(pts) == 15 and all(q0(p) == 0 for p in pts):
                        solids_set.add(frozenset(pts))

    solids = sorted(solids_set, key=lambda s: tuple(sorted(s)))
    if len(solids) != 270:
        raise AssertionError(f"Expected 270 solids in Q+(7,2), got {len(solids)}")

    # Partition into two Latin/Greek systems M1, M2: same system iff |S1 cap S2| in {0, 3, 15}.
    z_solid = frozenset(c << N for c in range(1, 16))
    m1 = [s for s in solids if len(s & z_solid) in (0, 3, 15)]
    m2 = [s for s in solids if len(s & z_solid) in (1, 7)]
    if len(m1) != 135 or len(m2) != 135:
        raise AssertionError(f"Bad solid systems: {len(m1)}, {len(m2)}")
    return q7p, q7p_lines, m1, m2


def find_spread_in_system(solids: list[frozenset[int]], seed_idx: int = 0) -> list[frozenset[int]]:
    n = len(solids)
    masks = [0] * n
    for i, s in enumerate(solids):
        m = 0
        for p in s:
            m |= 1 << p
        masks[i] = m
    chosen = [seed_idx]
    used = masks[seed_idx]
    cands = [i for i in range(n) if (masks[i] & used) == 0]

    def bt(used_m: int, pool: list[int]) -> bool:
        if len(chosen) == 9:
            return True
        if len(chosen) + len(pool) < 9:
            return False
        for idx_pos, i in enumerate(pool):
            mi = masks[i]
            if (mi & used_m) == 0:
                chosen.append(i)
                nxt = [j for j in pool[idx_pos + 1 :] if (masks[j] & mi) == 0]
                if bt(used_m | mi, nxt):
                    return True
                chosen.pop()
        return False

    if not bt(used, cands):
        raise RuntimeError("Failed to locate a 9-solid spread")
    spread = [solids[i] for i in chosen]
    union_pts = set().union(*spread)
    if len(union_pts) != 135:
        raise AssertionError("Spread does not partition all 135 points")
    return spread


def find_ovoid_in_q7plus(q7p: list[int]) -> list[int]:
    noncol = {u: [v for v in q7p if v > u and symp(u, v) == 1] for u in q7p}
    chosen: list[int] = []

    def bt(pool: list[int]) -> bool:
        if len(chosen) == 9:
            return True
        if len(chosen) + len(pool) < 9:
            return False
        for idx_pos, u in enumerate(pool):
            chosen.append(u)
            nxt = [v for v in pool[idx_pos + 1 :] if symp(u, v) == 1]
            if bt(nxt):
                return True
            chosen.pop()
        return False

    if not bt(q7p):
        raise RuntimeError("Failed to locate a 9-point ovoid")
    if not all(symp(a, b) == 1 for a, b in itertools.combinations(chosen, 2)):
        raise AssertionError("Ovoid points are not pairwise anticommuting")
    return chosen


def load_hoggar_q7p_signs(q7p: list[int]) -> dict[int, int]:
    parts = WITNESS_N4_H.read_text(encoding="utf-8").strip().split()
    h_mask = int(parts[3], 16)
    return {u: (-1 if ((h_mask >> u) & 1) else 1) for u in q7p}


def generate_all_240_dw52(
    q7p: list[int], q7p_lines: list[tuple[int, int, int, int]], f0: dict[int, int]
) -> tuple[list[frozenset[int]], dict[tuple[int, int, int], int], list[dict[int, int]]]:
    line_to_idx = {(u, v, w): idx for idx, (u, v, w, _) in enumerate(q7p_lines)}
    init_dw = frozenset(
        line_to_idx[(u, v, w)]
        for (u, v, w, s) in q7p_lines
        if f0[u] * f0[v] * f0[w] != s
    )
    if len(init_dw) != 315:
        raise AssertionError(f"Expected 315 violated lines in Q+(7,2), got {len(init_dw)}")

    refls = [v for v in range(1, 256) if q0(v) == 1]
    if len(refls) != 120:
        raise AssertionError(f"Expected 120 reflections, got {len(refls)}")

    # Precompute action of 25 reflections on line indices AND on sign assignments.
    # For reflection T_r(x) = x + <x, r> r with q0(r) = 1:
    # U_r P_x U_r^dagger = eta_r(x) P_{T_r(x)}, where U_r = (1 + i P_r)/sqrt(2).
    # For <r, x> = 1, P_r P_x = +- i P_{r^x}; specifically i P_r P_x = eta_r(x) P_{r^x}.
    def eta_refl(r: int, x: int) -> int:
        if symp(r, x) == 0:
            return 1
        rx, rz, xx, xz = r & MASK, r >> N, x & MASK, x >> N
        ph = (
            1  # factor of i
            + bin(rx & rz).count("1")
            + bin(xx & xz).count("1")
            - bin((rx ^ xx) & (rz ^ xz)).count("1")
            + 2 * bin(rz & xx).count("1")
        ) % 4
        if ph not in (0, 2):
            raise AssertionError("Bad transvection phase")
        return 1 if ph == 0 else -1

    gen_data: list[tuple[list[int], dict[int, tuple[int, int]]]] = []
    for r in refls[:25]:
        perm = [0] * len(q7p_lines)
        for idx, (a, b, c, _) in enumerate(q7p_lines):
            ta = a ^ (r if symp(a, r) else 0)
            tb = b ^ (r if symp(b, r) else 0)
            tc = c ^ (r if symp(c, r) else 0)
            t0, t1, t2 = sorted((ta, tb, tc))
            perm[idx] = line_to_idx[(t0, t1, t2)]
        pt_map = {x: (x ^ (r if symp(x, r) else 0), eta_refl(r, x)) for x in q7p}
        gen_data.append((perm, pt_map))

    seen: dict[frozenset[int], dict[int, int]] = {init_dw: f0}
    queue: deque[frozenset[int]] = deque([init_dw])
    while queue:
        cur = queue.popleft()
        cur_f = seen[cur]
        for perm, pt_map in gen_data:
            nxt = frozenset(perm[i] for i in cur)
            if nxt not in seen:
                nxt_f = {pt_map[x][0]: pt_map[x][1] * cur_f[x] for x in q7p}
                seen[nxt] = nxt_f
                queue.append(nxt)

    if len(seen) != 240:
        raise AssertionError(f"Expected 240 copies of DW(5,2), got {len(seen)}")
    dws = list(seen.keys())
    assigns = [seen[dw] for dw in dws]
    return dws, line_to_idx, assigns


def count_transversal_grids(
    spread: list[frozenset[int]], resid_lines: list[tuple[int, int, int, int]]
) -> tuple[set[frozenset[tuple[int, int, int]]], Counter[tuple[int, int, int]]]:
    solid_of = {p: si for si, sol in enumerate(spread) for p in sol}
    resid_triples = [tuple(sorted((u, v, w))) for (u, v, w, _) in resid_lines]
    resid_set = set(resid_triples)
    grids: set[frozenset[tuple[int, int, int]]] = set()
    for i, l1 in enumerate(resid_triples):
        a0, a1, a2 = l1
        sl1 = {solid_of[a0], solid_of[a1], solid_of[a2]}
        for l2 in resid_triples[i + 1 :]:
            b0, b1, b2 = l2
            if solid_of[b0] in sl1 or solid_of[b1] in sl1 or solid_of[b2] in sl1:
                continue
            c0 = (symp(a0, b0) == 0, symp(a0, b1) == 0, symp(a0, b2) == 0)
            if sum(c0) != 1:
                continue
            j0 = c0.index(True)
            c1 = (symp(a1, b0) == 0, symp(a1, b1) == 0, symp(a1, b2) == 0)
            if sum(c1) != 1:
                continue
            j1 = c1.index(True)
            if j1 == j0:
                continue
            j2 = 3 - j0 - j1
            if symp(a2, l2[j2]) != 0:
                continue
            bb0, bb1, bb2 = l2[j0], l2[j1], l2[j2]
            cc0, cc1, cc2 = a0 ^ bb0, a1 ^ bb1, a2 ^ bb2
            l3 = tuple(sorted((cc0, cc1, cc2)))
            k0 = tuple(sorted((a0, bb0, cc0)))
            k1 = tuple(sorted((a1, bb1, cc1)))
            k2 = tuple(sorted((a2, bb2, cc2)))
            if l3 in resid_set and k0 in resid_set and k1 in resid_set and k2 in resid_set:
                g6 = frozenset((l1, l2, l3, k0, k1, k2))
                if len(g6) == 6:
                    grids.add(g6)
    mult: Counter[tuple[int, int, int]] = Counter(ln for g6 in grids for ln in g6)
    return grids, mult


def count_intact_q5minus(
    pts: list[int], lines: list[tuple[int, int, int, int]]
) -> tuple[int, dict[int, int]]:
    pset = set(pts)
    lset = {tuple(sorted((u, v, w))) for (u, v, w, _) in lines}
    off_pts = [u for u in range(1, 256) if q0(u) == 1]
    q5m_subs: set[frozenset[int]] = set()
    for i, u in enumerate(off_pts):
        for v in off_pts[i + 1 :]:
            if symp(u, v) == 1 and q0(u ^ v) == 1:
                sub = frozenset(x for x in pset if symp(x, u) == 0 and symp(x, v) == 0)
                if len(sub) == 27:
                    q5m_subs.add(sub)
    lc: Counter[tuple[int, int, int]] = Counter()
    intact = 0
    for sub in q5m_subs:
        sub_s = sorted(sub)
        sl: list[tuple[int, int, int]] = []
        for ii, a in enumerate(sub_s):
            for jj in range(ii + 1, len(sub_s)):
                b = sub_s[jj]
                c = a ^ b
                if c > b and c in sub and symp(a, b) == 0:
                    sl.append((a, b, c))
        if len(sl) == 45 and all(ln in lset for ln in sl):
            intact += 1
            for ln in sl:
                lc[ln] += 1
    return intact, dict(sorted(Counter(lc.values()).items()))


def mat_mul_int(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    n = len(a)
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        ai = a[i]
        oi = out[i]
        for k in range(n):
            aik = ai[k]
            if aik:
                bk = b[k]
                for j in range(n):
                    oi[j] += aik * bk[j]
    return out


def mat_shift_int(a: list[list[int]], c: int) -> list[list[int]]:
    n = len(a)
    out = [row[:] for row in a]
    for i in range(n):
        out[i][i] -= c
    return out


def rational_nullspace(mat: list[list[int]]) -> list[list[Fraction]]:
    """Exact RREF nullspace basis over Q (zero floating point)."""
    m = len(mat)
    n = len(mat[0])
    a = [[Fraction(x) for x in row] for row in mat]
    piv_cols: list[int] = []
    r = 0
    for col in range(n):
        piv = next((i for i in range(r, m) if a[i][col] != 0), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = Fraction(1, 1) / a[r][col]
        a[r] = [v * inv for v in a[r]]
        for i in range(m):
            if i != r and a[i][col] != 0:
                fac = a[i][col]
                a[i] = [a[i][j] - fac * a[r][j] for j in range(n)]
        piv_cols.append(col)
        r += 1
    piv_set = set(piv_cols)
    free_cols = [c for c in range(n) if c not in piv_set]
    basis: list[list[Fraction]] = []
    for fc in free_cols:
        vec = [Fraction(0)] * n
        vec[fc] = Fraction(1)
        for row_idx, pc in enumerate(piv_cols):
            vec[pc] = -a[row_idx][fc]
        basis.append(vec)
    return basis


def verify_case_c4_exact_spectrum_and_uniqueness(
    q7p: list[int], q7p_lines: list[tuple[int, int, int, int]], f_hog: dict[int, int]
) -> dict[str, Any]:
    p_off = next(u for u in range(1, 256) if q0(u) == 1)
    q62_pts = sorted(u for u in q7p if symp(u, p_off) == 0)
    out_pts = sorted(u for u in q7p if symp(u, p_off) == 1)
    if len(q62_pts) != 63 or len(out_pts) != 72:
        raise AssertionError("Bad Q(6,2) split")
    q62_set, out_set = set(q62_pts), set(out_pts)
    resid_lines = [
        ln for ln in q7p_lines if not (ln[0] in q62_set and ln[1] in q62_set and ln[2] in q62_set)
    ]
    if len(resid_lines) != 1260:
        raise AssertionError(f"Expected 1260 residual lines for Q(6,2), got {len(resid_lines)}")

    out_idx = {o: i for i, o in enumerate(out_pts)}
    lam = [[0] * 72 for _ in range(72)]
    for u, v, w, s in resid_lines:
        h = next(p for p in (u, v, w) if p in q62_set)
        o1, o2 = [p for p in (u, v, w) if p in out_set]
        i1, i2 = out_idx[o1], out_idx[o2]
        val = s * f_hog[h]
        lam[i1][i2] = val
        lam[i2][i1] = val

    # Exact integer minimal polynomial check: (Lam - 21 I)(Lam - 9 I)(Lam + 3 I) == 0
    l_m21 = mat_shift_int(lam, 21)
    l_m9 = mat_shift_int(lam, 9)
    l_p3 = mat_shift_int(lam, -3)
    prod = mat_mul_int(mat_mul_int(l_m21, l_m9), l_p3)
    if any(x != 0 for row in prod for x in row):
        raise AssertionError("Minimal polynomial (Lam - 21 I)(Lam - 9 I)(Lam + 3 I) != 0")

    lam2 = mat_mul_int(lam, lam)
    tr1 = sum(lam[i][i] for i in range(72))
    tr2 = sum(lam2[i][i] for i in range(72))
    # Solve m21 + m9 + m_m3 = 72, 21 m21 + 9 m9 - 3 m_m3 = tr1, 441 m21 + 81 m9 + 9 m_m3 = tr2
    if tr1 != 0 or tr2 != 2520:
        raise AssertionError(f"Unexpected traces: tr1={tr1}, tr2={tr2}")
    # Unique solution: m21=2, m9=14, m_m3=56
    if 2 + 14 + 56 != 72 or 2 * 21 + 14 * 9 - 56 * 3 != 0 or 2 * 441 + 14 * 81 + 56 * 9 != 2520:
        raise AssertionError("Multiplicity arithmetic mismatch")

    # Exact rational nullspace of (Lam - 21 I): dimension MUST be 2
    basis = rational_nullspace(l_m21)
    if len(basis) != 2:
        raise AssertionError(f"Expected 2D +21 eigenspace, got dim {len(basis)}")
    u1, u2 = basis
    # Find two linearly independent coordinates (r0, r1)
    r0 = next(i for i in range(72) if u1[i] != 0 or u2[i] != 0)
    r1 = next(i for i in range(72) if u1[r0] * u2[i] - u2[r0] * u1[i] != 0)
    det = u1[r0] * u2[r1] - u2[r0] * u1[r1]

    binary_sets: set[frozenset[tuple[int, int, int]]] = set()
    binary_sols = 0
    for s1 in (Fraction(1), Fraction(-1)):
        # Solve c1 * u1[r0] + c2 * u2[r0] = 1, c1 * u1[r1] + c2 * u2[r1] = s1
        c1 = (Fraction(1) * u2[r1] - s1 * u2[r0]) / det
        c2 = (u1[r0] * s1 - u1[r1] * Fraction(1)) / det
        y_vec = [c1 * u1[i] + c2 * u2[i] for i in range(72)]
        if all(val in (Fraction(1), Fraction(-1)) for val in y_vec):
            binary_sols += 1
            asg = {h: f_hog[h] for h in q62_pts}
            for o, val in zip(out_pts, y_vec):
                asg[o] = int(val)
            vset = frozenset(
                (u, v, w) for (u, v, w, s) in resid_lines if asg[u] * asg[v] * asg[w] != s
            )
            if len(vset) != 252:
                raise AssertionError(f"Expected 252 violated lines, got {len(vset)}")
            binary_sets.add(vset)

    if binary_sols != 2 or len(binary_sets) != 2:
        raise AssertionError(f"Expected exactly 2 projective binary vectors & sets, got {binary_sols}, {len(binary_sets)}")

    return {
        "pole": fmt_pauli(p_off),
        "q62_points": 63,
        "outside_points": 72,
        "residual_lines": 1260,
        "tr_lambda": tr1,
        "tr_lambda_sq": tr2,
        "minimal_polynomial_roots": [21, 9, -3],
        "eigenvalue_multiplicities": {"21": 2, "9": 14, "-3": 56},
        "top_eigenspace_dim_exact_Q": len(basis),
        "projective_binary_eigenvectors": binary_sols,
        "distinct_optimal_252_sets_per_H2": len(binary_sets),
        "total_unique_optimal_sets": 120 * len(binary_sets),
        "exact_degree": 252,
    }


def mask_from_pts(pts: list[int] | set[int] | frozenset[int]) -> str:
    m = 0
    for p in pts:
        m |= 1 << p
    return f"0x{m:064x}"


def neg_mask_from_assign(asg: dict[int, int]) -> str:
    m = 0
    for p, val in asg.items():
        if val == -1:
            m |= 1 << p
    return f"0x{m:064x}"


def main() -> int:
    q7p, q7p_lines, m1, m2 = build_q7plus_solids()
    f0 = load_hoggar_q7p_signs(q7p)
    dws, line_to_idx, dw_assigns = generate_all_240_dw52(q7p, q7p_lines, f0)
    print(f"PASS  Q+(7,2) geometry: 135 pts, 1,575 lines, 135+135 solids, 240 DW(5,2) copies")

    # Case (0): Q+(7,2) \ DW(5,2) -> exact d = 0
    dw0 = dws[0]
    resid_dw0 = [ln for idx, ln in enumerate(q7p_lines) if idx not in dw0]
    if len(resid_dw0) != 1260:
        raise AssertionError("Bad DW(5,2) residual count")
    v_dw0 = sum(1 for (u, v, w, s) in resid_dw0 if f0[u] * f0[v] * f0[w] != s)
    if v_dw0 != 0:
        raise AssertionError(f"Expected 0 violations outside DW(5,2), got {v_dw0}")
    print("PASS  Case (0) Q+(7,2) \\ DW(5,2): 135 pts, 1,260 lines, exact d = 0")

    # Case (a): Q+(7,2) \ Spread on BOTH systems M1 and M2
    z_solid = frozenset(c << N for c in range(1, 16))
    spr1 = find_spread_in_system(m1, seed_idx=m1.index(z_solid))
    spr2 = find_spread_in_system(m2, seed_idx=0)
    spread_results: dict[str, Any] = {}
    opt_spread_assign: dict[int, int] | None = None
    for sname, spr in (("M1", spr1), ("M2", spr2)):
        spr_idx = {
            line_to_idx[(u, v, w)]
            for sol in spr
            for (u, v, w, _) in q7p_lines
            if u in sol and v in sol and w in sol
        }
        if len(spr_idx) != 315:
            raise AssertionError(f"Spread {sname} line count {len(spr_idx)} != 315")
        resid_spr = [ln for idx, ln in enumerate(q7p_lines) if idx not in spr_idx]
        grids, mult = count_transversal_grids(spr, resid_spr)
        mult_hist = dict(sorted(Counter(mult.values()).items()))
        if len(grids) != 5040 or mult_hist != {24: 1260}:
            raise AssertionError(f"Spread {sname} grid proof failed: {len(grids)}, {mult_hist}")
        inter_hist = dict(sorted(Counter(len(dw & spr_idx) for dw in dws).items()))
        rem_hist = {str(315 - k): v for k, v in sorted(inter_hist.items(), reverse=True)}
        if inter_hist != {45: 84, 63: 120, 105: 36}:
            raise AssertionError(f"Unexpected DW cap Spread spectrum on {sname}: {inter_hist}")
        # Verify an attaining 210-violation witness hits EVERY single grid in exactly 1 line
        opt_idx = next(i for i, dw in enumerate(dws) if len(dw & spr_idx) == 105)
        f_opt = dw_assigns[opt_idx]
        viol_set = {
            (u, v, w) for (u, v, w, s) in resid_spr if f_opt[u] * f_opt[v] * f_opt[w] != s
        }
        if len(viol_set) != 210:
            raise AssertionError(f"Expected 210 violated lines on {sname}, got {len(viol_set)}")
        grid_hit_hist = Counter(len(g6 & viol_set) for g6 in grids)
        if dict(grid_hit_hist) != {1: 5040}:
            raise AssertionError(f"Expected every grid hit once, got {grid_hit_hist}")
        if sname == "M1":
            opt_spread_assign = f_opt
            # Negative control: flipping any single observable sign cannot drop below 210
            min_flip = min(
                sum(
                    1
                    for (u, v, w, s) in resid_spr
                    if (f_opt[u] * (-1 if u == flip else 1))
                    * (f_opt[v] * (-1 if v == flip else 1))
                    * (f_opt[w] * (-1 if w == flip else 1))
                    != s
                )
                for flip in q7p
            )
            if min_flip < 210:
                raise AssertionError(f"Negative control failed: single flip gave {min_flip} < 210")
        spread_results[sname] = {
            "solids": [sorted(fmt_pauli(p) for p in sol) for sol in spr],
            "transversal_mermin_peres_grids": len(grids),
            "line_multiplicity_histogram": {str(k): v for k, v in mult_hist.items()},
            "dw52_removed_histogram": {str(k): v for k, v in inter_hist.items()},
            "dw52_residual_histogram": rem_hist,
            "exact_degree": 210,
            "all_5040_grids_hit_once_by_optimal_witness": True,
        }
        print(
            f"PASS  Case (a) Q+(7,2) \\ Spread({sname}): 5,040 transversal grids (mult 24 on 1,260 lines) "
            f"-> exact d = 210 (36 optimal DW(5,2) sets)"
        )

    # Case (a*): Triality dual Q+(7,2) \ Ovoid (126 pts, 1,260 lines) -> exact d = 252
    ov = find_ovoid_in_q7plus(q7p)
    ov_set = set(ov)
    ov_idx = {
        line_to_idx[(u, v, w)]
        for (u, v, w, _) in q7p_lines
        if u in ov_set or v in ov_set or w in ov_set
    }
    if len(ov_idx) != 315:
        raise AssertionError(f"Ovoid star lines {len(ov_idx)} != 315")
    inter_ov = dict(sorted(Counter(len(dw & ov_idx) for dw in dws).items()))
    if inter_ov != {63: 240}:
        raise AssertionError(f"Unexpected DW cap Ovoid spectrum: {inter_ov}")
    pts_no_ov = [u for u in q7p if u not in ov_set]
    lines_no_ov = build_lines(pts_no_ov)
    if len(pts_no_ov) != 126 or len(lines_no_ov) != 1260:
        raise AssertionError("Bad ovoid residual geometry")
    n_q5m, q5m_mult = count_intact_q5minus(pts_no_ov, lines_no_ov)
    if n_q5m != 280 or q5m_mult != {10: 1260}:
        raise AssertionError(f"Ovoid Q-(5,2) double-counting failed: {n_q5m}, {q5m_mult}")
    v_ov = sum(1 for (u, v, w, s) in lines_no_ov if f0[u] * f0[v] * f0[w] != s)
    if v_ov != 252:
        raise AssertionError(f"Expected 252 violated lines outside ovoid, got {v_ov}")
    print(
        "PASS  Case (a*) Q+(7,2) \\ Ovoid: 126 pts, 1,260 lines, 280 intact Q-(5,2)s (mult 10) "
        "-> exact d = 252 (all 240 DW(5,2)s)"
    )

    # Case (b): Q+(7,2) \ Q(6,2) (135 pts, 1,260 lines) -> exact d = 252 + 240-set uniqueness
    p_off = next(u for u in range(1, 256) if q0(u) == 1)
    q62_pts = {u for u in q7p if symp(u, p_off) == 0}
    q62_idx = {
        line_to_idx[(u, v, w)]
        for (u, v, w, _) in q7p_lines
        if u in q62_pts and v in q62_pts and w in q62_pts
    }
    inter_q62 = dict(sorted(Counter(len(dw & q62_idx) for dw in dws).items()))
    if inter_q62 != {63: 240}:
        raise AssertionError(f"Unexpected DW cap Q(6,2) spectrum: {inter_q62}")
    c4_info = verify_case_c4_exact_spectrum_and_uniqueness(q7p, q7p_lines, f0)
    print(
        "PASS  Case (b) Q+(7,2) \\ Q(6,2): exact integer minpoly (Lam-21)(Lam-9)(Lam+3)=0, "
        "dim_Q ker(Lam-21)=2 with 2 binary vectors -> exact d = 252 (240 unique optimal sets)"
    )

    assert opt_spread_assign is not None
    payload = {
        "status": "pass",
        "arithmetic": "exact_integer_and_rational_Q",
        "ambient": {"geometry": "Q+(7,2)", "points": 135, "lines": 1575, "dw52_copies": 240},
        "case_0_dw52_deleted": {"points": 135, "residual_lines": 1260, "exact_degree": 0},
        "case_a_spread_deleted": {
            "points": 135,
            "residual_lines": 1260,
            "exact_degree": 210,
            "systems": spread_results,
            "m1_optimal_witness_neg_mask": neg_mask_from_assign(opt_spread_assign),
            "m1_spread_solid_masks": [mask_from_pts(sol) for sol in spr1],
        },
        "case_a_dual_ovoid_deleted": {
            "points": 126,
            "residual_lines": 1260,
            "ovoid": [fmt_pauli(u) for u in ov],
            "ovoid_removed_mask": mask_from_pts(pts_no_ov),
            "intact_q5minus_count": n_q5m,
            "q5minus_line_multiplicity_histogram": {str(k): v for k, v in q5m_mult.items()},
            "spectral_floor_theorem1": 204,
            "exact_degree": 252,
            "dw52_removed_histogram": {str(k): v for k, v in inter_ov.items()},
            "optimal_witness_neg_mask": neg_mask_from_assign(f0),
        },
        "case_b_q62_deleted": {
            **c4_info,
            "dw52_removed_histogram": {str(k): v for k, v in inter_q62.items()},
            "q62_mask": mask_from_pts(q62_pts),
            "optimal_witness_neg_mask": neg_mask_from_assign(f0),
        },
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS  Wrote exact receipt -> {OUT_JSON.relative_to(REPO_ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
