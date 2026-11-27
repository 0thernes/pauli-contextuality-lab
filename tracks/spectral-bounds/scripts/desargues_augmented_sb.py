#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Exact pure-integer verification of Metod Saniga's Nov 27, 2026 Desargues (10_3)
observation, the universal [DHOP] fiber-flip quasi-quadric family S_eps, the exact ovoid
context parabola L(S_k) = 1575 - 256k + 32k^2, and the augmented quasi-quadric S_B^+
(Theorem 25).

Uses ZERO floating-point arithmetic (pure exact integers).
"""
from __future__ import annotations

import itertools
import json
import math
import sys
from collections import Counter
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve()
REPO_ROOT = HERE.parents[3]
PIVOT_FILE = REPO_ROOT / "data" / "flat" / "n4_pivot.txt"
OUT_JSON = REPO_ROOT / "tracks" / "spectral-bounds" / "results" / "desargues_augmented_sb.json"

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


def parse_pauli(s: str) -> int:
    x = 0
    z = 0
    for i, ch in enumerate(s):
        if ch in ("X", "Y"):
            x |= 1 << i
        if ch in ("Z", "Y"):
            z |= 1 << i
    return x | (z << N)


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


def spectral_floor(num_pts: int, num_lines: int, d_dim: int = 16) -> int:
    rhs = (d_dim - 2) ** 2 * (num_pts ** 3)
    b = math.isqrt(rhs // (36 * (d_dim - 1))) + 2
    while b >= 0:
        if ((b ^ num_lines) & 1) == 0 and 36 * (d_dim - 1) * b * b <= rhs:
            return (num_lines - b) // 2
        b -= 1
    return 0


def hyperplane_profile(pts: list[int]) -> dict[str, dict[str, int]]:
    pset = set(pts)
    hp_in: Counter[int] = Counter()
    hp_out: Counter[int] = Counter()
    for w in range(1, 256):
        cnt = sum(1 for u in pts if symp(u, w) == 0)
        if w in pset:
            hp_in[cnt] += 1
        else:
            hp_out[cnt] += 1
    return {
        "in_S": {str(k): v for k, v in sorted(hp_in.items())},
        "out_S": {str(k): v for k, v in sorted(hp_out.items())},
    }


def mermin_peres_grid_bound(lines: list[tuple[int, int, int, int]]) -> tuple[int, int, int]:
    llist = sorted({tuple(sorted((u, v, w))) for (u, v, w, _) in lines})
    lset = set(llist)
    grids: set[frozenset[tuple[int, int, int]]] = set()
    for i, l1 in enumerate(llist):
        a0, a1, a2 = l1
        for l2 in llist[i + 1 :]:
            b0, b1, b2 = l2
            if b0 in l1 or b1 in l1 or b2 in l1:
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
            if l3 in lset and k0 in lset and k1 in lset and k2 in lset:
                g6 = frozenset((l1, l2, l3, k0, k1, k2))
                if len(g6) == 6:
                    grids.add(g6)
    if not grids:
        return 0, 0, 0
    lc = Counter(ln for g6 in grids for ln in g6)
    max_m = max(lc.values())
    lb = (len(grids) + max_m - 1) // max_m
    return len(grids), max_m, lb


def f2_rank(vecs: list[int]) -> int:
    pivs: list[tuple[int, int]] = []
    for v in vecs:
        r = v
        for b, p in pivs:
            if (r >> p) & 1:
                r ^= b
        if r:
            pivs.append((r, r.bit_length() - 1))
    return len(pivs)


def mask_from_pts(pts: list[int] | set[int]) -> str:
    m = 0
    for p in pts:
        m |= 1 << p
    return f"0x{m:064x}"


# Pairwise-line-disjoint Mermin-Peres grid 4-tuples (u, v, x, y) certifying sharp lower bounds:
#   K_95 >= 53, K_103 >= 87, S_B^(4) >= 112, S_B^+ >= 121.
DISJOINT_MP_PACKINGS: dict[str, list[tuple[int, int, int, int]]] = {
    "K95": [
        (1, 96, 10, 16), (1, 160, 6, 16), (1, 224, 14, 16), (4, 16, 11, 64), (4, 48, 10, 64),
        (4, 160, 8, 64), (6, 96, 10, 80), (6, 224, 8, 32), (7, 48, 97, 32), (7, 96, 11, 144),
        (7, 224, 8, 112), (8, 16, 55, 128), (8, 48, 22, 128), (8, 96, 20, 128), (10, 160, 22, 96),
        (10, 224, 20, 48), (11, 48, 65, 192), (11, 160, 55, 80), (11, 224, 52, 176), (14, 96, 20, 32),
        (14, 160, 22, 144), (15, 96, 148, 176), (15, 160, 55, 208), (16, 36, 192, 95), (26, 160, 6, 128),
        (1, 74, 32, 80), (1, 102, 64, 24), (1, 110, 128, 112), (1, 134, 192, 112), (1, 170, 206, 90),
        (1, 174, 234, 26), (4, 24, 128, 80), (4, 26, 40, 246), (4, 56, 144, 64), (4, 59, 32, 193),
        (4, 155, 170, 235), (4, 171, 186, 219), (6, 24, 144, 36), (6, 97, 120, 207), (6, 104, 129, 32),
        (6, 225, 240, 64), (7, 56, 128, 36), (7, 59, 80, 144), (8, 52, 103, 128), (8, 87, 102, 135),
        (8, 118, 80, 186), (10, 65, 176, 215), (12, 20, 230, 144), (12, 22, 192, 126), (12, 231, 246, 102),
        (14, 118, 208, 44), (15, 52, 103, 28), (20, 170, 207, 80),
    ],
    "K103": [
        (1, 224, 14, 16), (4, 16, 11, 64), (4, 48, 10, 64), (4, 160, 8, 64), (6, 224, 8, 32),
        (7, 224, 8, 112), (8, 16, 55, 128), (8, 48, 22, 128), (8, 96, 20, 128), (10, 224, 20, 48),
        (11, 224, 52, 176), (14, 96, 20, 32), (14, 160, 22, 144), (15, 48, 97, 32), (15, 96, 52, 16),
        (15, 160, 55, 176), (16, 72, 192, 159), (20, 160, 12, 192), (30, 96, 4, 144), (30, 160, 6, 128),
        (36, 132, 8, 88), (40, 72, 4, 180), (48, 72, 192, 174), (48, 132, 80, 74), (52, 148, 12, 220),
        (1, 110, 10, 190), (1, 174, 32, 88), (1, 206, 6, 126), (4, 24, 59, 64), (4, 56, 128, 64),
        (4, 155, 32, 112), (4, 171, 186, 74), (6, 104, 11, 164), (7, 56, 90, 206), (7, 104, 128, 112),
        (8, 52, 87, 128), (8, 103, 118, 183), (10, 164, 240, 63), (11, 148, 112, 88), (14, 97, 118, 230),
        (14, 102, 161, 129), (14, 164, 193, 32), (14, 180, 208, 75), (15, 87, 192, 44), (15, 164, 193, 26),
        (20, 40, 132, 104), (20, 111, 170, 55), (22, 104, 10, 80), (24, 36, 72, 222), (24, 110, 231, 234),
        (28, 40, 192, 80), (30, 65, 164, 128), (40, 207, 222, 110), (59, 159, 134, 222), (1, 96, 12, 55),
        (1, 160, 44, 90), (1, 192, 74, 125), (6, 16, 97, 60), (6, 96, 10, 65), (6, 112, 26, 45),
        (7, 48, 10, 171), (7, 80, 11, 157), (7, 96, 59, 22), (10, 16, 87, 118), (10, 160, 230, 129),
        (10, 176, 225, 45), (11, 48, 65, 183), (11, 144, 161, 189), (11, 160, 215, 26), (12, 16, 215, 74),
        (12, 32, 22, 189), (12, 48, 225, 103), (13, 112, 225, 102), (13, 144, 183, 75), (13, 176, 33, 250),
        (16, 134, 234, 7), (16, 170, 236, 215), (26, 170, 129, 220), (28, 32, 230, 237), (32, 204, 144, 150),
        (45, 80, 134, 231), (48, 204, 219, 134), (59, 155, 220, 157), (96, 134, 161, 220), (112, 150, 189, 186),
        (123, 144, 26, 246), (125, 176, 60, 240),
    ],
    "SB_4flip": [
        (4, 16, 11, 64), (4, 48, 10, 64), (4, 160, 8, 64), (8, 16, 7, 128), (8, 48, 6, 128),
        (8, 96, 20, 128), (14, 16, 1, 32), (14, 96, 20, 32), (14, 160, 22, 128), (15, 96, 52, 16),
        (15, 160, 55, 176), (16, 72, 192, 159), (16, 104, 224, 7), (19, 64, 6, 144), (19, 128, 10, 80),
        (19, 227, 33, 65), (20, 36, 10, 234), (20, 160, 12, 192), (21, 128, 44, 192), (21, 229, 34, 226),
        (24, 40, 102, 246), (25, 233, 34, 114), (30, 96, 164, 48), (34, 64, 69, 240), (34, 128, 89, 240),
        (34, 208, 1, 96), (35, 211, 65, 97), (36, 132, 8, 120), (1, 224, 98, 80), (6, 224, 99, 192),
        (26, 224, 4, 144), (1, 110, 10, 190), (1, 162, 6, 16), (1, 174, 64, 88), (1, 206, 44, 52),
        (1, 226, 102, 16), (4, 24, 59, 231), (4, 40, 128, 215), (4, 56, 155, 230), (4, 170, 32, 80),
        (4, 171, 176, 87), (6, 104, 11, 164), (6, 120, 10, 164), (6, 147, 96, 57), (6, 227, 26, 74),
        (7, 50, 10, 169), (7, 56, 90, 36), (7, 98, 11, 114), (8, 22, 32, 144), (8, 52, 80, 144),
        (8, 55, 102, 150), (8, 103, 118, 157), (10, 83, 87, 50), (10, 227, 16, 34), (11, 50, 150, 181),
        (11, 52, 231, 128), (11, 148, 161, 32), (11, 226, 48, 35), (12, 21, 22, 118), (12, 36, 55, 95),
        (12, 52, 215, 175), (12, 53, 33, 83), (12, 197, 193, 162), (12, 229, 48, 99), (14, 97, 118, 230),
        (14, 102, 193, 225), (14, 161, 180, 235), (14, 164, 208, 155), (15, 87, 97, 189), (15, 103, 161, 125),
        (15, 148, 192, 176), (15, 164, 240, 26), (19, 74, 97, 125), (19, 101, 225, 160), (19, 134, 161, 1),
        (19, 169, 229, 69), (20, 40, 111, 206), (20, 174, 235, 230), (21, 103, 101, 204), (21, 134, 160, 74),
        (21, 162, 201, 35), (21, 227, 231, 48), (22, 69, 45, 204), (22, 197, 171, 34), (25, 163, 171, 48),
        (28, 137, 75, 233), (34, 149, 201, 169), (56, 95, 206, 132), (57, 197, 219, 102), (59, 201, 7, 176),
        (1, 192, 74, 157), (6, 112, 129, 189), (7, 80, 219, 205), (10, 176, 225, 205), (12, 32, 246, 93),
        (13, 32, 118, 220), (13, 80, 225, 103), (13, 112, 231, 102), (13, 176, 33, 26), (13, 192, 87, 161),
        (28, 32, 171, 205), (45, 144, 193, 123), (59, 144, 215, 125), (80, 135, 189, 28), (112, 134, 157, 97),
        (1, 204, 128, 183), (6, 155, 240, 90), (6, 235, 97, 160), (7, 234, 96, 246), (11, 230, 55, 22),
        (33, 205, 90, 134), (93, 161, 186, 64),
    ],
    "SB_aug_143": [
        (1, 224, 14, 16), (4, 16, 11, 64), (4, 32, 10, 64), (4, 48, 25, 64), (4, 144, 8, 64),
        (4, 160, 24, 64), (4, 176, 40, 64), (6, 224, 8, 32), (7, 224, 8, 29), (8, 16, 53, 128),
        (8, 48, 22, 128), (8, 80, 20, 128), (8, 96, 36, 128), (8, 112, 52, 128), (10, 224, 19, 48),
        (11, 224, 50, 80), (12, 224, 20, 109), (14, 112, 20, 32), (14, 160, 19, 128), (14, 176, 22, 55),
        (15, 48, 50, 211), (15, 96, 52, 16), (15, 144, 55, 118), (15, 160, 87, 176), (15, 192, 103, 44),
        (16, 40, 34, 29), (16, 104, 98, 7), (16, 110, 32, 1), (16, 132, 192, 95), (16, 164, 162, 11),
        (16, 206, 226, 29), (19, 99, 33, 129), (19, 163, 6, 1), (19, 192, 74, 160), (19, 227, 97, 1),
        (20, 36, 10, 90), (20, 132, 40, 88), (20, 160, 44, 21), (20, 164, 235, 59), (21, 32, 34, 129),
        (21, 69, 12, 204), (21, 101, 103, 28), (21, 128, 109, 192), (21, 197, 40, 150), (21, 229, 77, 141),
        (24, 32, 6, 97), (24, 40, 102, 246), (24, 72, 36, 206), (24, 96, 44, 25), (25, 169, 34, 69),
        (25, 233, 36, 132), (26, 224, 4, 173), (29, 77, 36, 222), (29, 141, 69, 83), (29, 192, 137, 60),
        (30, 110, 33, 250), (30, 160, 35, 197), (32, 69, 144, 150), (32, 72, 193, 207), (32, 77, 208, 34),
        (34, 192, 201, 176), (35, 192, 22, 28), (35, 211, 65, 126), (40, 72, 12, 197), (48, 72, 147, 149),
        (48, 132, 83, 74), (53, 208, 88, 174), (55, 215, 69, 120), (57, 201, 4, 171), (57, 208, 148, 222),
        (63, 159, 87, 98), (69, 128, 60, 4), (95, 160, 8, 69), (96, 190, 137, 99), (121, 169, 164, 186),
        (1, 34, 236, 89), (1, 98, 204, 89), (4, 155, 170, 125), (6, 227, 155, 162), (7, 178, 186, 25),
        (8, 103, 118, 157), (10, 83, 87, 50), (10, 163, 183, 197), (11, 226, 118, 101), (12, 53, 33, 83),
        (12, 229, 193, 99), (19, 134, 161, 189), (21, 134, 233, 219), (22, 197, 205, 103), (24, 110, 231, 234),
        (28, 169, 129, 227), (34, 65, 197, 252), (34, 137, 193, 236), (72, 150, 180, 235), (1, 192, 74, 125),
        (6, 112, 129, 93), (7, 80, 59, 45), (10, 176, 1, 45), (11, 144, 55, 45), (12, 32, 230, 157),
        (13, 32, 6, 252), (13, 80, 1, 103), (13, 112, 87, 246), (13, 144, 33, 59), (13, 176, 150, 74),
        (13, 192, 7, 97), (22, 102, 161, 60), (26, 170, 6, 235), (28, 32, 135, 205), (32, 93, 204, 171),
        (45, 192, 74, 65), (75, 144, 28, 125), (90, 176, 33, 205), (7, 90, 208, 155), (7, 234, 128, 161),
        (10, 231, 16, 60), (13, 183, 225, 75), (13, 193, 230, 96), (26, 205, 64, 225), (45, 204, 219, 48),
        (55, 157, 208, 252),
    ],
}


def verify_disjoint_mp_packing(pts: set[int], grids: list[tuple[int, int, int, int]]) -> int:
    seen_lines: set[tuple[int, int, int]] = set()
    for u, v, x, y in grids:
        uv, xy, ux, vy = u ^ v, x ^ y, u ^ x, v ^ y
        all4 = uv ^ xy
        nine = (u, v, uv, x, y, xy, ux, vy, all4)
        if any(p not in pts for p in nine):
            raise AssertionError(f"MP grid {nine} not contained in point set")
        if symp(u, v) != 0 or symp(x, y) != 0 or symp(u, x) != 0 or symp(v, y) != 0:
            raise AssertionError(f"MP grid {(u, v, x, y)} failed commutation")
        if symp(u, y) != 1 or symp(v, x) != 1:
            raise AssertionError(f"MP grid {(u, v, x, y)} failed anticommutation")
        sgn_prod = (
            line_sign(u, v) * line_sign(x, y) * line_sign(ux, vy)
            * line_sign(u, x) * line_sign(v, y) * line_sign(uv, xy)
        )
        if sgn_prod != -1:
            raise AssertionError(f"MP grid {(u, v, x, y)} sign product was {sgn_prod}, expected -1")
        six = [
            tuple(sorted((u, v, uv))),
            tuple(sorted((x, y, xy))),
            tuple(sorted((ux, vy, all4))),
            tuple(sorted((u, x, ux))),
            tuple(sorted((v, y, vy))),
            tuple(sorted((uv, xy, all4))),
        ]
        for ln in six:
            if ln in seen_lines:
                raise AssertionError(f"Duplicate line {ln} in disjoint MP packing")
            seen_lines.add(ln)
    return len(grids)


def main() -> int:
    raw = PIVOT_FILE.read_text(encoding="utf-8").strip().splitlines()
    sb_mask = int(raw[1].strip(), 16)
    sb_neg = int(raw[2].strip(), 16)
    sb_pts = [u for u in range(1, 256) if (sb_mask >> u) & 1]
    sb_set = set(sb_pts)
    f_sb = {u: (-1 if ((sb_neg >> u) & 1) else 1) for u in sb_pts}
    q7p = [u for u in range(1, 256) if q0(u) == 0]
    q7p_set = set(q7p)

    # 1. Verify the 5-frame E and 10-point Desargues (10_3) in the X-solid
    x_solid = [a for a in range(1, 16)]
    used_x = sorted({u for u in (sb_set & q7p_set) if (u >> N) == 0})
    outliers = sorted(set(x_solid) - set(used_x))
    expected_outliers = sorted(parse_pauli(s) for s in ("XIXX", "IXII", "XIIX", "XIXI", "XXII"))
    if outliers != expected_outliers:
        raise AssertionError(f"Outlier mismatch: {[fmt_pauli(x) for x in outliers]}")
    xor_sum = 0
    for a in outliers:
        xor_sum ^= a
    if xor_sum != 0:
        raise AssertionError("Outliers do not sum to 0")
    for quad in itertools.combinations(outliers, 4):
        if f2_rank(list(quad)) != 4:
            raise AssertionError("Four outliers fail to span F_2^4")

    # Desargues (10_3): pairwise XOR of outliers == used_x; 10 lines, 3 pts/line, 3 lines/pt
    pair_xors = sorted({a ^ b for a, b in itertools.combinations(outliers, 2)})
    if pair_xors != used_x or len(used_x) != 10:
        raise AssertionError("10 X-points are not the pairwise sums of the 5-frame")
    des_lines = build_lines(used_x)
    des_deg = Counter(p for (u, v, w, _) in des_lines for p in (u, v, w))
    if len(des_lines) != 10 or set(des_deg.values()) != {3}:
        raise AssertionError(f"Desargues (10_3) check failed: {len(des_lines)} lines, deg={des_deg}")
    print("PASS  Desargues (10_3): 5-frame E = {XIXX, IXII, XIIX, XIXI, XXII} (XOR=0, all 4-subsets basis) & 10-point/10-line 3-regular complement")

    # 2. Universal [DHOP] fiber-flip theorem for ALL 2^15 sets S_eps:
    # For EVERY a in F_2^4\{0}, every u in F_2^8\{0}, the fiber F_a^{eps} = {(a, c) : a.c = eps}
    # has |F_a^0 cap u^perp| == |F_a^1 cap u^perp| (unless x(u) = a and u in F_a^{eps}?)
    # WAIT: Let's verify the EXACT identity directly for every (a, u)!
    # If x(u) = 0 (u is pure-Z): <u, (a,c)> = z(u).a independent of c -> |F_a^0 cap u^perp| = |F_a^1 cap u^perp| = 8 if z(u).a=0 else 0!
    # If x(u) != 0 and x(u) != a: as c runs over {a.c = eps}, z(u).a + c.x(u) takes 0 and 1 equally often -> BOTH fibers give 4!
    # If x(u) = a: <u, (a,c)> = z(u).a + c.a = z(u).a + eps -> 8 if eps == z(u).a (i.e. u in F_a^{eps}), else 0!
    # Therefore: for EVERY eps : F_2^4\{0} -> F_2 and EVERY u in W(7,2):
    #   |S_eps cap u^perp| = 71 if u in S_eps, and 63 if u not in S_eps!
    for a in range(1, 16):
        f0_a = [a | (c << N) for c in range(16) if (bin(a & c).count("1") & 1) == 0]
        f1_a = [a | (c << N) for c in range(16) if (bin(a & c).count("1") & 1) == 1]
        for u in range(1, 256):
            xu = u & MASK
            c0 = sum(1 for v in f0_a if symp(u, v) == 0)
            c1 = sum(1 for v in f1_a if symp(u, v) == 0)
            if xu == 0:
                exp = 8 if (bin((u >> N) & a).count("1") & 1) == 0 else 0
                if c0 != exp or c1 != exp:
                    raise AssertionError("Fiber pure-Z invariance failed")
            elif xu != a:
                if c0 != 4 or c1 != 4:
                    raise AssertionError("Fiber cross-X invariance failed")
            else:
                # xu == a: u is in f0_a iff q0(u)==0, in f1_a iff q0(u)==1
                if c0 != (8 if q0(u) == 0 else 0) or c1 != (8 if q0(u) == 1 else 0):
                    raise AssertionError("Fiber self-X invariance failed")
    print("PASS  Universal [DHOP] fiber-flip theorem: exact 71/63 hyperplane invariance proved for ALL 2^15 = 32,768 sets S_eps")

    # 3. Exact ovoid context parabola L(S_T) = 1575 - 256k + 32k^2 across all 32 subsets T <= E
    z_pts = [c << N for c in range(1, 16)]
    parabola_by_k: dict[int, set[int]] = {k: set() for k in range(6)}
    sb4_pts: list[int] = []
    for mask_e in range(32):
        flipped = {outliers[i] for i in range(5) if (mask_e >> i) & 1}
        k = len(flipped)
        pts_t = list(z_pts)
        for a in range(1, 16):
            par = 1 if a in flipped else 0
            pts_t.extend(a | (c << N) for c in range(16) if (bin(a & c).count("1") & 1) == par)
        hp_t = hyperplane_profile(pts_t)
        if hp_t != {"in_S": {"71": 135}, "out_S": {"63": 120}}:
            raise AssertionError(f"Subset mask {mask_e} failed [DHOP] 71/63 property: {hp_t}")
        l_t = len(build_lines(pts_t))
        expected_l = 1575 - 256 * k + 32 * k * k
        if l_t != expected_l:
            raise AssertionError(f"Parabola mismatch at k={k}: got {l_t}, expected {expected_l}")
        parabola_by_k[k].add(l_t)
        # Canonical k=4 subset: flip E \ {XIXX} (leaving XIXX real!)
        if flipped == set(outliers) - {parse_pauli("XIXX")}:
            sb4_pts = sorted(pts_t)

    if len(sb4_pts) != 135:
        raise AssertionError("Missing canonical S_B^(4)")
    print("PASS  Ovoid context parabola L(S_k) = 1575 - 256k + 32k^2 verified across all 32 subsets T <= E (unique min 1,063 at k=4)")

    # 4. Exact algebraic decoupling of red_8(XIXX) from S_B \ Q+(7,2), tangent hyperplane IZZZ^perp,
    #    exact +52 extension spectrum, and augmented quasi-quadric S_B^+ (143 pts, 1,219 lines)
    xixx = parse_pauli("XIXX")
    izzz = parse_pauli("IZZZ")
    red_8 = sorted(u for u in q7p if (u & MASK) == xixx)
    if len(red_8) != 8:
        raise AssertionError("Expected 8 real points in XIXX fiber")
    fano_izzz = sorted(c << N for c in range(1, 16) if symp(c << N, xixx) == 0)
    solid_xixx = sorted(set(fano_izzz) | set(red_8))
    if len(fano_izzz) != 7 or len(solid_xixx) != 15:
        raise AssertionError("Bad Fano/solid size")
    if not all(symp(a, b) == 0 for a in solid_xixx for b in solid_xixx):
        raise AssertionError("Fano_IZZZ U red_8(XIXX) is not totally isotropic")

    k95_pts = sorted(sb_set & q7p_set)
    k103_pts = sorted(set(k95_pts) | set(red_8))
    sb_aug_pts = sorted(sb_set | set(red_8))
    if len(k95_pts) != 95 or len(k103_pts) != 103 or len(sb_aug_pts) != 143:
        raise AssertionError("Bad point counts for K95/K103/SB+")

    hp_izzz = {u for u in q7p if symp(u, izzz) == 0}
    if len(hp_izzz) != 71 or not hp_izzz.issubset(set(k103_pts)):
        raise AssertionError("K103 does not contain all 71 points of Q+(7,2) cap IZZZ^perp")
    if len(hp_izzz & set(k95_pts)) != 63:
        raise AssertionError("Expected 63/71 of IZZZ^perp in K95")

    k95_lines = build_lines(k95_pts)
    k103_lines = build_lines(k103_pts)
    sb4_lines = build_lines(sb4_pts)
    sb_aug_lines = build_lines(sb_aug_pts)
    if (len(k95_lines), len(k103_lines), len(sb4_lines), len(sb_aug_lines)) != (635, 759, 1063, 1219):
        raise AssertionError("Unexpected context counts")

    red_set = set(red_8)
    new_103 = {ln for ln in k103_lines if any(p in red_set for p in ln[:3])}
    new_143 = {ln for ln in sb_aug_lines if any(p in red_set for p in ln[:3])}
    if len(new_103) != 124 or new_103 != new_143:
        raise AssertionError("red_8(XIXX) failed decoupling from S_B \\ Q+(7,2)")
    solid_set = set(solid_xixx)
    new_in_solid = sum(1 for ln in new_143 if all(p in solid_set for p in ln[:3]))
    if new_in_solid != 28:
        raise AssertionError(f"Expected 28 solid new lines, got {new_in_solid}")

    # Exhaustive check over all 2^8 = 256 extensions of f_sb onto red_8(XIXX)
    v_k95 = sum(1 for (u, v, w, s) in k95_lines if f_sb[u] * f_sb[v] * f_sb[w] != s)
    if v_k95 != 55:
        raise AssertionError(f"Expected f_sb|_K95 = 55 violations, got {v_k95}")
    ext_hist: Counter[int] = Counter()
    best_bits = -1
    best_add = 10**9
    for bits in range(256):
        ext = dict(f_sb)
        for i, p in enumerate(red_8):
            ext[p] = -1 if ((bits >> i) & 1) else 1
        add_v = sum(1 for (u, v, w, s) in new_143 if ext[u] * ext[v] * ext[w] != s)
        ext_hist[add_v] += 1
        if add_v < best_add:
            best_add = add_v
            best_bits = bits
    if best_add != 52:
        raise AssertionError(f"Expected min added violations = 52, got {best_add}")
    if dict(sorted(ext_hist.items())) != {52: 2, 57: 16, 60: 64, 61: 64, 64: 56, 65: 48, 68: 6}:
        raise AssertionError(f"Unexpected 256-extension histogram: {ext_hist}")

    # Verify witness upper bounds: K95 <= 55, K103 <= 107, S_B^+ <= 127
    f_ext = dict(f_sb)
    for i, p in enumerate(red_8):
        f_ext[p] = -1 if ((best_bits >> i) & 1) else 1
    v_k103 = sum(1 for (u, v, w, s) in k103_lines if f_ext[u] * f_ext[v] * f_ext[w] != s)
    v_s143 = sum(1 for (u, v, w, s) in sb_aug_lines if f_ext[u] * f_ext[v] * f_ext[w] != s)
    v_sb4 = sum(1 for (u, v, w, s) in sb4_lines if f_ext[u] * f_ext[v] * f_ext[w] != s)
    if (v_k103, v_s143) != (107, 127):
        raise AssertionError(f"Unexpected extended witness counts: K103={v_k103}, S_B+={v_s143}")

    # Hyperplane profile of S_B^+ (143 pts): HP_in = {71:24, 75:112, 79:7}, HP_out = {67:112}!
    hp_143 = hyperplane_profile(sb_aug_pts)
    if hp_143 != {"in_S": {"71": 24, "75": 112, "79": 7}, "out_S": {"67": 112}}:
        raise AssertionError(f"Unexpected S_B^+ hyperplane profile: {hp_143}")
    if math.isqrt(15 * 143) ** 2 == 15 * 143:
        raise AssertionError("15 * 143 must not be a square")

    # Mermin-Peres grid lower bounds (both averaged & sharper pairwise-line-disjoint packings!)
    g_k95, m_k95, lb_k95 = mermin_peres_grid_bound(k95_lines)
    g_k103, m_k103, lb_k103 = mermin_peres_grid_bound(k103_lines)
    g_sb4, m_sb4, lb_sb4 = mermin_peres_grid_bound(sb4_lines)
    g_143, m_143, lb_143 = mermin_peres_grid_bound(sb_aug_lines)
    dlb_k95 = verify_disjoint_mp_packing(set(k95_pts), DISJOINT_MP_PACKINGS["K95"])
    dlb_k103 = verify_disjoint_mp_packing(set(k103_pts), DISJOINT_MP_PACKINGS["K103"])
    dlb_sb4 = verify_disjoint_mp_packing(set(sb4_pts), DISJOINT_MP_PACKINGS["SB_4flip"])
    dlb_143 = verify_disjoint_mp_packing(set(sb_aug_pts), DISJOINT_MP_PACKINGS["SB_aug_143"])
    fl_k95 = spectral_floor(95, 635)
    fl_k103 = spectral_floor(103, 759)
    fl_sb4 = spectral_floor(135, 1063)
    fl_143 = spectral_floor(143, 1219)
    if (fl_k95, fl_k103, fl_sb4, fl_143) != (39, 65, 59, 95):
        raise AssertionError(f"Floor mismatch: {(fl_k95, fl_k103, fl_sb4, fl_143)}")
    if lb_k95 != 40 or lb_sb4 != 69:
        raise AssertionError(f"Grid LB mismatch: K95={lb_k95}, SB4={lb_sb4}")
    if (dlb_k95, dlb_k103, dlb_sb4, dlb_143) != (53, 87, 112, 121):
        raise AssertionError(f"Disjoint MP packing mismatch: {(dlb_k95, dlb_k103, dlb_sb4, dlb_143)}")

    print(
        f"PASS  Decoupling & S_B^+: red_8(XIXX) adds 124 = 28 + 96 contexts (0 to S_B\\Q+), "
        f"71/71 of IZZZ^perp in K103, exact min ext = +52, HP_out(S_B^+) = {{67: 112}}, 15*143=2145 != sq"
    )
    print(
        f"PASS  Exact disjoint-grid brackets: K95 in [{dlb_k95}, 55] (floor 39, gap 2); "
        f"K103 in [{dlb_k103}, 107] (floor 65); "
        f"S_B^(4) in [{dlb_sb4}, {v_sb4}] (floor 59, breaks saturation by +{dlb_sb4 - fl_sb4}!); "
        f"S_B^+ in [{dlb_143}, 127] (floor 95, gap 6)"
    )

    # Negative control: flipping a non-ovoid 3-collinear triple (a, b, a^b) gives DIFFERENT context count than parabola!
    col_triple = [used_x[0], used_x[1], used_x[0] ^ used_x[1]]
    pts_col = list(z_pts)
    for a in range(1, 16):
        par = 1 if a in col_triple else 0
        pts_col.extend(a | (c << N) for c in range(16) if (bin(a & c).count("1") & 1) == par)
    l_col = len(build_lines(pts_col))
    if l_col == 1575 - 256 * 3 + 32 * 9:
        raise AssertionError("Negative control failed: collinear triple matched ovoid parabola")
    print(f"PASS  Negative control: collinear 3-flip has L = {l_col} != 1,095 (ovoid k=3 parabola value)")

    payload = {
        "status": "pass",
        "arithmetic": "exact_integer",
        "desargues_10_3": {
            "outliers_5_frame": [fmt_pauli(x) for x in outliers],
            "desargues_10_points": [fmt_pauli(x) for x in used_x],
            "desargues_lines": 10,
            "regular_degree": 3,
        },
        "universal_dhop_fiber_flip": {
            "total_family_size": 32768,
            "hyperplane_in_S": 71,
            "hyperplane_out_S": 63,
            "regular_ambient_degree": 70,
        },
        "ovoid_context_parabola": {
            "formula": "1575 - 256*k + 32*k^2",
            "values_by_k": {str(k): next(iter(v)) for k, v in parabola_by_k.items()},
            "unique_minimum_k": 4,
            "unique_minimum_contexts": 1063,
            "negative_control_collinear_k3_contexts": l_col,
        },
        "augmented_sb_variants": {
            "pole": "IZZZ",
            "red_8_XIXX": [fmt_pauli(u) for u in red_8],
            "fano_IZZZ": [fmt_pauli(u) for u in fano_izzz],
            "new_contexts_total": 124,
            "new_contexts_solid": 28,
            "new_contexts_cross": 96,
            "contexts_linking_red8_to_SB_minus_Q7p": 0,
            "tangent_hyperplane_IZZZ_in_K103": "71/71",
            "extension_256_histogram": {str(k): v for k, v in sorted(ext_hist.items())},
            "K95": {"pts": 95, "lines": 635, "floor": fl_k95, "grids": g_k95, "grid_max_mult": m_k95, "avg_grid_lb": lb_k95, "disjoint_grid_lb": dlb_k95, "witness_ub": 55, "mask": mask_from_pts(k95_pts)},
            "K103": {"pts": 103, "lines": 759, "floor": fl_k103, "grids": g_k103, "grid_max_mult": m_k103, "avg_grid_lb": lb_k103, "disjoint_grid_lb": dlb_k103, "witness_ub": 107, "mask": mask_from_pts(k103_pts)},
            "SB_4flip": {"pts": 135, "lines": 1063, "floor": fl_sb4, "grids": g_sb4, "grid_max_mult": m_sb4, "avg_grid_lb": lb_sb4, "disjoint_grid_lb": dlb_sb4, "witness_ub_ext": v_sb4, "breaks_floor_saturation": dlb_sb4 > fl_sb4, "mask": mask_from_pts(sb4_pts)},
            "SB_aug_143": {"pts": 143, "lines": 1219, "floor": fl_143, "grids": g_143, "grid_max_mult": m_143, "avg_grid_lb": lb_143, "disjoint_grid_lb": dlb_143, "witness_ub": 127, "hyperplane_profile": hp_143, "fifteen_times_card": 2145, "is_square": False, "mask": mask_from_pts(sb_aug_pts)},
        },
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS  Wrote exact receipt -> {OUT_JSON.relative_to(REPO_ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
