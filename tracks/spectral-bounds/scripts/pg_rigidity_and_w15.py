#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Exact symbolic (SymPy) & pure-integer verification of the all-N PG(N-1,2) rigidity
and imaginary-completion no-go theorem on W(2N-1,2), plus exact verification of 8-qubit
W(15,2) and Q+(15,2) witnesses (Theorem 24, motivated by Metod Saniga's 26 Nov 2026 email).

Uses ZERO floating-point arithmetic (pure exact SymPy algebra and exact Python integers).
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

import sympy as sp

HERE = Path(__file__).resolve()
REPO_ROOT = HERE.parents[3]
WITNESS_DIR = REPO_ROOT / "data" / "witness"
OUT_JSON = REPO_ROOT / "tracks" / "spectral-bounds" / "results" / "pg_rigidity_and_w15.json"


def symp_n(u: int, v: int, n: int) -> int:
    m = (1 << n) - 1
    return (bin((u & m) & (v >> n)).count("1") ^ bin((u >> n) & (v & m)).count("1")) & 1


def y_count_n(u: int, n: int) -> int:
    m = (1 << n) - 1
    return bin((u & m) & (u >> n)).count("1")


def line_sign_n(u: int, v: int, n: int) -> int:
    m = (1 << n) - 1
    ux, uz, vx, vz = u & m, u >> n, v & m, v >> n
    ph = (
        bin(ux & uz).count("1")
        + bin(vx & vz).count("1")
        - bin((ux ^ vx) & (uz ^ vz)).count("1")
        + 2 * bin(uz & vx).count("1")
    ) % 4
    if ph not in (0, 2):
        raise ValueError("Non-commuting pair")
    return 1 if ph == 0 else -1


def spectral_floor_exact(npts: int, nlines: int, d_dim: int) -> int:
    rhs = (d_dim - 2) ** 2 * (npts ** 3)
    b = math.isqrt(rhs // (36 * (d_dim - 1))) + 2
    while b >= 0:
        if ((b ^ nlines) & 1) == 0 and 36 * (d_dim - 1) * b * b <= rhs:
            return (nlines - b) // 2
        b -= 1
    return 0


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


def verify_symbolic_pg_rigidity() -> dict[str, Any]:
    s_d = sp.Symbol("sD", positive=True)
    d_sym = s_d ** 2
    c = 1 / s_d
    s = sp.sqrt(1 - 1 / d_sym)
    u = sp.Matrix([1, 0])
    v = sp.Matrix([c, s])
    # A_real = -3 I + M2 on span{|0>, |+>} and -3 I on its (D-2)-dimensional orthogonal complement
    m2 = 2 * d_sym * (u * u.T + v * v.T) - (d_sym * s_d / 2) * (u * v.T + v * u.T)
    tr_m = sp.simplify(m2.trace())
    det_m = sp.simplify(m2.det())
    disc_m = sp.factor(tr_m ** 2 - 4 * det_m)
    if tr_m != 3 * d_sym:
        raise AssertionError(f"Expected tr(M2) = 3D, got {tr_m}")

    g_plus = sp.simplify((3 * d_sym + s_d * (d_sym - 4)) / 2 - 3)
    g_minus = sp.simplify((3 * d_sym - s_d * (d_sym - 4)) / 2 - 3)
    # Check both are exact roots of lambda^2 - tr_m * lambda + det_m = 0 after shifting by +3
    for root in (g_plus + 3, g_minus + 3):
        if sp.simplify(root ** 2 - tr_m * root + det_m) != 0:
            raise AssertionError(f"Root verification failed for {root}")

    tr_a3 = sp.expand(g_plus ** 3 + g_minus ** 3 + (d_sym - 2) * (-3) ** 3)
    beta_q = sp.simplify(tr_a3 / (6 * d_sym))
    l_q = sp.simplify((d_sym - 1) * (d_sym + 2) * (d_sym - 2) * (d_sym + 4) / 48)
    viol_q = sp.factor(sp.simplify((l_q - beta_q) / 2))
    expected_viol_q = sp.factor((d_sym - 1) * (d_sym - 2) * (d_sym ** 2 - 12 * d_sym + 80) / 96)
    if sp.simplify(viol_q - expected_viol_q) != 0:
        raise AssertionError(f"viol(Q+) mismatch: {viol_q} != {expected_viol_q}")

    lam_max_ge4 = sp.simplify((g_plus + (-3)) / 2)
    expected_lam = sp.simplify((d_sym - 4) * (s_d + 3) / 4)
    if sp.simplify(lam_max_ge4 - expected_lam) != 0:
        raise AssertionError(f"lam_max mismatch: {lam_max_ge4} != {expected_lam}")

    expected_totals = {3: 63, 4: 1575, 5: 31081, 6: 571095, 7: 9907702, 8: 166115415}
    rows: list[dict[str, Any]] = []
    for n in range(3, 9):
        dv = 1 << n
        sdv = sp.sqrt(dv)
        gp = sp.simplify(g_plus.subs(s_d, sdv))
        gm = sp.simplify(g_minus.subs(s_d, sdv))
        vq = int(sp.simplify(viol_q.subs(s_d, sdv)))
        l_w = (dv * dv - 1) * (dv * dv - 4) // 12
        l_qv = (dv - 1) * (dv + 2) * (dv - 2) * (dv + 4) // 48
        l_out = l_w - l_qv
        n_imag = dv * (dv - 1) // 2
        second = gm if sp.simplify(gm - (-3)) > 0 else sp.Integer(-3)
        lam_m = sp.simplify((gp + second) / 2)
        lb_out_exact = sp.simplify(sp.Rational(l_out, 2) - sp.Rational(n_imag, 4) * lam_m)
        lb_out = int(sp.ceiling(lb_out_exact))
        lb_tot = vq + lb_out
        if lb_tot != expected_totals[n]:
            raise AssertionError(f"N={n}: expected {expected_totals[n]}, got {lb_tot}")
        rows.append(
            {
                "N": n,
                "D": dv,
                "L_W": l_w,
                "L_Qplus": l_qv,
                "viol_Qplus_forced": vq,
                "lam_max_Lambda_real": str(lam_m),
                "lb_outside": lb_out,
                "lb_total_PG_centered": lb_tot,
                "spectral_floor_W": spectral_floor_exact(dv * dv - 1, l_w, dv),
            }
        )
    print(
        "PASS  SymPy exact PG(N-1,2) rigidity theorem: N=3..8 bounds = "
        "[63, 1575, 31081, 571095, 9907702, 166115415]"
    )
    return {
        "tr_M2": str(tr_m),
        "disc_M2": str(disc_m),
        "gamma_plus": str(g_plus),
        "gamma_minus": str(g_minus),
        "viol_Qplus_formula": str(expected_viol_q),
        "lam_max_formula_N_ge_4": str(expected_lam),
        "table_N3_to_N8": rows,
    }


def verify_literal_integer_matrices_n3_n4() -> dict[str, Any]:
    """Verify A_real and Lambda_real literally over Z (zero float!) at N = 3 and N = 4."""
    out: dict[str, Any] = {}
    for n in (3, 4):
        dv = 1 << n
        mask = dv - 1
        reals = [u for u in range(1, 1 << (2 * n)) if (y_count_n(u, n) & 1) == 0]
        imags = [u for u in range(1, 1 << (2 * n)) if (y_count_n(u, n) & 1) == 1]

        # Build exact integer A_real directly from Pauli basis entries
        f_r: dict[int, int] = {}
        for u in reals:
            a, c = u & mask, u >> n
            k = bin(a & c).count("1")
            if a == 0 or c == 0:
                f_r[u] = 1
            else:
                f_r[u] = -1 if ((k // 2) & 1) == 0 else 1

        a_mat = [[0] * dv for _ in range(dv)]
        for u in reals:
            a, c = u & mask, u >> n
            k = bin(a & c).count("1")
            sgn_p = -1 if ((k // 2) & 1) else 1
            coef = f_r[u] * sgn_p
            for b in range(dv):
                r = b ^ a
                a_mat[r][b] += coef * (-1 if (bin(c & b).count("1") & 1) else 1)

        # Build exact integer Lambda_real on imags
        ni = len(imags)
        lam = [[0] * ni for _ in range(ni)]
        for i, u in enumerate(imags):
            for j in range(i + 1, ni):
                v = imags[j]
                if symp_n(u, v, n) == 0:
                    w = u ^ v
                    s = line_sign_n(u, v, n)
                    val = s * f_r[w]
                    lam[i][j] = val
                    lam[j][i] = val

        # Check exact polynomial identity!
        # At N=3: A_real has eigs 9 +- 4 sqrt(2) and (-3)^6 -> (A + 3 I)(A^2 - 18 A + 49 I) = 0!
        # And Lambda_real has eigs (g+ + g-)/2 = 9 (x1), (g+ - 3)/2 = 3 + 2 sqrt(2) (x6),
        # (g- - 3)/2 = 3 - 2 sqrt(2) (x6), -3 (x15) -> (L - 9 I)(L + 3 I)(L^2 - 6 L + I) = 0!
        # At N=4: A_real has eigs 45 (x1), -3 (x15) -> (A - 45 I)(A + 3 I) = 0!
        # And Lambda_real has eigs 21 (x15), -3 (x105) -> (L - 21 I)(L + 3 I) = 0!
        a2 = mat_mul_int(a_mat, a_mat)
        l2 = mat_mul_int(lam, lam)
        if n == 3:
            # Check (A + 3 I)(A^2 - 18 A + 49 I) == 0
            p1 = [[a_mat[i][j] + (3 if i == j else 0) for j in range(dv)] for i in range(dv)]
            p2 = [[a2[i][j] - 18 * a_mat[i][j] + (49 if i == j else 0) for j in range(dv)] for i in range(dv)]
            if any(x != 0 for row in mat_mul_int(p1, p2) for x in row):
                raise AssertionError("N=3 A_real minimal polynomial failed")
            # Check (L - 9 I)(L + 3 I)(L^2 - 6 L + I) == 0
            q1 = [[lam[i][j] - (9 if i == j else 0) for j in range(ni)] for i in range(ni)]
            q2 = [[lam[i][j] + (3 if i == j else 0) for j in range(ni)] for i in range(ni)]
            q3 = [[l2[i][j] - 6 * lam[i][j] + (1 if i == j else 0) for j in range(ni)] for i in range(ni)]
            if any(x != 0 for row in mat_mul_int(mat_mul_int(q1, q2), q3) for x in row):
                raise AssertionError("N=3 Lambda_real minimal polynomial failed")
            tr_l2 = sum(l2[i][i] for i in range(ni))
            if tr_l2 != 420:  # 1*81 + 6*(17+12s2) + 6*(17-12s2) + 15*9 = 81 + 204 + 135 = 420
                raise AssertionError(f"N=3 tr(Lam^2)={tr_l2} != 420")
            out["N3"] = {"dim_A": 8, "dim_Lambda": 28, "tr_Lambda_sq": tr_l2, "exact_minpoly_verified": True}
        else:
            p1 = [[a_mat[i][j] - (45 if i == j else 0) for j in range(dv)] for i in range(dv)]
            p2 = [[a_mat[i][j] + (3 if i == j else 0) for j in range(dv)] for i in range(dv)]
            if any(x != 0 for row in mat_mul_int(p1, p2) for x in row):
                raise AssertionError("N=4 A_real minimal polynomial failed")
            q1 = [[lam[i][j] - (21 if i == j else 0) for j in range(ni)] for i in range(ni)]
            q2 = [[lam[i][j] + (3 if i == j else 0) for j in range(ni)] for i in range(ni)]
            if any(x != 0 for row in mat_mul_int(q1, q2) for x in row):
                raise AssertionError("N=4 Lambda_real minimal polynomial failed")
            tr_l2 = sum(l2[i][i] for i in range(ni))
            if tr_l2 != 7560:  # 15*441 + 105*9 = 6615 + 945 = 7560
                raise AssertionError(f"N=4 tr(Lam^2)={tr_l2} != 7560")
            out["N4"] = {"dim_A": 16, "dim_Lambda": 120, "tr_Lambda_sq": tr_l2, "exact_minpoly_verified": True}
    print("PASS  Literal integer minimal polynomials of A_real & Lambda_real verified at N=3 (8x8 / 28x28) and N=4 (16x16 / 120x120)")
    return out


def fwht_int(vec: list[int]) -> None:
    n = len(vec)
    step = 1
    while step < n:
        twice = step << 1
        for i in range(0, n, twice):
            for j in range(i, i + step):
                a = vec[j]
                b = vec[j + step]
                vec[j] = a + b
                vec[j + step] = a - b
        step = twice


def verify_witness_exact_int(path: Path) -> dict[str, Any]:
    """Pure Python exact arbitrary-precision integer verification of a witness file."""
    lines = path.read_text(encoding="utf-8").strip().splitlines()
    n_str, kind, claim_str = lines[0].split()
    n = int(n_str)
    claim = int(claim_str)
    hex_str = lines[1].strip().lower()
    d = 1 << n
    nall = 1 << (2 * n)
    if len(hex_str) != nall // 4:
        raise AssertionError(f"{path.name}: bad hex length {len(hex_str)} != {nall // 4}")
    mask_int = int(hex_str, 16)
    real_only = kind == "h"

    pop = [bin(i).count("1") for i in range(d)]
    gr = [[0] * d for _ in range(d)]
    gi = [[0] * d for _ in range(d)]
    f_tab = [[0] * d for _ in range(d)]
    npts = 0
    for a in range(d):
        gra = gr[a]
        gia = gi[a]
        fa = f_tab[a]
        for c in range(d):
            if a == 0 and c == 0:
                continue
            k = pop[a & c] & 3
            if real_only and (k & 1):
                continue
            v = a | (c << n)
            sv = -1 if ((mask_int >> v) & 1) else 1
            fa[c] = sv
            npts += 1
            if k == 0:
                gra[c] = sv
            elif k == 1:
                gia[c] = sv
            elif k == 2:
                gra[c] = -sv
            else:
                gia[c] = -sv

    ar = [[0] * d for _ in range(d)]
    ai = [[0] * d for _ in range(d)]
    for a in range(d):
        fwht_int(gr[a])
        fwht_int(gi[a])
        gra = gr[a]
        gia = gi[a]
        for b in range(d):
            r = b ^ a
            ar[r][b] = gra[b]
            ai[r][b] = gia[b]

    # Exact Hermiticity
    for r in range(d):
        for b in range(r, d):
            if ar[r][b] != ar[b][r] or ai[r][b] != -ai[b][r]:
                raise AssertionError(f"{path.name}: A is not Hermitian")

    # Exact Hermitian B = A^2 and tr(A^3)
    tr_a3 = 0
    br = [[0] * d for _ in range(d)]
    bi = [[0] * d for _ in range(d)]
    for i in range(d):
        ari = ar[i]
        aii = ai[i]
        for j in range(i, d):
            arj = ar[j]
            aij = ai[j]
            sr = 0
            si = 0
            for k in range(d):
                sr += ari[k] * arj[k] + aii[k] * aij[k]
                si += aii[k] * arj[k] - ari[k] * aij[k]
            br[i][j] = sr
            bi[i][j] = si
            if i == j:
                tr_a3 += sr * ari[j] + si * aii[j]
            else:
                br[j][i] = sr
                bi[j][i] = -si
                tr_a3 += 2 * (sr * ari[j] + si * aii[j])

    if tr_a3 % (6 * d) != 0:
        raise AssertionError(f"{path.name}: tr(A^3) not divisible by 6*D")
    beta = tr_a3 // (6 * d)
    l_tot = (
        ((d - 1) * (d + 2) * (d - 2) * (d + 4)) // 48
        if real_only
        else ((d * d - 1) * (d * d - 4)) // 12
    )
    if (l_tot - beta) % 2 != 0:
        raise AssertionError(f"{path.name}: parity mismatch")
    viol = (l_tot - beta) // 2
    if viol != claim:
        raise AssertionError(f"{path.name}: claimed {claim} != exact {viol}")

    # Verify exact per-point excess sum == 3 * beta
    sum_exc = 0
    neg_exc = 0
    for a in range(d):
        hr = [br[b][b ^ a] for b in range(d)]
        hi = [bi[b][b ^ a] for b in range(d)]
        fwht_int(hr)
        fwht_int(hi)
        fa = f_tab[a]
        for c in range(d):
            sv = fa[c]
            if sv == 0:
                continue
            k = pop[a & c] & 3
            if k == 0:
                tr_mp = hr[c]
            elif k == 1:
                tr_mp = -hi[c]
            elif k == 2:
                tr_mp = -hr[c]
            else:
                tr_mp = hi[c]
            if tr_mp % (2 * d) != 0:
                raise AssertionError(f"{path.name}: tr(A^2 P_v) not divisible by 2*D")
            exc = sv * (tr_mp // (2 * d))
            sum_exc += exc
            if exc < 0:
                neg_exc += 1
    if sum_exc != 3 * beta:
        raise AssertionError(f"{path.name}: sum(exc)={sum_exc} != 3*beta={3 * beta}")

    return {
        "file": path.relative_to(REPO_ROOT).as_posix(),
        "N": n,
        "kind": kind,
        "points": npts,
        "contexts": l_tot,
        "exact_violated": viol,
        "beta": beta,
        "neg_excess_points": neg_exc,
        "spectral_floor": spectral_floor_exact(npts, l_tot, d),
    }


def main() -> int:
    sym_info = verify_symbolic_pg_rigidity()
    lit_info = verify_literal_integer_matrices_n3_n4()

    # Exact pure-Python integer verification of the 8-qubit W(15,2) and Q+(15,2) witnesses
    witnesses: list[dict[str, Any]] = []
    for fname in ("n8_f_pg_css.txt", "n8_f_l4_opt.txt", "n8_h_l4_opt.txt"):
        p = WITNESS_DIR / fname
        if not p.is_file():
            raise FileNotFoundError(f"Missing witness file: {p}")
        info = verify_witness_exact_int(p)
        witnesses.append(info)
        print(
            f"PASS  Exact-int witness {fname}: N={info['N']} kind={info['kind']} "
            f"viol={info['exact_violated']:,} / {info['contexts']:,} (floor={info['spectral_floor']:,}, negE={info['neg_excess_points']})"
        )

    # Key separation check: W(15,2) L4-opt witness STRICTLY beats the PG(7,2)-centered lower bound 166,115,415!
    w15_opt = next(w for w in witnesses if w["file"].endswith("n8_f_l4_opt.txt"))
    pg_lb_8 = 166115415
    if not (w15_opt["exact_violated"] < pg_lb_8 and w15_opt["neg_excess_points"] == 0):
        raise AssertionError("W(15,2) witness failed strict separation below PG(7,2) lower bound")
    print(
        f"PASS  Strict W(15,2) separation: {w15_opt['exact_violated']:,} < {pg_lb_8:,} "
        f"(margin = {pg_lb_8 - w15_opt['exact_violated']:,} contexts, negE = 0)"
    )

    payload = {
        "status": "pass",
        "arithmetic": "exact_integer_and_symbolic_sympy",
        "symbolic_pg_rigidity": sym_info,
        "literal_integer_matrices": lit_info,
        "n8_exact_witnesses": witnesses,
        "w15_strict_separation_below_pg72_lb": {
            "pg72_centered_lower_bound": pg_lb_8,
            "verified_w15_witness": w15_opt["exact_violated"],
            "strict_margin": pg_lb_8 - w15_opt["exact_violated"],
        },
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS  Wrote exact receipt -> {OUT_JSON.relative_to(REPO_ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
