"""Averaging lemmas that turn the direct third-moment bounds into better bounds on bigger configurations.

Facts checked here by brute force (bit-level symplectic code + verify/paulis.py matrices):

 (K) For every imaginary N-qubit Pauli w (P_w antisymmetric, there are 2^{N-1}(2^N-1) of them) the set
     E_w = {v != 0 : Pauli v is fixed by theta_w = P_w K}  satisfies theta_w^2 = P_w conj(P_w) = -P_w^2 = -I,
     so the Kramers form of the bound (n = D/2) applies to E_w directly.  E_w is an elliptic quadric:
     |E_w| = 2^{2N-1} - 2^{N-1} - 1 and its lines are the commuting triples inside it.
 (U) Every line of W(2N-1,2) lies in the same number c of the sets E_w.
     => d(W(2N-1,2)) >= ceil( #w * LB(Q-(2N-1,2)) / c ).
 (S) For Q+(2N+1,2) (N+1 qubits, real Paulis): for imaginary w, the section T_w = {v in Q+ : [v,w] = 0} is
     sign-isomorphic to W(2N-1,2) (explicit map checked for w = Y on the top qubit; all other w are images of that one
     under the real Clifford group, whose action on imaginary Paulis is checked to be transitive), and every line of
     Q+ lies in the same number c' of sections.
     => d(Q+(2N+1,2)) >= ceil( #w * LB(W(2N-1,2)) / c' ).
"""
import sys
import numpy as np
from math import gcd
from bounds import counts, n_eff, lower_bound
from brute_counts import popparity

OUT = []


def say(ok, msg):
    OUT.append(('PASS  ' if ok else 'FAIL  ') + msg)
    return ok


def sym(N):
    n = 4 ** N
    v = np.arange(1, n, dtype=np.uint64)
    a = v & np.uint64(2 ** N - 1); c = v >> np.uint64(N)
    return v, a, c


def line_list(N, mask):
    """all lines (u<v<w) of W(2N-1,2) restricted to points where mask is true (mask indexed by point value)."""
    v, a, c = sym(N)
    S = v[mask[1:]]
    res = []
    aS = S & np.uint64(2 ** N - 1); cS = S >> np.uint64(N)
    for i in range(len(S)):
        u = S[i]
        comm = popparity((aS[i] & cS) ^ (cS[i] & aS)) == 0
        w = S ^ u
        ok = comm & mask[w.astype(np.int64)] & (S > u) & (w > S)
        for x, y in zip(S[ok], w[ok]):
            res.append((int(u), int(x), int(y)))
    return np.array(res, dtype=np.int64)


def kramers_family(N):
    """imaginary w, the sets E_w as boolean masks over point values 0..4^N-1."""
    n = 4 ** N
    v = np.arange(n, dtype=np.uint64); a = v & np.uint64(2 ** N - 1); c = v >> np.uint64(N)
    ypar = popparity(a & c)                     # Q0(v) = #Y mod 2 : 1 <=> imaginary
    ws = [int(x) for x in v[1:] if ypar[int(x)] == 1]
    masks = []
    for w in ws:
        aw, cw = np.uint64(w & (2 ** N - 1)), np.uint64(w >> N)
        B = popparity((aw & c) ^ (cw & a))
        m = (ypar ^ B) == 0                       # theta_w P_v theta_w^-1 = (-1)^{Q0(v)+B(w,v)} P_v
        m[0] = False
        masks.append(m)
    return ws, masks


def check_K_and_U(N):
    ws, masks = kramers_family(N)
    P, L = counts(N, 'Q-'); PW, LW = counts(N, 'W')
    ok = say(len(ws) == 2 ** (N - 1) * (2 ** N - 1), 'N=%d: %d imaginary Paulis w' % (N, len(ws)))
    ok &= say(all(m.sum() == P for m in masks), 'N=%d: every E_w has %d points (elliptic quadric size)' % (N, P))
    # theta_w^2 = -I and invariance, checked with explicit matrices for N <= 4 on a few w
    if N <= 4:
        from paulis import matrix
        def lab(v):
            s = ''
            for j in range(N):
                x, z = (v >> j) & 1, (v >> (N + j)) & 1
                s += 'Y' if x and z else 'X' if x else 'Z' if z else 'I'
            return s
        for w in ws[:: max(1, len(ws) // 6)]:
            Pw = matrix(lab(w))
            ok &= say(np.allclose(Pw @ Pw.conj(), -np.eye(2 ** N)), 'N=%d w=%s: theta_w^2 = -I' % (N, lab(w)))
            mem = masks[ws.index(w)]
            good = all(np.allclose(Pw @ matrix(lab(v)).conj() @ Pw.conj().T, matrix(lab(v))) == bool(mem[v]) for v in range(1, 4 ** N))
            ok &= say(good, 'N=%d w=%s: E_w = exactly the theta_w-invariant Paulis (matrix check)' % (N, lab(w)))
    # line counts inside E_w and uniform coverage of W lines
    WL = line_list(N, np.ones(4 ** N, bool) & (np.arange(4 ** N) > 0))
    ok &= say(len(WL) == LW, 'N=%d: W(%d,2) has %d lines' % (N, 2 * N - 1, len(WL)))
    cover = np.zeros(len(WL), dtype=np.int64)
    for m in masks:
        inside = m[WL[:, 0]] & m[WL[:, 1]] & m[WL[:, 2]]
        if inside.sum() != L:
            return say(False, 'N=%d: an E_w has %d lines, expected %d' % (N, inside.sum(), L))
        cover += inside
    ok &= say(True, 'N=%d: every E_w contains exactly %d lines' % (N, L))
    ok &= say(cover.min() == cover.max(), 'N=%d: every W line lies in exactly %d of the E_w (uniform)' % (N, cover[0]))
    lbQ = lower_bound(P, L, n_eff(N, 'Q-'))
    num, den = len(ws) * lbQ, int(cover[0])
    avg = -(-num // den)
    OUT.append('INFO  N=%d: d(W(%d,2)) >= ceil(%d * %d / %d) = %d   (direct bound %d)' % (N, 2 * N - 1, len(ws), lbQ, den, avg, lower_bound(PW, LW, 2 ** N)))
    return ok, avg, len(ws), den


def check_S(N):
    """Q+(2N+1,2) on N+1 qubits, sections by imaginary w; N = 4 gives Q+(9,2) from W(7,2)."""
    from paulis import Geometry
    M = N + 1
    ok = True
    # explicit sign isomorphism for w = Y on top qubit (matrix-derived geometry)
    Gq = Geometry(M, 'Q+'); Gw = Geometry(N, 'W')
    topY = [i for i, l in enumerate(Gq.labels) if l[-1] in 'IY']   # commute with Y_top
    sec = set(topY)
    widx = {l: i for i, l in enumerate(Gw.labels)}
    phi = {i: widx[Gq.labels[i][:-1]] for i in topY if set(Gq.labels[i][:-1]) != {'I'}}
    ok &= say(len(sec) == len(phi) == Gw.n, 'Q+(%d,2): section by Y_top has %d points; map P(x)I, P(x)Y -> P is a bijection onto W(%d,2)' % (2 * M - 1, len(sec), 2 * N - 1))
    wl = {tuple(sorted(l)): s for l, s in zip(map(tuple, Gw.lines), Gw.signs)}
    mapped = 0; bad = 0
    for l, s in zip(map(tuple, Gq.lines), Gq.signs):
        if all(x in sec for x in l):
            mapped += 1
            if wl.get(tuple(sorted(phi[x] for x in l))) != s:
                bad += 1
    ok &= say(mapped == Gw.L and bad == 0, 'section lines %d map onto the %d W lines with identical signs (mismatches %d)' % (mapped, Gw.L, bad))
    # transitivity of real Clifford (H_j, CNOT_jk) on imaginary (M)-qubit Paulis, symplectic action
    def H(v, j):
        a, c = v & (2 ** M - 1), v >> M
        aj, cj = (a >> j) & 1, (c >> j) & 1
        a = (a & ~(1 << j)) | (cj << j); c = (c & ~(1 << j)) | (aj << j)
        return a | (c << M)
    def CX(v, s, t):
        a, c = v & (2 ** M - 1), v >> M
        a ^= ((a >> s) & 1) << t; c ^= ((c >> t) & 1) << s
        return a | (c << M)
    def imag(v):
        return bin((v & (2 ** M - 1)) & (v >> M)).count('1') & 1
    start = (1 << (M - 1)) | (1 << (2 * M - 1))
    seen = {start}; stack = [start]
    while stack:
        v = stack.pop()
        nb = [H(v, j) for j in range(M)] + [CX(v, s, t) for s in range(M) for t in range(M) if s != t]
        for u in nb:
            if u not in seen:
                seen.add(u); stack.append(u)
    nimag = sum(imag(v) for v in range(1, 4 ** M))
    ok &= say(len(seen) == nimag and all(imag(v) for v in seen), 'real Clifford group (H, CNOT) is transitive on the %d imaginary %d-qubit Paulis' % (nimag, M))
    # uniform coverage of Q+ lines by sections
    lines = []
    for l in Gq.lines:
        lines.append(tuple(Gq.labels[x] for x in l))
    from check_witness import label_to_index
    LV = np.array([[label_to_index(x, M) for x in t] for t in lines], dtype=np.int64)
    a = LV & (2 ** M - 1); c = LV >> M
    cover = np.zeros(len(LV), dtype=np.int64)
    ws = [v for v in range(1, 4 ** M) if imag(v)]
    for w in ws:
        aw, cw = w & (2 ** M - 1), w >> M
        comm = np.ones(len(LV), bool)
        for k in range(3):
            par = np.array([bin(x).count('1') & 1 for x in ((aw & c[:, k]) ^ (cw & a[:, k]))])
            comm &= par == 0
        cover += comm
    ok &= say(cover.min() == cover.max(), 'every Q+(%d,2) line lies in exactly %d sections T_w' % (2 * M - 1, cover[0]))
    return ok, len(ws), int(cover[0])


if __name__ == '__main__':
    allok = True
    res = {}
    for N in (3, 4, 5):
        ok, avg, nw, c = check_K_and_U(N); allok &= ok; res[N] = avg
    ok, nw, c = check_S(4); allok &= ok
    lbW7 = res[4]
    P, L = counts(5, 'Q+')
    OUT.append('INFO  d(Q+(9,2)) >= ceil(%d * %d / %d) = %d   (direct bound %d)' % (nw, lbW7, c, -(-nw * lbW7 // c), lower_bound(P, L, 32)))
    OUT.append('INFO  conditional chain: d(Q-(7,2))=315 => d(W(7,2)) >= %d ; d(W(7,2))=1575 => d(Q+(9,2)) >= %d' % (-(-120 * 315 // 24), -(-nw * 1575 // c)))
    print('\n'.join(OUT))
    sys.exit(0 if allok else 1)
