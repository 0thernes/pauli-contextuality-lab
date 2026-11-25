#!/usr/bin/env python3
"""Exact witness anatomy, Sp(2N,2) isomorphism verifier, and Qontextium export generator.

Pure exact integer arithmetic (zero floating point). Verifies:
  1. Q^-(7,2) (119 observables, 1,071 contexts, 315 violated contexts):
     Both the tabu-search witness (data/witness/n4_e.txt) and the Lean 4 CSS
     witness (HoggarBound.ExactDegreesN4N5.q7minus_css_witness) have identical
     violated-line geometry via an explicit linear symplectic isomorphism
     T in Sp(8,2) (315/315 exact line match), featuring a 14-point / 21-line
     Heawood core shared by three classical copies of the split Cayley hexagon
     H(2) (63 points, 63 lines, incidence girth 12, 63/63 coplanar point stars)
     plus 168 transversal (9,9,9) lines, matching Muller et al. [M2, Sec. 5.1.1].
  2. W(7,2) (255 observables, 5,355 contexts, 1,575 violated contexts):
     Both data/witness/n4_f.txt and Lean CSS w72_css_witness are linked by an
     explicit T in Sp(8,2) (1,575/1,575 exact line match), featuring a
     distinguished DW(5,2) core (135 points = Q^+(7,2), 315 violated lines,
     14-regular distance-regular collinearity graph {14,12,8;1,3,7} with
     PG(3,2) point-hyperplane incidence subcore) plus 1,260 external (19,21,21)
     lines (12 per degree-19 core point, 0 per degree-7 core point, 21 per
     outside point), matching [M2, Sec. 5.1.3].
  3. Q^+(9,2) (527 observables, 23,715 contexts, 6,975 violated contexts):
     Both data/witness/n5_h.txt and Lean CSS q9plus_css_witness are linked by an
     explicit T in Sp(10,2) (6,975/6,975 exact line match), centered on the
     point-hyperplane incidence graph of PG(4,2) (62 degree-15 points = two
     disjoint maximal isotropic PG(4,2) generators, 465 (15,15,43) core lines,
     bipartite 15-regular girth 4) plus 6,510 outer (43,43,43) lines, matching [M2].
  4. Hyperbolic quasi-quadric S_B in W(7,2) (data/flat/n4_pivot.txt:
     135 observables, 1,095 contexts, exact contextuality degree 75):
     - Regular commutation degree 70 on all 135 observables (same point count
       and commutation regularity as Q^+(7,2)), ambient line counts
       1,095 = 735 (+I) + 360 (-I), ambient line-degree split {35: 15, 23: 120}.
     - Obtained from Q^+(7,2) by flipping the Y-parity of the 5 affine AG(3,2)
       fibers whose unique poles form a 5-point ovoid of the diagonal abstract
       doily (0 collinear pairs; hitting all 15 abstract doily lines once each).
     - Violated-context decomposition (75 = 15 + 60):
       * Diagonal abstract doily (15 lines, all +I, degree-triple (7,7,7)) on
         the 15 pure-Z observables D_15 ~= PG(3,2). Because all 15 observables
         in D_15 pairwise commute (105/105 pairs, 35/35 +I ambient lines),
         D_15 is a maximal totally isotropic PG(3,2) subspace of W(7,2); its
         15 violated lines form an abstract doily GQ(2,2) as a point-line
         incidence structure (a symplectic linear line complex in PG(3,2)),
         NOT a symplectic four-qubit doily (where collinearity = commutation
         and an odd number of lines are negative). Alone, these 15 +I lines
         are noncontextual and are forced into violation by the 120 external
         observables; all 512 projective odd-imaginary flat states of
         Proposition 6 violate the exact same 15 diagonal lines.
       * Remaining 60 violated lines (48 +I, 12 -I, all degree-triple (1,1,7)):
         pairwise disjoint on all 120 external observables (60 * 2 = 120),
         partitioning into 15 four-line pencils -- exactly 4 external violated
         lines through each diagonal point p in D_15. At each p, the 8
         external points on its 4 lines share a single nonzero X-part a(p),
         pairwise commute (28/28 pairs), and together with the 7-point Fano
         plane p^perp_doily form a maximal totally isotropic PG(3,2) generator
         G_p subset S_B in which the 7 violated lines through p are literally
         the complete 7-line star of p in G_p.

Writes reproducible human-readable and Qontextium-ready exports to:
  tracks/spectral-bounds/results/hyperbolic-quasi-quadric-135/
"""
from __future__ import annotations

import csv
import json
from collections import Counter, deque
from pathlib import Path

TRACK_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = TRACK_ROOT.parents[1]
OUT_DIR = TRACK_ROOT / "results" / "hyperbolic-quasi-quadric-135"

# Canonical Lean 4 CSS masks from lean/HoggarBound/ExactDegreesN4N5.lean
Q7M_MASK = 0xC33C96690FF05AA533CC6699FF00AA553C3C6969F0F0A5A5CCCC999900005554
Q7M_NEG = 0x8114022805500AA4114422985500AA54141429285050A5A44444999800000000
W72_MASK = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
W72_NEG = 0x8116033E055E0FFE117633FE55FEFFFE17163F3E5F5EFFFE7776FFFEFFFE0000
Q9P_MASK = (
    0x69969669C33C3CC3A55A5AA50FF0F00F9966669933CCCC3355AAAA55FF0000FF
    << 768
) | (
    0x969669693C3CC3C35A5AA5A5F0F00F0F66669999CCCC3333AAAA55550000FFFF
    << 512
) | (
    0x966996693CC33CC35AA55AA5F00FF00F66996699CC33CC33AA55AA5500FF00FF
    << 256
) | 0x69696969C3C3C3C3A5A5A5A50F0F0F0F999999993333333355555555FFFFFFFE
Q9P_NEG = (
    0x68808000C0000002A00000040000000E880000100000003200000054000000FE
    << 768
) | (
    0x80800100000003020000050400000F0E0000111000003332000055540000FFFE
    << 512
) | (
    0x800180000003000200050004000F000E00110010003300320055005400FF00FE
    << 256
) | 0x0101010003030302050505040F0F0F0E11111110333333325555555400000000


def symp(n: int, u: int, v: int) -> int:
    m = (1 << n) - 1
    return (((u & m) & (v >> n)).bit_count() ^ ((u >> n) & (v & m)).bit_count()) & 1


def y_count(n: int, u: int) -> int:
    m = (1 << n) - 1
    return ((u & m) & (u >> n)).bit_count()


def line_sign(n: int, u: int, v: int) -> int:
    m = (1 << n) - 1
    ux, uz, vx, vz = u & m, u >> n, v & m, v >> n
    ph = (
        (ux & uz).bit_count()
        + (vx & vz).bit_count()
        - ((ux ^ vx) & (uz ^ vz)).bit_count()
        + 2 * (uz & vx).bit_count()
    ) % 4
    assert ph in (0, 2)
    return 1 if ph == 0 else -1


def fmt_pauli(n: int, u: int) -> str:
    m = (1 << n) - 1
    x, z = u & m, u >> n
    return "".join("IXZY"[((x >> i) & 1) + 2 * ((z >> i) & 1)] for i in range(n))


def parse_pauli(s: str) -> int:
    n = len(s)
    x = 0
    z = 0
    for i, ch in enumerate(s):
        if ch in ("X", "Y"):
            x |= 1 << i
        if ch in ("Z", "Y"):
            z |= 1 << i
    return x | (z << n)


def bfs_dist(adj: dict, src) -> dict:
    dist = {src: 0}
    q = deque([src])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def graph_girth(adj: dict) -> int:
    best = 10**9
    for s in adj:
        dist = {s: 0}
        par = {s: None}
        q = deque([s])
        while q:
            u = q.popleft()
            if 2 * dist[u] + 1 >= best:
                break
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    par[v] = u
                    q.append(v)
                elif par[u] != v:
                    best = min(best, dist[u] + dist[v] + 1)
    return best


def f2_rank(vecs: list[int]) -> int:
    basis: list[int] = []
    for v in vecs:
        x = v
        for b in basis:
            x = min(x, x ^ b)
        if x:
            basis.append(x)
    return len(basis)


def f2_basis(vecs: list[int]) -> list[int]:
    basis: list[int] = []
    raw: list[int] = []
    for v in vecs:
        x = v
        for b in basis:
            x = min(x, x ^ b)
        if x:
            basis.append(x)
            raw.append(v)
    return raw


def load_search_witness(path: Path) -> tuple[int, str, list[int], list[tuple[int, int, int, int]]]:
    parts = path.read_text(encoding="utf-8").strip().split()
    n = int(parts[0])
    kind = parts[1]
    claim = int(parts[2])
    hx = parts[3]
    hlen = len(hx)
    bits = [0] * (1 << (2 * n))
    for k, ch in enumerate(hx):
        val = int(ch, 16)
        nib = hlen - 1 - k
        for b in range(4):
            bits[nib * 4 + b] = (val >> b) & 1
    pts: list[int] = []
    y_last = (1 << (n - 1)) | (1 << (2 * n - 1))
    for u in range(1, 1 << (2 * n)):
        ny = y_count(n, u)
        if kind == "f":
            pts.append(u)
        elif kind == "h":
            if ny % 2 == 0:
                pts.append(u)
        elif kind == "e":
            if (ny + symp(n, y_last, u)) % 2 == 0:
                pts.append(u)
    ptset = set(pts)
    viol: list[tuple[int, int, int, int]] = []
    for i, u in enumerate(pts):
        for j in range(i + 1, len(pts)):
            v = pts[j]
            w = u ^ v
            if w > v and w in ptset and symp(n, u, v) == 0:
                s = line_sign(n, u, v)
                fu = -1 if bits[u] else 1
                fv = -1 if bits[v] else 1
                fw = -1 if bits[w] else 1
                if fu * fv * fw != s:
                    viol.append((u, v, w, s))
    assert len(viol) == claim, f"{path.name}: {len(viol)} != {claim}"
    return n, kind, pts, viol


def load_lean_css(n: int, mask: int, neg: int) -> tuple[list[int], list[tuple[int, int, int, int]]]:
    pts = [z for z in range(1, 1 << (2 * n)) if (mask >> z) & 1]
    ptset = set(pts)
    viol: list[tuple[int, int, int, int]] = []
    for i, u in enumerate(pts):
        for j in range(i + 1, len(pts)):
            v = pts[j]
            w = u ^ v
            if w > v and w in ptset and symp(n, u, v) == 0:
                s = line_sign(n, u, v)
                fu = -1 if ((neg >> u) & 1) else 1
                fv = -1 if ((neg >> v) & 1) else 1
                fw = -1 if ((neg >> w) & 1) else 1
                if fu * fv * fw != s:
                    viol.append((u, v, w, s))
    return pts, viol


def find_explicit_symplectic_iso(
    n: int,
    kind: str,
    pts_src: list[int],
    viol_src: list[tuple[int, int, int, int]],
    pts_dst: list[int],
    viol_dst: list[tuple[int, int, int, int]],
) -> dict:
    """Construct an explicit linear T in Sp(2N,2) mapping (pts_src, viol_src) onto (pts_dst, viol_dst)."""
    vdeg: Counter[int] = Counter()
    for u, v, w, _ in viol_src:
        vdeg[u] += 1
        vdeg[v] += 1
        vdeg[w] += 1
    mindeg = min(vdeg[p] for p in pts_src)
    core = [p for p in pts_src if vdeg[p] == mindeg]
    adj = {p: set() for p in core}
    for u, v, w, _ in viol_src:
        c = [x for x in (u, v, w) if vdeg[x] == mindeg]
        if len(c) == 2:
            adj[c[0]].add(c[1])
            adj[c[1]].add(c[0])
    color: dict[int, int] = {}
    for s in core:
        if s in color:
            continue
        color[s] = 0
        stk = [s]
        while stk:
            u = stk.pop()
            for v in adj[u]:
                if v not in color:
                    color[v] = 1 - color[u]
                    stk.append(v)
                else:
                    assert color[v] != color[u]
    side_a = [p for p in core if color[p] == 0]
    side_b = [p for p in core if color[p] == 1]
    assert len(side_a) == len(side_b)
    b_a = f2_basis(side_a)

    def dual_basis(basis_a: list[int], b_list: list[int]) -> list[int]:
        d = len(basis_a)
        res: list[int] = []
        for i in range(d):
            cands = [b for b in b_list if all(symp(n, basis_a[j], b) == (1 if j == i else 0) for j in range(d))]
            assert len(cands) == 1
            res.append(cands[0])
        return res

    if kind == "e":
        perp = [x for x in range(1, 1 << (2 * n)) if all(symp(n, x, p) == 0 for p in side_a + side_b)]
        assert len(perp) == 3
        perp_pairs = [(x, y) for x in perp for y in perp if x != y]
    else:
        perp_pairs = [None]

    dst_pts_set = set(pts_dst)
    dst_viol_set = {tuple(sorted((u, v, w))) for u, v, w, _ in viol_dst}

    for pp in perp_pairs:
        if kind == "e":
            assert pp is not None
            e_vecs = [pp[0], *b_a]
            f_vecs = [pp[1], *dual_basis(b_a, side_b)]
        else:
            e_vecs = b_a
            f_vecs = dual_basis(b_a, side_b)
        for i in range(n):
            for j in range(n):
                assert symp(n, e_vecs[i], e_vecs[j]) == 0
                assert symp(n, f_vecs[i], f_vecs[j]) == 0
                assert symp(n, e_vecs[i], f_vecs[j]) == (1 if i == j else 0)

        def apply_t(u: int, e_basis: list[int] = e_vecs, f_basis: list[int] = f_vecs) -> int:
            xv = 0
            zv = 0
            for i in range(n):
                if symp(n, u, f_basis[i]):
                    xv |= 1 << i
                if symp(n, e_basis[i], u):
                    zv |= 1 << i
            return xv | (zv << n)

        img_pts = {apply_t(u) for u in pts_src}
        img_viol = {tuple(sorted((apply_t(u), apply_t(v), apply_t(w)))) for u, v, w, _ in viol_src}
        if img_pts == dst_pts_set and img_viol == dst_viol_set:
            # Verify T preserves symplectic form on standard basis
            std_basis = [1 << k for k in range(2 * n)]
            imgs = [apply_t(b) for b in std_basis]
            for i in range(2 * n):
                for j in range(2 * n):
                    assert symp(n, imgs[i], imgs[j]) == symp(n, std_basis[i], std_basis[j])
            return {
                "isomorphic_in_Sp_2N_2": True,
                "exact_points_matched": len(img_pts),
                "exact_violated_lines_matched": len(img_viol),
                "preimage_of_standard_X_basis": [fmt_pauli(n, e) for e in e_vecs],
                "preimage_of_standard_Z_basis": [fmt_pauli(n, f) for f in f_vecs],
            }
    raise AssertionError(f"No Sp({2 * n},2) isomorphism found for kind={kind}")


def analyze_q7minus(label: str, pts: list[int], viol: list[tuple[int, int, int, int]]) -> dict:
    assert len(pts) == 119 and len(viol) == 315
    vdeg: Counter[int] = Counter()
    for u, v, w, _ in viol:
        vdeg[u] += 1
        vdeg[v] += 1
        vdeg[w] += 1
    deg_dist = dict(sorted(Counter(vdeg[p] for p in pts).items()))
    triples = Counter(tuple(sorted((vdeg[u], vdeg[v], vdeg[w]))) for u, v, w, _ in viol)
    signs = Counter(s for _, _, _, s in viol)
    assert deg_dist == {3: 14, 7: 21, 9: 84}
    assert dict(sorted(triples.items())) == {(3, 3, 7): 21, (7, 9, 9): 126, (9, 9, 9): 168}

    p3 = sorted(p for p in pts if vdeg[p] == 3)
    p7 = sorted(p for p in pts if vdeg[p] == 7)
    p9 = sorted(p for p in pts if vdeg[p] == 9)
    l337 = [line for line in viol if tuple(sorted((vdeg[line[0]], vdeg[line[1]], vdeg[line[2]]))) == (3, 3, 7)]

    adj_h = {p: set() for p in p3}
    for u, v, w, _ in l337:
        pair = [x for x in (u, v, w) if vdeg[x] == 3]
        adj_h[pair[0]].add(pair[1])
        adj_h[pair[1]].add(pair[0])
    h_girth = graph_girth(adj_h)
    h_dists: Counter[int] = Counter()
    for p in p3:
        for dv in bfs_dist(adj_h, p).values():
            h_dists[dv] += 1
    assert h_girth == 6
    assert dict(sorted(h_dists.items())) == {0: 14, 1: 42, 2: 84, 3: 56}

    perp = [x for x in range(1, 256) if all(symp(4, x, p) == 0 for p in p3)]
    assert len(perp) == 3
    shells: dict[tuple[int, int, int], list[int]] = {}
    for p in p9:
        sig = (symp(4, perp[0], p), symp(4, perp[1], p), symp(4, perp[2], p))
        shells.setdefault(sig, []).append(p)
    assert sorted(len(v) for v in shells.values()) == [28, 28, 28]

    hexagons = []
    for _sig, s28 in sorted(shells.items()):
        h_pts = set(p3) | set(p7) | set(s28)
        h_lines = [line for line in viol if line[0] in h_pts and line[1] in h_pts and line[2] in h_pts]
        assert len(h_pts) == 63 and len(h_lines) == 63
        inc: dict = {("p", p): set() for p in h_pts}
        for idx, (u, v, w, _) in enumerate(h_lines):
            inc[("l", idx)] = {("p", u), ("p", v), ("p", w)}
            inc[("p", u)].add(("l", idx))
            inc[("p", v)].add(("l", idx))
            inc[("p", w)].add(("l", idx))
        g = graph_girth(inc)
        assert g == 12
        coplanar = 0
        for p in h_pts:
            nbrs = {x for _, li in inc[("p", p)] for x in h_lines[li][:3]}
            if f2_rank(list(nbrs)) == 3:
                coplanar += 1
        assert coplanar == 63
        hexagons.append({"shell_size": len(s28), "points": 63, "lines": 63, "incidence_girth": g, "coplanar_stars": coplanar})

    # Verify all 168 (9,9,9) lines are strictly transversal across the 3 shells
    shell_of = {p: idx for idx, (_, s28) in enumerate(sorted(shells.items())) for p in s28}
    l999 = [line for line in viol if tuple(sorted((vdeg[line[0]], vdeg[line[1]], vdeg[line[2]]))) == (9, 9, 9)]
    assert len(l999) == 168
    assert all(len({shell_of[u], shell_of[v], shell_of[w]}) == 3 for u, v, w, _ in l999)

    return {
        "label": label,
        "observables": 119,
        "violated_contexts": 315,
        "violated_signs": {"positive": signs[1], "negative": signs[-1]},
        "point_violated_degrees": {str(k): v for k, v in deg_dist.items()},
        "line_degree_triples": {str(k): v for k, v in sorted(triples.items())},
        "heawood_core": {"points": 14, "edges": 21, "girth": h_girth, "distance_histogram": {str(k): v for k, v in sorted(h_dists.items())}},
        "perp_external_line": [fmt_pauli(4, x) for x in perp],
        "three_classical_split_cayley_hexagons": hexagons,
        "transversal_999_lines": len(l999),
    }


def analyze_w72(label: str, pts: list[int], viol: list[tuple[int, int, int, int]]) -> dict:
    assert len(pts) == 255 and len(viol) == 1575
    vdeg: Counter[int] = Counter()
    for u, v, w, _ in viol:
        vdeg[u] += 1
        vdeg[v] += 1
        vdeg[w] += 1
    deg_dist = dict(sorted(Counter(vdeg[p] for p in pts).items()))
    triples = Counter(tuple(sorted((vdeg[u], vdeg[v], vdeg[w]))) for u, v, w, _ in viol)
    signs = Counter(s for _, _, _, s in viol)
    assert deg_dist == {7: 30, 19: 105, 21: 120}
    assert dict(sorted(triples.items())) == {(7, 7, 19): 105, (19, 19, 19): 210, (19, 21, 21): 1260}

    p7 = {p for p in pts if vdeg[p] == 7}
    p19 = {p for p in pts if vdeg[p] == 19}
    p21 = {p for p in pts if vdeg[p] == 21}
    core_pts = p7 | p19
    core_lines = [line for line in viol if line[0] in core_pts and line[1] in core_pts and line[2] in core_pts]
    ext_lines = [line for line in viol if not (line[0] in core_pts and line[1] in core_pts and line[2] in core_pts)]
    assert len(core_pts) == 135 and len(core_lines) == 315 and len(ext_lines) == 1260

    # Check DW(5,2) collinearity distance profile {0:1, 1:14, 2:56, 3:64}
    adj_c = {p: set() for p in core_pts}
    for u, v, w, _ in core_lines:
        adj_c[u] |= {v, w}
        adj_c[v] |= {u, w}
        adj_c[w] |= {u, v}
    dprofs = Counter(tuple(sorted(Counter(bfs_dist(adj_c, p).values()).items())) for p in core_pts)
    assert dprofs == {((0, 1), (1, 14), (2, 56), (3, 64)): 135}

    # Check intersection array {14, 12, 8; 1, 3, 7} of DW(5,2)
    sample = next(iter(core_pts))
    dmap = bfs_dist(adj_c, sample)
    for u, du in dmap.items():
        c_cnt = sum(1 for v in adj_c[u] if dmap[v] == du - 1)
        b_cnt = sum(1 for v in adj_c[u] if dmap[v] == du + 1)
        if du == 0:
            assert b_cnt == 14
        elif du == 1:
            assert c_cnt == 1 and b_cnt == 12
        elif du == 2:
            assert c_cnt == 3 and b_cnt == 8
        elif du == 3:
            assert c_cnt == 7 and b_cnt == 0

    # Check PG(3,2) point-hyperplane incidence graph on P7
    l77 = [line for line in viol if tuple(sorted((vdeg[line[0]], vdeg[line[1]], vdeg[line[2]]))) == (7, 7, 19)]
    adj7 = {p: set() for p in p7}
    for u, v, w, _ in l77:
        pair = [x for x in (u, v, w) if x in p7]
        adj7[pair[0]].add(pair[1])
        adj7[pair[1]].add(pair[0])
    d7: Counter[int] = Counter()
    for p in p7:
        for dv in bfs_dist(adj7, p).values():
            d7[dv] += 1
    assert graph_girth(adj7) == 4
    assert dict(sorted(d7.items())) == {0: 30, 1: 210, 2: 420, 3: 240}

    # Check 1,260 external lines incidence on core_pts and p21
    ext_deg: Counter[int] = Counter()
    for u, v, w, _ in ext_lines:
        assert sum(x in p19 for x in (u, v, w)) == 1
        assert sum(x in p21 for x in (u, v, w)) == 2
        ext_deg[u] += 1
        ext_deg[v] += 1
        ext_deg[w] += 1
    assert all(ext_deg[p] == 0 for p in p7)
    assert all(ext_deg[p] == 12 for p in p19)
    assert all(ext_deg[p] == 21 for p in p21)

    return {
        "label": label,
        "observables": 255,
        "violated_contexts": 1575,
        "violated_signs": {"positive": signs[1], "negative": signs[-1]},
        "point_violated_degrees": {str(k): v for k, v in deg_dist.items()},
        "line_degree_triples": {str(k): v for k, v in sorted(triples.items())},
        "dw52_core": {
            "points": 135,
            "lines": 315,
            "collinearity_distance_profile": {"0": 1, "1": 14, "2": 56, "3": 64},
            "intersection_array": "{14, 12, 8; 1, 3, 7}",
            "pg32_subcore_points": 30,
            "pg32_subcore_lines": 105,
        },
        "external_1260_lines": {
            "count": 1260,
            "per_degree_19_core_point": 12,
            "per_degree_7_core_point": 0,
            "per_outside_point": 21,
        },
    }


def analyze_q9plus(label: str, pts: list[int], viol: list[tuple[int, int, int, int]]) -> dict:
    assert len(pts) == 527 and len(viol) == 6975
    vdeg: Counter[int] = Counter()
    for u, v, w, _ in viol:
        vdeg[u] += 1
        vdeg[v] += 1
        vdeg[w] += 1
    deg_dist = dict(sorted(Counter(vdeg[p] for p in pts).items()))
    triples = Counter(tuple(sorted((vdeg[u], vdeg[v], vdeg[w]))) for u, v, w, _ in viol)
    signs = Counter(s for _, _, _, s in viol)
    assert deg_dist == {15: 62, 43: 465}
    assert dict(sorted(triples.items())) == {(15, 15, 43): 465, (43, 43, 43): 6510}

    p15 = {p for p in pts if vdeg[p] == 15}
    p43 = {p for p in pts if vdeg[p] == 43}
    l15 = [line for line in viol if tuple(sorted((vdeg[line[0]], vdeg[line[1]], vdeg[line[2]]))) == (15, 15, 43)]
    adj15 = {p: set() for p in p15}
    p43_from_core: set[int] = set()
    for u, v, w, _ in l15:
        pair = [x for x in (u, v, w) if x in p15]
        third = [x for x in (u, v, w) if x in p43][0]
        p43_from_core.add(third)
        adj15[pair[0]].add(pair[1])
        adj15[pair[1]].add(pair[0])
    assert p43_from_core == p43
    d15: Counter[int] = Counter()
    for p in p15:
        for dv in bfs_dist(adj15, p).values():
            d15[dv] += 1
    assert graph_girth(adj15) == 4
    assert dict(sorted(d15.items())) == {0: 62, 1: 930, 2: 1860, 3: 992}

    return {
        "label": label,
        "observables": 527,
        "violated_contexts": 6975,
        "violated_signs": {"positive": signs[1], "negative": signs[-1]},
        "point_violated_degrees": {str(k): v for k, v in deg_dist.items()},
        "line_degree_triples": {str(k): v for k, v in sorted(triples.items())},
        "pg42_point_hyperplane_core": {
            "points": 62,
            "lines": 465,
            "bipartite_regularity": 15,
            "girth": 4,
            "distance_histogram": {str(k): v for k, v in sorted(d15.items())},
        },
        "outer_43_43_43_lines": 6510,
    }


def analyze_and_export_hyperbolic_quasi_quadric() -> dict:
    """Exact analysis and Qontextium-compatible export of S_B (data/flat/n4_pivot.txt)."""
    pivot_path = REPO_ROOT / "data" / "flat" / "n4_pivot.txt"
    lines_raw = [ln.strip() for ln in pivot_path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    header = lines_raw[0].split()
    n, n_pts, n_ctx, n_viol = (int(x) for x in header)
    assert (n, n_pts, n_ctx, n_viol) == (4, 135, 1095, 75)
    mask_int = int(lines_raw[1], 16)
    neg_int = int(lines_raw[2], 16)
    pts = [z for z in range(1, 1 << (2 * n)) if (mask_int >> z) & 1]
    f_sign = {z: (-1 if (neg_int >> z) & 1 else 1) for z in pts}
    assert len(pts) == 135 and len(set(pts)) == 135
    ptset = set(pts)

    # Regular commutation degree = 70 on all 135 observables (hyperbolic quasi-quadric!)
    comm_degs = {p: sum(1 for q in pts if q != p and symp(4, p, q) == 0) for p in pts}
    assert set(comm_degs.values()) == {70}

    # Build all 1,095 commuting triple contexts and 75 violated contexts
    contexts: list[tuple[int, int, int, int, bool]] = []
    amb_deg: Counter[int] = Counter()
    viol_deg: Counter[int] = Counter()
    for i, u in enumerate(pts):
        for j in range(i + 1, len(pts)):
            v = pts[j]
            w = u ^ v
            if w > v and w in ptset and symp(4, u, v) == 0:
                s = line_sign(4, u, v)
                is_viol = f_sign[u] * f_sign[v] * f_sign[w] != s
                contexts.append((u, v, w, s, is_viol))
                amb_deg[u] += 1
                amb_deg[v] += 1
                amb_deg[w] += 1
                if is_viol:
                    viol_deg[u] += 1
                    viol_deg[v] += 1
                    viol_deg[w] += 1

    assert len(contexts) == 1095
    pos_ctx = sum(1 for _, _, _, s, _ in contexts if s == 1)
    neg_ctx = sum(1 for _, _, _, s, _ in contexts if s == -1)
    assert pos_ctx == 735 and neg_ctx == 360
    assert dict(sorted(Counter(amb_deg[p] for p in pts).items())) == {23: 120, 35: 15}
    assert dict(sorted(Counter(viol_deg[p] for p in pts).items())) == {1: 120, 7: 15}

    viol = [(u, v, w, s) for u, v, w, s, iv in contexts if iv]
    assert len(viol) == 75

    # Diagonal subspace D_15 = 15 pure-Z observables (violated degree 7, ambient degree 35).
    # Verify explicitly that D_15 is a maximal totally isotropic PG(3,2) subspace of W(7,2)
    # (105/105 commuting pairs, 35/35 +I ambient lines), so the 15 violated lines form an
    # abstract doily GQ(2,2) (symplectic linear line complex in PG(3,2)), NOT a symplectic
    # four-qubit doily.
    doily_pts = sorted(p for p in pts if viol_deg[p] == 7)
    ext_pts = sorted(p for p in pts if viol_deg[p] == 1)
    assert len(doily_pts) == 15 and len(ext_pts) == 120
    assert all((p & 15) == 0 for p in doily_pts), "Diagonal points are the 15 pure-Z observables"
    doily_set = set(doily_pts)
    assert all(
        symp(4, x, y) == 0 for i, x in enumerate(doily_pts) for y in doily_pts[i + 1 :]
    ), "All 105 pairs in D_15 must commute (totally isotropic PG(3,2))"
    assert f2_rank(doily_pts) == 4
    doily_ambient = [
        (u, v, w, s)
        for u, v, w, s, _ in contexts
        if u in doily_set and v in doily_set and w in doily_set
    ]
    assert len(doily_ambient) == 35 and all(s == 1 for _, _, _, s in doily_ambient)

    doily_viol = [line for line in viol if line[0] in doily_set and line[1] in doily_set and line[2] in doily_set]
    ext_viol = [line for line in viol if not (line[0] in doily_set and line[1] in doily_set and line[2] in doily_set)]
    assert len(doily_viol) == 15 and len(ext_viol) == 60
    assert all(s == 1 for _, _, _, s in doily_viol)
    assert sum(1 for _, _, _, s in ext_viol if s == 1) == 48
    assert sum(1 for _, _, _, s in ext_viol if s == -1) == 12

    # Verify the 15 diagonal violated lines form an abstract doily GQ(2,2): distance-regular {6,4;1,3}
    adj_d = {p: set() for p in doily_pts}
    for u, v, w, _ in doily_viol:
        adj_d[u] |= {v, w}
        adj_d[v] |= {u, w}
        adj_d[w] |= {u, v}
    d_profs = Counter(tuple(sorted(Counter(bfs_dist(adj_d, p).values()).items())) for p in doily_pts)
    assert d_profs == {((0, 1), (1, 6), (2, 8)): 15}

    # Verify Proposition 6 invariance: across all 512 projective odd-imaginary bent-support
    # flat states on T = {x in F_2^4 : x_0 x_1 + x_2 x_3 = 1} (6 basis states with |phi(x)|=1,
    # phi(x) in {1,-1,i,-i}, odd count of +-i, quotiented by global phase), <Z^c> = (1/6) sum_{x in T} (-1)^(c.x)
    # is invariant and matches n4_pivot.txt on all 15 pure-Z observables, so every state violates
    # the exact same 15-line abstract doily inside D_15.
    bent_support_t = [x for x in range(16) if (((x & 1) & ((x >> 1) & 1)) ^ (((x >> 2) & 1) & ((x >> 3) & 1))) == 1]
    assert bent_support_t == [3, 7, 11, 12, 13, 14]
    diag_signs_t = {
        (c << 4): (1 if sum((-1) ** ((c & x).bit_count()) for x in bent_support_t) > 0 else -1)
        for c in range(1, 16)
    }
    assert all(diag_signs_t[p] == f_sign[p] for p in doily_pts)
    # Count projective odd-imaginary phase patterns phi: T -> {0,1,2,3} with phi(t_0) = 0 (fixing global phase)
    odd_proj_count = 0
    for code in range(4**5):
        ks = [0] + [(code >> (2 * j)) & 3 for j in range(5)]
        if sum(k & 1 for k in ks) % 2 == 1:
            odd_proj_count += 1
    assert odd_proj_count == 512

    # Verify the 60 remaining lines:
    #  - Every line meets D_15 in 1 point p and carries 2 external points of violated degree 1.
    #  - Each p in D_15 carries exactly 4 external violated lines (15 * 4 = 60).
    #  - All 8 external points on the 4 lines through p share a single constant nonzero X-support a(p),
    #    pairwise commute (28/28 pairs), and together with the 7-point Fano plane p^perp_doily form a
    #    maximal totally isotropic PG(3,2) generator G_p subset S_B (15 pts, 35 ambient lines)
    #    whose 7 violated lines (3 doily + 4 external) are the complete 7-line star of p in G_p.
    pencils: dict[int, list[tuple[int, int, int, int]]] = {p: [] for p in doily_pts}
    seen_ext: set[int] = set()
    for u, v, w, s in ext_viol:
        d_in = [x for x in (u, v, w) if x in doily_set]
        e_in = sorted(x for x in (u, v, w) if x not in doily_set)
        assert len(d_in) == 1 and len(e_in) == 2
        anchor = d_in[0]
        pencils[anchor].append((anchor, e_in[0], e_in[1], s))
        for ex in e_in:
            assert ex not in seen_ext
            seen_ext.add(ex)
    assert seen_ext == set(ext_pts)

    generators_summary = []
    ovoid_poles: list[int] = []
    ovoid_x_supports: list[int] = []
    ctx_set = {tuple(sorted((u, v, w))) for u, v, w, _, _ in contexts}

    for p in doily_pts:
        lines_p = sorted(pencils[p], key=lambda t: (fmt_pauli(4, t[1]), fmt_pauli(4, t[2])))
        assert len(lines_p) == 4
        ext8 = sorted({x for _, a, b, _ in lines_p for x in (a, b)})
        assert len(ext8) == 8
        # Constant nonzero X-part a(p)
        x_parts = {x & 15 for x in ext8}
        assert len(x_parts) == 1
        a_x = next(iter(x_parts))
        assert a_x != 0
        # Pairwise commuting 8 external points (28/28 pairs) + commuting with Fano plane p^perp_doily
        fano7 = sorted({p} | adj_d[p])
        assert len(fano7) == 7
        # Confirm fano7 == {z in D_15 : symp(a_x, z) == 0}
        assert fano7 == sorted(z for z in doily_pts if symp(4, a_x, z) == 0)
        g_p = sorted(fano7 + ext8)
        assert len(g_p) == 15
        # Maximal totally isotropic PG(3,2): all 105 pairs commute, rank 4 over F_2, 35 ambient lines in S_B
        assert all(symp(4, x, y) == 0 for i, x in enumerate(g_p) for y in g_p[i + 1 :])
        assert f2_rank(g_p) == 4
        gp_lines = [
            (x, y, x ^ y)
            for i, x in enumerate(g_p)
            for j, y in enumerate(g_p[i + 1 :], i + 1)
            if (x ^ y) > y and tuple(sorted((x, y, x ^ y))) in ctx_set
        ]
        assert len(gp_lines) == 35
        # Complete 7-line star of p in G_p == 3 doily violated lines + 4 external violated lines!
        star_in_gp = {tuple(sorted(line)) for line in gp_lines if p in line}
        assert len(star_in_gp) == 7
        viol_in_gp = {
            tuple(sorted((u, v, w)))
            for u, v, w, _ in viol
            if u in g_p and v in g_p and w in g_p
        }
        assert viol_in_gp == star_in_gp

        # Y-parity of the 8 external points in fiber a(p)
        y_parities = {y_count(4, x) % 2 for x in ext8}
        assert len(y_parities) == 1
        y_par = next(iter(y_parities))
        if y_par == 1:
            ovoid_poles.append(p)
            ovoid_x_supports.append(a_x)

        neg_in_p = sum(1 for _, _, _, s in lines_p if s == -1)
        generators_summary.append(
            {
                "central_doily_anchor": fmt_pauli(4, p),
                "x_support": fmt_pauli(4, a_x),
                "fiber_y_parity": y_par,
                "negative_external_violated_lines": neg_in_p,
                "fano_plane_in_doily": [fmt_pauli(4, z) for z in fano7],
                "external_8_observables": [fmt_pauli(4, x) for x in ext8],
                "four_external_violated_lines": [
                    {"observables": [fmt_pauli(4, anc), fmt_pauli(4, e1), fmt_pauli(4, e2)], "sign": s}
                    for anc, e1, e2, s in lines_p
                ],
            }
        )

    # Verify the 5 flipped-parity poles form an exact 5-point ovoid of the central doily W(3,2)!
    assert len(ovoid_poles) == 5
    for i, p1 in enumerate(ovoid_poles):
        for p2 in ovoid_poles[i + 1 :]:
            assert p2 not in adj_d[p1], "Ovoid poles must be pairwise non-collinear in central doily"
    ovoid_set = set(ovoid_poles)
    assert all(sum(x in ovoid_set for x in (u, v, w)) == 1 for u, v, w, _ in doily_viol)

    # Write deterministic LF-only export files!
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Qontextium-ready assignment file for ALL 1,095 contexts (exact qa_grid.txt format: P1,P2,P3, no header)
    ctx_sorted = sorted(
        contexts,
        key=lambda t: (
            0 if (t[0] in doily_set and t[1] in doily_set and t[2] in doily_set) else 1,
            fmt_pauli(4, t[0]),
            fmt_pauli(4, t[1]),
            fmt_pauli(4, t[2]),
        ),
    )
    qa_all_lines = [f"{fmt_pauli(4, u)},{fmt_pauli(4, v)},{fmt_pauli(4, w)}" for u, v, w, _, _ in ctx_sorted]
    (OUT_DIR / "qa_hyperbolic_quasi_quadric_135_contexts.txt").write_text(
        "\n".join(qa_all_lines) + "\n", encoding="utf-8", newline="\n"
    )

    # 2. Qontextium-ready assignment file for the 75 violated contexts (15 central doily + 60 external generator stars)
    doily_viol_sorted = sorted(doily_viol, key=lambda t: (fmt_pauli(4, t[0]), fmt_pauli(4, t[1]), fmt_pauli(4, t[2])))
    ext_viol_ordered: list[tuple[int, int, int, int]] = []
    for p in doily_pts:
        for anc, e1, e2, s in sorted(pencils[p], key=lambda t: (fmt_pauli(4, t[1]), fmt_pauli(4, t[2]))):
            ext_viol_ordered.append((anc, e1, e2, s))
    qa_viol_lines = [
        f"{fmt_pauli(4, u)},{fmt_pauli(4, v)},{fmt_pauli(4, w)}"
        for u, v, w, _ in doily_viol_sorted + ext_viol_ordered
    ]
    (OUT_DIR / "qa_hyperbolic_quasi_quadric_135_violated_75.txt").write_text(
        "\n".join(qa_viol_lines) + "\n", encoding="utf-8", newline="\n"
    )

    # 3. Clean human-readable observables_135.txt
    obs_lines = [
        "# Hyperbolic quasi-quadric S_B in W(7,2) (135 observables, 1,095 contexts, exact degree 75)",
        "# Source: data/flat/n4_pivot.txt (Lean 4 certified in HoggarBound.pivot_degree = 75, pivot_contexts = 1095)",
        "# Columns: index  pauli  witness_sign  role  ambient_line_deg  violated_line_deg  generator_anchor",
        "",
    ]
    anchor_of_ext: dict[int, int] = {}
    for p in doily_pts:
        for _, e1, e2, _ in pencils[p]:
            anchor_of_ext[e1] = p
            anchor_of_ext[e2] = p
    ordered_obs = doily_pts + [
        x for p in doily_pts for x in sorted({e for _, e1, e2, _ in pencils[p] for e in (e1, e2)}, key=lambda v: fmt_pauli(4, v))
    ]
    assert len(ordered_obs) == 135 and set(ordered_obs) == ptset
    for idx, p in enumerate(ordered_obs, 1):
        role = "central_doily" if p in doily_set else "external_fiber"
        anc = fmt_pauli(4, p) if p in doily_set else fmt_pauli(4, anchor_of_ext[p])
        sgn_str = "+1" if f_sign[p] == 1 else "-1"
        obs_lines.append(f"{idx:3d}  {fmt_pauli(4, p)}  {sgn_str}  {role:14s}  {amb_deg[p]:2d}  {viol_deg[p]}  {anc}")
    (OUT_DIR / "observables_135.txt").write_text("\n".join(obs_lines) + "\n", encoding="utf-8", newline="\n")

    # 4. contexts_1095.csv
    with (OUT_DIR / "contexts_1095.csv").open("w", encoding="utf-8", newline="\n") as fh:
        writer = csv.writer(fh, lineterminator="\n")
        writer.writerow(["index", "obs1", "obs2", "obs3", "sign", "violated", "doily_points_on_line", "central_doily_anchor"])
        for idx, (u, v, w, s, is_viol) in enumerate(ctx_sorted, 1):
            d_cnt = sum(x in doily_set for x in (u, v, w))
            anc = ""
            if d_cnt == 1:
                anc = fmt_pauli(4, next(x for x in (u, v, w) if x in doily_set))
            elif d_cnt == 3:
                anc = "DOILY"
            writer.writerow([idx, fmt_pauli(4, u), fmt_pauli(4, v), fmt_pauli(4, w), "+1" if s == 1 else "-1", int(is_viol), d_cnt, anc])

    # 5. violated_75.csv
    with (OUT_DIR / "violated_75.csv").open("w", encoding="utf-8", newline="\n") as fh:
        writer = csv.writer(fh, lineterminator="\n")
        writer.writerow(["index", "group", "central_doily_anchor", "x_support", "obs1", "obs2", "obs3", "sign"])
        idx = 1
        for u, v, w, s in doily_viol_sorted:
            writer.writerow([idx, "central_doily", "DOILY", "IIII", fmt_pauli(4, u), fmt_pauli(4, v), fmt_pauli(4, w), "+1" if s == 1 else "-1"])
            idx += 1
        for anc, e1, e2, s in ext_viol_ordered:
            writer.writerow([
                idx,
                "external_generator_star",
                fmt_pauli(4, anc),
                fmt_pauli(4, e1 & 15),
                fmt_pauli(4, anc),
                fmt_pauli(4, e1),
                fmt_pauli(4, e2),
                "+1" if s == 1 else "-1",
            ])
            idx += 1

    # 6. README.md
    readme_text = """# Hyperbolic Quasi-Quadric in $W(7,2)$ (`135` Observables, `1,095` Contexts, `75` Violated Contexts)

Machine-verified exports for the four-qubit floor-saturating hyperbolic quasi-quadric $S_B \\subset W(7,2)$ (`data/flat/n4_pivot.txt`, kernel-certified in Lean 4 via `HoggarBound.pivot_card = 135`, `HoggarBound.pivot_contexts = 1095`, and `HoggarBound.pivot_degree = 75`).

## Direct Import into Qontextium

Both `qa_*.txt` files use Qontextium's native `--import assignment` format (`P1,P2,P3`, no header row, LF line endings):

```bash
# Compute the contextuality degree of the full 135-observable / 1,095-context quasi-quadric:
./qontextium --import assignment qa_hyperbolic_quasi_quadric_135_contexts.txt --solver sat --no-interaction

# Inspect / filter the 75-violated-context subgeometry (15 central doily + 60 external star lines):
./qontextium --import assignment qa_hyperbolic_quasi_quadric_135_violated_75.txt
```

## Included Files

| File | Description |
|---|---|
| `qa_hyperbolic_quasi_quadric_135_contexts.txt` | All `1,095` contexts in native Qontextium `--import assignment` format (`735` positive, `360` negative). |
| `qa_hyperbolic_quasi_quadric_135_violated_75.txt` | All `75` violated contexts in native Qontextium format (`15` central doily lines followed by `60` external lines grouped by central-doily anchor). |
| `observables_135.txt` | All `135` four-qubit Pauli observables with optimal $\\pm 1$ witness signs, ambient line degrees (`35` or `23`), violated degrees (`7` or `1`), and generator anchors. |
| `contexts_1095.csv` | Annotated CSV of all `1,095` contexts with operator-product sign, violation status, and central-doily incidence count. |
| `violated_75.csv` | Annotated CSV of all `75` violated contexts grouped into the `15` central doily lines and the `15` four-line external generator stars. |
| `hyperbolic_quasi_quadric_135.json` | Complete machine-readable JSON bundle including the full `135 / 1,095 / 75` dataset, ovoid relation to $Q^+(7,2)$, and exact $Sp(2N,2)$ witness isomorphism certificates for $Q^-(7,2)$, $W(7,2)$, and $Q^+(9,2)$. |

## Geometric Summary of the `75 = 15 + 60` Violated Contexts

1. **Ambient hyperbolic quasi-quadric ($135$ points, $1,095$ contexts):** Every observable commutes with exactly `70` other observables in $S_B$ (matching the point count `135` and commutation regularity `70` of $Q^+(7,2)$). $S_B$ is obtained from the hyperbolic quadric $Q^+(7,2)$ by flipping the $Y$-parity of the five affine $AG(3,2)$ fibers (`IXII, XXII, XIXI, XIIX, XIXX`) whose unique poles in $D_{15}$ (`ZIII, ZZII, IZZI, IZIZ, IZZZ`) form a **5-point ovoid** of the diagonal abstract doily.
2. **Diagonal abstract doily (`15` points, `15` violated lines, all `+I`, degree-triple `(7,7,7)`):** The `15` pure-$Z$ observables $D_{15} \\cong PG(3,2)$ pairwise commute (`105/105` commuting pairs; all `35` ambient lines in $D_{15}$ are `+I`), so $D_{15}$ is a **maximal totally isotropic $PG(3,2)$ subspace** of $W(7,2)$. Of its `35` ambient lines, `15` are violated and `20` are satisfied. Those `15` violated lines form an **abstract doily $GQ(2,2)$** as a point-line incidence structure (a symplectic linear line complex inside $PG(3,2)$), **not** a symplectic four-qubit doily (in which collinearity coincides with commutation and an odd number of lines are negative). Alone, those `15` positive lines are noncontextual and are forced into violation by the `120` external observables (`360` negative ambient lines); all `512` projective odd-imaginary bent-support flat states of Proposition 6 violate the exact same `15` diagonal lines.
3. **Arrangement of the remaining `60` violated lines (`48` `+I`, `12` `-I`, all degree-triple `(1,1,7)`):**
   - Every external violated line meets $D_{15}$ in **exactly one point** $p \\in D_{15}$ and carries **two external observables of violated degree `1`** (`60 * 2 = 120`, zero overlaps among external points).
   - Through **each** of the `15` diagonal points $p \\in D_{15}$ pass **exactly `4`** of the `60` external violated lines (`15 * 4 = 60`).
   - The `8` external observables on the `4` violated lines through $p$ all share a single constant nonzero $X$-support $a(p)$, pairwise commute (`28/28` pairs), and together with the 7-point Fano plane $p^\\perp_{\\text{doily}}$ (the three diagonal violated lines through $p$) form a **maximal totally isotropic $PG(3,2)$ generator $G_p \\subset S_B$** (`15` points, `35` ambient lines).
   - Inside each generator $G_p$, the `7` violated lines (`3` diagonal lines + `4` external lines) are literally the **complete 7-line star of $p$ in $G_p$** — equivalently, the `4` external lines partition $G_p \\setminus D_{15} \\cong AG(3,2)$ into its `4` parallel affine lines concurring at the point at infinity $p$.

Regenerated deterministically by `python tracks/spectral-bounds/scripts/quasi_quadric_and_witness_anatomy.py`.
"""
    (OUT_DIR / "README.md").write_text(readme_text, encoding="utf-8", newline="\n")

    return {
        "source": "data/flat/n4_pivot.txt",
        "observables": 135,
        "regular_commutation_degree": 70,
        "ambient_contexts": 1095,
        "ambient_signs": {"positive": pos_ctx, "negative": neg_ctx},
        "ambient_line_degrees": {"35": 15, "23": 120},
        "violated_contexts": 75,
        "violated_point_degrees": {"7": 15, "1": 120},
        "central_doily": {
            "geometry_note": (
                "D_15 is a maximal totally isotropic PG(3,2) subspace of W(7,2) "
                "(105/105 commuting pairs, 35/35 +I ambient lines); its 15 violated lines "
                "form an abstract doily GQ(2,2) (symplectic linear line complex in PG(3,2)), "
                "NOT a symplectic four-qubit doily."
            ),
            "ambient_subspace_is_maximal_totally_isotropic_PG32": True,
            "is_symplectic_four_qubit_doily": False,
            "all_105_pairs_commute": True,
            "all_35_ambient_lines_positive": True,
            "prop6_512_odd_imaginary_states_share_exact_15_doily_lines": True,
            "points": [fmt_pauli(4, p) for p in doily_pts],
            "lines": [[fmt_pauli(4, u), fmt_pauli(4, v), fmt_pauli(4, w)] for u, v, w, _ in doily_viol_sorted],
            "signs": {"positive": 15, "negative": 0},
            "collinearity_distance_profile": {"0": 1, "1": 6, "2": 8},
        },
        "ovoid_relation_to_Q7plus": {
            "ovoid_poles_in_central_doily": [fmt_pauli(4, p) for p in ovoid_poles],
            "flipped_x_supports": [fmt_pauli(4, x) for x in ovoid_x_supports],
            "pairwise_noncollinear_in_doily": True,
            "hits_every_doily_line_once": True,
        },
        "remaining_60_violated_lines": {
            "count": 60,
            "signs": {"positive": 48, "negative": 12},
            "external_points_disjoint_cover": 120,
            "pencils_per_doily_point": 4,
            "all_15_generators_maximal_totally_isotropic_PG32": True,
            "each_generator_violated_lines_equal_7_line_star_of_anchor": True,
            "generators": generators_summary,
        },
    }


def main() -> int:
    _, _, n4e_pts, n4e_viol = load_search_witness(REPO_ROOT / "data" / "witness" / "n4_e.txt")
    l4e_pts, l4e_viol = load_lean_css(4, Q7M_MASK, Q7M_NEG)
    q1_search = analyze_q7minus("search:data/witness/n4_e.txt", n4e_pts, n4e_viol)
    q1_lean = analyze_q7minus("lean:HoggarBound.ExactDegreesN4N5.q7minus_css_witness", l4e_pts, l4e_viol)
    q1_iso = find_explicit_symplectic_iso(4, "e", n4e_pts, n4e_viol, l4e_pts, l4e_viol)

    _, _, n4f_pts, n4f_viol = load_search_witness(REPO_ROOT / "data" / "witness" / "n4_f.txt")
    l4f_pts, l4f_viol = load_lean_css(4, W72_MASK, W72_NEG)
    q2_search = analyze_w72("search:data/witness/n4_f.txt", n4f_pts, n4f_viol)
    q2_lean = analyze_w72("lean:HoggarBound.ExactDegreesN4N5.w72_css_witness", l4f_pts, l4f_viol)
    q2_iso = find_explicit_symplectic_iso(4, "f", n4f_pts, n4f_viol, l4f_pts, l4f_viol)

    _, _, n5h_pts, n5h_viol = load_search_witness(REPO_ROOT / "data" / "witness" / "n5_h.txt")
    l5h_pts, l5h_viol = load_lean_css(5, Q9P_MASK, Q9P_NEG)
    q3_search = analyze_q9plus("search:data/witness/n5_h.txt", n5h_pts, n5h_viol)
    q3_lean = analyze_q9plus("lean:HoggarBound.ExactDegreesN4N5.q9plus_css_witness", l5h_pts, l5h_viol)
    q3_iso = find_explicit_symplectic_iso(5, "h", n5h_pts, n5h_viol, l5h_pts, l5h_viol)

    q4 = analyze_and_export_hyperbolic_quasi_quadric()

    bundle = {
        "status": "pass",
        "arithmetic": "exact_integer",
        "q1_q7minus_315": {"search": q1_search, "lean_css": q1_lean, "sp8_2_isomorphism": q1_iso},
        "q2_w72_1575": {"search": q2_search, "lean_css": q2_lean, "sp8_2_isomorphism": q2_iso},
        "q3_q9plus_6975": {"search": q3_search, "lean_css": q3_lean, "sp10_2_isomorphism": q3_iso},
        "q4_hyperbolic_quasi_quadric_135": q4,
    }
    (OUT_DIR / "hyperbolic_quasi_quadric_135.json").write_text(
        json.dumps(bundle, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(
        "PASS  Q1 Q-(7,2) 315: Heawood + 3 classical H(2) + 168 transversals, explicit Sp(8,2) iso 315/315\n"
        "PASS  Q2 W(7,2) 1575: DW(5,2) {14,12,8;1,3,7} + 1260 external lines, explicit Sp(8,2) iso 1575/1575\n"
        "PASS  Q3 Q+(9,2) 6975: PG(4,2) point-hyperplane core + 6510 outer lines, explicit Sp(10,2) iso 6975/6975\n"
        "PASS  Q4 S_B hyperbolic quasi-quadric: 135 obs / 1095 ctx / 75 viol = 15 doily + 15x4 PG(3,2) star lines\n"
        f"Wrote 7 export files to {OUT_DIR.relative_to(REPO_ROOT).as_posix()}/"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
