"""Exact ILP for the contextuality degree of Q-(7,2) (HiGHS through scipy.optimize.milp).

Variables: x_i in {0,1} (f_i = (-1)^x_i), y_l in {0,1} (line l violated), k_l in {0,1,2}.
Constraint per line: x_u + x_v + x_w + y_l - 2 k_l = b_l  (b_l = 1 for negative lines) -> parity is forced.
Gauge: f -> f * (-1)^{<a, v>} (a linear character) preserves every line product, so x can be fixed to 0
on a basis of the span of S (8 independent points).  The proven bound sum y >= 291 is added as a cut and
the search for an assignment with sum y <= 314 is posed as a feasibility problem.
What a run proves: 'infeasible' (status 2) would prove d(Q-(7,2)) = 315.  A time-out proves nothing beyond
the dual bound HiGHS reports (which we print)."""
import sys, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
sys.path.insert(0, '.')
from check_witness import label_to_index
from paulis import Geometry

def main(limit, ub):
    G = Geometry(4, 'Q-'); n, L = G.n, G.L
    nv = n + 2 * L
    A = lil_matrix((L + 1, nv)); lo = np.zeros(L + 1); hi = np.zeros(L + 1)
    for l, (u, v, w) in enumerate(G.lines):
        for p in (u, v, w): A[l, p] = 1
        A[l, n + l] = 1; A[l, n + L + l] = -2
        lo[l] = hi[l] = 1 if G.signs[l] < 0 else 0
    A[L, n:n + L] = 1; lo[L] = 291; hi[L] = ub
    # gauge fixing on a GF(2) basis of the points
    vecs = [label_to_index(l, 4) for l in G.labels]
    basis, piv = [], []
    for i, v in enumerate(vecs):
        r = v
        for b, p in zip(basis, piv):
            if r >> p & 1: r ^= b
        if r:
            basis.append(r); piv.append(r.bit_length() - 1)
            basis_idx.append(i)
    lb = np.zeros(nv); ubv = np.ones(nv); ubv[n + L:] = 2
    for i in basis_idx: ubv[i] = 0
    c = np.zeros(nv); c[n:n + L] = 1
    t = time.time()
    res = milp(c, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=np.ones(nv), bounds=Bounds(lb, ubv),
               options={'time_limit': limit, 'disp': True})
    print('gauge-fixed points:', len(basis_idx))
    print('status', res.status, res.message, 'objective', res.fun, 'dual bound', getattr(res, 'mip_dual_bound', None),
          'time %.0fs' % (time.time() - t))

basis_idx = []
if __name__ == '__main__':
    main(float(sys.argv[1]), int(sys.argv[2]))
