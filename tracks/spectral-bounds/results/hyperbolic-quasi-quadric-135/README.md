# Hyperbolic Quasi-Quadric in $W(7,2)$ (`135` Observables, `1,095` Contexts, `75` Violated Contexts)

Machine-verified exports for the four-qubit floor-saturating hyperbolic quasi-quadric $S_B \subset W(7,2)$ (`data/flat/n4_pivot.txt`, kernel-certified in Lean 4 via `HoggarBound.pivot_card = 135`, `HoggarBound.pivot_contexts = 1095`, and `HoggarBound.pivot_degree = 75`).

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
| `observables_135.txt` | All `135` four-qubit Pauli observables with optimal $\pm 1$ witness signs, ambient line degrees (`35` or `23`), violated degrees (`7` or `1`), and generator anchors. |
| `contexts_1095.csv` | Annotated CSV of all `1,095` contexts with operator-product sign, violation status, and central-doily incidence count. |
| `violated_75.csv` | Annotated CSV of all `75` violated contexts grouped into the `15` central doily lines and the `15` four-line external generator stars. |
| `hyperbolic_quasi_quadric_135.json` | Complete machine-readable JSON bundle including the full `135 / 1,095 / 75` dataset, ovoid relation to $Q^+(7,2)$, and exact $Sp(2N,2)$ witness isomorphism certificates for $Q^-(7,2)$, $W(7,2)$, and $Q^+(9,2)$. |

## Geometric Summary of the `75 = 15 + 60` Violated Contexts

1. **Ambient hyperbolic quasi-quadric ($135$ points, $1,095$ contexts):** Every observable commutes with exactly `70` other observables in $S_B$ (matching the point count `135` and commutation regularity `70` of $Q^+(7,2)$). $S_B$ is obtained from the hyperbolic quadric $Q^+(7,2)$ by flipping the $Y$-parity of the five affine $AG(3,2)$ fibers (`IXII, XXII, XIXI, XIIX, XIXX`) whose unique symplectic poles in the central doily (`ZIII, ZZII, IZZI, IZIZ, IZZZ`) form a **5-point ovoid** of the central doily.
2. **Central doily (`15` points, `15` violated lines, all `+I`, degree-triple `(7,7,7)`):** The `15` pure-$Z$ observables $D_{15} \cong PG(3,2)$ carry `35` ambient lines in $S_B$, of which `15` are violated and `20` are satisfied. Those `15` violated lines form an exact doily $W(3,2) = GQ(2,2)$ embedded as a linear symplectic line complex inside $D_{15}$.
3. **Arrangement of the remaining `60` violated lines (`48` `+I`, `12` `-I`, all degree-triple `(1,1,7)`):**
   - Every external violated line meets the central doily $D_{15}$ in **exactly one point** $p \in D_{15}$ and carries **two external observables of violated degree `1`** (`60 * 2 = 120`, zero overlaps among external points).
   - Through **each** of the `15` central-doily points $p \in D_{15}$ pass **exactly `4`** of the `60` external violated lines (`15 * 4 = 60`).
   - The `8` external observables on the `4` violated lines through $p$ all share a single constant nonzero $X$-support $a(p)$, pairwise commute (`28/28` pairs), and together with the 7-point Fano plane $p^\perp_{\text{doily}}$ (the three central-doily lines through $p$) form a **maximal totally isotropic $PG(3,2)$ generator $G_p \subset S_B$** (`15` points, `35` ambient lines).
   - Inside each generator $G_p$, the `7` violated lines (`3` central-doily lines + `4` external lines) are literally the **complete 7-line star of $p$ in $G_p$** — equivalently, the `4` external lines partition $G_p \setminus D_{15} \cong AG(3,2)$ into its `4` parallel affine lines concurring at the point at infinity $p$.

Regenerated deterministically by `python tracks/spectral-bounds/scripts/quasi_quadric_and_witness_anatomy.py`.
