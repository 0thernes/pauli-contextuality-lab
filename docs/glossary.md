# Glossary

## Finding Taxonomy (Build Standard v1.2.0, Rule R7)

Every finding across issues, audits, and reviews is classified as exactly one of these ten mutually exclusive classes:

| Class | Definition |
|---|---|
| **bug** | A defect in program logic: the code runs but does something different from its specification or intent. |
| **error** | A wrong artifact or failed execution outside program logic: an incorrect number, claim, doc, config, version, build, or command. |
| **issue** | A weakness in something that exists: it works and is not wrong, but is unclear, inconsistent, fragile, or hard to maintain. |
| **problem** | An external obstacle that blocks progress and is not caused by the project's own code or artifacts. |
| **concern** | A risk that has not caused harm yet: something that could fail, mislead, cost money, or create security or legal exposure later. |
| **dilemma** | A trade-off between two or more valid options where the right choice depends on the owner's priorities. |
| **conflict** | Two requirements, sources, or rules contradict each other, so satisfying one violates the other. |
| **gap** | Something required or expected is missing: a file, feature, doc, or standard item does not exist yet, while nothing present is wrong. |
| **hole** | A missing check or safeguard: a path that nothing verifies or protects, so a defect could get through unnoticed. |
| **blindspot** | Something outside current attention: a user, platform, failure mode, or assumption nobody has examined yet, so what is wrong there is unknown. |

## Domain Vocabulary (Pauli Contextuality & Formal Verification)

- **Context (Pauli):** Three mutually commuting non-identity $N$-qubit Pauli observables whose product is $\pm I$. A classical $\pm 1$ assignment *violates* a context if the product of assigned values disagrees with the operator sign.
- **Contextuality degree $d(S)$:** The minimum number of contexts of an observable configuration $S$ violated by any noncontextual assignment $f: S \to \{\pm 1\}$.
- **Symplectic polar space $W(2N-1,2)$:** The geometry of all $4^N - 1$ non-identity $N$-qubit Pauli observables and their commuting triples (lines / contexts), isomorphic to isotropic lines of $\mathbb{F}_2^{2N}$ under the symplectic commutator form.
- **Hyperbolic / Elliptic quadrics $Q^+(2N-1,2)$ and $Q^-(2N-1,2)$:** The subsets of symmetric (real, even number of $Y$ factors) and antiunitary-commuting observables inside $W(2N-1,2)$.
- **Hoggar / Spectral floor bound:** The third-moment inequality $\beta \le (n-2)|S|^{3/2} / (6\sqrt{n-1})$ bounding satisfied minus violated contexts via Okumura's maximal-skewness lemma, attained on $W(5,2)$ by the Hoggar SIC fiducial state ($n=D=2^N$, or $n=D/2$ under Kramers doubling).
- **Flat state / Floor-saturating configuration:** A pure quantum state whose non-zero Pauli expectation values all share a single modulus; saturation of the spectral floor is proved equivalent to flatness (`saturation_tfae`).
- **Jonah's Conjecture E:** The conjecture (B. W. Jonah, Zenodo preprint, Oct 2026) that in every vertex case of the hyperplane-carrier classification ($N \ge 4$), two sign carriers can share identical carrier characteristic polynomials while their full completions have distinct spectra.
- **Case C3 binary completion optima:** For the four-qubit C3 cospectral pair $(\sigma_0, \sigma_1)$, the exact minimum number of violated outside contexts over all binary completions: `368` vs `344` (gap `24`).
- **Disjoint Mermin full context family:** Given $k$ disjoint copies of the Peres-Mermin square (or Mermin pentagram), all nonempty unions choosing at most one local context from each copy; exact degrees $(7^k - 5^k)/2$ and $(6^k - 4^k)/2$.
- **Sequential contextuality evidence (e-process / wealth martingale):** An adaptive nonnegative betting process with conditional expected factor $\le 1$ under the noncontextual null, guaranteeing finite-horizon stopping-time validity $\Pr(\text{wealth} \ge T) \le 1/T$ when calibrated to the true conditional setting floor $\beta$.
- **Statement fidelity:** Whether a Lean 4 formal statement accurately encodes the intended mathematical definition in the published literature without hidden extra assumptions or vacuity.
