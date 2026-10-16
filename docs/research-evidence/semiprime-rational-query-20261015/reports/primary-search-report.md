# Positive literature search for aggregating the sparse actual-sector remainder

2026-10-15. Fresh primary-source search; no repository edits/builds. The full soft O(J+sqrt L) row-product or arbitrary-weight evaluator was not found. A useful positive fixed-coefficient-stream subroutine is isolated separately in selected-qbinomial-primitive.md.

## Positive result that IS applicable

The ONE q-binomial coefficient stream of P_L(Z;q) has a first-order degree-one rational recurrence. Unlike the family of changing-target row recurrences, up to J~sqrt L selected terms of this COMMON stream can be acquired together in soft O(sqrt L+J), using the several-index q-holonomic idea of Bostan–Yurkevich §3.4. The separate report gives a direct ring-safe construction, arbitrary indexed refinement by monic remainder trees, one batch unit inversion and full bit/index charging. At k=L no zero numerator is included. Actual local q orders>L license all denominators. This removes a possible false charge of J separate sqrt L computations in a future residue/boundary formula.

What remains missing is an exact actual-source certificate reducing the weighted sector expression to O(m) such discrete coefficient queries and cheaply acquired coefficients. Parameter-continuation jets, poles indexed by unknown local discrete logarithms, or the row products themselves are not supplied by this subroutine. Root/parallel algebra may independently rule out particular whole-operator certificates; no such no-go is inferred merely from this literature search.

## Rational reduction: what the primary theorem actually permits

Rong-Hua Wang and Michael X.X. Zhong, *q-Rational Reduction and q-Analogues of Series for pi*, arXiv:2203.16047v2 (July31,2022):
https://arxiv.org/abs/2203.16047
Fresh PDF/text saved as q-rational-2022.*.

Section2 explicitly works over C with0<|q|<1. Theorem3.1 describes necessary denominator structure using shift-free conditions for ALL nonnegative shifts. At actual finite order R, gcd(B(x),B(q^(R)x))=gcd(B,B), so the stated infinite shift-free condition fails for every nonconstant B. Theorem3.3 gives rational reduction using shifted-product denominators, whose degree grows with the shift length. It is not an algorithm acquiring the actual finite-ring aggregate with a degree/output-independent bound. Individual algebraic identities can still be specialized when every necessary division is licensed; the theorem cannot simply be imported unchanged at a root of unity.

Qing-Hu Hou and Guo-Jie Li, *Gosper Summability of Rational Multiples of Hypergeometric Terms*, arXiv:2105.05567:
https://arxiv.org/abs/2105.05567
Fresh PDF/text saved as gosper-multiples-2021.*. It analyzes numerator/denominator structure of rational multiples and includes q-analogues. Such summability/identity structure is useful for searching a certificate, but is not a nearlinear evaluator for arbitrary supplied target phases or an automatic composite-ring singularity rule.

## Boundary poles require an explicit finite-sum interpretation

Sergei Abramov and Marko Petkovsek, *Gosper's Algorithm, Accurate Summation, and the Discrete Newton–Leibniz Formula*, ISSAC2005, DOI10.1145/1073884.1073888:
https://users.fmf.uni-lj.si/petkovsek/gasRevised.pdf
Fresh author PDF/text saved as accurate-summation-2005.*. The paper assumes a characteristic-zero field and gives precise sufficient conditions for finite summation when certificates/recurrences have integer singularities; factoring a polynomial may enlarge a safe interval. Its results are not permission to cancel a zero factor at a pole or divide by a nonunit modulo N. A composite-safe use must provide a cleared polynomial identity, the exact boundary/regularization data and paid unit/factor checks.

Carlos Arreche and Hari Sitaula, *A computational approach to rational summability and its applications via discrete residues*, arXiv:2503.15636 / JSC DOI10.1016/j.jsc.2025.102552:
https://arxiv.org/abs/2503.15636
Fresh PDF/text saved as discrete-residues-2025.*. It treats additive-shift rational summability over a computable characteristic-zero field. It computes rational residue representations without a full partial-fraction decomposition, but requires an autodispersion black box. The introduction expressly does not claim a complete worst-case complexity analysis. This does not supply a q-root-of-unity composite-ring evaluator or the required target dependence at soft O(m).

## Why the geometric clustering does not trigger a found theorem

The actual z_j=gamma^(-N-delta_j), with delta in a band of width4m², lie in a sparse subset of a length-O(m²) GEOMETRIC progression for base gamma. Their q-product step is q=gamma^(m²), not gamma. A numeric exponent band is not an analytic/nilpotent cluster: no absolute-value proximity or small nilpotent difference follows over Z/N. Floating-point clustered-node algorithms therefore do not specialize directly.

Completing to every gamma-grid node yields O(m²) outputs/input slots, outside the desired soft O(m) clock. Existing exact geometric multipoint methods charge the represented polynomial degree or full grid size. The q-Gosper papers above do not state a theorem replacing that charge by sqrt L+J for this sparse clustered target set. This is an interface mismatch, not a lower bound against a future sparse-grid algorithm.

The classical square-root isogeny/resultant literature also uses structured additive index decompositions but still requires the relevant index sets/resultant inputs to be acquired. No primary theorem found in this focused search evaluates the sparse actual exponential-polynomial resultant without that input cost. Recent general resultant formulas or sparse interpolation results assume explicit coefficient data or an evaluation black box; treating the desired long norm as that black box would be circular.

## Exact scope

This search adds a rigorously costed selected-coefficient primitive and clarifies four relevant summation interfaces, including the2025 paper. It does not repeat the old finite-Laurent, cyclic-singularity or branch-packet obstructions as new results. No completeness claim about all literature is made. The missing positive theorem is still a restriction-stable exact scalar/weighted aggregate with all source phases, rational poles and proper-factor recovery paid at soft O(m).
