# Additional knot literature screened, 26 October 2026

These are source checks, not new factorization results. The three executed
calculations in this packet have priority over untested analogies.

## Arborescent tensor networks

Amena Al Rawi, Hisham Sati and Vivek Kumar Singh,
*A TQFT-based Platform for Efficient Computation of Knot Invariants*,
[arXiv:2607.23551v1](https://arxiv.org/html/2607.23551v1), §§2–3,
gives a concrete tree-contraction implementation. Its leg and propagator
formulas sum over the color-dependent internal states. Twist integers appear
as powers of supplied braiding eigenvalues. The implementation distinguishes
two independent internal indices; identifying them is a special construction,
not an automatic simplification of the general invariant. Some tensor
derivations are deferred to a companion work. The reported benchmarks concern
knot-invariant calculations, not integer factorization.

**Our applicability test.** Binary twist exponents can be cheap once their
eigenvalues and finite fusion data are acquired. To exploit that here, we
would still need an explicit tree with an acquired, sufficiently small state
space whose scalar equals the native collision prefix up to certified units.
Neither a compact drawing nor a binary twist label establishes that identity.
The finite Racah calculation in this packet tests one such small-state route
and retains the terminal kernel. The new platform is a useful implementation
reference if a valid native tree construction is found; it does not itself
supply the missing construction or its finite-ring normalization.

## Periodic knots and cyclic resultants

Jonathan A. Hillman, Charles Livingston and Swatee Naik,
*Twisted Alexander polynomials of periodic knots*,
[Algebraic & Geometric Topology 6 (2006), 145–169](https://msp.org/agt/2006/6-1/agt-v6-n1-p05-p.pdf),
Theorems 1–5, gives product and congruence constraints under actual knot
periodicity, together with twisted analogues requiring a lifted quotient
representation. James F. Davis and Charles Livingston,
*Alexander polynomials of periodic knots*,
[primary paper](https://jfdavis.pages.iu.edu/papers/dliv1.pdf), §§1–2,
studies necessary conditions and realization under additional hypotheses.

**Our applicability test.** No periodic action of the required order or
quotient representation has been acquired for the native sparse Seifert
model. Substituting a large-order arithmetic clock into a polynomial does
not establish either hypothesis. Thus these are conditional construction
leads, not currently licensed norm shortcuts. Their complete root-of-unity
products must also be distinguished from a partial native geometric orbit.

Hillar–Levine,
[*Polynomial recurrences and cyclic resultants*](https://arxiv.org/abs/math/0411414),
was re-encountered in this search. It was already audited in
`semiprime-knot-advancement-20261025/alexander-realization.md` and is not
counted as a new lead or a new result here.

## Priority after this pass

For a further knot calculation, request an initialized, zero-preserving
identity for the retained fusion correction, with a concrete cost on the
acquired root list. For an arithmetic calculation, request simultaneous
square-point acquisition or safe interval selection for the explicit
Euclidean conics. Neither task is discharged by another determinant or
representation alone.
