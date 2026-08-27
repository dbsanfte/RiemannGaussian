# RiemannGaussian

## Project and build

RiemannGaussian is a research project whose goal is a completely formal,
`sorry`-free proof of the Riemann hypothesis. The repository contains the
developing proof in Lean, together with exact rational certificates used to
test and calibrate parts of the argument. The proof is not complete: every
claim described as proved below is checked by Lean, while the remaining
research frontier is stated explicitly.

The project currently uses Lean 4.33.1 and Mathlib 4.33.1. From the repository
root:

```bash
lake exe cache get
lake build --wfail
```

GitHub Actions runs the same warning-as-error build on every pushed proof
slice and rejects any Lean source containing `sorry` or `admit`.

## Formalized progress

The project has two connected lines of attack: a Gaussian--Weil positivity
reduction and a finite Hardy/Gram--Weil defect theory. The following is the
current checked state, not a list of conjectural steps.

### Gaussian--Weil and the explicit formula

- Lean proves that Mathlib's `RiemannHypothesis` is equivalent to reality of
  all nontrivial zeta zeros in the rotated spectral coordinate
  `A(z) = xi(1/2 - i*z)`.
- Multiplicity-aware canonical translated and symmetric Gaussian zero sums
  are constructed unconditionally. Their convergence follows from a checked
  growth bound for the pole-cleared xi function.
- The xi contour argument, zero-separated truncations, logarithmic-derivative
  bounds, and limiting passage are formalized. Consequently the canonical
  symmetric zero sum is proved equal, for every positive width and every real
  center, to the arithmetic Gaussian explicit formula.
- Nonnegativity of that common value at every positive width and real center
  is proved equivalent to the Riemann hypothesis. Heat propagation and a
  cofinal-width theorem reduce all-width positivity to positivity along an
  unbounded family of widths.
- The arithmetic expression is decomposed exactly into endpoint, prime, and
  Archimedean terms. Lean proves the high-prime tail estimates, Abel
  identities, continuous-PNT cancellation, digamma transform, and the
  Gaussian/Suzuki curvature identity used by the current transport attack.
- A sound certificate architecture is formalized: an unbounded family of
  valid certificates would imply RH. The exact rational ledgers at widths
  `0.04`, `0.05`, and `0.06` are checked as calibration artifacts; they
  are not being treated as a scalable certificate ladder.
- The Suzuki hinge/Legendre route has been reduced to explicit transport gaps
  and cumulative prime-versus-curvature surplus inequalities. The finite
  shift, slope reset, cell recurrence, and telescoping identities are checked.

### Finite Hardy and Gram--Weil theory

- For a separable real polynomial `A`, Lean develops the homotopy
  `E_eta = A + i*eta*A'`, including coprimality, degree preservation, exact
  upper/lower root factors, conjugation symmetry, and unconditional
  upper-half-plane root-count invariance for positive `eta`, including through
  multiple-root collisions.
- The corresponding finite Krein--Langer factorization is constructed
  algebraically. Its rational model spaces are then realized as genuine
  closed finite-dimensional subspaces of boundary `L²(R, C)`.
- The actual Hardy cross angle, orthogonal projections, residual Cauchy
  kernels, and two-node Gram matrices are identified. Lean proves the exact
  basis-independent determinant identity
  `det(I - C† C) = |S(w0) * S(w1)|²` in the degree-two case.
- In arbitrary finite dimension, Lean now proves the corresponding weighted
  Gram theorem: whenever a complete basis is made of root Cauchy vectors,
  `det(I - C† C) = |∏ᵢ S(wᵢ)|²`. This theorem does not assume distinct
  singular values; its explicit basis hypothesis leaves the repeated-root
  construction open rather than hiding it.
- When the upper root factor is separable, Lean constructs that complete
  Cauchy basis at every degree from all distinct upper roots and obtains the
  product formula with no basis hypothesis. The proof includes the full
  polynomial linear-independence, boundary-map injectivity, and dimension
  count.
- For repeated roots, Lean now constructs the full multiplicity-indexed
  confluent quotient basis of the algebraic model. Each coordinate is proved
  to be the literal higher-order inverse-power kernel, partial-fraction
  uniqueness proves independence, and the multiplicity sum proves
  completeness. Lean also realizes every such kernel in boundary `L²` and
  transports the family to a complete basis of the actual negative Hardy
  subspace, without a separability hypothesis. Multiplication by the residual
  inner function is now proved, for every negative-model coordinate at once,
  to land in the orthogonal complement of the entire positive model. The
  Sylvester projection decomposition, triangular residual law, and determinant
  are the remaining confluent steps.
- The abstract Gram--Weil block defect and metric-pencil algebra are checked,
  including exact finite-dimensional inertia and the complete one-pair model.
- For an even polynomial containing one symmetric off-axis quartet, Lean
  derives the relevant reflected roots and logarithmic-derivative pole
  equations from structure rather than assuming them. In the isolated
  quartic case, the strict Hardy determinant bound is proved end to end with
  no background-sign, root-count, or reflection hypothesis left open.
- The exact multiplicity-counted identity
  `-eta*A'(z)/A(z) = sum_w -eta/(z-w)` is formalized. It proves the required
  background sign for arbitrary additional real roots.
- For additional off-axis conjugate pairs, Lean factors the imaginary
  contribution exactly. At positive weight it is negative if and only if
  the candidate pole lies strictly inside the pair's Euclidean influence
  disk. Any finite upper-root multiset is partitioned, with multiplicity,
  into outside- and inside-disk parts; the outside contribution is proved
  nonnegative and every negative total budget transfers to the inside core.
- For an arbitrary finite collection of equal-height, equal-weight pairs,
  binary hyperbolic-cost superadditivity is lifted to a multiplicity-aware
  product theorem. With at least two genuine radii, a unit collective pole
  budget forces their complete product strictly below the exact one-pair
  threshold.
- The unequal-height extension is also checked. Replacing all heights by any
  common positive lower bound dominates the true weighted costs. For an exact
  finite polynomial root decomposition and a root of `E_eta`, Lean transfers
  the full unit pole budget past the nonnegative real roots into the
  inside-disk core and, when that core has at least two members, proves its
  complete radius product strictly below the corresponding threshold.

### Formal integrity

- The library builds with warnings and Lean lints treated as errors.
- CI rejects `sorry` and `admit` before building.
- The current frontier theorems have been audited with `#print axioms`; they
  depend only on Lean's standard `propext`, `Classical.choice`, and
  `Quot.sound` axioms.
- Numerical and symbolic experiments may guide research, but they do not
  count as progress until the corresponding statement is proved in Lean.

## Proof architecture and current frontier

The Gaussian route has reached a clean RH-strength statement:

```text
for every epsilon > 0 and every real t,
gaussianArithmeticExplicitFormula epsilon t >= 0.
```

Everything connecting this statement to the canonical zero sum and then to
RH is formalized. What remains is a scalable proof of the positivity itself.
The leading arithmetic approach is the Suzuki transport formulation; its
open obligations are the explicit tail normalization and the uniform
cumulative-surplus lower bound over all cutoffs.

The Hardy route seeks a structural contradiction from any off-axis xi zero.
The one-quartet finite theory and its real/Herglotz background are formalized.
The unequal-height finite hyperbolic optimization and its exact-polynomial
inside-core specialization are now formalized, as is the higher-index Hardy
determinant formula conditional on a complete root Cauchy basis. The immediate
frontier is to turn the exact Sylvester numerator decomposition into the actual
orthogonal projection decomposition, then prove the triangular residual law
for the now-checked complete boundary confluent basis and derive its
determinant. It must then be joined to the structural inside-core selection.
Beyond that lies the genuinely analytic passage from finite polynomial models
to the entire xi function.

Neither frontier is assumed. Closing the Gaussian positivity statement, or
completing the finite-to-xi Hardy route, is the RH-level part of the project.

## Repository guide

- [`RiemannGaussian/GaussianZetaBridge.lean`](RiemannGaussian/GaussianZetaBridge.lean)
  develops the spectral Gaussian/RH bridge.
- [`RiemannGaussian/GaussianXiLogDerivativeGrowth.lean`](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean)
  closes the xi contour and arithmetic explicit-formula identification.
- [`RiemannGaussian/GaussianPositivityCertificate.lean`](RiemannGaussian/GaussianPositivityCertificate.lean)
  contains the scalable certificate soundness and cofinal-width reductions.
- [`RiemannGaussian/SuzukiTransportBarrier.lean`](RiemannGaussian/SuzukiTransportBarrier.lean)
  and [`RiemannGaussian/SuzukiTransportTail.lean`](RiemannGaussian/SuzukiTransportTail.lean)
  contain the current hinge/Legendre transport reduction.
- [`RiemannGaussian/PairHyperbolicEnergy.lean`](RiemannGaussian/PairHyperbolicEnergy.lean)
  and the `SymmetricQuartet*` files contain the quartet energy and defect
  argument.
- The `FiniteE*`, `FiniteRoot*`, `FiniteModel*`, and `FiniteHardy*` files build
  the finite Krein--Langer and boundary-Hardy realization.
- The `GramWeil*` files contain the abstract block defect, inertia, and metric
  pencil theory.
- [`RiemannGaussian.lean`](RiemannGaussian.lean) is the umbrella module built
  by the default target.

This repository should be read as an active formal research program. Git
history records the fine-grained proof audit; this README records the purpose,
the checked mathematical state, and the exact open frontier.
