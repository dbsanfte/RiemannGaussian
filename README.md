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
  to land in the orthogonal complement of the entire positive model. The exact
  Sylvester numerator decomposition is also proved to be the genuine boundary
  `L²` orthogonal-projection decomposition, so its first coordinate is exactly
  the Hardy projection residual before the isometric inner multiplier. Lean
  now also proves the lower-triangular Sylvester comparison law and computes
  the residual-coordinate determinant as both a quotient of resultants and a
  product of inner values over the upper-root multiset. Thus repeated roots
  are counted with their full algebraic multiplicity, with no separability
  hypothesis. This determinant is transported through the actual boundary
  realization and residual-inner isometry, proving the unconditional
  complement Gram formula
  `det(I - C† C) = |∏ S(w)|²` for the complete upper-root multiset. Lean also
  proves that any chosen upper-root occurrence controls the complete square-
  root determinant by `sqrt(det(I - C† C)) ≤ |S(w)|`, since every remaining
  factor is contractive. A denominator-free Schwarz--Pick contraction for
  `S` at arbitrary upper-half-plane points is derived directly from the
  positive `2 × 2` Pick matrix and exact norm-square identities. Combining
  this with `S(alpha) = -B(alpha)` at every base root proves the root-level
  bridge
  `sqrt(det(I - C† C)) ≤ 2*rho(z,alpha)/(1 + rho(z,alpha)^2)`
  for every upper root `z` of `E` and upper-half-plane root `alpha` of `A`.
- The root-multiset decomposition is connected directly to that Pick bridge:
  every occurrence in the inside influence-disk core is proved to be a
  genuine base zero and carries the exact interpolation identity and both
  Schwarz--Pick inequalities. The same theorem packages those data beside
  the strict complete core-radius product bound while keeping the core and
  determinant products logically distinct.
- The sharp scalar terminal step for the collective comparison is also
  checked. A common radial disk automorphism converts a `2*R` difference
  estimate, where `R` is the complete zero-radius product, into exactly
  `2*R/(1+R^2)`; the denominator is not lost to a triangle estimate.
- The common transform of `-S` and `B` is now represented by explicit
  numerator and denominator polynomials. Separability proves that the
  inside-core nodes are distinct, their interpolation identities make every
  node a literal numerator root, and Lean proves that the complete core-root
  polynomial divides the transformed difference numerator.
- Lean proves a rational maximum principle on the closed upper half-plane:
  a polynomial quotient with no closed-half-plane poles and numerator degree
  at most its denominator degree inherits every uniform real-boundary norm
  bound. This is the analytic engine for the remaining factored-quotient
  estimate. For the actual finite common transform, Lean now proves the
  required pole exclusion and degree inequality and derives its global
  unfactored norm bound.
- The complete inside-core factor is now cancelled rigorously. Its reflected
  polynomial has the same degree and unit real-boundary norm; the residual
  quotient satisfies the maximum principle, and Lean obtains the exact
  collective transformed-difference bound `2 * ∏ rho` with every core
  occurrence retained.
- At an actual upper root of the finite homotopy, the collective estimate is
  now fed through the sharp radial disk-automorphism identity. Combining it
  with the strict hyperbolic-energy threshold proves the closed residual-inner
  bound and the corresponding strict bound for the unconditional confluent
  Hardy complement-Gram determinant.
- The first finite-to-entire limiting bridge is checked. Locally uniform
  convergence of holomorphic functions transports locally uniformly through
  `f ↦ f + i*eta*f'`, and any convergent sequence of zeros of the finite
  polynomial homotopies is proved to limit to a genuine zero of the analytic
  homotopy. This is deliberately one-way: it assumes the approximating real
  polynomials and the convergent finite roots, rather than silently invoking
  either their existence or converse root persistence.
- For the reverse root-matching direction, Lean now verifies an explicit
  alternative to invoking Hurwitz. A vanishing real affine correction pins a
  prescribed upper-half-plane zero of `f + i*eta*f'` into every finite
  homotopy while preserving locally uniform convergence to `f`. Thus the
  chosen homotopy root need not be selected from drifting finite root sets.
  Separability and control of the corrected base-root multisets remain open.
- The real-polynomial approximation premise is now discharged for spectral
  xi itself. Lean proves the conjugation laws for the real Gamma factor, the
  pole-cleared xi normalization, and spectral xi; hence spectral xi is entire
  and real on the real axis. Its explicit real Taylor polynomials are proved
  to converge locally uniformly on the whole complex plane. Applying the
  vanishing affine correction gives an explicit real-polynomial sequence
  which still converges to xi and whose finite homotopies all contain any
  prescribed limiting upper homotopy root exactly.
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
determinant formula conditional on a complete root Cauchy basis. The complete
finite confluent determinant is now unconditional, including repeated roots.
The collective finite Hardy chain is now composed through its strict
determinant conclusion. The complete core product is used directly and is not
identified with the determinant product by assumption. A first analytic
passage is now formalized: homotopies converge locally uniformly and limits of
convergent finite roots are genuine roots of the limiting homotopy. Exact
vanishing affine corrections also pin a prescribed limiting homotopy root
into every corrected approximant without changing the locally uniform limit.
Explicit real Taylor approximants to spectral xi are now constructed and
proved locally uniform, so that approximation premise is closed. The next
Hardy frontier is to obtain separable corrected models with controlled
base-root multisets and then pass the finite strict defect mechanism through
that limit.

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
- [`RiemannGaussian/FiniteToEntireHomotopy.lean`](RiemannGaussian/FiniteToEntireHomotopy.lean)
  begins the checked locally uniform passage from finite homotopies to xi.
- [`RiemannGaussian/FiniteToEntireRootPinning.lean`](RiemannGaussian/FiniteToEntireRootPinning.lean)
  gives the exact vanishing affine correction for a prescribed homotopy root.
- [`RiemannGaussian/FiniteToEntireRealApproximation.lean`](RiemannGaussian/FiniteToEntireRealApproximation.lean)
  constructs the locally uniform real Taylor approximants to spectral xi.
- The `GramWeil*` files contain the abstract block defect, inertia, and metric
  pencil theory.
- [`RiemannGaussian.lean`](RiemannGaussian.lean) is the umbrella module built
  by the default target.

This repository should be read as an active formal research program. Git
history records the fine-grained proof audit; this README records the purpose,
the checked mathematical state, and the exact open frontier.
