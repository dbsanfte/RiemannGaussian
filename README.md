# RiemannGaussian

## Project and build

RiemannGaussian is a research project whose goal is a completely formal,
`sorry`-free proof of the Riemann hypothesis. The repository contains the
developing proof in Lean, together with exact rational certificates used to
test and calibrate parts of the argument. The proof is not complete: every
claim described as proved below is checked by Lean, while the remaining
research frontier is stated explicitly.

**Research environment:** [GPT-5.6 Sol](https://developers.openai.com/api/docs/models/gpt-5.6-sol)
with **Max** reasoning effort, running in the **Codex CLI harness**.

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
  Subsequent checked perturbations make these models separable; quantitative
  control of their base-root multisets remains open.
- The real-polynomial approximation premise is now discharged for spectral
  xi itself. Lean proves the conjugation laws for the real Gamma factor, the
  pole-cleared xi normalization, and spectral xi; hence spectral xi is entire
  and real on the real axis. Its explicit real Taylor polynomials are proved
  to converge locally uniformly on the whole complex plane. Applying the
  vanishing affine correction gives an explicit real-polynomial sequence
  which still converges to xi and whose finite homotopies all contain any
  prescribed limiting upper homotopy root exactly.
- Every real base polynomial now has a canonical, multiplicity-preserving
  decomposition into real-axis roots and conjugate pairs represented by
  their upper-half-plane members. Lean also checks the exact degree count
  `#real + 2 * #upper = degree` and proves that the upper multiset has no
  repetitions whenever the polynomial is separable. Thus the qualitative
  root-decomposition premises of the finite Hardy estimates are discharged
  canonically. The complete product, residual-inner, and determinant
  conclusions are now stated directly for this canonical influence core.
  Its nonemptiness is automatic, and every core root lies strictly above the
  fixed pinned height. Thus `z.im` is a common lower bound across the entire
  approximating sequence, rather than a stage-dependent minimum.
- The separability gap for root-pinned approximants is now closed. Lean
  constructs explicit quadratic and cubic perturbations in the kernel of
  homotopy evaluation at the prescribed root. A nonzero Wronskian reduces
  every nonseparable pencil parameter to an explicit finite set; choosing
  vanishing parameters outside those sets yields separable real polynomials
  converging locally uniformly to spectral xi while retaining the same exact
  upper homotopy root in every finite model.
- The canonical inside influence core at every such finite homotopy root is
  now proved nonempty and carries the full imaginary pole budget `≤ -1`.
  A nonaligned singleton satisfies the strict one-pair threshold, leaving
  only a vertically aligned singleton as the equality geometry. More
  importantly, a cardinality-free cost theorem covers that equality case and
  proves the uniform bound
  `sqrt(det) ≤ eta / sqrt(eta^2 + z.im^2) < 1`
  for every approximant. The finite singleton and uniform-height obstructions
  are therefore closed. Convergence and identification of these varying
  finite Hardy determinants in the entire limit remains open.
- The positive-homotopy-root premise is now discharged under failure of RH.
  Lean proves that `¬RH` gives an upper spectral-xi zero. A multiple zero is
  fixed by every homotopy, while at a simple zero the local analytic inverse
  of `i*xi/xi'` supplies an upper root of `xi + i*eta*xi'` for some positive
  real `eta`. Thus `¬RH` now produces the complete separable, root-pinned
  canonical finite Hardy frontier sequence without an assumed starting root.
- The fixed meromorphic quotient `Theta_eta = E_eta^sharp/E_eta` is now
  constructed in the entire setting. Lean proves that its finite polynomial
  counterparts converge locally uniformly on every open region where the
  limiting homotopy has no zero, and verifies that the spectral-xi numerator
  is the literal conjugate reflection of `E_eta`. Passing through the pinned
  zero still requires the global Krein--Langer cancellation and remains open.
- Compactness now extracts a convergent subsequence of the fully cancelled
  finite residual-inner values at the fixed pinned root. Its scalar limit
  retains the explicit uniform gap
  `norm(s) <= eta / sqrt(eta^2 + z.im^2) < 1`, while the same finite sequence
  has the locally uniform theta limit away from homotopy zeros. The scalar is
  not yet proved independent of the subsequence or identified with a
  spectral-xi arithmetic invariant; that identification is the active
  rigidity frontier.
- The logarithmic pseudo-hyperbolic defect now has an exact Gaussian
  proper-time representation in Lean. For two distinct upper-half-plane
  points, the truncated integral of a positive heat-kernel difference tends
  to `-2 log rho`. This is lifted with full multiplicities to finite root
  multisets, where the limiting heat mass is exactly `-2 log` of the complete
  radius product. For every canonical finite Hardy core, that mass is bounded
  below by one fixed positive threshold defect. Consequently failure of RH
  produces a root-pinned approximating sequence carrying these uniformly
  positive finite heat frontiers at every stage. Passing those varying heat
  actions to an arithmetic or entire limiting object remains open.
- At each fixed positive proper time, Lean now constructs the complete
  multiplicity-counted upper spectral-xi heat sum and proves its absolute
  convergence from the unconditional Gaussian zero bound. Every coefficient
  is identified with the heat-weighted local residue of the genuine spectral
  xi logarithmic derivative, rather than assigned a formal zero weight. The
  sum is nonnegative, any upper spectral zero makes it strictly positive, and
  its vanishing for all upper observation points and positive times is proved
  equivalent to RH. Canonical finite spectral windows, including a concrete
  sequence with zero-free boundaries, are proved to converge to this sum in
  their literal logarithmic-residue form; RH is also equivalent to every such
  finite window vanishing. What remains open is convergence of the varying
  finite Hardy heat sums to these spectral windows and a global arithmetic
  evaluation of the complete sum.
- On every zero-free open region, Lean now proves locally uniform convergence
  of the root-pinned polynomial logarithmic derivatives to the genuine
  spectral-xi logarithmic derivative. On each compact zero-free subset the
  approximants are eventually zero-free, and their logarithmic-derivative
  circle integrals converge to the xi circle integral. These results apply to
  the same exact finite Hardy sequence forced by failure of RH.
- On the finite side of that step, Lean proves the full polynomial argument
  principle on a circle: when the boundary is root-free, the integral of
  `p'/p` is exactly `2*pi*i` times the number of roots in the disk, counted by
  the polynomial root multiset with algebraic multiplicity. The proof expands
  every Cauchy kernel and checks its inside/outside circle integral directly.
- Combining those results, Lean now proves genuine local multiplicity
  stability. For every circle avoiding the spectral-xi divisor, the number of
  roots of any globally locally-uniform real-polynomial approximating net is
  eventually constant, and the limiting xi logarithmic-derivative integral is
  exactly that stabilized natural number times `2*pi*i`. In particular, this
  holds simultaneously for every zero-free circle along the same root-pinned
  canonical Hardy sequence forced by failure of RH. The discreteness passage
  is explicit: convergence of fixed positive multiples of natural numbers is
  proved to force eventual equality, rather than assumed from an informal
  argument-principle limit.
- Lean now identifies those local counts with the actual analytic divisor at
  every spectral-xi zero. A direct local argument principle isolates any
  finite-order analytic point and proves that its logarithmic-derivative
  circle integral is its analytic order times `2*pi*i`. Therefore each zeta
  zero has a fixed isolating ball in which the approximating polynomial root
  multiset eventually has exactly the genuine analytic zeta multiplicity.
  This holds for every zeta zero along the same root-pinned canonical Hardy
  sequence forced by failure of RH; no simplicity assumption is made.
- The local divisor passage is now assembled over arbitrary finite families.
  Lean chooses pairwise disjoint isolating balls and synchronizes all exact
  multiplicity counts. For any continuous real weight, the weighted sum over
  the full polynomial root multiset in one isolating ball converges to the
  analytic multiplicity times the weight at the limiting xi zero. Applying
  this to the fixed-proper-time upper-half-plane heat kernel proves that every
  finite upper spectral-xi heat window is the limit of literal heat sums over
  pairwise disjoint polynomial-root clusters. Under `¬RH` this convergence
  holds along the same root-pinned canonical Hardy sequence. This is a
  bounded-window result; it asserts neither uniform control of roots outside
  the selected clusters nor a complete-window tail limit.
- The canonical Hardy influence core is now connected to the complete
  polynomial upper divisor with algebraic multiplicity, not merely as a set
  of root locations. At every positive proper time its fixed-time heat sum is
  bounded by the full upper-divisor heat sum, and the same domination is
  proved for positive truncated actions and limiting logarithmic heat masses.
  Consequently the root-pinned sequence forced by `¬RH` has strictly positive
  full upper-divisor heat sums at every stage and time, while its full masses
  retain the same explicit stage-independent lower bound as the Hardy cores.
  This does not yet give a uniform positive lower bound at one fixed time.
- The bounded spectral clusters are now placed inside that common full
  divisor exactly. Their isolating radii are chosen below the centers'
  positive heights, so the entire multiplicity-counted cluster union is an
  upper-root submultiset. At fixed positive time, Lean proves the identity
  `full polynomial heat = convergent xi-window cluster heat + nonnegative
  unused-root remainder`. For any proposed full limit `L`, convergence of the
  full polynomial heat sums to `L` is proved equivalent to convergence of the
  remainder to `L` minus the finite xi window. Taking `L` to be the complete
  spectral-xi heat sum identifies the exact tail theorem still needed. This
  package holds for every window along the same root-pinned sequence under
  `¬RH`.
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
proved locally uniform, and separable root-pinned versions retain both that
limit and the prescribed finite homotopy root. Their canonical influence
cores are nonempty and carry the full pole budget at every finite stage; each
core root lies above the fixed pinned height. Consequently all stages obey
the same strict-from-one closed determinant bound, including singleton cores.
Failure of RH is now proved to supply the required positive homotopy and upper
root, for both simple and multiple spectral-xi zeros, so the full finite
frontier is a checked consequence of the reductio hypothesis rather than a
conditional construction.
The un-cancelled theta quotients now converge locally uniformly on every
zero-free open region. The next Hardy frontier is to construct and identify
the corresponding cancelled entire-limit invariant at the pinned zero and
rigorously pass the uniform finite bound to it. The new proper-time bridge
recasts the complete finite hyperbolic product as a positive Gaussian heat
mass with a stage-independent lower bound. Independently, the complete
fixed-time spectral-xi heat sum is now constructed as an absolutely
convergent sum of heat-weighted local residues of `xi'/xi`, and its vanishing
is equivalent to RH. Expanding finite spectral windows and zero-free boundary
truncations are now proved to converge to it. Zero-free circle integrals have
now been combined with the exact polynomial argument principle to prove
eventual local multiplicity stability for the same finite Hardy sequence. The
stabilized counts are identified with genuine analytic multiplicities, finite
families are isolated simultaneously in disjoint balls, and continuous
weighted root sums now converge. In particular, every bounded upper spectral
heat window is a checked limit of fixed-time heat sums over the corresponding
full polynomial-root clusters. The Hardy cores are now proved to be
multiplicity-preserving submultisets of those polynomials' complete upper
divisors, so their fixed-time and integrated heat contributions are dominated
by the common full-divisor object. Each bounded xi window now cuts an actual
upper-root submultiset out of that divisor, and the complement is an explicit
nonnegative heat remainder. Lean proves that full polynomial convergence to
the complete xi heat sum is equivalent to convergence of this remainder to
the exact spectral tail `complete sum - window`. The immediate open passage
is therefore a uniform Gaussian estimate proving that remainder convergence
and controlling it as the windows expand; proper-time endpoint control is a
separate subsequent requirement. A global logarithmic-derivative or
arithmetic evaluation of the complete sum is the later rigidity target.

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
- [`RiemannGaussian/FiniteRealRootDecomposition.lean`](RiemannGaussian/FiniteRealRootDecomposition.lean)
  canonically decomposes every real polynomial root multiset with multiplicity.
- [`RiemannGaussian/FiniteHardyCanonicalConclusion.lean`](RiemannGaussian/FiniteHardyCanonicalConclusion.lean)
  specializes the complete finite Hardy chain to that canonical root multiset.
- [`RiemannGaussian/FiniteHardySingletonFrontier.lean`](RiemannGaussian/FiniteHardySingletonFrontier.lean)
  proves strict one-pair energy away from vertical alignment and isolates the
  equality geometry.
- [`RiemannGaussian/FiniteToEntireSeparableApproximation.lean`](RiemannGaussian/FiniteToEntireSeparableApproximation.lean)
  constructs separable root-pinned approximants converging to spectral xi.
- [`RiemannGaussian/FiniteToEntireHardyFrontier.lean`](RiemannGaussian/FiniteToEntireHardyFrontier.lean)
  composes those approximants with the canonical pole-budget and finite Hardy
  determinant alternatives.
- [`RiemannGaussian/FiniteToEntireHardyReductio.lean`](RiemannGaussian/FiniteToEntireHardyReductio.lean)
  proves that failure of RH reaches that finite frontier, including analytic
  persistence of simple homotopy roots and the multiple-root case.
- [`RiemannGaussian/FiniteToEntireTheta.lean`](RiemannGaussian/FiniteToEntireTheta.lean)
  proves locally uniform convergence of `E_eta^sharp/E_eta` away from zeros
  of the limiting homotopy and isolates the required cancellation at a pole.
- [`RiemannGaussian/HyperbolicHeatBridge.lean`](RiemannGaussian/HyperbolicHeatBridge.lean)
  identifies finite hyperbolic product defects with positive Gaussian
  proper-time heat actions.
- [`RiemannGaussian/FiniteToEntireHeatFrontier.lean`](RiemannGaussian/FiniteToEntireHeatFrontier.lean)
  composes that identity with the finite Hardy sequence forced by failure of
  RH and proves a uniform positive lower bound for every finite heat mass.
- [`RiemannGaussian/RiemannXiHyperbolicHeat.lean`](RiemannGaussian/RiemannXiHyperbolicHeat.lean)
  constructs the complete fixed-time spectral-xi heat sum, derives every
  coefficient from a local logarithmic-derivative residue, proves absolute
  convergence, and characterizes RH by its vanishing.
- [`RiemannGaussian/RiemannXiHyperbolicHeatWindow.lean`](RiemannGaussian/RiemannXiHyperbolicHeatWindow.lean)
  realizes that sum as the limit of finite spectral residue windows, including
  canonical zero-free boundary truncations.
- [`RiemannGaussian/FiniteToEntireLogDerivative.lean`](RiemannGaussian/FiniteToEntireLogDerivative.lean)
  proves zero-free locally uniform convergence of the root-pinned polynomial
  logarithmic derivatives and convergence of their circle integrals.
- [`RiemannGaussian/PolynomialLogDerivativeCircle.lean`](RiemannGaussian/PolynomialLogDerivativeCircle.lean)
  proves the exact multiplicity-counted polynomial argument principle on
  root-free circles.
- [`RiemannGaussian/FiniteToEntireRootCountCircle.lean`](RiemannGaussian/FiniteToEntireRootCountCircle.lean)
  combines the zero-free integral limit with discreteness to prove eventual
  local multiplicity stability, including for the root-pinned Hardy sequence
  under failure of RH.
- [`RiemannGaussian/FiniteToEntireLocalDivisor.lean`](RiemannGaussian/FiniteToEntireLocalDivisor.lean)
  proves the local analytic argument principle and identifies each stabilized
  polynomial count with the exact spectral-xi zero multiplicity.
- [`RiemannGaussian/FiniteToEntireBoundedHeat.lean`](RiemannGaussian/FiniteToEntireBoundedHeat.lean)
  synchronizes finite disjoint divisor clusters and proves convergence of
  their continuous weighted sums, including every fixed finite spectral heat
  window along the root-pinned Hardy sequence.
- [`RiemannGaussian/FiniteToEntireFullDivisorHeat.lean`](RiemannGaussian/FiniteToEntireFullDivisorHeat.lean)
  embeds the Hardy core in the full upper polynomial divisor with
  multiplicity and proves fixed-time, truncated-action, and total-mass heat
  domination, including the uniform `¬RH` sequence-level frontier.
- [`RiemannGaussian/FiniteToEntireHeatWindowRemainder.lean`](RiemannGaussian/FiniteToEntireHeatWindowRemainder.lean)
  embeds each bounded xi cluster in that full divisor and splits its
  fixed-time heat sum into the convergent window term plus an exact
  nonnegative remainder, reducing full convergence to a precise tail limit.
- The `GramWeil*` files contain the abstract block defect, inertia, and metric
  pencil theory.
- [`RiemannGaussian.lean`](RiemannGaussian.lean) is the umbrella module built
  by the default target.

This repository should be read as an active formal research program. Git
history records the fine-grained proof audit; this README records the purpose,
the checked mathematical state, and the exact open frontier.
