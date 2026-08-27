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
- The theta-tail Mellin estimate underlying that growth bound has now been
  sharpened in Lean. Young's inequality with conjugate exponents `4/3` and
  `4` absorbs `x^u` into half the exponential tail at an explicit cost growing
  like `u^(4/3)`, instead of the earlier quadratic cost. The resulting entire
  upper-tail Mellin bound is strictly subquadratic in the positive real
  exponent.
- That improvement has been propagated through both reflected halves of the
  completed-zeta formula and the polynomial xi prefactor. Lean now proves
  unconditionally that some `A >= 1` satisfies
  `norm(riemannXi(z)) <= exp(A*(norm(z)+1)^(3/2))` for every complex `z`.
  This checked global exponent is strictly below two. Jensen's inequality has
  now also been specialized to turn it into an unconditional
  multiplicity-aware `O(r^(3/2))` bound for the xi divisor in centered disks.
  A checked dyadic-shell argument then proves unconditional convergence of
  both `sum_rho m(rho)/(1+norm(rho)^2)` and
  `sum_rho m(rho)/(1+gamma(rho)^2)`, where `gamma` is the real spectral
  coordinate. This convergence now proves that the complete Poisson mass is
  finite at every upper observation point, and that the logarithmic
  proper-time action is finite at every noncolliding upper point. The complete
  elementary Blaschke derivative variation is finite as well. Each extended
  mass is identified with the embedding of an actually convergent real
  series, so the frontier no longer hides a possible infinite value.
- The finite Blaschke variation has therefore been promoted to its actual
  real total `V(z)`. Lean proves `V(z) = 0` exactly under RH and `V(z) > 0`
  under `not RH`. At every noncolliding upper point, failure of RH now forces
  a direct two-way finite-window frontier: either the exact xi reflection
  residual is at least `V(z)/4` along arbitrarily late windows, or the
  weighted unit-phase chordal energy is eventually at least `(V(z)/4)^2`.
  This result has no polynomial-height or infinite-mass escape branch.
- At every noncolliding upper point, the selected signed Blaschke
  logarithmic-derivative terms are now proved absolutely summable. Their
  complete complex sum is the limit of both the genuine finite Blaschke
  windows and the exact xi reflection residuals. Consequently the residual
  side of the preceding frontier is static: under `not RH`, either the norm
  of this complete signed sum is at least `V(z)/4`, or the finite-window
  weighted phase energy is eventually at least `(V(z)/4)^2`.
- The signed-term variation and phase dispersion now have complete finite
  limits too. Lean proves the sharper static alternative that at least
  `V(z)/2` survives in the complete signed resultant or at least
  `(V(z)/2)^2` survives in complete phase dispersion. At every noncolliding
  upper point it also proves the exact rigidity criterion
  `RH <-> (complete resultant = 0 and complete phase dispersion = 0)`.
- On the real spectral boundary, Lean now proves that all selected upper-zero
  logarithmic-derivative terms align in the same positive imaginary
  direction. Inverse-square divisor summability makes their positive density
  total finite at every real point, including critical-line spectral zeros:
  analyticity isolates any boundary zero from the selected upper divisor.
  The norm of the complete signed resultant is exactly that density, so there
  is no phase cancellation. Consequently the single fixed condition
  `complete resultant at 0 = 0` is equivalent to RH, with no noncollision
  premise. This is an exact rigidity reformulation, not yet the arithmetic
  theorem forcing that resultant to vanish.
- The existing upper-half-plane Poisson/Blaschke chain now reaches that
  boundary invariant rigorously. Along `x + i*y` as `y -> 0+`, every
  elementary derivative-variation term is dominated by its summable boundary
  density, so a checked Tannery argument passes the limit through the complete
  multiplicity-counted divisor. The real variation total, its extended mass,
  and the Poisson mass divided by its exact factor `2*y` all converge to one
  finite boundary limit. That limit equals the embedded norm of the complete
  signed boundary log derivative and vanishes exactly under RH. The remaining
  hard step is an arithmetic or entire-function argument forcing this limit
  to vanish, not an unproved interchange of a limit and an infinite zero sum.
- The full positive-proper-time heat action now has the same boundary limit.
  The upper-divisor gap persists with half its size along short vertical
  approaches, even when the endpoint is a critical-line zero. Lean sandwiches
  `heatAction(x+i*y)/(2*y)` between the normalized Poisson mass and a factor
  `1 + 2*y/(delta/2)^2` times that mass; the factor tends to one. Hence, for
  every real `x`, the normalized action tends to the norm of the complete
  boundary log derivative. Lean proves the exact reformulation
  `RH <-> heatAction(x+i*y)/(2*y) -> 0` at any one real `x`. The remaining
  RH-level target is therefore the concrete arithmetic/entire-function
  estimate `heatAction(x+i*y) = o(y)`; no divisor-limit or proper-time
  interchange is left implicit in that target.
- The boundary layer is now resolved before proper-time integration as well.
  For every fixed `tau > 0`, Lean differentiates each reflected Gaussian heat
  pair at height zero and proves that the complete spectral-xi heat sum
  divided by `2*y` converges to an absolutely summable positive boundary heat
  density. A uniform divisor gap supplies a checked `4/tau` Poisson-density
  dominator for Tannery's theorem. The resulting Gaussian-weighted boundary
  total vanishes exactly under RH, so this fixed-time limit is a direct
  sorry-free RH reformulation derived from the genuine spectral-xi
  logarithmic-derivative residues, not a formal interchange assumption.
  Lean now also integrates this entire boundary heat sum over positive
  proper time. Termwise exponential integration plus Tonelli proves that its
  integral is exactly the finite Poisson boundary limit and exactly the
  embedded norm of the complete boundary Blaschke logarithmic derivative.
  The fixed-time residue construction and integrated action therefore meet
  by a checked identity; the remaining problem is to force this common
  positive invariant to vanish. The complex residue series itself is now
  carried through the boundary limit too: every term remains explicitly the
  local heat-weighted residue of `logDeriv riemannXiSpectral`, its complete
  normalized series converges to the embedded boundary heat total, and that
  complex total vanishes exactly under RH.
- The fixed-time boundary invariant now has an exact two-point Gaussian/Gram
  realization. Lean defines a kernel that is jointly entire in a spectral
  zero and its critical-line-reflected partner; on every actual reflected
  zeta pair it is exactly the positive boundary heat residue. The kernel
  factors through the same analytic half-Gaussian used by the one-point
  explicit formula, with the precise transverse damping
  `exp(-2 * tau * height^2)`. These features form a proved square-summable
  vector indexed by the nontrivial zeta zeros, and its squared `ℓ²` norm is
  exactly the complete boundary heat total. Thus the matched two-zero
  correlation, spectral-xi residue limit, and Hilbert Gram diagonal are one
  rigorously identical invariant, zero exactly under RH. The remaining new
  mathematics is now sharply localized: obtain independent arithmetic or
  Suzuki/Fredholm control of this reflected-pair correlation; the existing
  one-point Gaussian explicit formula alone does not perform the required
  pair matching.
- Spatial integration now links that boundary Gram invariant to the existing
  radial-height frontier. Lean integrates the complete fixed-time boundary
  density over every real center by Tonelli, without assuming the result is
  finite. After division by the exact Gaussian mass
  `2 * sqrt(pi / tau)`, the result is the pure positive transform
  `sum m * height * exp(-tau * height^2)`. The zero-free strip gives the
  rigorous two-sided bound `exp(-tau/4) * heightMass <= transform <=
  heightMass`; hence damping preserves vanishing and divergence. As
  `tau -> 0+`, the normalized spatial boundary heat converges in `ℝ≥0∞` to
  the full upper spectral height mass, exactly the previously constructed
  zero-time heat trace at canonical observation height `1/4`. This is now a
  proved meeting point between the reflected Gaussian Gram density and the
  off-critical radial-width/Suzuki program.
- That meeting point now extends to an exact complex screw-time bridge. Lean
  proves that a reflected spectral pair of upper height `h` contributes
  `2*h*exp(2*h*t)` on real screw time, while its normalized imaginary-time
  Gaussian average is exactly `2*h*exp(-tau*h^2)`. Genuine finite zeta-zero
  windows of these Wick-rotated modes converge to the normalized spatial
  boundary heat, including when the complete mass is infinite. The associated
  positive real-time mass equals the full upper-height mass at time zero,
  vanishes at any fixed time exactly under RH, and is subexponential exactly
  under RH. This isolates a concrete remaining arithmetic target: prove the
  subexponential estimate from Suzuki's arithmetic screw function or an
  equivalent explicit-formula rigidity theorem. The spectral equivalence
  itself does not supply that arithmetic estimate.
- The screw bridge now also has a finite Hilbert-space realization with the
  first-order spectral resolvent `1 + i*alpha`. Lean proves the exact ODE
  identity `u - u' = exp(-i*alpha*z)` for each regularized mode and uses the
  unconditional inverse-square xi-divisor theorem to assemble the modes into
  an actual `ℓ²` vector at every real time. Its squared norm is the positive
  resolvent-weighted reflected-pair mass, is always finite, has an
  unconditional `O(exp(|t|))` bound, and is subexponential exactly under RH.
  The corresponding Gaussian/Wick mass is also absolutely convergent and is
  the limit of genuine finite zeta windows. This removes the unregularized
  mass's possible value `∞` and puts the frontier in the same inverse-square
  Hilbert setting as a Suzuki screw norm; identifying or dominating this norm
  arithmetically remains open.
- The resolvent is now identified in Lean as an actual time-domain operator:
  each regularized spectral coordinate is the exponential future convolution
  `integral_0^infinity exp(-s) * rawMode(t+s) ds`. A general normed-space
  theorem proves that a rate-`epsilon < 1` input bound passes through this
  convolution with the exact factor `1/(1-epsilon)`, and hence that the
  operator preserves subexponential growth. This creates a rigorous transfer
  channel from a future arithmetic Suzuki-screw signal to the finite spectral
  norm. What is still missing is a new theorem identifying the appropriate
  arithmetic signal with, or proving it dominates, the raw spectral
  coordinates; that theorem will also have to be formalized in Lean.
- Lean now reaches Suzuki's published zero-expansion coefficient itself. The
  continuously extended `(exp(-i*alpha*t)-1)/alpha`, including its removable
  value at `alpha = 0`, has derivative `-i*exp(-i*alpha*t)`. Exponential future
  convolution of that derivative is exactly `-i` times the resolvent mode, so
  every coordinate of the finite RH-detecting Hilbert vector is a proved
  height-weighted convolution of the derivative of Suzuki's coefficient. This
  is the coefficient-level bridge into Suzuki's construction.
- The finite zero-function layer of Suzuki's expansion is now formalized too.
  Lean defines the actual spectral-xi functions `E_xi`, `E_xi^sharp`, and
  `Theta_xi`; proves real-axis unimodularity wherever the quotient is defined;
  installs the published square-root multiplicity normalization; and proves
  the exact finite genuine-zero version of equation (3.6). Finite `P_t` and
  `S_t` windows vanish at time zero and differentiate term by term to the raw
  screw modes. This does not silently totalize the analytic gap: the canonical
  holomorphic values at removable points, the full arithmetic formula for
  `P_t`, unconditional `L²` membership of `S_t`, the real-axis infinite
  expansion, and the off-RH Gram comparison remain to be proved before an
  arithmetic growth estimate can cross the bridge.
- The complete Suzuki coefficient sequence is nevertheless now a rigorous
  unconditional Hilbert vector. Lean represents the extended coefficient as
  the exact interval integral of its raw screw derivative, proves uniform
  critical-strip and large-ordinate bounds, and derives an explicit
  inverse-square majorant. Combined with the xi-divisor summability theorem,
  this puts the genuine sequence
  `sqrt(m_alpha) * (exp(-i*alpha*t)-1)/alpha` in `ℓ²` for every real `t`, with
  zero initial vector; multiplying its coordinates by `sqrt(pi)` recovers the
  published coefficients in Suzuki's expansion. The remaining Hilbert-space
  obstruction is now the synthesis operator generated by the zero functions:
  its off-RH Gram geometry must be constructed and controlled in `L²(R)`.
- At Suzuki's safe evaluation point `z = i`, Lean now constructs the matching
  Cauchy-evaluation vector in `ℓ²` as well. The denominator `i-alpha` is proved
  to be exactly `i` times the existing screw resolvent, so its energy is again
  controlled by the inverse-square xi-divisor series. The full spectral
  `P_t(i)` zero sum is consequently absolutely convergent, equals the Hilbert
  pairing of the evaluation and coefficient vectors, satisfies the exact
  Cauchy--Schwarz bound, and is the limit of genuine symmetric zeta windows.
  This is an infinite spectral Suzuki quantity, not yet the arithmetic
  formula: proving equality with Suzuki's prime/gamma expression and lifting
  evaluation to the entire arithmetic `L²` signal are the next gaps.
- The point `i` has now been generalized to Suzuki's full safe half-plane
  `Im(z) > 1/2`. A proved vertical-gap inequality produces an explicit
  point-dependent inverse-square majorant, hence an `ℓ²` Cauchy-evaluation
  vector at every such `z`. Lean constructs absolutely convergent infinite
  spectral functions `P_t(z)` and `S_t(z)`, identifies `P_t(z)` with the
  coefficient-space Hilbert pairing, proves convergence of genuine finite
  zero windows, and proves the infinite normalized zero-function expansion
  (3.6) there. What remains is analytically sharp: identify this safe-domain
  function with the arithmetic prime/gamma formula, continue its carrier-
  cancelled boundary values into `L²(R)`, and control the resulting off-RH
  synthesis/Gram operator.
- That safe-half-plane series is now a genuine holomorphic object, not merely
  a pointwise sum. Lean proves a compact-uniform Weierstrass majorant from the
  same inverse-square divisor weight, local uniform convergence of the actual
  symmetric zero windows, and termwise spatial differentiation of the
  complete series. The derivative is the unconditional sum of the explicit
  double-pole summands. This supplies the analytic side needed for a future
  identity theorem; the missing meeting theorem is still the arithmetic
  prime/gamma identification itself.
- The first non-elementary term of that arithmetic formula is now constructed
  from first principles. For every positive screw time, Lean proves uniform
  geometric convergence of the defining Hurwitz--Lerch series on a common
  right half-plane containing both `1/4 - i*z/2` and `1/4`, and proves their
  exact difference holomorphic on `Im(z) > 1/2`. The divergent nome-one case
  at time zero is explicitly excluded pending a separate removable-limit
  theorem; no analytic-continuation value is assumed.
- Suzuki's complete positive-time arithmetic expression (1.6) is now a Lean
  definition with a checked analytic domain. Its two completed-zeta pole
  terms, zeta logarithmic derivative at `1/2 - i*z`, exact finite von Mangoldt
  window `1 <= n <= exp(t)`, digamma difference, and Lerch difference are all
  individually proved holomorphic on `Im(z) > 1/2`, hence so is their sum for
  every `t > 0`. No equality to the spectral zero sum is claimed yet: the
  remaining meeting theorem is precisely the specialized Weil explicit
  formula proving those two independently constructed holomorphic functions
  coincide.
- Suzuki's piecewise positive-half-line Weil test is now literal Lean code,
  not an informal input to that meeting theorem. Lean proves its absolute
  integrability whenever the evaluation point lies above the spectral
  frequency and evaluates its full Fourier--Laplace transform exactly as
  `(exp(-i*gamma*t)-1)/(gamma*(z-gamma))`, with the correct removable value at
  `gamma = 0`. For every genuine zeta zero, analytic multiplicity times this
  integral is exactly one summand of the already constructed spectral
  `P_t(z)`; finite symmetric sums recover the genuine zero windows and
  converge to the complete spectral function. The remaining gap is global,
  not local: prove the specialized Weil distribution identity and evaluate
  its prime and Archimedean terms as the arithmetic expression.
- The elementary part of that global evaluation is now discharged. Lean
  identifies `exp(x/2)` and `exp(-x/2)` with the test transform at the two
  completed-zeta pole frequencies, proves both weighted tests absolutely
  integrable, evaluates their integrals exactly, and recovers the two-pole
  term in Suzuki's arithmetic formula (1.6). No invocation of the Weil
  formula is hidden in this calculation.
- The complete prime-sum part is now discharged as well. Lean proves every
  negative-logarithm sample vanishes, splits each positive-logarithm sample at
  the exact finite cutoff `1 <= n <= exp(t)`, and identifies the remaining
  exponential sequence term by term with Mathlib's von Mangoldt `L`-series at
  `1/2 - i*z`. Absolute convergence in `Im(z) > 1/2` and the Euler-product
  theorem then sum the tail to `-zeta'/zeta`, while the finite part is exactly
  Suzuki's prime correction. With the explicit-formula signs, the two prime
  sums therefore recover the zeta and finite-prime terms of (1.6). Combined
  with the preceding integral, Lean now evaluates the full elementary and
  non-Archimedean RHS. The unchecked RHS component is the Archimedean
  digamma/Lerch integral, followed by the global Weil distribution identity.
- The Archimedean calculation has now been reduced one level further. Lean
  proves the full complex Euler series for a digamma difference is absolutely
  summable on the right half-plane, constructs every lower-half-plane mode of
  the Archimedean geometric kernel, and identifies each mode with an actual
  integral of Suzuki's test. Partial fractions then sum the complete mode
  family exactly to the negative of Suzuki's digamma-plus-Lerch contribution,
  with no appeal to the Weil formula. The remaining local obligation is to
  prove that expanding the single Archimedean kernel and interchanging its
  integral with this absolutely convergent mode family is valid. After that,
  only the global specialized Weil distribution identity remains.
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
- The simple/multiple split is no longer needed to obtain a noncolliding
  homotopy root. At a spectral zero of multiplicity `m`, Lean uses the exact
  logarithmic-derivative principal part to regularize `i*xi/xi'` as
  `i*(z-a)/(m + (z-a)*h(z))`. This map is proved analytic with derivative
  `i/m`, so its local inverse gives a positive upper homotopy root where xi
  itself is nonzero. This strengthened choice is now propagated through the
  scheduled radial/Rouché construction, the full fixed-time heat limit, and
  the compact proper-time passage.
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
  positive finite heat frontiers at every stage. The full fixed-time and
  compact positive-time limiting passages for this same sequence are
  formalized below. The large-time endpoint is closed; only quantitative
  control as proper time tends to zero remains open.
- Lean now makes that endpoint obstruction quantitative. Every compact
  positive-time action is at most the complete finite logarithmic heat mass,
  so their difference is a genuine nonnegative endpoint defect. Under
  `¬RH`, along the same canonical sequence and on every fixed compact
  interval, this defect eventually retains the uniform Hardy mass lower bound
  minus the limiting spectral-xi compact action and an arbitrary positive
  error. Thus no mass can disappear in the already-controlled interior: any
  contradiction must come from ruling out escape through proper time zero or
  infinity.
- The large-time endpoint is now closed for the actual canonical sequence. Lean
  proves that the complete spectral-xi heat tends to zero as proper time tends
  to infinity at the chosen nonzero observation point. Locally uniform
  polynomial convergence then supplies one eventual positive gap from that
  point to every polynomial upper root. A relative exponential-decay estimate
  converts fixed-time heat convergence into uniform tightness of all later
  finite actions. The same `¬RH` sequence retains its stage-independent
  positive full-mass lower bound and compact-action convergence, so endpoint
  escape is now forced entirely toward proper time zero.
- That last statement is now quantitative in Lean. Every finite action is
  split exactly into small-, compact-, and large-time pieces. For every
  `a > 0` and every positive error, Lean chooses a finite `T >= a` such that,
  at every sufficiently late canonical stage, some `0 < c_n < a` captures
  before time `a` at least the fixed Hardy threshold minus the spectral-xi
  action on `[a,T]` and the error. Thus the sole endpoint question is whether
  these stage-dependent small-time concentrations can be uniformly ruled out
  or converted into an arithmetic contradiction.
- The small-time kernel itself is now evaluated sharply. Lean proves that one
  upper root has zero-time heat trace exactly
  `4 * Im(z) * Im(alpha)`, and that its heat is bounded above by this trace at
  every positive time. Thus a finite divisor's action before `a` is at most
  `a` times four times the observation height times the total upper-root
  height, counted with multiplicity. Combining this with the concentration
  theorem forces an explicit eventual lower bound on that height statistic
  under `¬RH`; controlling or arithmetically identifying its growth is the
  newly exposed small-time frontier.
- Lean also identifies why the first coefficient moment does not immediately
  control this statistic. For every real polynomial, the signed sum of all
  root imaginary parts is exactly zero by conjugate cancellation, whereas the
  upper-root height mass is half the total unsigned imaginary variation. That
  variation is bounded by half the total root-norm mass. The canonical
  `¬RH` sequence is now proved to obey explicit eventual lower bounds on both
  unsigned variation and root-norm mass, isolating a genuinely global root
  statistic rather than a signed Vieta moment.
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
  finite window vanishing. The later radial chain now proves convergence of
  the varying full finite Hardy heat sums to this complete sum. What remains
  open is endpoint-uniform passage of the integrated defect and a global
  arithmetic evaluation of the complete sum.
- Lean now also constructs the complete upper spectral height mass in
  `ℝ≥0∞`, so no unproved summability assumption is hidden at proper time zero.
  For every observation point above the real axis, the lifted complete
  spectral heat is proved to converge as `tau -> 0+` to its exact extended
  zero-time trace, not just along a subsequence. That trace factors as
  `ofReal(4 * Im(z))` times the upper spectral height mass, and vanishing of
  the mass is equivalent to RH. This identifies the entire-side small-time
  boundary object exactly; it does not yet prove convergence or uniform
  tightness of the finite polynomials' growing height masses.
- The complete spectral heat is now integrated over all positive proper time
  as an extended nonnegative Lebesgue integral. Lean proves a genuine Tonelli
  identity equating this action to the full multiplicity-counted sum of
  logarithmic pseudo-hyperbolic defects
  `sum_rho m(rho) * (-2 * log rho_H(z,A(rho)))`, including the value
  `infinity`; no global integrability assumption is used. At every upper
  observation point away from the xi divisor, vanishing of this complete
  action is equivalent to RH. What remains is the rigidity comparison that
  would force the persistent finite Hardy mass into this entire action, or
  otherwise contradict its arithmetic structure.
- That comparison is now formalized conditionally and as an exact
  alternative. If the canonical polynomials' upper-height masses are
  eventually uniformly bounded, Lean proves that the fixed finite Hardy
  threshold survives in the complete spectral logarithmic-defect mass.
  Without assuming such a bound, `¬RH` yields the rigorous dichotomy: either
  the complete spectral defect already dominates that threshold, or the
  finite upper-height masses exceed every nonnegative bound arbitrarily far
  along the same sequence. Proving that neither branch can occur is the new
  arithmetic/entire-function rigidity frontier.
- The two complete spectral endpoint statistics are now quantitatively
  linked. At every upper observation point outside the xi divisor,
  continuity of spectral xi yields one positive distance from all of its
  zeros. Lean combines this gap with `log(1+x) <= x` to prove, first per zero
  and then for the full extended sums, that the complete logarithmic defect
  is at most a finite positive constant times the complete upper spectral
  height mass. In particular, finiteness of the latter implies finiteness of
  the full proper-time action. Finiteness or a decisive arithmetic bound for
  the spectral height mass itself is not assumed.
- Functional-equation symmetry now identifies that height mass in the
  original zeta coordinate. Lean proves the exact extended-real identity
  `sum_rho m(rho) * |Re(rho) - 1/2| = 2 * upperSpectralHeightMass`, using the
  genuine analytic multiplicities and the critical-line reflection
  equivalence. Vanishing of this full absolute displacement is again proved
  equivalent to RH. Thus the new entire-side size target is a literal global
  arithmetic displacement of the zeta divisor, not an artifact of the
  rotated coordinate.
- The complete upper-height, absolute-displacement, and logarithmic-defect
  masses now have explicit finite approximants. Lean proves that the same
  symmetric spectral windows used by the xi contour argument are cofinal and
  that all three finite sums converge to their complete `ℝ≥0∞` masses,
  including when a limit is infinite. Critical-line reflection preserves
  every finite window, so its absolute displacement is already exactly twice
  its upper-height sum before passage to the limit.
- The logarithmic defect now also has a checked Poisson lower bound. For each
  upper spectral zero, Lean proves the exact identity
  `1 - rho_H(z,alpha)^2 = 4*Im(z)*Im(alpha)/|z-conj(alpha)|^2` and bounds this
  quantity by `-2*log rho_H(z,alpha)`. With genuine analytic multiplicities,
  the resulting finite Poisson sums converge to a complete extended mass
  below both the logarithmic defect and the full proper-time action. Its
  vanishing at any upper observation point is equivalent to RH and hence to
  vanishing of the full absolute critical-line displacement.
- At a noncolliding upper observation point the comparison is now two-sided.
  The positive distance from that point to the complete xi divisor, together
  with the strict critical-strip height bound, gives an explicit finite
  coefficient `C = 1 + 2*Im(z)/delta^2`. Lean proves in `ℝ≥0∞` that
  `PoissonMass <= LogDefectMass = HeatAction <= C*PoissonMass`, without a
  finiteness assumption on either mass. Consequently any lower bound that
  survives in the complete logarithmic Hardy defect also survives,
  quantitatively, in the Poisson/Blaschke derivative-variation statistic.
- The canonical `not RH` alternative has now been transported through that
  comparison in Lean. Writing `D > 0` for the fixed finite Hardy threshold and
  `C = 1 + 2*Im(z)/delta^2` for the divisor-gap coefficient, Lean proves that
  `D/C` and `D/(C*2*Im(z))` are positive and that either the complete Poisson
  mass and complete Blaschke derivative variation dominate their respective
  normalized thresholds, or the same finite polynomial upper-height masses
  exceed every nonnegative bound arbitrarily far along the canonical
  sequence. This puts the persistent finite Hardy obstruction directly into
  the analytic statistic whose cancellation must now be controlled.
- That complete-mass alternative has now been returned to concrete finite
  spectral windows. If the Blaschke-variation branch holds with positive
  normalized threshold `q`, Lean proves that every sufficiently large window
  satisfies `q/2 <= norm(reflectionResidual_T) + cancellationGap_T`. The
  reflection residual is proved exactly equal to the finite Blaschke
  product's logarithmic derivative and is expanded without omission into
  genuine `xi'/xi`, the analytic window remainder, the critical-line Cauchy
  part, and the upper divisor Cauchy sum. Thus the remaining rigidity theorem
  must defeat a persistent lower bound on named finite analytic quantities,
  or rule out the alternative of unbounded polynomial height mass.
- Lean now separates the two terms in that finite analytic lower bound. Under
  `not RH`, one of three rigorously quantified behaviors must occur: the exact
  xi reflection residual is at least one quarter of the normalized threshold
  along arbitrarily late windows; the Blaschke cancellation gap is at least
  one quarter of that threshold in every sufficiently large window; or the
  canonical polynomial upper-height masses are unbounded. This is the current
  rigidity trichotomy: a proof of RH must eliminate all three branches, not
  assume that divisor-product cancellation disappears.
- The cancellation branch now has an exact pair-interaction formulation.
  Lean defines the finite Blaschke phase-dispersion energy as the double sum
  of `norm(u_rho)*norm(u_sigma) - re(inner(u_rho,u_sigma))`, proves every term
  nonnegative, and proves exactly that this is
  `Variation_T^2 - norm(SignedSum_T)^2 = Gap_T*(Variation_T +
  norm(SignedSum_T))`. Hence an eventual cancellation lower bound `q/4`
  forces eventual phase dispersion at least `(q/4)^2`. The hard cancellation
  branch is therefore a positive pairwise angular-energy branch, not an
  undefined loss in a triangle inequality.
- That angular energy now has literal unit-circle geometry. Lean proves that
  every signed upper-zero Blaschke term is nonzero at a noncolliding upper
  observation point, normalizes each term to unit modulus, and identifies
  every pair defect exactly with
  `norm(u)*norm(v)/2 * norm(unitPhase(u)-unitPhase(v))^2`. Thus the complete
  double sum is a weighted squared chordal phase-separation energy. No
  informal appeal to phases or angular cancellation remains in this branch.
- The connection to the actual spectral-xi logarithmic derivative is now
  formalized at every finite window without dropping an entire-function
  term. Lean decomposes `xi'/xi` exactly into the genuine multiplicity-
  weighted Cauchy principal sum plus a raw remainder. Every selected pole of
  that remainder is proved removable, and the finitely many removals are
  patched into one analytic representative on the full safe contour
  rectangle. Thus the cancellation/residual term requiring new rigidity is
  explicit in the checked chain rather than tacitly set to zero.
- The Poisson statistic now has an exact analytic derivative interpretation.
  Lean computes the derivative of each elementary upper-half-plane Blaschke
  factor and proves that its multiplicity-weighted Poisson contribution is
  exactly `2*Im(z)` times that derivative's norm. The finite-window identity
  passes to the complete extended sums, so the full Poisson mass is precisely
  `ofReal(2*Im(z))` times total spectral Blaschke-derivative variation,
  including infinity. Vanishing of this variation is equivalent to RH. The
  next unchecked issue is cancellation when these individual derivatives are
  assembled into one finite divisor product.
- That finite-product assembly and its cancellation bookkeeping are now
  checked. Lean constructs the multiplicity-weighted upper spectral Blaschke
  product in every window and identifies its logarithmic derivative exactly
  with the signed paired Cauchy sum. It defines the difference between the
  sum of individual term norms and the norm of their sum, proves this
  cancellation gap nonnegative, and obtains the finite bound
  `PoissonWindow <= ofReal(2*Im(z)) * ofReal(norm(product'/product) + gap)`.
  Thus a rigidity theorem must now control two explicit analytic objects—the
  finite-product resultant and its cancellation gap—alongside the already
  exposed analytic remainder relating finite Cauchy windows to genuine
  `xi'/xi`; none is being assumed negligible.
- Critical-line reflection now joins those two analytic objects in one exact
  equation. Lean partitions every full xi Cauchy window into upper,
  critical-line, and lower pieces, proves the lower piece is the reflected
  upper piece with unchanged multiplicity, and combines the paired plus sum
  with the signed Blaschke sum. At every noncolliding upper point it obtains
  `2*upperCauchy = (xi'/xi - analyticRemainder - criticalCauchy)
  + product'/product`. This is a rigorous bottom-to-frontier identity: both
  the entire-function remainder and finite Blaschke cancellation remain
  visible, and controlling them is now the concrete rigidity task.
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
- At fixed positive proper time, Lean now proves a direct Euclidean Gaussian
  bound for every hyperbolic heat term. Consequently the radial upper-root
  heat tail of any real polynomial is bounded, with multiplicity, by
  `degree * tau⁻¹ * exp(-R²*tau)`. The exact unused-root remainder inherits
  this bound whenever all unused roots lie at least `R` from the observation
  point, and an asymptotic squeeze theorem proves its convergence to zero
  whenever that degree-weighted envelope tends to zero. This isolates the
  global root-localization premise used by the later radial construction
  rather than deriving it incorrectly from locally uniform convergence.
- Degree is now tracked through the actual xi construction. Taylor
  truncation, affine root pinning, cubic degree lifting, and the separable
  quadratic perturbation produce the same canonical Hardy reductio sequence
  under `¬RH` with `(B n).natDegree ≤ max n 3`. The exact heat splitting and
  Gaussian bound are also generalized to an arbitrary, stage-varying selected
  root multiset, so expanding windows are not restricted to a fixed number of
  clusters. Lean proves that if every unused root is at least `√n` from the
  observation point, its complete fixed-time remainder tends to zero. The
  later zero-free radial-circle construction supplies a stronger expanding
  selection and discharges this localization premise for the scheduled
  sequence; identifying the selected heat with the complete xi heat remains.
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
the exact spectral tail `complete sum - window`. The quantitative Gaussian
half of the tail estimate is now checked: a radially separated polynomial
tail is at most `degree * tau⁻¹ * exp(-R²*tau)`, and Lean proves the
corresponding vanishing criterion. The specific root-pinned separable
sequence can now be chosen with degree at most `max n 3`, and the selected
root multiset may vary with the stage. Any fixed positive multiple of `√n`
is enough separation to force the entire unused-root heat remainder to zero
at every fixed positive time. The analytic approximation now reaches that
same scale: a Cauchy coefficient estimate combined with the proved quadratic
growth of spectral xi gives constants `A ≥ 1` and `c > 0` for which the
order-`n` real Taylor polynomial converges uniformly to spectral xi throughout
the expanding disk `‖w‖ ≤ c * √n`, with an explicit geometrically decaying
majorant. The separability half of this passage is now discharged: Lean can
avoid every finite bad-parameter set inside an arbitrary positive vanishing
budget, and coefficientwise radial majorants make the resulting cubic and
quadratic modification at most `exp(-n) / 2` on any prescribed growing disk.
Thus separability and degree lifting preserve any expanding-disk convergence
already possessed by a root-pinned input sequence. The affine root-pinning
gap is now closed as well: a Cauchy derivative estimate propagates the
geometric Taylor error through the finite homotopy residual, and the resulting
affine correction vanishes uniformly on the same `c * √n` disks. Combining
this with the fast separability construction gives actual separable,
exact-root polynomials of degree at most `max n 3` converging uniformly to
spectral xi on those expanding disks. Under `¬RH`, Lean proves that one common
positive homotopy parameter and upper-half-plane root make every member of
this sequence a canonical finite Hardy frontier. That construction is now
fed into a quantitative radial passage: canonical
factorization, zero separation, and the Jensen multiplicity bound give one
`C > 0` such that spectral xi is at least
`exp(-C * exp(5 * Tₙ))` on all four sides of every selected expanding
zero-free spectral rectangle. More importantly for global tail control, Lean
now selects radii `rₙ ∈ (n, n + 1)` tending to infinity and quantitatively
separated from every spectral xi zero. Every point on the full circle
`‖w‖ = rₙ` is proved to have that separation, and the same canonical argument
gives the uniform radial floor `exp(-C * exp(5 * rₙ)) ≤ ‖xi(w)‖`. Lean now
also defines an explicit single-exponential Taylor schedule, performs the
exact root pinning and separability perturbation at that schedule, and proves
that the resulting canonical finite Hardy polynomial differs from spectral
xi by strictly less than both this floor and `‖xi(w)‖` at every point of the
circle. Its index tends to infinity and its degree is bounded by a fixed
multiple of `exp(5 * rₙ)`, so the reindexing remains compatible with a
quadratic Gaussian tail. The Rouché step itself is now formalized directly:
the principal logarithm of the boundary quotient proves equality of the two
logarithmic-derivative circle integrals, and the exact polynomial argument
principle identifies the scheduled polynomial root count with the spectral-xi
integral at every stage. The genuine divisor inside an arbitrary positive
radial disk is now defined as an exact finite subfamily of the spectral zero
window. Lean proves that it contains every and only xi zero in the disk and
constructs synchronized pairwise-disjoint isolating balls, all strictly
inside the disk, whose polynomial root counts equal the genuine analytic
multiplicities. The compact complement of those balls is now proved
xi-zero-free, hence sufficiently late approximants have no roots there; an
exact multiset partition identifies their complete enclosed count with the
genuine radial divisor. Consequently the xi circle integral is proved equal
to that finite divisor count times `2*pi*i`. Combining this identity with the
scheduled Rouché theorem shows, at every stage under `¬RH`, that the canonical
finite Hardy polynomial has exactly the genuine xi divisor multiplicity
inside its selected expanding circle. Lean now selects the literal upper-root
multiset inside that circle and proves every complementary occurrence is at
least `rₙ - ‖z‖` from any fixed observation point. The scheduled degree is at
most a fixed multiple of `exp(5*rₙ)`, which the quadratic Gaussian beats at
every fixed positive proper time. Thus the outside-root heat tends to zero,
and the complete upper-polynomial heat differs from the literal inside-circle
heat by a vanishing term. The same boundary error now propagates through the
whole disk by maximum modulus. Since its double-exponential value is strictly
below every earlier selected-circle xi floor, Lean proves that the stage-`n`
polynomial has the genuine xi divisor count simultaneously inside every
selected circle `rₘ` with `m + 1 ≤ n`. Lean now converts these nested
cumulative counts into a multiplicity-aware annular heat decomposition, the
first of the two steps needed to identify the varying inside-circle heat with
the complete spectral-xi heat sum:
the polynomial divisor in nested disks splits into the inner divisor plus the
annular divisor, with algebraic multiplicity, and synchronized inner/outer
counts identify the complete annular cardinality with the corresponding
genuine spectral-xi divisor increment. The upper annular roots form a checked
submultiset. Jensen's quadratic xi-divisor bound then gives every sufficiently
early consecutive annulus of a cross-stage polynomial a uniform
quadratic-times-Gaussian heat majorant. Fixed-shell transport is now checked as
well. Lean replaces the discontinuous upper-half-plane root cutoff by the
continuous positive part of the heat kernel, proves that this weight equals
the heat kernel on upper roots and vanishes on real and lower roots, and then
uses exact multiplicity counts to show that the local divisor clusters fill
every fixed zero-free radial disk. Continuous weighted disk sums therefore
converge to the genuine spectral divisor, and subtraction of nested disks
gives convergence on every fixed selected annulus. Under `¬RH`, one theorem
now packages these shell limits for the same canonical Hardy sequence beside
its cross-stage counts, vanishing outer heat, and common quadratic-Gaussian
shell majorant. That majorant is now proved summable, including the finite
prefix of shells that do not yet surround the observation point, by direct
comparison with a quadratic polynomial times a linear exponential tail. Lean
also proves the required triangular-array form of Tannery's theorem for a
moving finite cutoff; it returns both summability of the pointwise shell
limits and convergence of the moving sums. That theorem is now instantiated
with the synchronized polynomial annuli. Lean proves the selected finite
spectral windows are cofinal in the complete zero divisor, telescopes both the
polynomial and spectral annuli exactly, and identifies the varying
inside-circle polynomial heat with the complete spectral-xi heat sum. Adding
the vanishing outside-root remainder proves convergence of the full upper
polynomial heat. Under `¬RH`, this fixed-time limit holds at every upper
observation point and positive proper time for the same canonical finite
Hardy sequence carrying the persistent integrated defect. The immediate open
step is proper-time endpoint control strong enough to pass that integrated
defect through the fixed-time limit. Lean now closes the entire compact
positive-time part of that passage: a one-root heat term is proved to be an
integral of `exp(-x*t)` over an ordered nonnegative squared-distance interval,
so it is antitone in `t`; finite upper-divisor heats inherit this property.
Convergence at the left endpoint of any `0 < a <= b` therefore gives a single
dominating constant on `[a,b]`, and dominated convergence proves that the
finite polynomial heat actions converge to the interval integral of the
complete spectral-xi heat. The limiting spectral heat is also proved
interval-integrable there. Under `¬RH`, the same canonical sequence now
simultaneously carries the fixed positive total-mass lower bound and this
compact-action convergence. Hence any surviving finite Hardy defect must
escape through `t -> 0` or `t -> infinity`; there is no longer an unformalized
interior proper-time gap. Lean now defines that missing endpoint mass as a
nonnegative defect and proves an exact eventual lower bound for it under
`not RH`: on every compact interval it retains the fixed finite Hardy lower
bound minus the limiting spectral-xi compact action, up to any prescribed
positive error.

At the large-time endpoint, that task is now closed for the canonical
sequence. The regularized homotopy-root construction chooses its pinned point
away from the spectral-xi divisor. The complete heat therefore tends to zero,
the approximating upper-root divisors acquire a common positive observation
gap, and every finite action after time `T` is bounded by its heat at `T`
divided by the squared gap. Lean packages this uniform large-time tightness
beside the same sequence's fixed positive mass lower bound and compact-action
convergence. The only remaining proper-time escape frontier is `t -> 0`.
Lean now also splits each finite action into its three adjacent pieces and
proves the corresponding small-time concentration theorem: for every
`a > 0`, a suitable finite `T` makes the unaccounted Hardy mass occur in
stage-dependent intervals `(c_n,a)`, up to arbitrary error. The immediate
analytic task is now concrete: the zero-time trace is exactly four times the
observation height times the total upper-root height, so one must control or
arithmetically rigidify that statistic as the approximation degree grows.
Conjugate decomposition now proves that it is half of the full unsigned
imaginary variation, while the signed first root moment vanishes identically;
coefficient control must therefore reach an unsigned/global root statistic.
On the entire side, the complete zero-time trace is now constructed without a
finiteness assumption and identified exactly with four times the observation
height times the extended upper spectral height mass; its vanishing is
equivalent to RH. The full positive-proper-time integral has now also been
constructed in extended nonnegative reals and evaluated, by Tonelli, as the
complete multiplicity-counted spectral logarithmic defect. The remaining
mismatch is therefore precise. Lean now proves that any eventual uniform
bound on the finite upper-height masses forces the finite Hardy threshold into
the complete spectral defect. Consequently `¬RH` has been reduced to an
explicit alternative: the spectral defect dominates that threshold, or the
finite upper-height masses are unbounded along arbitrarily late stages. The
remaining arithmetic/entire-function rigidity theorem must exclude both
possibilities (or strengthen the dichotomy until one becomes contradictory).
The complete spectral defect is now also bounded by a finite observation-
dependent constant times the extended upper spectral height mass, reducing
the entire-side size question to a concrete divisor statistic. That statistic
is now exactly half the full multiplicity-counted sum
`sum_rho m(rho) * |Re(rho) - 1/2|`. A global logarithmic-derivative or
explicit-formula evaluation remains the natural route to the required
rigidity.

The remaining small-time estimate is not assumed. Closing the Gaussian
positivity statement, or completing the finite-to-xi Hardy route, is the
RH-level part of the project.

## Repository guide

- [`RiemannGaussian/GaussianZetaBridge.lean`](RiemannGaussian/GaussianZetaBridge.lean)
  develops the spectral Gaussian/RH bridge.
- [`RiemannGaussian/GaussianXiLogDerivativeGrowth.lean`](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean)
  closes the xi contour and arithmetic explicit-formula identification.
- [`RiemannGaussian/GaussianXiMellinSubquadratic.lean`](RiemannGaussian/GaussianXiMellinSubquadratic.lean)
  replaces the quadratic Mellin power-absorption estimate by a checked
  `4/3`-power Young bound, preparing a subquadratic xi divisor count.
- [`RiemannGaussian/GaussianXiSubquadraticGrowth.lean`](RiemannGaussian/GaussianXiSubquadraticGrowth.lean)
  propagates that estimate through completed zeta and proves unconditional
  global `3/2`-power exponential growth for the pole-cleared xi function.
- [`RiemannGaussian/GaussianXiSubquadraticCounting.lean`](RiemannGaussian/GaussianXiSubquadraticCounting.lean)
  inserts the global `3/2` bound into Jensen's inequality and obtains an
  unconditional multiplicity-aware `O(r^(3/2))` xi-divisor count.
- [`RiemannGaussian/GaussianXiInverseSquareSummability.lean`](RiemannGaussian/GaussianXiInverseSquareSummability.lean)
  partitions the xi divisor into dyadic norm shells and proves unconditional
  multiplicity-weighted inverse-square summability in both the complex norm
  and spectral ordinate.
- [`RiemannGaussian/GaussianXiCompleteMassFiniteness.lean`](RiemannGaussian/GaussianXiCompleteMassFiniteness.lean)
  applies inverse-square summability to prove the complete Poisson,
  logarithmic heat-action, and Blaschke-variation masses finite and realizes
  them as convergent nonnegative real series.
- [`RiemannGaussian/RiemannXiFiniteVariationFrontier.lean`](RiemannGaussian/RiemannXiFiniteVariationFrontier.lean)
  defines the actual finite real Blaschke-variation total and, under failure
  of RH, derives a direct residual-versus-unit-phase-energy dichotomy with no
  approximation-height branch.
- [`RiemannGaussian/RiemannXiBlaschkeLogDerivativeSummability.lean`](RiemannGaussian/RiemannXiBlaschkeLogDerivativeSummability.lean)
  proves absolute convergence of the complete signed Blaschke logarithmic
  derivative, identifies the finite residual limit, and makes the residual
  branch of the finite-total frontier a static complete-series bound.
- [`RiemannGaussian/RiemannXiCompletePhaseDispersion.lean`](RiemannGaussian/RiemannXiCompletePhaseDispersion.lean)
  constructs the complete signed variation, cancellation, and phase
  dispersion limits and proves their joint-vanishing criterion is exactly RH.
- [`RiemannGaussian/RiemannXiBoundaryBlaschkeRigidity.lean`](RiemannGaussian/RiemannXiBoundaryBlaschkeRigidity.lean)
  proves absolute convergence and exact positive-imaginary alignment of the
  complete signed Blaschke logarithmic derivative on the real spectral
  boundary, including at critical-line zeros, and reduces RH to one fixed
  cancellation-free invariant at the origin.
- [`RiemannGaussian/RiemannXiBoundaryPoissonLimit.lean`](RiemannGaussian/RiemannXiBoundaryPoissonLimit.lean)
  proves dominated convergence of the complete Blaschke variation to that
  boundary invariant and identifies it as the zero-height limit of the
  exactly normalized complete Poisson mass.
- [`RiemannGaussian/RiemannXiBoundaryHeatActionLimit.lean`](RiemannGaussian/RiemannXiBoundaryHeatActionLimit.lean)
  squeezes the normalized complete proper-time heat action to the same limit
  and proves that its zero boundary slope at any real point is equivalent to
  RH.
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
- [`RiemannGaussian/FiniteToEntireHomotopyNoncollision.lean`](RiemannGaussian/FiniteToEntireHomotopyNoncollision.lean)
  removes the logarithmic-derivative pole at an arbitrary finite-multiplicity
  xi zero and proves that `¬RH` supplies an upper positive-homotopy root at
  which spectral xi is nonzero.
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
- [`RiemannGaussian/FiniteToEntireGaussianTail.lean`](RiemannGaussian/FiniteToEntireGaussianTail.lean)
  proves degree-weighted Gaussian bounds for radial polynomial heat tails and
  arbitrary selected-root complements, reducing remainder vanishing to
  explicit escape and growth conditions.
- [`RiemannGaussian/FiniteToEntireDegreeControl.lean`](RiemannGaussian/FiniteToEntireDegreeControl.lean)
  proves linear degree growth for the separable root-pinned xi sequence and
  the resulting `√n` unused-root separation criterion.
- [`RiemannGaussian/FiniteToEntireExpandingTaylor.lean`](RiemannGaussian/FiniteToEntireExpandingTaylor.lean)
  derives quantitative Cauchy remainder bounds from xi growth and proves
  uniform convergence of the real Taylor approximants on disks of radius
  `c * √n` for a checked constant `c > 0`.
- [`RiemannGaussian/FiniteToEntireFastSeparable.lean`](RiemannGaussian/FiniteToEntireFastSeparable.lean)
  constructs separable exact-root perturbations under arbitrary budgets and
  proves an `exp(-n) / 2` uniform modification bound on any prescribed
  stage-dependent disk.
- [`RiemannGaussian/FiniteToEntireExpandingPinned.lean`](RiemannGaussian/FiniteToEntireExpandingPinned.lean)
  controls the affine exact-root correction through value and derivative
  remainders, then constructs the degree-linear canonical finite Hardy
  sequence converging to spectral xi on `c * √n` disks.
- [`RiemannGaussian/FiniteToEntireBoundaryLowerBound.lean`](RiemannGaussian/FiniteToEntireBoundaryLowerBound.lean)
  derives a quantitative lower modulus for spectral xi on every side of the
  expanding zero-free rectangles from canonical factorization, divisor
  separation, and Jensen's multiplicity bound.
- [`RiemannGaussian/FiniteToEntireRadialBoundary.lean`](RiemannGaussian/FiniteToEntireRadialBoundary.lean)
  selects genuinely expanding zero-free spectral circles, proves uniform
  separation from every xi zero, and derives the corresponding explicit
  double-exponential lower modulus on the full circle.
- [`RiemannGaussian/FiniteToEntireRadialApproximation.lean`](RiemannGaussian/FiniteToEntireRadialApproximation.lean)
  reindexes the exact-root separable Taylor sequence at a controlled
  single-exponential rate and proves its error is strictly below xi on each
  selected circle while retaining an explicit degree-growth bound.
- [`RiemannGaussian/FiniteToEntireRouche.lean`](RiemannGaussian/FiniteToEntireRouche.lean)
  proves the Rouché comparison through an explicit principal-logarithm
  primitive and equates every scheduled polynomial root count with the
  spectral-xi logarithmic-derivative circle integral.
- [`RiemannGaussian/FiniteToEntireRadialDivisor.lean`](RiemannGaussian/FiniteToEntireRadialDivisor.lean)
  defines the exact finite genuine xi divisor in a radial disk and constructs
  synchronized disjoint multiplicity balls contained strictly inside it.
- [`RiemannGaussian/FiniteToEntireRadialRootCount.lean`](RiemannGaussian/FiniteToEntireRadialRootCount.lean)
  proves the compact-complement root partition, identifies the xi circle
  integral with the genuine radial divisor, and gives the scheduled canonical
  Hardy sequence that has exactly this enclosed multiplicity at every stage.
- [`RiemannGaussian/FiniteToEntireRadialHeatTail.lean`](RiemannGaussian/FiniteToEntireRadialHeatTail.lean)
  selects the literal roots inside each scheduled circle, proves every unused
  upper root lies outside it, and shows their complete fixed-time heat tends
  to zero because the quadratic Gaussian beats the exponential degree bound.
- [`RiemannGaussian/FiniteToEntireRadialCrossStage.lean`](RiemannGaussian/FiniteToEntireRadialCrossStage.lean)
  propagates each scheduled boundary error across its disk and proves the
  same polynomial has exact genuine divisor counts on every earlier selected
  circle, preparing a nested annular heat comparison.
- [`RiemannGaussian/FiniteToEntireRadialAnnulus.lean`](RiemannGaussian/FiniteToEntireRadialAnnulus.lean)
  splits nested polynomial divisors exactly into radial annuli, identifies
  their total multiplicities with genuine spectral-divisor increments under
  the cross-stage counts, and proves uniform quadratic-Gaussian upper bounds
  for their upper-root heat.
- [`RiemannGaussian/FiniteToEntireRadialShellTransport.lean`](RiemannGaussian/FiniteToEntireRadialShellTransport.lean)
  uses a continuous positive-part heat weight to transport complete radial
  divisors across the real axis, proves fixed-disk and fixed-annulus heat
  convergence, and packages those limits with the same `¬RH` Hardy sequence
  and its uniform shell majorants.
- [`RiemannGaussian/FiniteToEntireRadialShellSummability.lean`](RiemannGaussian/FiniteToEntireRadialShellSummability.lean)
  proves summability of the selected quadratic-Gaussian shell majorant and a
  reusable Tannery theorem for dominated triangular arrays with moving finite
  cutoffs.
- [`RiemannGaussian/FiniteToEntireRadialHeatLimit.lean`](RiemannGaussian/FiniteToEntireRadialHeatLimit.lean)
  instantiates that triangular array, proves radial spectral windows exhaust
  the complete residue heat series, and establishes full fixed-time
  polynomial-heat convergence for the canonical `¬RH` Hardy sequence.
- [`RiemannGaussian/FiniteToEntireProperTimeCompact.lean`](RiemannGaussian/FiniteToEntireProperTimeCompact.lean)
  proves positive-time antitonicity of the hyperbolic heat kernel and uses
  dominated convergence to identify every compact proper-time polynomial
  action with the corresponding complete spectral-xi heat integral, leaving
  only the endpoints `0` and `infinity` open.
- [`RiemannGaussian/FiniteToEntireProperTimeEscape.lean`](RiemannGaussian/FiniteToEntireProperTimeEscape.lean)
  proves compact actions are bounded by complete finite mass, defines the
  nonnegative endpoint defect, and gives its exact eventual lower bound along
  the canonical `¬RH` sequence.
- [`RiemannGaussian/FiniteToEntireProperTimeLarge.lean`](RiemannGaussian/FiniteToEntireProperTimeLarge.lean)
  proves spectral heat decay at infinity away from the xi divisor, derives an
  eventual uniform polynomial-root gap from locally uniform convergence, and
  uses the noncolliding canonical sequence to close the large-time endpoint
  outright, leaving only proper time zero.
- [`RiemannGaussian/FiniteToEntireProperTimeSmall.lean`](RiemannGaussian/FiniteToEntireProperTimeSmall.lean)
  proves exact three-piece action additivity and forces every remaining
  canonical Hardy defect into quantitatively bounded, stage-dependent
  small-time intervals.
- [`RiemannGaussian/FiniteToEntireProperTimeSmallBound.lean`](RiemannGaussian/FiniteToEntireProperTimeSmallBound.lean)
  identifies the exact zero-time heat trace with total upper-root height,
  bounds small-time actions by that statistic, and derives its necessary
  canonical growth inequality under `¬RH`.
- [`RiemannGaussian/FiniteToEntireProperTimeHeightVariation.lean`](RiemannGaussian/FiniteToEntireProperTimeHeightVariation.lean)
  identifies upper-root height with half the unsigned imaginary variation,
  proves exact cancellation of the signed first moment, and propagates the
  canonical obstruction to total root-norm mass.
- [`RiemannGaussian/RiemannXiUpperHeightTrace.lean`](RiemannGaussian/RiemannXiUpperHeightTrace.lean)
  constructs the extended upper spectral height mass, proves that the
  complete spectral heat tends to its exact trace as proper time approaches
  zero, factors that trace by observation height, and characterizes RH by
  vanishing of the resulting mass.
- [`RiemannGaussian/RiemannXiHyperbolicHeatAction.lean`](RiemannGaussian/RiemannXiHyperbolicHeatAction.lean)
  constructs the complete extended proper-time action, proves the one-zero
  Lebesgue integral identity, exchanges the spectral series and integral by
  Tonelli, and identifies the result with the full logarithmic-defect sum.
- [`RiemannGaussian/FiniteToEntireProperTimeActionTransfer.lean`](RiemannGaussian/FiniteToEntireProperTimeActionTransfer.lean)
  proves compact spectral actions are dominated by the complete action,
  transfers the finite Hardy threshold under eventual height control, and
  derives the canonical spectral-defect-versus-unbounded-height dichotomy.
- [`RiemannGaussian/RiemannXiHyperbolicDefectHeight.lean`](RiemannGaussian/RiemannXiHyperbolicDefectHeight.lean)
  obtains a uniform gap from a noncolliding observation point to the spectral
  divisor and uses it to bound the complete logarithmic defect and heat action
  by the extended upper spectral height mass.
- [`RiemannGaussian/RiemannXiCriticalLineDeviation.lean`](RiemannGaussian/RiemannXiCriticalLineDeviation.lean)
  uses critical-line reflection and multiplicity invariance to identify twice
  the upper spectral height with the full absolute horizontal displacement of
  nontrivial zeta zeros from `Re(s) = 1/2`.
- [`RiemannGaussian/RiemannXiSpectralWindowMass.lean`](RiemannGaussian/RiemannXiSpectralWindowMass.lean)
  realizes the complete upper-height, absolute-displacement, and logarithmic-
  defect masses as limits of explicit cofinal finite spectral-window sums and
  proves the finite-window reflection identity exactly.
- [`RiemannGaussian/RiemannXiHyperbolicPoissonDefect.lean`](RiemannGaussian/RiemannXiHyperbolicPoissonDefect.lean)
  identifies the disk defect with its upper-half-plane Poisson weight, proves
  its lower comparison with logarithmic defect per zero and over the complete
  divisor, and characterizes RH by vanishing of the resulting Poisson mass.
- [`RiemannGaussian/RiemannXiSpectralLogDerivativeWindow.lean`](RiemannGaussian/RiemannXiSpectralLogDerivativeWindow.lean)
  decomposes the genuine spectral-xi logarithmic derivative into its finite
  multiplicity-weighted Cauchy divisor sum and a remainder, proves all
  selected singularities removable, and patches the remainder analytically
  across the complete safe contour rectangle.
- [`RiemannGaussian/RiemannXiBlaschkeDerivativeVariation.lean`](RiemannGaussian/RiemannXiBlaschkeDerivativeVariation.lean)
  computes the elementary spectral Blaschke derivatives and identifies the
  finite and complete Poisson masses exactly with observation height times
  total multiplicity-weighted derivative variation.
- [`RiemannGaussian/RiemannXiBlaschkeLogDerivativeCancellation.lean`](RiemannGaussian/RiemannXiBlaschkeLogDerivativeCancellation.lean)
  assembles the finite spectral Blaschke product, identifies its logarithmic
  derivative with the signed paired Cauchy sum, isolates the nonnegative
  triangle-cancellation gap, and bounds finite Poisson mass by the product
  log-derivative norm plus that gap.
- [`RiemannGaussian/RiemannXiSpectralReflectionPairing.lean`](RiemannGaussian/RiemannXiSpectralReflectionPairing.lean)
  partitions full xi Cauchy windows by spectral height, pairs upper and lower
  terms through critical-line reflection, and derives the unified identity
  connecting genuine `xi'/xi`, its analytic window remainder, critical-line
  poles, and the finite spectral Blaschke logarithmic derivative.
- [`RiemannGaussian/RiemannXiHyperbolicDefectPoissonEquivalence.lean`](RiemannGaussian/RiemannXiHyperbolicDefectPoissonEquivalence.lean)
  combines the uniform noncollision gap with the critical-strip height bound
  to prove two-sided comparability of complete logarithmic defect, proper-time
  heat action, and Poisson defect by an explicit finite positive coefficient.
- [`RiemannGaussian/FiniteToEntirePoissonBlaschkeTransfer.lean`](RiemannGaussian/FiniteToEntirePoissonBlaschkeTransfer.lean)
  transports the canonical failure-of-RH Hardy alternative into explicit
  positive normalized lower thresholds for complete Poisson mass and complete
  spectral Blaschke derivative variation, retaining the unbounded-height
  alternative exactly.
- [`RiemannGaussian/FiniteToEntireBlaschkeCancellationFrontier.lean`](RiemannGaussian/FiniteToEntireBlaschkeCancellationFrontier.lean)
  exhausts a positive complete variation threshold through finite windows and
  forces half of it into the exact xi reflection residual plus the explicit
  finite Blaschke cancellation gap at every sufficiently large window.
- [`RiemannGaussian/FiniteToEntireBlaschkeRigidityTrichotomy.lean`](RiemannGaussian/FiniteToEntireBlaschkeRigidityTrichotomy.lean)
  separates that sum into a frequently-large xi residual, an eventually-large
  Blaschke cancellation gap, or unbounded canonical polynomial height mass.
- [`RiemannGaussian/RiemannXiBlaschkePhaseDispersion.lean`](RiemannGaussian/RiemannXiBlaschkePhaseDispersion.lean)
  identifies the squared Blaschke cancellation loss with an exact nonnegative
  double sum of pairwise angular defects and transfers the canonical
  cancellation branch into an eventual positive phase-dispersion threshold.
- [`RiemannGaussian/RiemannXiBlaschkePhaseGeometry.lean`](RiemannGaussian/RiemannXiBlaschkePhaseGeometry.lean)
  proves nonvanishing of every upper spectral Blaschke summand at a
  noncolliding point and rewrites each pair defect as a weighted squared
  chordal distance between genuine unit complex phases.
- The `GramWeil*` files contain the abstract block defect, inertia, and metric
  pencil theory.
- [`RiemannGaussian.lean`](RiemannGaussian.lean) is the umbrella module built
  by the default target.

This repository should be read as an active formal research program. Git
history records the fine-grained proof audit; this README records the purpose,
the checked mathematical state, and the exact open frontier.
