# RiemannGaussian

Lean 4.33.1/Mathlib 4.33.1 checks the finite rational portions of the
restricted Gaussian-Weil positivity certificates at epsilon 0.04, 0.05,
and 0.06.

> [!IMPORTANT]
> This is an incomplete research formalization. It does **not** contain a
> proof of the Riemann hypothesis; the unproved bridges are listed below.

What is checked here:

- every derivative interval at all three endpoints, including the signed
  8,400-cell epsilon 0.06 partition;
- the epsilon 0.06 downward-rounded cumulative derivative increase;
- the final rational endpoint and large-t budgets.
- the exact Gaussian heat-convolution identities;
- construction of every positive-width symmetric Gaussian as a Schwartz map;
- the abstract closed-positive-cone extension theorem;
- normalized real-Schwartz Gaussian smoothing and its positivity/evenness;
- the entire spectral Gaussian, its convolution-square factorization on the
  critical line, and the exact sign-changing contribution of an off-line
  conjugate pair;
- the exact packet-gap exponent, decay of every positive-gap relative
  envelope, and domination of any finite competing packet family by a
  maximal-height off-axis packet;
- dominated-convergence separation against an arbitrary infinite weighted
  packet family from one summable baseline Gaussian envelope;
- the distinct translated and symmetric zero-sum interfaces, including the
  exact normalization used by the arithmetic certificates and eventual
  detection of an isolated off-axis packet by that symmetric family;
- equivalence between Mathlib's `RiemannHypothesis` and reality of all
  nontrivial zeros in the rotated spectral coordinate;
- the multiplicity-aware zero-sum bridge interface, including local
  finiteness of distinct zeta zeros, construction and positivity of their
  analytic order-of-vanishing multiplicities, and preservation of those
  multiplicities by conjugation and the functional equation;
- absolute Gaussian-envelope summability deduced directly from a complex
  `HasSum` representation, countability of the packet-tie exceptional set,
  existence of a uniquely maximal off-axis packet, and the complete global
  translated-Gaussian zero-divisor separation theorem;
- the resulting unconditional equivalence, given a translated `HasSum`
  representation, between all-translated-Gaussian nonnegativity and Mathlib's
  `RiemannHypothesis`;
- functional-equation reindexing showing that every represented translated
  value is even and that a compatibly represented symmetric value is exactly
  twice the translated value; hence symmetric nonnegativity is also
  equivalent to RH when both representations are supplied;
- construction of canonical translated and symmetric `HasSum`
  representations from the isolated condition that every positive Gaussian
  in the multiplicity-counted zero ordinate is summable;
- an unconditional quadratic growth bound for the pole-cleared xi function,
  obtained from Mathlib's theta-kernel estimates, and the resulting
  unconditional Gaussian ordinate summability and canonical zero sums;
- the unconditional equivalence between nonnegativity of the canonical
  symmetric Gaussian zero sum at every positive width and Mathlib's
  `RiemannHypothesis`;
- complex Gaussian heat convolution at arbitrary spectral points, absolute
  integral/sum interchange over the complete multiplicity-aware zeta zero
  divisor, and unconditional heat propagation of both canonical zero sums;
- propagation of canonical nonnegativity from one width to every smaller
  positive width;
- the exact arithmetic normalization of the prime, boundary, and digamma
  terms, with absolute convergence of the Gaussian von Mangoldt series;
- a vertical exponential bound for
  `digamma (1/4 + I*r/2)`, derived from Euler's Gamma integral and reflection
  formula, proving that the Archimedean digamma integral converges at every
  positive Gaussian width;
- an elementary, multiplicity-aware xi divisor calculation on every finite
  zero-free spectral rectangle: each enclosed principal part contributes
  exactly `2*pi*I` times its residue, and the full xi contour is exactly
  `-2*pi` times the corresponding finite symmetric Gaussian zero sum;
- cofinal convergence of those multiplicity-weighted finite windows to the
  canonical symmetric Gaussian `HasSum`, construction of a zero-free
  truncation in every interval `(n,n+1)`, convergence of the horizontal safe
  lines, and an exact reduction of the explicit-formula identification to
  decay of one right vertical-side integral along an arbitrary admissible
  truncation sequence;
- a quantitative contour interface that existentially selects the admissible
  sequence (so it may be kept away from zeros), together with a proof that any
  fixed exponential bound for the xi logarithmic derivative on those contours
  is overwhelmed by the Gaussian and therefore gives the required vertical
  decay at every positive width;
- an explicit pigeonhole construction of one quantitatively zero-separated
  contour in every unit height interval; Jensen's divisor bound makes the
  reciprocal separation radius at most quadratic, and the complete vertical
  segment is proved to stay at least that radius from every spectral xi zero;
- construction, at each contour scale, of a larger zero-free circle and an
  extended canonical decomposition of xi there; on that circle the zero-free
  residual has exactly the same norm as xi, so maximum modulus transfers the
  checked quadratic-exponential xi growth bound throughout the enclosed disk;
- a normalized analytic logarithm of that residual, including the exact
  exponential reconstruction identity and the lower normalization
  `1 ≤ ‖g 0‖`; Borel--Carathéodory followed by Cauchy's estimate now gives
  an explicit polynomial bound for the residual logarithmic derivative on the
  inner quarter-disk;
- exact logarithmic differentiation of the finite canonical zero-factor
  product, an explicit reciprocal-separation bound for each factor, Jensen
  control of the total multiplicity, and transfer of the resulting bound to
  the quantitatively separated spectral contours;
- an unconditional exponential bound for the xi logarithmic derivative on
  those contours, hence Gaussian decay of the final vertical sides and an
  unconditional proof of `GaussianArithmeticExplicitFormulaIdentified`;
- the pointwise identity
  `gaussianArithmeticExplicitFormula ε t =
  canonicalZetaSymmetricGaussianZeroSum ε t` for every `0 < ε`, exact
  arithmetic heat propagation, and the unconditional equivalence of
  all-width arithmetic nonnegativity with RH;
- the exact cofinal-width reduction: all-width positivity is equivalent to
  finding good arithmetic Gaussian widths arbitrarily far to the right, so a
  successful certificate program only needs an unbounded family of widths;
- an exact low-prime/infinite-tail decomposition of the convergent arithmetic
  expression and a soundness theorem for the endpoint/compact/tail/large-`t`
  certificate architecture; an unbounded family of sound certificates is
  proved to imply RH;
- parameter-uniform high-prime control: whenever `log N ≥ 8 * epsilon`, the
  complete tail beyond `N` is bounded by a fixed summable von-Mangoldt
  `n^(-2)` tail, and Lean proves that comparison tail tends to zero as
  `N → ∞`;
- the complete integrated prime oscillation energy
  `sum q_n(epsilon) * (1 - cos(t * log n))`: every summand is nonnegative,
  every finite analytically chosen block is a rigorous lower bound, and the
  full energy is exactly the drop in the oscillatory prime contribution;
- the exact margin-aware energy budget saying that the endpoint value plus
  prime energy must pay the Archimedean drop.  At one width this is equivalent
  to full centerwise positivity, and having such widths cofinally is proved
  equivalent to RH; no assertion that center zero is a global minimum is
  smuggled into the reduction;
- exact cancellation of the continuous-PNT prime-energy main term against the
  exponentially large elementary boundary drop.  The surviving formula is
  endpoint plus digamma gain plus a Gaussian-smoothed von-Mangoldt
  discrepancy, and cofinal validity of this cancellation-aware budget is
  again proved equivalent to RH;
- a fully checked bilateral Gaussian-transform evaluation, including
  integrability, proving that this closed-form main term is exactly the
  continuous density integral against `exp (u / 2) du`; consequently the
  remaining prime discrepancy is now an exact normalized difference between
  the von-Mangoldt atoms at `log n` and that continuous measure, ready for a
  summation-by-parts or transport estimate;
- the exact split of that bilateral density into the forward PNT measure on
  positive logarithmic coordinates and its reflected Archimedean correction;
  the combined digamma-plus-prime frontier is correspondingly reduced to a
  forward prime discrepancy plus an explicit digamma remainder;
- finite Abel summation specialized to the exact multiplicative Gaussian
  kernel: every cutoff of the forward discrepancy is a boundary term
  `K(b) * (psi(b) - b)` plus one integral of the explicit derivative `K'`
  against the classical Chebyshev error `x - psi(x)`, with the logarithmic
  change of variables back to the project energy coordinates checked in Lean;
- passage of that Abel identity to the infinite forward discrepancy: the
  finite atomic and continuous energies converge to their full counterparts,
  the Chebyshev boundary term tends to zero using an explicit linear bound for
  `psi` plus Gaussian decay, and the normalized improper Chebyshev-error
  integrals converge to the exact forward discrepancy;
- a finite phase-block interface: any lower bound for weighted von-Mangoldt
  mass on a block where `1 - cos (t * log n)` has a uniform floor becomes a
  kernel-checked lower bound for the true prime energy and hence a sufficient
  centerwise positivity criterion;
- exact differentiation of the retained prime block at arbitrary width and
  cutoff, including its closed signed-sinc form
  `F_prime'(t) = t * sum (q_n(epsilon) * sinc(t * log n))`; this is the
  parameterized low-prime object a uniform argument must control;
- the abstract frozen-hinge/Legendre reduction suggested by the screw-function
  attack: every nonnegative-weight frozen regime majorizes the true locally
  finite hinge model, agrees with it on its event cell, and pointwise
  nonnegativity is exactly equivalent to nonnegativity of all bounded-below
  frozen infimum barriers;
- specialization of that reduction to the complete Suzuki von-Mangoldt event
  schedule `log (n + 2)` with weights `Lambda(n + 2) / sqrt(n + 2)`, including
  local finiteness and coverage of every center; positivity of the exact
  smooth curvature beyond `log 2` and its strict comparison with the pure
  exponential approximation; and the order-theoretic Legendre transport
  comparison, stated correctly as a sufficient condition while retaining the
  exact positive base-margin obligation;
- the exact curvature-mass form of every frozen Legendre barrier: a point
  whose accumulated smooth curvature equals the frozen prime mass is proved,
  without differentiating an infimum, to be the global half-line minimizer;
  Suzuki curvature is continuous, bounded below by `1/2` beyond `log 2`, and
  has a unique mass-matching point for every prefix, so tail-model
  nonnegativity is reduced canonically to one transport-moment inequality
  quantified uniformly over all cutoffs;
- the exact consecutive-cell dynamics of that transport criterion: canonical
  mass points are monotone, the curvature mass of each cell is exactly the
  next von-Mangoldt weight, and the next gap equals the old gap plus the
  signed prime-versus-smooth barycenter surplus.  Prefix and arbitrary-block
  gaps telescope to cumulative cell surpluses, with sharp endpoint bounds;
  zero-weight non-prime-powers contribute identically zero.  Consequently the
  full tail criterion is now equivalent to one cumulative-surplus lower bound
  at every cutoff, retaining rather than discarding cancellation across cells;
- the corrected tail reset needed for an actual Suzuki trajectory: Lean splits
  the full locally finite hinge model after an arbitrary finite prime prefix,
  shifts the remaining event schedule, and represents a nonpositive audited
  base slope by one synthetic nonnegative event at the base.  The corrected
  transport gaps again telescope exactly; cell zero is the descent to the
  zero-slope point and subsequent cells correspond to the genuine future
  prime weights.  Subject to one explicit tail-normalization identity, full
  model positivity is equivalent to the cumulative-surplus bound for this
  shifted schedule, rather than for an incorrectly restarted prime sequence;
- the exact Gaussian/Suzuki curvature interface: the quarter-line digamma
  density splits pointwise into the reflected continuous-PNT density plus
  Suzuki's missing curvature; its Gaussian missing-curvature integrand is
  proved integrable both across the apparent singularity at zero and at
  infinity; and subtracting it from the forward continuous energy is proved
  to be the literal Gaussian transform of `suzukiSmoothCurvature`;
- a proof of the pointwise identity
  `QuarterLineDigammaGaussDifferenceFormula` from Mathlib's Gamma integral and
  Euler approximation: Lean differentiates the compact Euler approximants,
  proves dominated convergence for the log-weighted kernels, derives Euler's
  digamma series on the right half-plane, evaluates each nonnegative vertical
  difference term as a damped-cosine Laplace integral, performs the Tonelli
  exchange, sums the geometric kernel, and checks the final `t = 2u`
  substitution;
- the resulting unconditional `GaussianDigammaScrewTransform`: the arithmetic
  formula is exactly endpoint plus atomic prime energy minus Suzuki
  smooth-curvature energy, and cofinal validity of that exact energy budget is
  kernel-checked equivalent to RH;
- the abstract finite-dimensional Gram--Weil block-defect theorem over real or
  complex Hilbert spaces: for every injective `C : N → P`, Lean constructs
  maximal positive and negative subspaces for
  `[[0, -C], [-C†, 2I]]`, proves both have dimension `dim N`, and proves its
  kernel has dimension `dim P - dim N`; thus its basis-free quadratic inertia
  is exactly `(dim N, dim P - dim N, dim N)` in negative/null/positive order;
- the matching finite metric-pencil algebra for
  `G = [[I,-C],[-C†,I]]` and `J = diag(I,-I)`: `G-J` is definitionally linked
  to the checked defect, every generalized eigenvector away from `lambda = 1`
  yields `C† C n = (1-lambda^2)n`, every such mode has a proved converse
  lift, the `lambda = 1` kernel has dimension `dim P - dim N`, and explicit
  injectivity plus pointwise strict contraction forces every supplied real
  nonexceptional pencil eigenvalue into `(-1,1)`;
- the complete one-dimensional metric-pencil classification: for the scalar
  cross-angle `0 < c < 1`, a nonzero generalized eigenvector exists exactly at
  `lambda = ± sqrt (1 - c^2)`, with both converse eigenvectors constructed
  explicitly and the exceptional value `lambda = 1` excluded;
- the analytic quadratic one-pair realization for `A(z) = z^2 + a^2`: the
  two improper rational integrals and the odd cross integral are proved from
  Mathlib's full-line Cauchy integral, the normalized complex zero functions
  have literal `2 × 2` Gram matrix
  `(1 / sqrt (1 + a^2)) I`, and the corresponding Weil metric pencil is
  singular exactly at `lambda = ± 1 / sqrt (1 + a^2)`;
- the algebraic barriers for the general finite homotopy
  `E_tau = A + I * tau * A'`: for separable real `A` and nonzero `tau`, Lean
  proves that `E_tau` and `E_tau^sharp` have no real zeros and no common
  complex zero, hence are coprime; both retain the degree and leading
  coefficient of `A`; coefficient conjugation exactly interchanges them and
  conjugates their root multisets with multiplicity; and their open
  upper/lower root counts exhaust `A.natDegree`;
- the corresponding literal upper and lower monic root factors, retaining
  multiplicity, and the exact reconstruction of `E_tau` as its leading
  coefficient times those two factors; the conjugate of the upper factor is
  proved zero-free throughout the open upper half-plane, and its finite
  Blaschke quotient has equal numerator/denominator degree and norm exactly
  one at every real point;
- the direct finite Krein--Langer identity in the field `RatFunc ℂ`:
  `B * Theta = S` and equivalently `Theta = S / B`, with both removable
  root factors cancelled algebraically; the pointwise `B` and `S` are proved
  complex differentiable throughout the open upper half-plane, bounded there
  by one in norm, and unimodular on the real axis; their degrees add to
  `A.natDegree`, with the exact `kappa`/`A.natDegree - kappa` split reduced to
  the isolated upper-root-count theorem; moreover `Theta(gamma) = -1` is
  proved at every complex zero `gamma` of separable `A`;
- the pointwise form `B(z) * Theta(z) = S(z)` wherever the rational
  representatives are defined, and the exact de Branges kernel-numerator
  identity expressing the transformed `Theta` kernel as the `S` kernel minus
  the `B` kernel; at every zero `gamma` of `A`, all required denominators are
  proved nonzero and Lean derives `S(gamma) = -B(gamma)` and hence
  `B(gamma) + S(gamma) = 0`;
- the normalized finite zero-vector split from the proposed analytic route:
  `A(z) / (z - gamma)` is represented by a literal polynomial quotient,
  its value at the removed root is proved to equal `A'(gamma)`, and Lean
  proves `B * F_gamma = u_gamma - n_gamma` with the exact `I / sqrt pi`
  normalization; for separable `A`, the quotient polynomials indexed by all
  complex roots are linearly independent, and that root index set is proved
  to have cardinality `A.natDegree`;
- the finite algebraic model spaces for the rational factors `S` and `B` as
  numerator spaces of degree below their denominators: Lean proves their
  exact dimensions, constructs canonical polynomial coordinates for every
  `S`- and `B`-difference quotient, and identifies their evaluations with the
  normalized positive and negative zero-vector splits; after clearing the
  common denominator, the coordinate pair reconstructs the original
  Lagrange quotient exactly, which proves that the root-coefficient-to-pair
  map is a complex-linear isomorphism rather than just a dimension count;
- the common-numerator algebra behind the next Hilbert-space step: all needed
  reflected and cross-factor coprimality statements are proved, the
  `D * q_S + V * q_B` Sylvester map is promoted to a literal linear
  equivalence, the common-denominator copies of `K_S` and `K_B` are proved
  transverse, and the corresponding `S K_B` transversality needed for an
  injective cross-angle is proved under the isolated degree inequality;
- an explicit finite algebraic Hilbert realization obtained by transporting
  the Sylvester coordinates to Euclidean coefficient spaces with the `L²`
  product norm: the negative Blaschke copy is embedded as a subspace, its
  first-coordinate cross angle is proved pointwise strictly contractive, and
  it is proved injective under the isolated degree inequality; Lean then
  derives the exact Gram--Weil defect inertia from the abstract block theorem;
- the first genuine Hardy-boundary realization of the finite model spaces:
  every rational numerator coordinate is proved continuous and square
  integrable by an explicit `O(1/|x|)` estimate, embeds faithfully into
  complex `L²(ℝ)`, and has finite-dimensional closed image.  The positive and
  negative images are proved transverse, so their actual orthogonal
  cross-angle is pointwise strictly contractive;
- the exact root-count bridge behind that degree inequality: conjugation
  proves equal upper/lower counts at homotopy parameter zero, and Lean proves
  that invariance of the upper count from zero to the target parameter implies
  the required degree inequality, cross-angle injectivity, and defect inertia;
- the first rigorous continuity layer for that finite homotopy: after a monic
  normalization which preserves every root with multiplicity, all coefficients
  converge uniformly in their index, Mathlib's quantitative root-stability
  theorem gives nearby roots, and a separation argument proves local constancy
  of the upper-half-plane root count at every nonzero separable homotopy
  member; consequently the count is globally constant on all positive
  parameters whenever the positive homotopy is collision-free;
- the collision-safe completion of that continuity argument: reverse root
  persistence proves that every nearby root remains close to the base root
  set, Newton identities and Vieta's formulas prove continuity of every root
  power sum with multiplicity, and Lagrange interpolation turns those moments
  into an exact local upper-half-plane count; Lean therefore proves, without
  assuming the homotopy members separable, that the upper count is locally
  constant at every nonzero parameter and hence constant throughout the entire
  positive parameter interval, including through multiple-root collisions;
- the endpoint evaluation of that constant count: a branch-free local quotient
  argument proves that every real zero of the separable base polynomial moves
  into the lower half-plane for small positive parameter, while nonreal roots
  retain their half-plane classification; root moments and interpolation then
  prove exact equality with the parameter-zero upper count.  Thus the root
  factor degree inequality, cross-angle injectivity, and exact algebraic
  Gram--Weil inertia now hold unconditionally for every positive parameter;
- the separation-free scalar core of the symmetric-quartet attack: for one
  conjugate zero pair Lean proves the exact pseudo-hyperbolic lower bound for
  its logarithmic-derivative imaginary part; the associated cost is proved
  strictly superadditive under multiplication, its sharp unit-cost threshold
  is evaluated exactly, and a symmetric quartet pole equation against any
  background with nonnegative imaginary part forces the degree-two Blaschke
  modulus strictly below that threshold, with no restriction on the quartet's
  horizontal separation;
- the complete finite-residual symmetric two-node Pick calculation: Lean
  factors the degree-two base kernel through two explicit features, identifies
  its determinant as a positive squared wedge norm, proves both exact inverse
  Schur coefficients (including the reflected phase identity), and identifies
  the literal sampled `3 × 3` Pick matrix with the general Schur block.  Every
  elementary upper-half-plane Blaschke factor has a rank-one positive Pick
  kernel, finite products remain positive by the Schur product theorem, and
  the existing finite residual inner factor therefore satisfies the sharp
  separation-free bound `|S(p)| ≤ 2*b/(1+b^2)` under the two symmetric
  interpolation identities.  Composing this with the strict quartet pole
  threshold gives the end-to-end strict bound
  `|S(p)| < m / sqrt (m^2 + a^2)`; under the reflected-value identity, Lean
  also proves the squared two-pole product bound
  `|S(p) S(-conj p)| < m^2 / (m^2 + a^2)`;
- the coherent Gaussian cross-term formula and the proof that, under RH and a
  represented zero sum, every finite coherent-state Gram matrix is positive
  semidefinite.

What is not yet checked here:

- the fixed-point integration loops mirrored by the Python certificates;
- a definition and continuity theorem for Weil's functional on the correct
  analytic-strip test class;
- the theorem connecting each endpoint certificate's scalar ledgers to the
  convergent arithmetic expression itself;
- an unbounded family of certified good widths (and hence nonnegativity of the
  arithmetic/canonical expression for every `epsilon > 0`; only the finite
  rational portions at 0.04--0.06 are checked).
- a uniform positivity mechanism for the growing retained prime block below
  the parameter-dependent cutoff; the new tail theorem shows that this, not
  the infinite high-prime tail, is the scalable obstruction.
- the analytic identification of the full Suzuki screw function with the new
  hinge model, the exact audited initial value/slope normalization, or
  nonnegativity of the resulting canonical infinite transport-gap sequence.
  The finite-prefix shift and nonzero-slope reset are now checked and the
  required normalization is isolated as the function-valued proposition
  `SuzukiTailNormalization`; it has not yet been discharged for Suzuki's
  explicit Archimedean term.  Existence, exact evaluation, and the
  consecutive/block recurrence of the corrected gaps are checked, but their
  cumulative-surplus lower bound over all cutoffs remains RH-strength.
- the remaining analytic finite-polynomial realization of the checked
  abstract Gram--Weil block theorem: although the rational model spaces now
  embed faithfully as closed subspaces of actual boundary `L²` and their
  orthogonal cross angle is strictly contractive, the Hardy orthogonality
  calculation needed to prove that projection injective and identify the
  resulting Gram geometry is not yet checked.  No claim is made that the
  auxiliary Euclidean coefficient norm is the Hardy boundary norm.  Spectral
  completeness for
  all `±sqrt(1-s_j^2)` pencil modes is also not yet formalized beyond the
  checked scalar and analytic one-pair cases. Nor is any infinite-dimensional
  lift to the xi function; that remains a research program, not an RH proof.
- extension of the now-checked finite-residual symmetric two-node estimate to
  the intended general/infinite inner factor, and its claimed identification
  with the two nonunit Gram--Weil metric-pencil magnitudes.  The exact finite
  Schur coefficients, symmetry identities, sampled matrix equality, Pick
  positivity, and sharp value bound are checked; the infinite analytic
  passage and the metric-pencil link remain separate proof obligations and
  are not assumed;
- a parameter-uniform lower bound for the combined Gaussian prime discrepancy
  plus digamma gain.  Numerical falsification shows that neither term may be
  discarded: they undergo a large cancellation before the very small spectral
  margin remains.  The phase-block theorem now isolates the required weighted
  prime-mass input without signed summands.

The finite endpoint files are calibration and audit artifacts, not a proposed
infinite certificate ladder.  Closing the final item requires one
parameter-uniform mechanism producing an unbounded family (or a stronger
structural positivity theorem); enumerating successively larger endpoint
ledgers will not scale.

The ordinary Schwartz closed-cone theorem is now explicitly treated as an
abstract auxiliary result.  The classical unconditional Weil functional is
defined on an analytic-strip class and the RH criterion is quadratic on
convolution squares; ordinary Schwartz density alone is not a valid bridge.
The direct spectral argument now proves that scalar all-Gaussian positivity
is sufficient for the unconditional canonical sum; coherent Gram matrix
positivity remains a separate, stronger connection to Weil's quadratic
formulation.  The arithmetic/canonical equality is now unconditional.  The
decisive remaining problem is nonnegativity of that explicit common value for
every positive `epsilon` and every real center.  The completed contour and
logarithmic-derivative development is in
[`GaussianXiLogDerivativeGrowth.lean`](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean).

Build from this directory with:

```bash
lake exe cache get
lake build
```
