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
  hinge model, boundedness below of its frozen regimes, or nonnegativity of the
  resulting infinite barrier sequence.  The cumulative transport inequality
  proposed in the research note is stronger than necessary when the verified
  base margin is positive, and proving it globally remains RH-strength.

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
