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
- a single explicit predicate,
  `GaussianArithmeticExplicitFormulaIdentified`, isolating equality of that
  convergent arithmetic expression with the canonical symmetric zero sum;
- conditional on that identification, exact arithmetic heat propagation and
  equivalence of all-width arithmetic nonnegativity with RH;
- the coherent Gaussian cross-term formula and the proof that, under RH and a
  represented zero sum, every finite coherent-state Gram matrix is positive
  semidefinite.

What is not yet checked here:

- the resulting exponential bound for the xi logarithmic derivative on the
  now-constructed quantitatively separated contours; deriving this from the
  checked quadratic xi growth and zero-counting estimates is now the isolated
  infinite-height input needed to prove
  `GaussianArithmeticExplicitFormulaIdentified` (Lean already proves that
  such a bound kills the vertical contours, while the horizontal limit,
  canonical zero-sum limit, analytic digamma convergence, and finite residue
  identity are checked, but the prime/zero equality is not);
- the fixed-point integration loops mirrored by the Python certificates;
- a definition and continuity theorem for Weil's functional on the correct
  analytic-strip test class;
- the theorem connecting each endpoint certificate's scalar ledgers to the
  convergent arithmetic expression itself;
- nonnegativity of the arithmetic/canonical expression for every
  `epsilon > 0` (only the finite rational portions at 0.04--0.06 are checked).

The ordinary Schwartz closed-cone theorem is now explicitly treated as an
abstract auxiliary result.  The classical unconditional Weil functional is
defined on an analytic-strip class and the RH criterion is quadratic on
convolution squares; ordinary Schwartz density alone is not a valid bridge.
The direct spectral argument now proves that scalar all-Gaussian positivity
is sufficient for the unconditional canonical sum; coherent Gram matrix
positivity remains a separate, stronger connection to Weil's quadratic
formulation.  The decisive remaining analytic equality is between that
canonical sum and `gaussianArithmeticExplicitFormula`. The active
finite-divisor contour development is in
[`GaussianXiDivisorContour.lean`](RiemannGaussian/GaussianXiDivisorContour.lean).

Build from this directory with:

```bash
lake exe cache get
lake build
```
