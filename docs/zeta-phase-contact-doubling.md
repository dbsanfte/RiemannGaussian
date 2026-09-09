# Prime-square work forced by the exact phase optimiser

The exact optimiser supplies a local arithmetic improvement through its
contact geometry. Its four contact cosines cannot return to that contact
set under the angle-doubling map. Lean now proves a uniform positive floor
for the two kernel values, transfers it to a prime and its square, and
retains the resulting reserve in the actual zeta zero inequality.

This is an independent bound for the original nonnegative phase work.
It does not bound the different signed finite prime moment needed by the
global RH goal. The new local nonvanishing test has a proved positive
constant, but no new numerical value for that constant or calibrated
zero-free strip is claimed.

The existing general recurrence already forces positive work from a
longer prime-power block. The new result locates an obstruction within
just the prime and its square. It is not claimed to provide a larger
floor: exploratory evaluation of the rational coefficient centre suggests
the uniform two-term minimum gives a substantially smaller floor than the
earlier four-return estimate. This comparison is numerical evidence only;
the new positive-floor and local-exclusion theorems do not rely on it.

## The contact set cannot persist under doubling

Write the exact kernel as `P(theta)=Q(cos(theta))`. The existing
`phaseContactExactKernel_eq_zero_iff` identifies precisely four roots
`c_j` of `Q` in `[-1,1]`; the quotient after their squared factors is
strictly positive. These are exact roots, with proved rational enclosures.

Angle doubling acts on cosine coordinates by `T2(x)=2*x^2-1`.
The new theorem `phaseContactExact_doubled_contact_gap` proves

\[
\boxed{|T_2(c_i)-c_j|\ge\frac1{20}\quad\text{for all four }i,j.}
\]

The proof checks the separation at the rational contact centre and pays
the already proved exact-root error using the Chebyshev secant estimate.
No floating-point root is treated as an exact contact.

Because `Q>=0`, simultaneous vanishing of `Q(x)` and `Q(T2(x))` would
contradict this separation. Thus `phaseContactExactKernel_add_double_pos`
proves strict positivity of their sum throughout `[-1,1]`. Continuity and
compactness then give one constant `c>0`, independent of angle, with

\[
\boxed{P(\theta)+P(2\theta)\ge c\quad\text{for every real }\theta.}
\]

This is `exists_phaseContactExact_doubling_floor`. A value of `c` is
obtained from a minimum of the exact continuous polynomial expression on
the full compact interval, not a sampled numerical minimum. The theorem
does not identify the largest possible `c` or assert `c=1/20`: the latter
is a gap between contact cosines, a different quantity.

The structural point is stronger than mere nonnegativity. A phase can
make one term vanish, but the linked doubled phase must pay a positive
cost. The coefficient optimiser itself still attains its proved optimum;
it is the zero inequality that loses information when it drops all
arithmetic work.

## A general arithmetic transfer

`zetaPhase_prime_square_floor` applies to any summable nonnegative
real-frequency spectrum with a nonnegative kernel satisfying the displayed
doubling floor. It is not restricted to the exact optimiser, a finite
frequency count, or integer frequencies.

For a prime `p`, let `theta=y*log p`. The terms indexed by `p` and `p^2`
in the actual phase work are

\[
(\log p)p^{-\sigma}P(\theta)
  +(\log p)p^{-2\sigma}P(2\theta).
\]

For `sigma>1`, both are nonnegative and the first weight is at least
the second. All remaining terms are also nonnegative and the full series
converges. Therefore

\[
\boxed{W_\sigma(y)
 =\sum_{n\ge1}\Lambda(n)n^{-\sigma}P(y\log n)
 \ge c(\log p)p^{-2\sigma}.}
\]

The genuine Dirichlet-series identity already identifies `W` with the
corresponding sum of real logarithmic derivatives of zeta. The new
`exists_phaseContactExact_prime_square_floor` discharges the kernel
hypotheses from the exact optimiser. Its constant is uniform in `p`,
`sigma>1`, and `y`, with their dependence retained in the displayed weight.

This proof uses the exact relation between a prime and its square.
It requires no assertion about cancellation across distinct primes.

## The resulting local contradiction

Let `rho=beta+i*gamma`, `d=1-beta`, and let `m` be its analytic
multiplicity. For `beta>=15/16`, the existing argument uses
`sigma=1+(13/4)*d <= 5/4`. Choose the prime `2`. The new arithmetic floor
gives one `b>0`, uniform in all such zeros, with

\[
b=c(\log2)2^{-5/2}\le W_\sigma(\gamma).
\]

`exists_phaseContactExact_positive_zero_budget_reserve` retains the exact
source efficiency, multiplicity term, height sum, and pole allowance.
After applying their already proved explicit bounds,
`exists_phaseContactExact_refined_zero_source` gives

\[
\boxed{
\frac{11}{625}+bd
\le448d\left(\frac{61}{100}\log(|\gamma|+22)+\frac{83}{100}\right)
 +\frac{793}{400}\frac{d^2}{\gamma^2}.}
\]

The former checked inequality has the same right side and only `11/625`
on the left. The positive reserve makes this constraint strictly stronger
at an actual zero, where `d>0`.

`exists_phaseContactExact_prime_square_exclusion` concludes literal
`riemannZeta(s) != 0` whenever `Re(s)>=15/16`, `|Im(s)|>=1`, and the
right side is strictly below the new left side. The constant `b` is
proved to exist independently; an RH-like arithmetic estimate is not an
antecedent. This is a local nonvanishing test, not an exclusion throughout
the right half of the critical strip.

The reserve is bounded as `sigma` decreases to one and does not grow
with height. It therefore supplies no cancellation of the increasing
logarithmic height cost. Further use toward the global goal needs a new
estimate beyond this two-term mechanism.

## What this says about the optimiser and novelty

The eight nonconstant frequencies are necessary and sufficient for the
specified fixed-shift, linear-cost optimisation; the exact theorem already
covers infinite integer-frequency competitors. Adding more such
frequencies cannot improve that same objective. The arithmetic doubling
relation is an additional constraint on zeta's use of the kernel, not a
failure of the proved coefficient optimum.

Positive trigonometric polynomials and their optimisation have an
established role in zero-free-region proofs; see
[Mossinghoff and Trudgian](https://arxiv.org/abs/1410.3926).
The specific contact analysis and its Lean transport above are additions
to this repository. Uniqueness of the optimum does not establish
literature novelty, and no priority claim is made here.

The new module is `ZetaPhaseContactDoubling.lean`. Its eight public theorems
passed direct warnings-as-errors elaboration, the focused build (4416 jobs),
the full build (9822 jobs), whole-project declaration lint, and a verbose
root-imported module audit. Explicit axiom reports for all eight contain
only `propext`, `Classical.choice`, and `Quot.sound`. The user subsequently
authorised committing the accumulated work before further research.
