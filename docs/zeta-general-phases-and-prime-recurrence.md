# Arbitrary spectra, forced prime returns, and the actual zeta cost

This slice moves from a particular optimizer to structural constraints on
the literal zeta logarithmic derivative and its local zero sums. The three
modules are:

- `ZetaPhaseArithmetic.lean`: the exact arithmetic transport and coupled zero inequality;
- `ZetaPhasePrimeRecurrence.lean`: mixed phase energy and a forced prime-power floor;
- `ZetaPhaseHeightAsymptotic.lean`: the actual cost of arbitrary real frequencies.

There is no prescribed support, degree, integer frequency lattice, shift
ratio, or linear frequency cost. This does not prove RH or discharge the
independent signed Suzuki-work bound. It does not establish priority for a
new mathematical result.

## The arithmetic object retained by the theorem

Let `a_n >= 0`, assume `sum a_n` converges, and choose arbitrary real
frequencies `omega_n`. Define

\[
 P(t)=\sum_{n\ge0}a_n\cos(\omega_n t),\qquad
 D_\sigma(t)=\Re\!\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right).
\]

For `sigma > 1`, `hasSum_zetaPhase_arithmetic` proves

\[
 W_\sigma(y):=\sum_n a_nD_\sigma(\omega_n y)
   =\sum_{m\ge1}\frac{\Lambda(m)}{m^\sigma}P(y\log m).
\]

The prime-power series, frequency series, and joint double series are
genuinely absolutely convergent. The proof justifies their interchange.
No assertion that the kernel is nonnegative is needed for this identity.
If `P(t) >= 0` for every real `t`, every arithmetic summand is nonnegative.

The integer-frequency kernel from the optimizer is an instance through
`zetaPhaseKernel_natCast`. Its feasibility and convergence were already
proved; they need not be assumed again for an application.

## A general obstruction to simultaneous contact zeros

`hasSum_zetaPhase_gramEnergy` uses the same exact cosine Gram identity as
the eta support/gap matrix module. For every finite collection of locations
`u_i` and real weights `c_i`, it proves

\[
 \sum_{i,j}c_ic_jP(u_j-u_i)
 =\sum_n a_n\left[
   \left(\sum_i c_i\cos(\omega_nu_i)\right)^2+
   \left(\sum_i c_i\sin(\omega_nu_i)\right)^2\right].
\]

Both squares and all cross terms remain available upstream. If
`omega_r = 0`, retaining that frequency gives the lower bound
`a_r (sum_i c_i)^2`.

Write `A = sum_n a_n`. Apply this identity at
`u_i = i*theta`, `i = 0,...,N`, with all `c_i = 1`.
`zetaPhase_return_ceiling_constraint` proves

\[
 \bigl[P(k\theta)\le B\text{ for }1\le k\le N\bigr]
 \quad\Longrightarrow\quad (N+1)a_r-A\le NB.
\]

This does not need pointwise nonnegativity of `P`. In particular:

- `zetaPhase_contactBlock_mass_constraint`: if those first `N` returns
  all vanish, then `(N+1)*a_r <= A`;
- `zetaPhase_exists_positive_return`: if `(N+1)*a_r > A`, at least one
  of the first `N` returns is strictly positive.

Thus a contact set cannot absorb an arbitrarily long sequence of multiples
of an angle. The relevant threshold is a coefficient-mass ratio, not the
number of nonzero coefficients. This covers infinite support and arbitrary
real frequencies without a density or independence hypothesis.

## An independent floor for the actual signed zeta sum

Choose any prime `p`. At `theta = y*log p`, successive phase returns are
the phases of `p,p^2,...,p^N`. Their von Mangoldt weights share the positive
lower bound

\[
 c_{\sigma,p,N}=(\log p)p^{-\sigma N}.
\]

For a nonnegative kernel, `zetaPhase_primePower_floor` proves

\[
 \boxed{c_{\sigma,p,N}\bigl((N+1)a_r-A\bigr)\le N W_\sigma(y).}
\]

This holds for every height, prime, and natural block cutoff. Taking
`(N+1)*a_r > A` yields a positive floor; taking `a_r > 0` permits such a
finite cutoff. `zetaPhase_logDeriv_pos` concludes that `W_sigma(y) > 0`
at every height. The proof exhibits finite-depth forcing rather than
invoking an unspecified density argument.

This is an arithmetic floor for `W_sigma`, not a floor for the different,
signed Suzuki transport work. The two must not be identified.

## What this forces on the actual zeros

Set `sigma = 1+x`, with `0 < x <= 1/4`, and retain

\[
 Z_x(y)=\sum_n a_n\Re\operatorname{localZetaPoleSum}
       (\omega_n y,x-\tfrac12),
\]

\[
 H_x(y)=\sum_n a_n\frac{x}{x^2+(\omega_ny)^2},\qquad
 L_a(y)=\sum_n a_n\log(|\omega_ny|+22).
\]

When `L_a(y)` is summable, `zetaPhase_primeWork_add_localZeros_le` proves

\[
 W_{1+x}(y)+Z_x(y)\le H_x(y)+448L_a(y).
\]

The summability of the entire zero sum is proved, not assumed. Combining
this with the prime-power floor gives the compiled theorem
`zetaPhase_primePower_add_localZeros_le`:

\[
 c_{1+x,p,N}\bigl((N+1)a_r-A\bigr)+N Z_x(y)
 \le N\bigl(H_x(y)+448L_a(y)\bigr).
\]

If `omega_s = 1` selects a literal nontrivial zero
`rho = beta + i*gamma`, with `beta >= 3/4`,
`zetaPhase_primePower_add_multiplicity_le` replaces `Z_x(gamma)` by

\[
 a_s\frac{m(\rho)}{x+1-\beta},
\]

retaining the zero's full analytic multiplicity. This is a stronger
inequality whenever the displayed arithmetic floor is positive. It is not
yet a newly optimized numerical zero-free strip.

## The leading height cost is mass, not a frequency count

The mild logarithmic-moment hypothesis

\[
 \sum_n a_n\log(1+|\omega_n|)<\infty
\]

suffices for all actual height costs to converge. It allows infinite spectra
and frequencies accumulating at zero. The exact finite-height estimate is

\[
 L_a(y)\le A\log(|y|+22)+\sum_n a_n\log(1+|\omega_n|).
\]

For every fixed spectrum satisfying these conditions,
`tendsto_zetaPhase_height_div_logHeight` proves

\[
 \boxed{\frac{L_a(y)}{\log(|y|+22)}
   \longrightarrow\sum_{\omega_n\ne0}a_n\quad(y\to+\infty).}
\]

The proof uses a summable dominator for the entire family; it does not
interchange an infinite sum and a limit without justification. This is not
a uniform theorem for spectra chosen as a function of height. Such a claim
would require further control of the moving spectra.

Consequently the earlier eight-frequency optimum describes its fixed
linear cost and fixed shift. It does not identify an intrinsic preferred
frequency count of zeta, nor optimize the literal asymptotic height cost.

## The next research test

The [canonical boundary-weight successor](zeta-canonical-boundary-source.md)
now extends the signed source constraint to every actual zero right of
the critical line. It controls negative canonical responses by their
Jensen boundary weights and retains the exact selected source in arbitrary
finite or infinite real-frequency families. The formerly required
`beta >= 3/4` restriction is removed in this new source interface; the
decisive independent arithmetic estimate is still open.

The [actual zero-budget successor](zeta-phase-zero-budget.md) now separates
the fixed constant-phase cost from nonconstant mass and logarithmic
frequency overhead. Its general signed inequality constrains every finite
prime-phase window at an actual zero. Applying it to the fully proved
exact family strengthens the project's unconditional edge margin to
`1/(15600*log(|gamma|+22)+21200)`, and hence uniformly to
`1/(23000*log(|gamma|+22))` for `|gamma| >= 1`. The exact arithmetic and
multiplicity terms remain available before this scalar consequence.

The [full complex prime Gram successor](zeta-prime-gram-separation.md)
now combines the repo's eta prime-base separation with the literal zeta
logarithmic derivative. Arbitrary distinct complex probes give a positive
definite matrix, and removing any finite prime prefix preserves full rank.
An explicit block of consecutive powers of one prime witnesses the strict
remaining energy. This separates arithmetic independence from the finite
support of a selected optimizer; it does not supply a uniform conditioning
bound or the signed Suzuki estimate.

The [signed Suzuki bridge and actual-cutoff successor](suzuki-phase-curvature-and-actual-cutoff.md)
now proves the exact transport direction. A prime-work lower floor yields
an upper bound on the complete Suzuki curvature response, which includes
an essential sine channel. It does not establish the lower time-signal
bound required for RH. The successor also proves that an eventual upper
bound on the actual finite logarithmic prime average suffices without a
separate canonical entropy estimate.

The new carrier retains actual arithmetic work in the zero inequality and
proves that reducing it to zero loses information. However, a fixed prime
block supplies a bounded floor as `x` tends to zero. Its magnitude does not
grow with `log |y|` and cannot by itself pay the full local analytic cost,
let alone the independent global signed RH obstruction.

A useful next advance would control the aggregate arithmetic work on
growing prime ranges, preserving interactions and proving all cutoff costs.
The mixed phase identity allows arbitrary locations and real test weights,
so a proof need not remain confined to a single prime-power progression.
No bound on cross-prime interactions follows merely from positivity of this
matrix. In particular, the existing signed Suzuki-work target still needs
its own independent estimate or a proved quantitative transport to it.

Positive trigonometric kernels and their optimization have an established
role in zero-free-region arguments; see
[Mossinghoff and Trudgian](https://arxiv.org/abs/1410.3926).
Optimality also depends on the exact zeta objective, as illustrated by
[Leong and Mossinghoff](https://arxiv.org/abs/2404.05928).
The generalizations and connections above are checked additions to this
repository. A literature search does not establish novelty of these exact
formulations, and no priority claim is made.

## Validation

The slice contains 32 public theorems across three modules. Direct
warnings-as-errors checks, focused builds, and the full build passed
(9780 jobs). Whole-project declaration lint and all three verbose module
audits passed. Every one of the 32 new public theorems uses only `propext`,
`Classical.choice`, and `Quot.sound` transitively.

The root-importing audit also checked concrete applications of strict
arithmetic positivity and the actual height-cost limit to the existing
exact optimizer, discharging feasibility and convergence from its proved
theorems. Source-integrity and whitespace checks passed. No files were
staged, committed, or pushed, and no remote CI or generated-status update
was performed during this slice.
