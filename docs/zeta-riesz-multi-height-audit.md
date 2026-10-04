# Native-weight multi-height preflight

The canonical frontier remains the **actual complete ordinary-prime**
`D_N-Q_N` from `ZetaRieszCoupledSignedBound`. The independent cofinal
`399/5000` upper bound is open. This slice tests an external trigonometric
constraint; it does not optimize any previous cutoff, order, comparison,
variation or square-budget constant.

## Exact comparison with the whole correlation credit

Put `r_i = symmetricWeight N K b i`, with the unchanged native
`K=13N/32` and `b=lengthFactor u N`. For an ordinary prime, the normalized
logged atom is

\[
a_i(y)=\sum_p u^{i+1}\frac{(\log p)^{i+1}}{i!}
 p^{-3/2}e^{-iy\log p}.
\]

The checked theorem `signedPrice_eq_pair_phase` expands the **whole**
`D-Q`, including the negative correlation credit, into

\[
F_N(y):=D_N(y)-Q_N(y)
 =\sum_{p,q} W_N(p,q)\cos\bigl(y(\log p+\log q)\bigr).
\]

All ordered incidences, diagonals, factorial orders zero and one, and both
native prefixes remain. The sum converges; no prime-support completion is
introduced. With `x=log p`, `z=log q`, `T=x+z`, its collected coefficient is

\[
W_N(p,q)=u^{N+1}xz\,e^{-3T/2}
 \frac{T^{N-1}}{(N-1)!}
 \sum_{i<N}r_i\binom{N-1}{i}(x/T)^i(1-x/T)^{N-1-i}.
\]

The corresponding von Mangoldt expansion retains **all** proper prime
powers, using `Lambda(p)*Lambda(q)` instead of `xz`. Neither prime measure
gives the joined binomial coefficient a sign.

The exact three-height identities are

\[
3F_N(0)\pm4F_N(y)+F_N(2y)
 =2\sum_{p,q}W_N(p,q)(1\pm\cos(yT))^2.
\]

`three_height_plus_eq_signed_square` proves the proposed plus polynomial.
`ordinary_three_height_eq_signed_square` and
`mangoldt_three_height_eq_signed_square` prove the minus comparison, which
would supply an upper bound on the target if the right side were
nonnegative. **No sign is asserted for these signed sums.** `Q_N` has not
been dropped or replaced by a smaller credit.

## First gate: the native coefficient changes sign

The optional ball preflight collects factorial indices **before** checking
the polynomial. At `u=10001/20000`, the order-65536 binomial coefficient
multiplied by `N` is approximately

| Actual prime geometry | Collected native coefficient |
|---|---:|
| Equal prime logs, share `1/2` | `+0.11382145` |
| Primes `2,3`, share `log(2)/log(6)` | `-0.17679524` |

This also occurs for pinned large actual primes, rather than only for the
small prime head. A positive Stechkin multiplier
`1-kappa*exp(-h*T)` preserves the negative coefficient.

There is a finite actual-prime counterexample to the unsigned minus
comparison. Use the set `{2,3}` and `y=20*pi/log(3)>54`. The larger-prime
diagonal has exact phase `40*pi` and contributes zero to the minus square.
Both ordered off-diagonal terms are negative; the smaller-prime diagonal
does not compensate. At native order65536, the comparison is approximately
`-1.31574059` **after division by a specified positive pair scale**. This
number is not `D-Q` itself, a global floor margin or source-scale progress.
The same test succeeds on a fixed large-prime set, with its diagonal phase
removed exactly, at orders4096 and65536.

These are finite-prime controls, not samples of the complete prime
population or actual-zero ordinates. In particular they do **not** disprove
a complete-prime comparison relying on additional correlations. They do
refute applying the scalar nonnegative square term by term to this native
quadratic. Literal core membership of the controls is not asserted.

The checked `minus_square_pointwise_iff` makes the missing requirement
explicit: multiplying that square by a coefficient is nonnegative at all
phases if and only if the coefficient is nonnegative. Optimizing the
coefficients of another nontrivial nonnegative scalar polynomial cannot
repair a negative coefficient at a phase where that polynomial is positive.

## Second gate: safe-center shifts cannot erase the height-zero cost

`pairAmplitude_shift` proves, at the **same native factorial indices**,

\[
W_N^{\sigma+h}(p,q)=e^{-hT}W_N^\sigma(p,q).
\]

Suppose every auxiliary center has a shift `h_j>=delta>0`, and a pointwise
comparison at phase zero needs

\[
1\le\sum_j c_j e^{-h_jT}.
\]

The checked necessary-cost theorem gives

\[
e^{\delta T}\le\sum_j|c_j|.
\]

Consequently **no fixed finite coefficient family of any degree** at only
safe shifted centers can make that comparison for every total logarithm.
`no_all_safe_pointwise_comparison` proves this without a source assumption,
norm estimate on the carrier or an assumed prime bound.

Allowing order-dependent coefficients instead restores an exponentially
growing price on the factorial saddle. For the proposed illustrative
`delta=1/10000` and `T=2N`, the necessary coefficient price multiplied by
the putative auxiliary radius saving has exponent

\[
2\delta+\log\frac{10001/20000}{1/2+\delta}
 \approx 0.000100014997667>0.
\]

This is a **necessary pointwise-cost model**, not an estimate for a literal
packet. It explains why paying the auxiliary shifted terms separately
does not give a saving.

Keeping an unshifted height-zero term avoids that pointwise failure but
leaves the zeta pole at denominator `1/2`. The geometric-array preflight
proves exactly

\[
F_N\bigl(a_i=q^{i+1}\bigr)=q^{N+1}\sum_{i<N}r_i.
\]

The pole channel has `q=2u>1`; its native scalar tends to the already-proved
positive constant-array source. This auxiliary channel is not covered by
an independent full radius `R>u`. A nonnegative degree-two cosine
polynomial with zero constant term is identically zero, also proved here;
deleting the height-zero term is not a positivity-preserving pole filter.

## Verdict and next mathematical requirement

The direct scalar multi-height/Stechkin comparison fails its preflight:
the native pair amplitude is signed, and uniformly safe auxiliary shifts
cannot supply the required pointwise domination. No absolute pair price
or `(2u)^N` allowance is introduced to rescue it. No new hypothesis of
bilinear cancellation is installed.

An alternative multi-height theorem would have to bound the **assembled
signed** prime-pair square using an additional global prime correlation,
including its height-zero pole cancellation, rather than multiply each
native pair by a nonnegative scalar polynomial. That estimate is not proved
here. The arithmetic-radius theorem and all prior positive results/no-gos
remain intact. The uncovered floor, ceiling and RH remain open; global
floor credit earned in this slice is zero.

## Scoped validation

The warning-as-error leaf build,14 namespace linters and transitive
standard-axiom checker are scoped to `ZetaRieszMultiHeightAudit`.
The optional768-bit producer and independent920-bit replay check54 balls
and widths on six actual-prime rows, two at native order65536, plus the
necessary safe-shift costs. The replay computes direct binomial masses and
joins the two original prefixes independently of the producer's rescaled
recurrence. Neither numerical file is a proof dependency or ordinary CI job.

See `scripts/CheckRieszMultiHeightAudit.lean`,
`data/riesz-multi-height-preflight.json`,
`data/riesz-multi-height-replay.json`, and the scoped audit JSON.
Those scoped checks preceded root registration and publication. The
user-authorized [coherence checkpoint](prime-moment-coherence-audit.json)
records the later wider gates and registration of this accumulated work.
The original scoped audit is retained as a historical validation snapshot;
no exhaustive certificate verification is part of this checkpoint.
