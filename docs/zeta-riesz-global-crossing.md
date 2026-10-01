# One cutoff-crossing bound across counts and radial periods

Lean now bounds the affine cutoff error of the **literal allocated prime
sum** without fixing its number of prime factors, its share geometry or its
radial center. The bound applies on both sides. It does **not** yet bound the
whole signed carrier: two actual weighted prime moments and clipped-period
boundary contributions remain.

## The estimate

Write the existing Riesz response and its exact finite slope as

\[
 R_D(a)=\sum_{d\mid a}\mu(d)(D-\log d)_+,
 \qquad S_D(a)=\sum_{\substack{d\mid a\\\log d<D}}\mu(d).
\]

For \(|x|\le h\), subtract the affine part before taking absolute values:

\[
 \left|R_{D+x}(a)-R_D(a)-xS_D(a)\right|
 \le\sum_{d\mid a}(h-|D-\log d|)_+.
\]

Only divisors within one half-period of the cutoff are charged. The symmetric
second difference is exactly the same tent sum with each Möbius sign retained.
Reindexing the divisor incidences over **all integers** gives the checked bound

\[
 \boxed{\quad
 \sum_{1\le a\le X}\frac{|R_{D+h}(a)-2R_D(a)+R_{D-h}(a)|}{a}
 \le (1+\log X)h\left(e^{2h}-1+e^{h-D}\right).
 \quad}
\]

There is no prime-count ceiling and no squarefree hypothesis in this estimate.
The affine-error version holds on every masked cofactor subfamily. When
\(0<h\le1/16\) and \(D\ge h-\log h\), its cost is at most

\[
 \frac{23}{7}(1+\log X)h^2.
\]

This replaces a charge for every divisor choice by a charge for the divisors
actually crossed. It removes the exponential dependence on prime count from
this particular error term.

## Direct connection to the retained carrier

Let \(T=\log(pa)\). The signed weight used by the theorem is exactly

\[
 g_N(a,p)=\frac{(-1)^{\omega(a)+2}}{L}
 (1-\theta_N(pa))\frac{e^{-T/2}T^{N+1}}{N!p}\cos(yT).
\]

Both reflected responses remain in the literal coefficient:

\[
 \operatorname{Re}\bigl(c^{\rm residual}_{L,N}(pa)K_N(pa)\bigr)
 =\frac{g_N(a,p)}a
 \left[R_{T-L}(a)-R_{\log a-L}(a)\right].
\]

For every cofactor selection \(S\subseteq[1,X]\), retain its actual prime set
\(P(a)\), including any physical, ownership, count, radial or other masks.
The theorem requires squarefree cofactors with at least two factors and prime
\(p\nmid a\). It permits all such counts, without an upper ceiling. Put

\[
 M_0(a)=\sum_{p\in P(a)}g_N(a,p),\qquad
 M_1(a)=\sum_{p\in P(a)}g_N(a,p)(T-v).
\]

For \(|T-v|\le h\), the **literal signed sum** lies between \(M-E\) and
\(M+E\), where

\[
 M=\sum_{a\in S}\frac{
 [R_{v-L}(a)-R_{\log a-L}(a)]M_0(a)+S_{v-L}(a)M_1(a)}a,
\]

\[
 E=W(1+\log X)h\left(e^{2h}-1+e^{h-(v-L)}\right),
 \qquad \sum_{p\in P(a)}|g_N(a,p)|\le W.
\]

`owned_population_affine_bounds` identifies this with a literal union of
integers when the marked prime is the unique largest prime. No label is
counted twice. Close largest-prime pairs are allowed; an incomplete period
keeps its actual moments instead of receiving a free cancellation claim.
The allocation is inside \(g_N\), so it has not been replaced by a limiting
share or charged through a separate worst derivative estimate.

`radial_affine_error_le` sums arbitrary finite radial collections. If their
cutoffs are at least \(D_0\), the total crossing cost is bounded by

\[
 \left(\sum_j W_j\right)(1+\log X)h
       \left(e^{2h}-1+e^{h-D_0}\right).
\]

This is an actual combined inequality, but **the total weight budget and the
retained signed moments are not proved small at source scale**. For an
integer union across periods, use disjoint radial selections; the theorem
on an indexed collection retains any multiplicities in that collection.

## Numerical checks and their limits

The optional `probe_riesz_global_curvature.py` evaluates the all-integer
crossing majorant by divisor incidence. At radial center 50 and
\(h=\pi/54\), it gives approximately 0.07094, below the proved bound evaluated
as 0.36074. A coarse all-divisor comparison is approximately 146.9. These
are floating-point diagnostics, not certificates or asymptotic prime counts.

With `--literal`, the script also enumerates small finite uniquely owned
prime populations at orders 6, 8 and 10. It retains the exact rational
moving cutoff, all unpaid allocation orders, the phase and both responses,
and compares the direct sum with its two signed moments and crossing bound.
At order 10 it enumerates 493,241 distinct labels (490,738 triples and
2,503 four-prime labels). The direct crossing error is approximately
`1.3205e-5`, below the bound evaluated as `0.7775`; the reflected coefficient
identity agrees to roundoff below `7e-15`. The loose upper bound is a warning
against treating this probe as a source-scale estimate. These finite orders
do not establish an eventual endgame estimate.

The same diagnostic exposes cancellation that must remain joint: at order 10,
triples contribute approximately `+1.1835e-4` and four-prime labels
`-5.5492e-5`. The constant-moment total is `+7.9291e-5`, while the first-moment
total is `-2.9633e-5`. Taking their separate absolute values would erase both
savings. The exact local crossing-weight profile evaluates to `9.5953e-5`,
much smaller than the uniform-budget bound; this motivates preserving the
cofactor dependence of that budget in the next estimate. None of these
finite computations proves a uniform prime-density comparison.


The all-integer diagnostic grows roughly as a constant times \(v h^2\).
That observation does not suggest source-normalized decay by itself.
Multiplying a relative improvement by the old \((2u)^N\) envelope is still
insufficient. The next target is a joint estimate for the retained
\(M_0\) and \(M_1\), with their allocation and boundary correlations intact,
and a source-scale bound for the combined crossing cost. A complete-period
estimate cannot be added to favorable subperiod credits without subtracting
their exact signed overlap.

The response is also the classical truncated divisor sum
`Lambda_R(a)` with `R=exp(D)`. Goldston and Yıldırım, Theorem 5.1, prove
`sum_(a<=X) Lambda_R(a)^2 = X log R + O(X) + O(R^2)`.
That suggests a possible mean-square control of the retained cofactor
profile, but their statement does not include this carrier's allocation,
prime-phase weights or hard masks. It is not imported or used by the Lean
proof above, and it does not by itself discharge the source-scale estimate.
[Primary paper, §5](https://math.colgate.edu/~integers/d5/d5.pdf).

The independent whole floor \(-79/1000-o(1)\), the ceiling \(3/2+o(1)\), and
the RH contradiction remain open. No zero hypothesis is used in these new
finite inequalities; no new zero-free region is claimed.

- [Global crossing estimate](../RiemannGaussian/ZetaRieszGlobalCurvature.lean)
- [Literal prime sum and both signed bounds](../RiemannGaussian/ZetaRieszGlobalPrimePeriod.lean)
- [Optional quantitative probe](../scripts/probe_riesz_global_curvature.py)
- [Verification record](riesz-global-crossing-audit.json)

## Joining the moments and the crossing before applying a sieve

`ZetaRieszSignedConvolution.joint_periods_eq_bilinear` now works one level
upstream of the one-sided crossing bounds. It sums the literal `M_0`, `M_1`
and **exact signed crossing remainder** across any finite collection of
periods and cofactor counts, before taking any inequality. Squarefreeness
gives `mu(a)*mu(d)=mu(b)` for `a=d*b`. The period centers then disappear:

\[
\boxed{
 \sum_{\text{periods}}(M+\text{signed crossing})
 =\operatorname{Re}\sum_{p,d,b}
 W_N(p,db)\,\mu(b)
 \big[(\log(pb)-L)_+-(\log b-L)_+\big].
}
\]

Here `W_N` is exactly `phaseWeight`: the original complex factorial kernel
on `p*d*b`, multiplied by `(1-boundedShare)*log(p*d*b)/L`. The bilinear
theorem retains the literal mask `d*b in S` and original prime selection
`p in P(d*b)`; it does not complete a cofactor or replace coprimality by a
density. The core specialization retains **every** original core mask.
`core_sub_convolution_bound` pays the entire nonowner-allocation difference
once, using the existing geometric `nonownerRate < 124/125` bound. Neither
the signed main nor the crossing is norm-paid separately.

The unit complementary divisor is zero when `log(p)<=L`. An ordinary prime
`b=q` contributes exactly `-(log(p*q)-L)_+` when `log(q)<=L`. Thus the
prime-pair boundary must remain joined to the composite `b` terms. A sign
for its arithmetic coefficient is not a sign for its complex weighted sum.

The repository's Suzuki logarithmic convolution supplies the exact
Selberg identity. With `x=log(b)`, any centered quadratic can be subtracted
inside the signed profile at the cost of the explicit channel

\[
 \mu(a)c\,[\Lambda(a)(\log a-r)+(\Lambda*\Lambda)(a)].
\]

`selberg_cutoff_split` and `residual_atom_eq_selberg_cutoff` prove this with
the same complex weight. The factor `mu(a)` is essential after divisor
complementation. For squarefree cofactors with at least three prime factors,
both classical channels vanish; `higher_count_quadratic_cancellation` then
removes the quadratic **exactly**. What survives is the nonpolynomial,
moving-cutoff profile with its Möbius signs and product phase. It has no
proved source-scale bound. The identity is infrastructure, not a new
arithmetic floor or a proof that this remainder is harmless.

This is the useful part of the Diamond–Steinig approach: join the linear
and prime-pair convolution before estimating the remainder. Ramaré's
asymptotic theorem additionally requires weighted distribution-error
control, notably hypotheses H4/H9; its identity alone does not provide
that control for the present masks and weights.
[Ramaré, Lemma 4 and hypotheses](https://ramare-olivier.github.io/Maths/V12BombieriSieve.pdf).
Friedlander–Iwaniec likewise introduces its bilinear condition B as an
additional hypothesis. We have not assumed it, and cannot substitute it
for the missing estimate.
[Friedlander–Iwaniec, §§1 and 10](https://arxiv.org/pdf/math/9811186).

The next arithmetic target is a **joint signed estimate** of this clipped
Möbius convolution and its prime-pair boundary over the original owner
population and radial periods. Using SharpSieve on a residual counting
error is legitimate only after that signed main stays intact. Another
absolute crossing allowance, separate count debit, or inverse-polynomial
relative improvement cannot overcome the already proved global debit
obstruction.

The optional `probe_riesz_signed_convolution.py` joins all adjacent periods
in the small-order logarithmic window. At order 10 it checks 2,943,562
distinct finite prime labels. Its source-normalized prime-`b` contribution
is about `-1.29505e-4`, the composite-`b` contribution `+1.08694e-4`, and
their joined value `-2.08110e-5`; both exact ledgers agree to roundoff.
**None of these small-order labels survives the original annulus.** These
numbers test the algebra and illustrate signed cancellation, but are not
evidence for the current core floor, growing-count band or a large-order
rate. The previous order-6/8/10 crossing probe has the same annulus issue.

- [Exact joined convolution and Selberg bridge](../RiemannGaussian/ZetaRieszSignedConvolution.lean)
- [Optional finite-prime regression](../scripts/probe_riesz_signed_convolution.py)

## A geometric payment for the unsigned-leg comparison error

The joined convolution has an unsigned squarefree leg `d` and a signed
complementary leg `b`. `active_divisor_core_log_bound` proves that every
active literal core incidence satisfies `log(d)<131N/200`. On a saturated
owner row, `log(b*d)<=L`, the active hinge also forces `d<p`. Thus the
largest-prime condition adds no extra prime-factor cutoff on that row.
This does not extend automatically to unsaturated rows.

`ZetaRieszUnsignedDivisorError` proves a power error for the unsigned leg
with the **entire** coprimality sieve retained:

\[
 \left|\sum_{d\le X}\mathbf1_{\mathrm{sf}(d),\,(d,pb)=1}
       -\mathfrak d(pb)X\right|
 \le C X^{3/4}3^{\omega(pb)}.
\]

The density `density` includes every finite intersection; no prime-density
approximation or cancellation hypothesis is assumed. More precisely,
`prefix_error_product` retains the product of the actual prime-square
corrections before bounding it by `3^omega(pb)`. Consequently its cost does
not grow exponentially in the square root of the largest forbidden prime.

On a shell `exp(N/10)<=M<X<=2M`, the literal smooth weight is

\[
 w_N(d)=\frac{\cos(y\log(pbd))}{d}
  \operatorname{ownerWeight}_N\!\left(1-\frac{\log p}{\log(pbd)}\right)
  \frac{e^{-\log(pbd)/2}\log(pbd)^{N+1}}{N!}.
\]

`owner_phase_eq_amplitude` proves its exact identification with the
original factorial kernel and owner allocation. The owner variation is at
most two; the full product amplitude has variation at most
`(N+4)*(N+1)*2^(N+1)` on each shell. Both exterior jumps and the full fixed
height phase are included in the error bound. The signed main is kept as
one row:

\[
 \frac{\mu(b)H_L(p,b)}{Lpb}\,\mathfrak d(pb)\sum_d w_N(d),
 \qquad H_L(p,b)=(\log(pb)-L)_+-(\log b-L)_+.
\]

`ownedShellDiscrepancy_eq_literal` identifies the difference from the
original owner-divisor incidence exactly, under the displayed finite
ownership geometry. `mem_core_of_strict_prime_share` checks the inherited
original masks for squarefree labels with `3<=omega<K`, the literal core
window and strict prime shares below `13/20`; it requires the already
available eventual length lower bound `L>=11N/8`. The count cutoff is not
silently removed: `tendsto_high_count_partial_incidence` proves source-o(1)
for arbitrary selected high-count owner incidences, including their masks.

The outer-pair cost is then summed over **all** counts by a convergent
Rankin/count-generating bound, with `sigma=1025/1024`. Its exponential cost
is at most `exp(203N/102400)`. After including the full source growth, the
comparison error has rate

\[
 \boxed{2u\,e^{-2357/102400}\le\frac{49}{50}<1.}
\]

`source_scaled_shells_error` joins at most `N+1` shells and gives

\[
 \boxed{\left|u^{N+1}\sum_{\mathrm{shells},p,b}
       \mathrm{comparisonError}_{N,p,b}\right|
 \le C(8+|y|)(N+1)^3(49/50)^N\longrightarrow0.}
\]

This is a genuine geometric **error** payment after count and radial
aggregation. It is not a bound for the signed density main. The small leg
`d<exp(N/10)` and the unsigned-leg prime-factor ownership restrictions on
unsaturated rows remain unpaid. A complete literal-core replacement by
the density main has not been proved. The next estimate must keep this
main joined with those boundaries and its prime-pair contribution.
The independent `-79/1000` floor, `3/2` ceiling and zero exclusion remain
open.

- [Checked unsigned-leg error and literal row ledger](../RiemannGaussian/ZetaRieszUnsignedDivisorError.lean)
- [Local verification record and exact remaining scope](riesz-signed-convolution-audit.json)

## Applying the error payment to the literal core

`ZetaRieszSaturatedRowFloor` checks the row endpoints directly. On an
active saturated row, the squarefree product sieve implies that the
cofactor has at least two distinct primes and that the unsigned divisor
is smaller than the canonical owner. Its endpoint inequalities imply
the original core window and strict nondominant share. Consequently
`row_mem_core_iff` shows that the only remaining selection is the
**original** prime-count cutoff.

The checked exact identity is

\[
 \mathrm{coreRow}+\mathrm{overflowRow}
   =\mathrm{densityRow}+\mathrm{ownedShellDiscrepancy}.
\]

The high-count extension is reindexed into a partial divisor coefficient
on the original squarefree product label. Every selected divisor lies
in its literal antidiagonal; different outer pairs cannot duplicate an
owner incidence. `overflowRows_bound` uses the fixed count tilt
`q=49/100`, with rate at most `97/100`. After the count exponential and at
most `N+1` shells are joined, the extension costs eventually at most

\[
 \mathrm{highCountConstant}(N+1)^2(49/50)^N.
\]

Thus `eventually_signed_rows_floor` pays both comparison errors with

\[
 E_N=\left[C(8+|y|)(N+1)^3+C_{\rm count}(N+1)^2\right](49/50)^N\to0.
\]

Most importantly, `coreConvolution_eq_remaining_rows` puts the selected
rows back into the original whole-carrier ledger. `remainingIncidences`
is the exact sum over unselected original divisor incidences, including
the small unsigned divisors, unsaturated rows and any uncovered saturated
rows. It is not an anonymous completion error. The resulting theorem
`eventually_joined_floor_with_signed_rows` gives

\[
 \boxed{\Re\bigl(u^{N+1}\mathrm{joinedPhysical}\bigr)
 \ge u^{N+1}\left(\mathrm{remainingIncidences}
           +\sum_{p,b}\mathrm{densityRow}_{p,b}\right)
       -\mathrm{joinedRowErrorBudget}_N,}
\]

where the displayed error tends to zero and includes the two previously
paid whole-carrier differences once. No sign or norm allowance has been
attached separately to either retained signed term.

This closes the literal comparison for **explicitly selected eligible
rows**. The canonical interval/shell construction for eligible saturated
large-divisor incidences is supplied in the next section. More importantly, the
joint arithmetic expression on the right has no independently proved
`-79/1000` floor. The numerical floor, ceiling and zero exclusion remain
open; the published RH endpoint is unchanged.

- [Checked literal-row comparison floor and whole-carrier ledger](../RiemannGaussian/ZetaRieszSaturatedRowFloor.lean)

## Canonical interval coverage and paid rounding endpoints

`ZetaRieszCanonicalOwnerRows` removes the free choice of eligible row
selection. For each physical owner prime `p` and squarefree `b` with all
its prime factors below `p`, the construction uses

\[
 \begin{aligned}
 E_{N,p,b}&=\max\left\{\frac N{10},
            \frac{39N}{20}-\log(pb),
            \frac{20}{13}\log p-\log(pb)\right\},\\
 U_{N,p,b}&=\min\left\{\frac{203N}{100}-\log(pb),
                   L_N-\log b\right\},\\
 M_{N,p,b}&=\lceil e^{E_{N,p,b}}\rceil,
 \qquad X_{N,p,b}=\lfloor e^{U_{N,p,b}}\rfloor.
 \end{aligned}
\]

The actual finite `rows` selection retains the physical owner support,
squarefreeness, coprimality, largest-prime mask and nonzero joined hinge,
and requires `M<=X`. `rows_geometry` checks the original lower/upper
window, saturation and strict owner-share selection on every integer in
`M<d<=X`. The intervals are partitioned disjointly by clamped dyadic
boundaries. At most `N+1` shells reach the exact upper endpoint; the
literal core sum and its **signed** density sum both telescope back to
the full interval before the main is estimated.

`literal_row_covered_or_endpoint` proves that every incidence satisfying
the displayed original eligibility conditions and `d>=exp(N/10)` is
included in its canonical interval, except possibly the **single**
integer `d=M`. These rounding endpoints retain the actual core mask,
full squarefree sieve, allocation and phase in `endpointRows`. Their
source cost is now independently paid after summing **all** outer counts:

\[
 \boxed{\left|u^{N+1}\mathrm{endpointRows}_N\right|
 \le C_{\rm end}(N+1)(23/25)^N\longrightarrow0.}
\]

The checked sharper rate before the rational ceiling is
`2*u*exp(-10037/102400)`. This bounds only the rounding endpoints, not
the signed density main.

`eventually_joined_floor_without_endpoints` gives a deterministic
whole-carrier comparison inequality:

\[
 \boxed{\Re\bigl(u^{N+1}\mathrm{joinedPhysical}\bigr)
 \ge u^{N+1}\bigl(\mathrm{canonicalSignedMain}
                   -\mathrm{endpointRows}\bigr)
        -\mathrm{canonicalErrorBudget}_N.}
\]

The error is the previous comparison/count and whole-carrier budget,
plus the endpoint bound; it tends to zero. The main contains the signed
density intervals and **every** original unselected incidence. Small
unsigned divisors, unsaturated rows and any original geometry outside
the displayed eligibility remain there. This is a canonical coverage and
error payment, **not** an independent `-79/1000` bound for the remaining
joined main. The floor, ceiling, zero exclusion and published RH endpoint
remain unchanged.

- [Canonical literal interval comparison and endpoint saving](../RiemannGaussian/ZetaRieszCanonicalOwnerRows.lean)

## A signed main sector now paid across all counts

`ZetaRieszFreeRadialRows` proves cancellation for every original canonical
row satisfying

\[
 \log(pb)\le\frac{37N}{20},\qquad
 \log p\le\frac{507N}{400},\qquad
 \frac{203N}{100}\le\log p+L_N.
\]

These are exactly the sufficient inequalities making the moving endpoints
span the full original total-log window, rather than shorten it. The
owner prime and squarefree signed outer cofactor stay literal. Only the
unsigned divisor logarithm is integrated, after the already-proved
squarefree comparison. Its Fourier integral is evaluated with the full
owner allocation before norms are taken.

The complete integral has bound `(N+1)(N+3)*(3/4)^N`. The original radial
tails also have a strict geometric margin. The integer transfer uses
summable `1/d^2` local variation and pays both exact endpoint-rounding
slivers. Finally the entire outer-row mass is bounded by
`(1+203*N/100)^2`, with no exponential cost in prime count. For fixed
`abs(y)>=54`, `N>=32` and `L_N>=11*N/8`, Lean proves

\[
 \boxed{\left|u^{N+1}\mathrm{freeDensityMain}_N\right|
 \le 9(33+4|y|)(N+1)^4 r^N\longrightarrow0,\qquad r<1.}
\]

This is an independent bound on the selected **signed main**, not only
on a comparison error. Its rate is the maximum of `3/4`, `23/25` and the
two original radial-tail rates. At the radius ceiling the slowest rate
is about `0.99998860756`; no numerical starting order is proved. Intermediate
orders can grow, so finite floating quadrature is not evidence of a small
floor allowance.

`eventually_joined_floor_with_clipped_rows` removes this sector exactly
once. The unpaid expression is now

\[
 u^{N+1}\bigl(\mathrm{canonicalRemaining}
              -\mathrm{endpointRows}
              +\mathrm{clippedDensityMain}\bigr).
\]

Every old mask and every other literal incidence remains. The comparison
budget is `canonicalErrorBudget + freeErrorBudget`, and tends to zero.
The independent `-79/1000` floor for this joined remainder is still open;
no new zero exclusion or RH conclusion is claimed.

- [Signed full-window row payment and updated floor ledger](../RiemannGaussian/ZetaRieszFreeRadialRows.lean)

## Paying the owner-share boundary without fixing a count

`ZetaRieszClippedAllocationPayment` removes a second, disjoint signed main
sector: shortened canonical rows with `log(p)>=507*N/400`. The literal
nondominant mask and core upper endpoint force their cofactor share into
`[7/20,47/125]`. The exact missing owner allocation, including both
integer order endpoints, satisfies

\[
 \mathrm{ownerWeight}_N(x)\le3e^{-N/600}\quad(N\ge320).
\]

This saving beats source growth before the whole all-count harmonic row
mass is charged. The independent main-sector estimate is

\[
 \boxed{\left|u^{N+1}\mathrm{allocationDensityMain}_N\right|
 \le162(N+1)^4(999/1000)^N\longrightarrow0.}
\]

No phase replacement, completed prime cofactor or extra nonowner charge
enters this payment. Its rows are explicitly disjoint from `freeRows`.
The exact `residualRows` left after both payments satisfy

\[
 \log p<\frac{507N}{400},\qquad
 \log(pb)>\frac{37N}{20}\quad\text{or}\quad
 \log p+L_N<\frac{203N}{100}.
\]

Thus the owner-threshold boundary is gone from the unpaid density main.
Only the unsigned-divisor threshold and cofactor-saturation boundaries
remain there, still joined with `canonicalRemaining - endpointRows`.
`eventually_joined_floor_with_residual_rows` gives the whole-carrier
comparison with a budget tending to zero. The required numerical floor
for that **combined** remainder is unproved.

- [All-count owner-threshold payment and remaining boundary taxonomy](../RiemannGaussian/ZetaRieszClippedAllocationPayment.lean)

## A joint radial/allocation payment on the original prime sum

`ZetaRieszJointOwnerEnvelope` retains the correlation between the owner
logarithm `P` and the radial variable `T` before estimating either.
With the rational tilt `q=41/40`, the exact identity is

\[
 \boxed{
 [q(1-P/T)+P/T]^{N+1}\,\mathrm{radialMoment}_N(T)
 =q^{N+1}e^{-P/82}\,
   \mathrm{radialMoment}_N(T-P/41).
 }
\]

The shifted saddle gives a saving lost by separate envelopes. At
`P>=243*N/200`, the source-rate exponent is proved at most `-1/20000`.
The other owner tail is also paid, retaining the literal integer endpoints
`N/5+2` and `13*N/32`. For `N>=320`, `P<=13*T/20` and every ordinate,

\[
 \boxed{
 u^{N+1}\mathrm{ownerWeight}_N(1-P/T)
 \mathrm{radialMoment}_N(T)
 \le6(N+1)e^{-N/20000}.
 }
\]

Applied only to the previously unpaid density rows, this removes an
additional **disjoint** sector with source cost
`162*(N+1)^4*exp(-N/20000)`. The remaining density main has
`log(p)<243*N/200`, improving the previous `507*N/400` cut. Its two
signed moving boundaries and the untouched literal incidences stay joined
in `eventually_joined_floor_with_lowOwner_rows`. This is still a comparison
floor, not the numerical `-79/1000` floor.

The same joint estimate is proved directly for the **original finite
prime sum**, without a density replacement. `literalPopulation S A N`
selects original squarefree labels with at least three prime factors,
their unique largest prime in the original physical set `A`, and
`243*N/200<=log(p)<=13*log(n)/20`. Every further mask stays in `S`; the
full residual coefficient, all cofactor counts and the complex phase
are unchanged. For `log(n)<=203*N/100`, the checked bound is

\[
 \boxed{
 \left\|u^{N+1}\sum_{n\in\mathrm{literalPopulation}}
  \mathrm{residualCoefficient}_N(n)K_N(s_0,n)\right\|
 \le C(N+1)e^{-N/25000}\longrightarrow0,
 }
\]

where `C=6*divisorSquareDirichletMass(1+1/262144)` is a genuinely convergent
arithmetic constant. The small Rankin cost in summing **every** prime
count is absorbed in the joint exponential saving. No hypothetical zero,
selected-mode norm payment, prime completion or relative-error-times-carrier
estimate enters this theorem.

`coreResponse_eq_paid_rest` is the exact original-carrier partition.
`joined_sub_literalCoreRest_bound` and
`tendsto_joined_sub_literalCoreRest` give the explicit bound and source
equivalence after deleting only that independently paid population. They
remain valid for arbitrary moving heights/counts and cofinal orders.
`literal_rest_owner_cut` checks that every nonzero original core atom
left on the actual dyadic schedule has `log(largestPrime)<243*N/200`.
The complementary signed carrier still needs an independent floor;
the source and balanced obstruction have not been discarded.

The optional `probe_riesz_joint_owner_rate.py` selects the rational tilt
and tests the exact binomial tails times the radial kernel on a floating
mesh. The optimized scalar exponent is positive at owner slope `1.205`
and negative at `1.215`. The finite normalized amplitudes can grow at
intermediate orders before decaying. These are diagnostic scalar-kernel
calculations, not literal prime counts, certified intervals, a numerical
starting order or a whole-floor certificate. The Lean theorem supplies
the uniform saving.

- [Joint radial/owner saving, literal signed sum and exact rest](../RiemannGaussian/ZetaRieszJointOwnerEnvelope.lean)

The next checked slice, `ZetaRieszFineDivisorRows`, improves the unsigned
comparison threshold from `N/10` to **`N/1000`** on the original saturated
full-window row population. With summable tilt `65537/65536`, the exact
counting-error rate after source growth and all-count cost is bounded by
`exp(-N/10000)`. The signed density main retains the complete factorial
allocation and is cancelled across the original radial window first.
Integer quadrature and both rounding slivers also have a strict geometric
rate. No owner prime/cofactor is completed.

This extends full-window eligibility from `log(pb)<=1.85N` to
**`log(pb)<=1.949N`**, for `log(p)<1.215N` and
`log(p)+L_N>=2.03N`. The literal squarefree sieve, unique-largest owner,
original core masks, actual count cutoff and full phase are retained.
`eventually_abs_fineLiteralRows_bound` gives a source-normalized bound
for the **original signed incidences**, by a fixed height-dependent
polynomial times subunit geometric rates. In particular,

\[
 u^{N_j+1}\,\mathrm{fineLiteralRows}_j\longrightarrow0.
\]

`coreConvolution_re_eq_fineRemaining` partitions the actual owner
incidences exactly. `tendsto_joined_re_sub_fineRemaining` gives

\[
 u^{N_j+1}\bigl(\Re\mathrm{joinedPhysical}_j-
                   \mathrm{fineRemaining}_j\bigr)\longrightarrow0.
\]

The rounding boundary is now paid on the **actual original endpoint
atoms**, not left as an anonymous discrepancy. For every real height,
`source_scaled_fineEndpointRows_bound` proves

\[
 \left|u^{N_j+1}\,\mathrm{fineEndpointRows}_j\right|
 \le18(N_j+1)^3e^{-9N_j/10000}\longrightarrow0.
\]

`fine_rows_closed_eq` shows that adding this endpoint gives the closed
integer interval. `fine_endpoint_not_selected` proves its divisor
incidence is disjoint from all previously paid fine-row incidences, and
`fine_literal_row_covered` covers every label satisfying the displayed
outer conditions. The final checked source equivalence is

\[
 u^{N_j+1}\bigl(\Re\mathrm{joinedPhysical}_j-
       (\mathrm{fineRemaining}_j-\mathrm{fineEndpointRows}_j)\bigr)
 \longrightarrow0.
\]

Every other original incidence stays signed in this remainder, including
smaller unsigned legs and clipped/unsaturated geometries. The theorem
`unit_unsigned_not_selected` checks explicitly that **`d=1` is unpaid**:
the balanced-triple obstruction is not removed by the finer threshold.
This is an alternative ledger to overlapping previous row
payments; it does not add duplicate credits. The global nonowner payment
is used once. The independent `-79/1000` floor remains unproved.
The optional fine-rate probe checks floating scalar exponents only;
no evaluated starting order or numerical floor is certified.

- [Fine-threshold literal signed payment and exact remainder](../RiemannGaussian/ZetaRieszFineDivisorRows.lean)

`ZetaRieszOwnerSafeRows` removes a **new unsaturated all-count population**
from the literal signed real carrier. Saturation was used to establish
that the unsigned divisor remained below the owner prime. This follows
directly on the concrete cone

\[
 \frac N2\le\log p,\qquad
 \frac{31N}{20}<\log(pb)\le\frac{1949N}{1000},\qquad
 \log p<\frac{243N}{200},\qquad
 \log p+L_N<\frac{203N}{100}.
\]

Every original unsigned integer in the closed radial row is below `p`.
The actual length, both hinges, physical primes, owner allocation,
squarefree/coprimality conditions, phase and count masks are unchanged.
An auxiliary length certifies finite ownership only. It does not change
the carrier. The signed full-window radial/Fourier estimate is applied
before taking an absolute value, and its original finite counting error
is paid by the summable fine-divisor tilt.

The **literal** signed real row sum has bound `fineRowBudget`; the closed
lower endpoint has bound `fineEndpointBudget`. Both tend to zero at source
scale. `ownerSafe_selected_disjoint_fine` proves disjointness at the
original divisor-incidence level, not just at the level of outer pairs.
`ownerSafe_unsigned_gt_one` also excludes the unit divisor from the
closed row, so balanced-triple unit incidences remain in the signed rest.

With

\[
 \mathrm{ownerSafeRemaining}
 =\mathrm{fineRemaining}-\mathrm{fineEndpointRows}
  -\mathrm{ownerSafeLiteralRows}-\mathrm{ownerSafeEndpointRows},
\]

the checked whole-real-carrier comparison is

\[
 \left|u^{N_j+1}\bigl(\Re\mathrm{joinedPhysical}_j
        -\mathrm{ownerSafeRemaining}_j\bigr)\right|
 \le \mathrm{joinedRowErrorBudget}-\mathrm{rowErrorBudget}
       +2(\mathrm{fineRowBudget}+\mathrm{fineEndpointBudget})
 \longrightarrow0.
\]

Shared carrier errors, including the global nonowner payment, occur once.
This is a geometric signed saving on a new literal population. It does
**not** establish the independent numerical floor for the remaining
incidences, a complex packet norm bound or a zero exclusion. The other
signed clipped rows and unit/small-unsigned contributions remain joined.

- [Unsaturated literal signed payment and explicit whole-real-carrier error](../RiemannGaussian/ZetaRieszOwnerSafeRows.lean)

`ZetaRieszUnifiedSignedRows` now uses the **same singleton owner
allocation** to join the literal large-owner payment with the two closed
divisor-row payments. Its variable-population estimate pools the
arithmetic mass over all labels. Closed divisor incidences cannot overlap
the large-owner population, including at rounded endpoints. The actual
signed remainder is

\[
 \mathrm{unifiedRemaining}
 =\mathrm{ownerSafeRemaining}-\Re\mathrm{largeOwnerIncidences}.
\]

The shared nonowner and carrier errors are charged once. For every
nonzero original canonical-owner atom outside the large-owner payment,
`unpaid_owner_cut` proves the strict cut `log(p)<243N/200` on the actual
dyadic core.

`ZetaRieszEdgeDivisorRows` then independently pays another **literal
signed all-count band**:

\[
 \frac{1949N}{1000}<\log(pb)\le\frac{3899N}{2000},\qquad
 \frac N2\le\log p<\frac{243N}{200}.
\]

Every original ownership, physical-prime, squarefree/coprimality,
core/count, phase and owner-allocation condition remains. The actual
moving Riesz length is unchanged; saturation is not required on this
band. The improved squarefree counting exponent is **`17/32`**, so the
unsigned-leg comparison gains `exp(-15N/64000)` at `log(d)>=N/2000`.
After the summable outer tilt and source normalization, the comparison
rate is at most `exp(-N/10000)`. With the old exponent `3/4`, this smaller
threshold does not give source decay. The exact signed radial/Fourier
main is retained before its absolute value is taken.

`eventually_abs_edgeLiteralRows_bound` gives the actual signed row bound
`edgeRowBudget`. Original rounded endpoints have independent bound
`18*(N+1)^3*exp(-N/2500)`. Closed incidence credits are disjoint from
both previous divisor-row populations and the whole large-owner payment.
The new whole-real-carrier comparison is

\[
 \left|u^{N_j+1}\bigl(\Re\mathrm{joinedPhysical}_j
       -\mathrm{edgeRemaining}_j\bigr)\right|
 \le\mathrm{unifiedErrorBudget}+\mathrm{edgeRowBudget}
       +\mathrm{edgeEndpointBudget}\longrightarrow0,
\]

where `edgeRemaining` subtracts only these newly paid closed rows from
`unifiedRemaining`. The numerical **`-79/1000` floor remains open** for
this single signed scalar. The unsigned unit and small-divisor/clipped
incidences of remaining owners are not norm-paid or assigned positive
count allowances. No cofinal starting order or zero exclusion is claimed.

- [One signed ledger with no overlapping credits](../RiemannGaussian/ZetaRieszUnifiedSignedRows.lean)
- [New literal signed band and finer squarefree error](../RiemannGaussian/ZetaRieszEdgeDivisorRows.lean)

`ZetaRieszLowOwnerRows` now removes a further **disjoint original signed
population across all its prime counts**:

\[
 \frac{7N}{25}\le\log p<\frac N2,\qquad
 \frac{7N}{4}<\log(pb)\le\frac{3899N}{2000},\qquad
 \log p+L_N<\frac{203N}{100}.
\]

The shared mechanism is complete-row ownership: if
`log(pb)+log(p)>203N/100`, an auxiliary cutoff between the two endpoints
certifies that the entire unsigned row stays below `p`. The new generic
finite-geometry theorem proves this exact criterion; the concrete cone
above is the region to which the signed estimate is applied. Neither the
auxiliary cutoff nor a completed cofactor enters an arithmetic atom.

The actual full-window sum has the existing `edgeRowBudget`, and the
original rounded endpoint has `edgeEndpointBudget`. Both tend to zero
at source scale. All original phases, factorial owner allocations,
physical support, coprimality and core/count masks survive. Every
nonzero selected closed incidence has at least **five** distinct prime
factors. Disjointness is proved against every previous closed divisor
credit and the whole large-owner payment.

With `lowOwnerRemaining = edgeRemaining - lowOwnerLiteralRows -
lowOwnerEndpointRows`, the checked comparison is

\[
 \left|u^{N_j+1}\bigl(\Re\mathrm{joinedPhysical}_j
       -\mathrm{lowOwnerRemaining}_j\bigr)\right|
 \le \mathrm{edgeErrorBudget}+\mathrm{edgeRowBudget}
       +\mathrm{edgeEndpointBudget}\longrightarrow0.
\]

This is an independent signed estimate on a previously unpaid region,
**not** the numerical `-79/1000` floor for the remaining global scalar.
Unit incidences are still unselected, including those of balanced
triples. Other small-divisor and ownership-boundary terms remain signed
and joined. No deficit percentage or cofinal starting order is inferred.

- [Smaller-owner signed payment, exact ownership criterion and ledger](../RiemannGaussian/ZetaRieszLowOwnerRows.lean)

`ZetaRieszOwnerGapRows` now applies the signed estimate to the **whole
common ownership-gap population**, retaining the quantitative outer cut:

\[
 \log(pb)+\log p>\frac{203N}{100},\qquad
 \log(pb)\le\frac{3899N}{2000},\qquad
 \log p<\frac{243N}{200}.
\]

The row-dependent auxiliary length only proves ownership. Arithmetic
atoms still use the original moving Riesz length, full phase, factorial
allocation, physical support, coprimality and core/count masks. The
checked independent bound for the entire original signed population is
`edgeRowBudget + edgeEndpointBudget`, tending to zero at source scale.
All four older row families are proved subsets. They are replaced by
this one payment, rather than added to it; the whole large-owner labels
are disjoint from the new closed incidences.

The exact ledger is now

\[
 \mathrm{ownerGapRemaining}_j
 =\Re\mathrm{coreConvolution}_j
  -\Re\mathrm{largeOwnerIncidences}_j
  -\mathrm{ownerGapLiteralRows}_j
  -\mathrm{ownerGapEndpointRows}_j.
\]

The real source-scaled difference from `joinedPhysical` is bounded by
one shared carrier/nonowner cost, one whole large-owner cost, and the
single common row cost; this budget tends to zero. The numerical
`-79/1000` floor for `ownerGapRemaining` remains **open**.

For an unselected active incidence with the theorem's original physical
owner, squarefree/coprimality, canonical ownership and core-window
hypotheses, Lean proves the sharper exhaustive support alternative

\[
 \log d<\frac{161N}{2000}
 \quad\text{or}\quad
 \log p<\log d+\frac{2N}{25}.
\]

In the second case, outside the first boundary, the original Riesz
support further forces `log(p)<147N/200`. This ceiling does not apply to
the short-leg boundary. The unit terms remain in that boundary, with
their phase and correlation with every unselected nonunit term retained.
No independent floor or new zero exclusion follows from this support
classification alone.

- [Complete ownership-gap signed payment and remaining geometry](../RiemannGaussian/ZetaRieszOwnerGapRows.lean)

The optional `probe_riesz_owner_safe.py` samples and factors actual integer
labels and uses the concrete cones and common ownership-gap predicate. It joins all divisor/count
contributions with their common complex phase and checks the ledger.
The diagnostic orders 20, 24 and 28 contain selected incidences, but are
not cofinal and fail the eventual length hypothesis. Their means and
sampling errors certify no floor or source-scale rate.

Its optional `--witness-orders 1536` diagnostic constructs a six-prime
integer with 1335 digits, total log `2N`, owner log approximately `0.4N`,
outer log approximately `1.786N` and unsigned log approximately `0.214N`.
It selects a new smaller-owner incidence and no prior row credit, and
the separate moving-length inequality is met. Numerical primality,
logarithms and the mask transcription are not Lean certificates. This
example measures neither population mass nor progress toward the floor.

Its optional `--owner-gap-witness-orders 1536` constructs a four-prime
integer with the same 1335-digit total size. The selected additional
incidence has approximate owner/outer/unsigned logs `0.55N`, `1.51N`,
`0.49N`, and falls outside all four older row cones. It passes the
transcribed core masks and eventual length inequality. This is an
actual-integer diagnostic, not a Lean nonemptiness theorem or a source
mass/floor certificate. Small-order regressions check the expanded
signed ledger and its old-to-new selection inclusion; they are not
cofinal asymptotic evidence.

The new [short-divisor cancellation](../RiemannGaussian/ZetaRieszShortDivisorCancellation.lean)
applies exact Möbius cancellation INSIDE this unpaid remainder. For a
squarefree cofactor `a` and a composite divisor block `R|a`, put
`T=log(pa)` and `D=T-L_N`. If

\[
 \log R<T-\frac{3899N}{2000},\qquad \log R\le D,
 \qquad D\le\log p\ \text{or}\ \log p+\log R\le D,
\]

the complete signed incidence block `d|R` has contribution **exactly
zero**, with the actual allocation, factorial weight and full phase
common to every term. Both its constant and first logarithmic moments
cancel. The block includes `d=1`; it lies strictly outside the paid
closed rows. The canonical selection also excludes the already paid
whole large-owner labels. The exact `ownerGapRemaining` ledger can
therefore omit these blocks without a new error or duplicate payment.
No count is fixed or completed, and no factorial order is discarded.

For two distinct small cofactor primes `r,s`, even a block that crosses
the second hinge has an exact joined formula:

\[
 \sum_{d\mid rs}\mu(a/d)H_{L_N}(p,a/d)
 =-\mu(a)\operatorname{Tent}_{\log r,\log s}(\log a-L_N),
 \quad \log(rs)\le T-L_N.
\]

The surviving tent has width `log(rs)`, height at most
`min(log r,log s)` and keeps its Möbius sign. Its arithmetic value is
independent of the marked prime. Joining that prime's complete retained
finite population yields the checked literal row floor

\[
 \Re\sum_{p\in P}\sum_{d\mid rs}
   w_{N,y}(p,a)\mu(a/d)H_{L_N}(p,a/d)
 \ge -\min(\log r,\log s)
     \left|\Re\sum_{p\in P}w_{N,y}(p,a)\right|.
\]

Here `w` is the original `phaseWeight`; `P` keeps all its original
support and owner masks. The right-hand side observes ONE signed prime
aggregate, not a sum of absolute prime terms. Its global source-scaled
cost has not been proved small enough for the `-79/1000` floor.

For labels with `log(R)<=B*log(N+1)`, Lean further proves uniformly in
the original count cutoff that surviving unit incidences eventually
require

\[
 T-L_N-B\log(N+1)<\log p<T-L_N.
\]

The cofinal starting order is not evaluated. Labels without a sufficiently
small block, the compact reflected crossing and the other short/near-owner
incidences remain signed and unpaid. This is an exact reduction of part
of the global arithmetic gap, **not** a proved numerical whole floor.

The optional `probe_riesz_short_divisor_blocks.py` checks actual factored
integer labels and this tent formula. At `N=1536` its six-prime cancelling
example has separate unsigned charge about `3732.23` but joined block
zero, while the complete label has a nonzero reflected coefficient about
`12.99`. Six- and seven-prime crossing examples have joined blocks about
`+20.67` and `-20.67` respectively. These raw coefficient diagnostics
are not population/source mass, Lean nonemptiness proofs or a bound on
the whole signed rest. Small-order sample tests are not cofinal and fail
the separate eventual-length hypothesis. The probe stays outside CI.

`ZetaRieszShortDivisorOrbits` now applies this zero payment throughout
the short-divisor population. Write `R` for the two-smallest-cofactor-prime
block and `m=a/R`. Squarefreeness gives a disjoint partition of every
original cofactor incidence into

\[
 d=e\delta,\qquad e\mid m,\quad\delta\mid R.
\]

Every complete block below the short cutoff that crosses neither hinge
cancels exactly. The common observation is evaluated at **the original
label `p*a`**, including its complex phase, factorial kernel and allocation.
It is never moved to `p*(a/e)`. The selected union contains all previous
unit-based blocks, stays outside both paid populations, and has exactly
zero source-scaled norm for every finite order, count cutoff and height.
`ownerGapRemaining_eq_sum_sdiff` removes it from the existing ledger with
no extra error and no duplicate credit.

For `T=log n` and `H=T-3899N/2000`, every surviving short incidence
belongs to a based block whose base satisfies one of

\[
 H-\log R\le\log e<H,
 \qquad
 \log a-L_N-\log R<\log e<\log a-L_N.
\]

These are respectively the short-cutoff crossing and the reflected
cofactor-hinge crossing. If `log R <= B log(N+1)`, both have logarithmic
width. On the reflected strip the original moving length further gives,
eventually on the requested radius interval,

\[
 9N/16<\log p<131N/200.
\]

**Neither remaining strip is norm-paid.** Rough blocks and the other
near-owner incidences remain signed and unpaid; the whole `-79/1000`
floor is still open. The thresholds in the eventual statements are not
evaluated.

The optional block probe now checks all disjoint based blocks. At
`N=1536`, a nine-prime diagnostic label has 21 original short incidences:
16 belong to four cancelling blocks and the other five meet the short
cutoff. Their separate raw charges total about `14756.90`, while their
joint coefficient is zero. A second nine-prime label has one cancelling
block and retains both kinds of crossing. These are actual-integer
transcription regressions, not Lean nonemptiness, global proportions,
population/source mass or a floor certificate.

The optional `probe_riesz_fine_remaining.py` separates the unit and
nonunit parts of this exact signed remainder **after retaining their
common product phase**. It samples and factors actual integer labels,
checks the divisor/remainder ledger, and reports joint covariance and
sampling errors. At diagnostic orders 16 and 20 their covariance is
strongly negative in the tested heights. Those orders fail the eventual
length condition and are not the cofinal schedule; this observation is
not a floor, an asymptotic rate or a paid arithmetic error.

The optional `probe_riesz_canonical_joint.py` samples actual integers,
checks their factorizations and keeps the full phase when evaluating the
literal/density/remainder channels together. Orders 28 and 32 are diagnostic
only: they are outside the cofinal schedule and do not satisfy the eventual
length hypothesis. The observed covariance and free/clipped split are
uncertified Monte Carlo evidence; they do not prove any floor or asymptotic
rate. Divisor regression uses the reflected response `-R_L(n)`, without
an extra outer Möbius sign.


## Independent payment of the fixed-block short-cutoff crossing

`ZetaRieszShortCutoffRows` pays a new literal signed population, including
its original count cutoff and rounded endpoints. This is an independent
arithmetic estimate; no exposed-zero, RH, prime-density or unproved bilinear
hypothesis enters. It does not yet establish the whole `-79/1000` floor.

Write a selected original cofactor as `a=B*e`, with `6|B`, and freeze the
canonical owner `p`. For `delta|6`, the original divisor incidence is
`(e*delta,B/delta)` and its common phase/allocation is evaluated at `p*B*e`.
Exactly,

\[
 \log(e\delta)<\log(pBe)-3899N/2000
 \iff \log\delta<\log(pB)-3899N/2000.
\]

Thus the cutoff is independent of the unsigned variable `e`. The entire
clipped block can be summed first into one signed scalar

\[
 \kappa_N(L,p,B)=
 \frac{\displaystyle\sum_{\substack{\delta\mid6\\
                \log\delta<\log(pB)-3899N/2000}}
            \mu(\delta)H_L(p,B/\delta)}{H_L(p,B)},
 \qquad |\kappa_N|\le4.
\]

Here `H_L` is the original joined two-hinge difference. The exact identity
`cutoff_row_atom_eq` keeps the original label and both hinges, and
`literalCutoffPacket_eq_rows` retains every original core/count, prime,
squarefree, coprimality, moving-length, factorial and owner-allocation mask.
The multiplier is applied to the **whole signed unsigned row before**
bounding it. The high-count overflow is independently paid with the
original weighted partial-divisor majorant, not inferred from the norm of
an unweighted overflow sum.

The new row conditions are

\[
 3899N/2000<\log(pB)\le3899N/2000+\log6,
 \quad \log(pB)+\log p>203N/100,
 \quad \log p<243N/200.
\]

A temporary quantitative cutoff
`log(pB)<=(39/20-1/2016)N` certifies `e>=exp(N/2016)`.
`eventually_cutoff_strip_gap` proves that this contains the whole displayed
fixed-width strip eventually; no excluded slice is silently discarded.
The concrete owner cone `log(p)>=81N/1000` suffices for whole-row ownership
inside this strip. All primes of `B` must still be below `p`, and every
literal support condition in `cutoffRows` is retained.

The counting exponent is `17/32`. After the original outer-count Rankin
cost, its source rate is

\[
 2u\exp\left(-\frac{15}{64512}+\frac{203}{6553600}\right)
 \le \exp(-1/10000)<1.
\]

The signed density main uses the existing full-window Fourier cancellation,
with the proved smaller lattice gap. For fixed `|y|>=54`,
`1/2<u<=10001/20000`, and the original cofinal orders/counts, Lean proves

\[
 \left|u^{N_j+1}\operatorname{literalCutoffPacket}_j\right|
 \le4\operatorname{edgeRowBudget}(y,N_j)
       +72(N_j+1)^3\exp(-N_j/10000)
 \longrightarrow0.
\]

The rounded lower endpoint is included explicitly. Every nonzero term is
an original squarefree antidiagonal incidence, and `gcd(e*delta,6)=delta`
recovers the block tag: distinct row/base/tag triples cannot duplicate an
original incidence. Selected terms have `log(p*(B/delta))>3899N/2000`, so
none overlaps the previous owner-gap row credit.
`cutoff_incidence_not_cancelledOrbit` also excludes every previously
zero-cancelled affine orbit, including every alternate based-block index.

Reverse coverage is also checked. `cutoff_crossing_covered` starts
with an original squarefree core label `p*B*e`, its canonical owner and
nonzero based-block hinge. Whenever the displayed cutoff crossing has
whole-row ownership, it lands in the paid closed row with its exact
`delta` and sieve value one. The quantitative gap is automatic eventually.

There is a count-uniform consequence. For an original squarefree label,

\[
 \log n=\sum_{q\mid n,\ q\text{ prime}}\log q
 \le\omega(n)\log p.
\]

The core lower bound therefore forces whole-row ownership if
`omega(n)<=24`. `cutoff_crossing_covered_of_count_le` covers these original
incidences by the **same all-count payment**; it does not norm-bound a
separately count-truncated packet. Conversely,
`eventually_unpaid_six_crossing_geometry` proves that, below the old owner
ceiling and with every stated original predicate retained, an unselected
nonzero fixed-block cutoff crossing must satisfy

\[
 \omega(n)\ge25,
 \qquad\log p<\frac{161}{2000}N.
\]

This removes an ownership exception in this population and localizes its
surviving part. It does not establish a cost bound for that high-count,
small-owner remainder, nor pay other block or reflected-hinge geometries.

The surviving tiny-owner sector has a second, **exact** payment. On

\[
 \log2<\log(pB)-3899N/2000\le\log3,
\]

`cutoffDivisors_eq_pair` proves that the original strict cutoff retains
precisely `delta=1,2`. With `log(p)<=161N/2000`, `N>=32`, and `u>=1/2`,
the actual moving length saturates both hinges. Consequently,

\[
 w\mu(B)H_{L_N}(p,B)
 +w\mu(B/2)H_{L_N}(p,B/2)
 =w\log p\,[\mu(B)+\mu(B/2)]=0.
\]

Here `w` is the full original common observation at `p*B*e`, with no
change to its factorial allocation, phase or label. The squarefree block
makes `mu(B/2)=-mu(B)`.
`literal_middle_cutoff_population_eq_zero` proves **zero complex
source-scaled cost for the whole selected literal population**, with its
core/count mask and physical canonical owner retained. This payment needs
no whole-row ownership or counting comparison and adds no error budget.
It does not bound the two remaining edges of the cutoff strip or any
reflected crossing.

`cutoffRemaining = ownerGapRemaining - literalCutoffPacket` now has an
independent source-o(1) comparison to the whole real `joinedPhysical`, with
shared payments charged once. Its numerical floor remains **open**. Other
small blocks, the reflected-hinge crossing, rough labels and unselected
ownership geometries have not received this new payment. No global
percentage of the remaining deficit, packet nonemptiness or zero exclusion
is asserted.

## Uniform canonical-pair cutoff payment

[`ZetaRieszRoughCutoffRows`](../RiemannGaussian/ZetaRieszRoughCutoffRows.lean)
extends the fixed-six payment to the actual canonical pair
`R(B)=minFac(B)*minFac(B/minFac(B))`, with second prime at most
`floor(sqrt(N))`. This is a joined signed estimate on the original prime
sum, independent of exposed-zero assumptions. It keeps the same
ownership-safe crossing geometry, the actual moving Riesz length and
every original phase/allocation/core/count/physical mask.

Canonicity has a counting cost. The unsigned variable is squarefree and
avoids the **exact** forbidden set

\[
 S(p,B)=\operatorname{primeFactors}(pB)
        \cup\{q\text{ prime}:q\le\operatorname{secondPrime}(B)\}.
\]

`roughTag_eq_one_of_original_pair` proves that an original based orbit
already satisfies this mask. It is not a completed density carrier or a
deletion of original canonical incidences. The extra counting factor is
at most `3^floor(sqrt(N))`. Lean proves

\[
 e^{-N/10000}3^{\lfloor\sqrt N\rfloor}\le e^{-N/20000}
 \quad(N\ge1600000000).
\]

That large explicit threshold certifies **only this cost absorption**;
the complete packet theorem still has unevaluated eventual hypotheses.
The original strict cutoff is independent of the unsigned variable, so
all four clipped divisor terms are joined into a signed multiplier before
the complete signed row is estimated. The high-count bound now allows an
incidence-dependent multiplier, retaining the exact roughness mask.
All original rounded lower endpoints are also included.

For fixed `|y|>=54`, `1/2<u<=10001/20000`, and the original cofinal
orders/counts, `eventually_literalCutoffPacket_bound` gives

\[
 \left|u^{N_j+1}\operatorname{literalCutoffPacket}_j\right|
 \le\operatorname{roughRowBudget}(y,N_j)
      +\operatorname{cutoffEndpointBudget}(N_j)\longrightarrow0,
\]

where the new row budget is

\[
 4\operatorname{fineMainBudget}(y,N)
 +4\operatorname{edgeErrorConstant}(8+|y|)(N+1)^3e^{-N/20000}
 +4\operatorname{highCountConstant}(N+1)^2(49/50)^N.
\]

Canonical-owner and gcd recovery prove incidence injectivity.
`cutoff_incidence_not_cancelledOrbit` and
`cutoff_incidence_not_ownerGapRows` exclude duplicate previous credits.
Reverse coverage starts from an original core label and proves the new
roughness mask rather than assuming it. Since `R(B)<=N`, its logarithmic
crossing width fits the proved unsigned gap eventually. Counts through 24
force the whole-row ownership condition and are included in the **same
all-count payment**, not separately norm-paid. Below the old owner ceiling,
an unselected nonzero crossing of this small-pair type therefore has
`omega(n)>=25` and `log(p)<161N/2000` eventually.

The exact tiny-owner zero payment is more general still. For **any**
canonical pair `r<s`, including rough pairs with `s>sqrt(N)`, the middle
cutoff strip

\[
 \log r<\log(pB)-3899N/2000\le\log s
\]

retains exactly `delta=1,r`. With the actual moving length, `N>=32`,
`u>=1/2` and `log(p)<=161N/2000`, its lower cutoff itself forces both
hinges to equal `log(p)`. Thus the original common complex observation
multiplies `mu(B)+mu(B/r)=0`. The full literal population has **exactly
zero** source-scaled complex value at every height, without a whole-row
ownership or small-pair hypothesis. The optional actual-prime probe also
checks a 36-prime rough example with canonical pair `(43,47)`; this floating
regression is not a Lean population or cofinal certificate.

The current signed rest is
`roughCutoffRemaining = ownerGapRemaining - literalCutoffPacket`.
This replaces the fixed-six subtraction; those credits must never be
added twice. Its exact comparison to real `joinedPhysical` has error
`ownerGapErrorBudget + roughRowBudget + cutoffEndpointBudget -> 0`, with
shared earlier errors charged once. The cutoff edges, reflected crossings,
rough ownership failures and other original unselected incidences remain
joined and unpaid. **No numerical whole floor, ceiling or new zero
exclusion is proved.**


## Literal lower radial payment

[`ZetaRieszLowerRadialPayment`](../RiemannGaussian/ZetaRieszLowerRadialPayment.lean)
pays the entire lower boundary of the original canonical-owner sum:

\[
  1.95N<\log n\le1.97N.
\]

The original `coreBand`, count cutoff, physical prime masks, full phase,
actual Riesz length and `1-boundedShare` are unchanged. The main is only
restricted by total logarithm, after an independent arithmetic estimate.
This payment does not split the signed main by prime count.

Put `U=10001/20000`, `sigma=1+1/1048576`, and
`M_sigma=zetaMoebiusLogMajorantMass sigma`. For any finite original
selection below `197N/100`, and any coefficient family satisfying
`norm(c(n))<=H*zetaMoebiusLogMajorant(n)`, Lean proves

\[
 \left\|u^{N+1}\sum_n c(n)K_N(3/2+iy,n)\right\|
 \le H U M_\sigma e^{-N/100000},\qquad 0\le u\le U.
\]

Heights and selections may vary freely. The reference mass is genuinely
summable, and the strict geometric rate is certified by the exact rational
inequality

\[
 U\frac{197}{100}\le
 \left(\frac{99984988}{100000000}\right)^{100},
\]

followed by `log x<=x-1`. No floating saddle calculation is used in the
Lean proof. `norm_lower_partial_sum_bound` also applies to **any retained
original divisor suballocation** in this strip, with `H=2`, under its
explicit positive-length and `log n<=2L` hypotheses. It does not complete
the cofactor or discard its masks.

`coreConvolution_eq_lower_add_central` is an exact whole-label split. Its
lower term has the bound `norm_lowerPacket_bound` with `H=1`; the central
term consists of the same original owner atoms on

\[
 1.97N<\log n\le2.03N.
\]

The narrowed support provides a larger unsigned gap for the next signed
row estimates. If `n=p*b*d` and `log(pb)<=3899N/2000`, then

\[
 \log d>\frac{41}{2000}N.
\]

This is a support improvement; it does **not** itself pay an enlarged
rough canonical-pair packet or remove the literal largest-prime mask.

The exact current ledger is

\[
 \begin{split}
 \operatorname{centralRemaining}_j
 ={}&\operatorname{centralConvolution}_j^{\rm re}
       -\operatorname{largeOwnerIncidences}_j^{\rm re}\\
    &-\operatorname{ownerGapLiteralRows}_j
       -\operatorname{ownerGapEndpointRows}_j
       -\operatorname{literalCutoffPacket}_j.
 \end{split}
\]

All older payment terms keep their original supports, including any
lower-boundary pieces. Their whole-row source-o(1) estimates are retained
once; no claim that partial rows inherit whole-row cancellation is made.
`eventually_abs_joined_sub_centralRemaining_bound` adds only
`lowerBudget(N)=U*M_sigma*exp(-N/100000)` to the preceding comparison
budget. The total budget tends to zero. The sufficient numerical
`-79/1000` floor for this signed rest remains **open**.

The optional `probe_riesz_lower_radial.py` checks genuine five-prime
labels at `N=256,640` in the paid strip and the central window against the
original masks. It also checks a 36-prime, tiny-owner cutoff example at
`N=256`: two distinct based blocks on the **same** original label have
cuts selecting `{1,2,3}` and `{1}` for the canonical pair `2*3`. Deleting
the third prime `5` flips the frozen cofactor's Mobius sign, and both
saturated blocks contribute `-log p`, giving `-2log p` together. This is a
diagnostic rejection of that particular adjacent-edge pairing, not a
proof that every joint pairing fails. The regressions certify neither
population mass, a cofinal starting order, a fraction of the floor deficit,
nor a zero exclusion. They remain outside the ordinary build and CI.

## Canonical cutoff payment through the physical smooth threshold

[`ZetaRieszPrimeWeightedSieve`](../RiemannGaussian/ZetaRieszPrimeWeightedSieve.lean)
recovers information discarded by the old forbidden-prime comparison.
The exact finite intersection cost is

\[
 \mathcal C_\sigma(S)=\prod_{p\in S}
   (1+p^{-\sigma}+p^{-2\sigma}).
\]

The old estimate replaced every factor by three. At `sigma=17/32`,
for `p<=N^2` the exact logarithmic weights instead give

\[
 p^{-17/32}\le N^{31/32}p^{-65/64},\qquad
 \mathcal C_{17/32}(S)\le
 \exp\bigl(2\,\mathrm{countMass}(65/64)N^{31/32}\bigr).
\]

The reference integer mass is genuinely summable. For the actual forbidden
set, its outer coprimality factors still contribute at most `3^omega(pB)`;
their aggregate cost is already controlled by the finite outer-row estimate.
The additional small-prime product is subexponential, so Lean proves

\[
 e^{-N/10000}
 \exp\bigl(2\,\mathrm{countMass}(65/64)N^{31/32}\bigr)
 \le e^{-N/20000}\quad\text{eventually}.
\]

[`ZetaRieszPolynomialCutoffRows`](../RiemannGaussian/ZetaRieszPolynomialCutoffRows.lean)
uses that estimate on the **same original canonical cutoff crossings**,
enlarging only `secondPrime(B)<=sqrt(N)` to `secondPrime(B)<=N^2`.
The complete signed density main is still bounded jointly; no new
prime-density estimate or assumed bilinear saving is used. All original
phase, moving-length, allocation, roughness, count, radial and physical
masks are retained. The old whole-window owner condition remains required.
The stronger unsigned gap of the central radial window is not used to
assert cancellation of a partial row.

`eventually_literalCutoffPacket_bound` bounds the literal enlarged packet
by `roughRowBudget+cutoffEndpointBudget`, both tending to zero at source
scale. The comparison cost has the explicit eventual saving above; the
signed density and count-overflow costs retain their previously proved
geometric rates. Original canonical incidence injectivity and reverse
coverage are proved, including the rounded lower endpoint. These incidences
do not duplicate previous owner-gap rows or cancelled affine orbits.

`sqrt_cutoffRows_subset` proves containment of the previous selector. The
new credit **replaces** the old canonical cutoff packet. Their values must
not be subtracted twice. The current exact ledger is

\[
 \begin{split}
 \mathrm{polynomialCentralRemaining}_j
 ={}&\mathrm{centralConvolution}_j^{\rm re}
      -\mathrm{largeOwnerIncidences}_j^{\rm re}\\
    &-\mathrm{ownerGapLiteralRows}_j
      -\mathrm{ownerGapEndpointRows}_j
      -\mathrm{literalCutoffPacket}^{(N^2)}_j.
 \end{split}
\]

The original main is still `197N/100<log(n)<=203N/100`. Older whole-row
credits keep their original supports. The independent comparison budget
is `ownerGapErrorBudget+roughRowBudget+cutoffEndpointBudget+lowerBudget`,
charged once and tending to zero. The numerical `-79/1000` floor for this
retained signed rest remains **open**.

The enlarged block satisfies `R(B)<=N^4`; its crossing width is at most
`4 log N`, which fits the original unsigned gap eventually. Reverse
coverage includes counts through 24 in the same all-count signed payment.
An unselected active crossing with second prime at most `N^2`, under the
stated original physical and owner predicates, therefore still has
`omega(n)>=25` and `log(p)<161N/2000` eventually. Tiny-owner cutoff edges,
pairs beyond `N^2`, reflected crossings and other signed geometries remain
unpaid. This support restriction is not a floor for them.

The optional `probe_riesz_weighted_sieve.py` checks genuine seven-prime
original-label rows with pairs `(17,19)`, `(257,263)` and `(65519,65521)` at
`N=256,640`. It retains each original observation and exercises rows beyond
the old cap. Finite prime-prefix tests compare the actual product with the
old factor-three estimate. At `N=1536` their logarithmic costs are about
`173.22` and `190624.61`; nevertheless the weighted cost at these sample
orders **does not yet satisfy** the eventual geometric comparison.
Neither a finite starting order, a proportion of the global deficit,
population mass nor a whole floor is certified by these experiments.
Explicit log-amplitudes flag floating underflow; rounded zero is never
used as cancellation evidence. The probe remains outside ordinary builds
and CI. The checked local batch contains 471 public theorem axiom records;
the affected namespaces pass all 14 scoped linters. The RH floor, ceiling
and any new zero exclusion remain open.

## Exact restoration of the remaining cutoff crossings

[`ZetaRieszCrossingOrbitCancellation`](../RiemannGaussian/ZetaRieszCrossingOrbitCancellation.lean)
removes the tiny-owner exception left by the canonical polynomial
cutoff payment. The cancellation restores **full original based blocks**
across the artificial cutoff, including their previously unjoined members.
It does not bound the clipped edges separately.

Write `p=largestPrime(n)`, `a=n/p`, `R=leastPairBlock(a)`, and `T=log(n)`.
For a base `e` dividing `a/R`, select the crossing precisely when

\[
 \log e<T-\frac{3899}{2000}N\le\log(eR),\qquad
 T-\log e+\log p\le\frac{203}{100}N.
\]

The last condition is the failure of the whole-window ownership gap.
It implies

\[
 \log p<\frac{161}{2000}N.
\]

The two canonical cofactor primes are bounded by the original owner,
so `log R<=2 log p`, even for rough pairs. With the actual moving length
`L<=3N/2`, valid here for `u>=1/2` and `N>=32`, Lean proves

\[
 \log p+\log e+\log R\le T-L.
\]

Thus every original two-hinge coefficient on the entire orbit
`d=e*delta`, `delta|R`, equals `log p`. Their original complex observation
is common: it is evaluated at `n`, with its literal allocation, factorial
kernel, phase and all label masks unchanged. Since `R` consists of two
distinct primes, their four Möbius signs sum to zero. Consequently

\[
 \sum_{\delta\mid R}W_N(n)\mu\bigl(a/(e\delta)\bigr)
    \operatorname{pairHinge}_L\bigl(p,a/(e\delta)\bigr)=0.
\]

`source_scaled_crossing_population_norm_eq_zero` is the **independent
exact zero norm bound** for the whole literal selected population, at every
height and count cutoff, not merely a numerical example or a conditional
phase estimate. Polynomial pair smallness is unnecessary for this payment.
It does not say that every tiny-owner label or its entire residual vanishes.

The restored blocks are disjoint original antidiagonal subsets. They do
not overlap the old short-interior zero blocks, prior owner-gap row credits,
whole large-owner labels or the enlarged polynomial packet. For the last
claim, canonical incidence recovery first identifies the same orbit base;
the paid packet requires a strict owner gap, while the restored orbit
fails it. No credit is spent twice.

Combined with the preceding geometric payment,
`eventually_polynomial_crossing_paid_or_cancelled` now covers **every
active canonical artificial-cutoff crossing in the second-prime cap
`N^2`**, under its stated original predicates: it is either in the literal
paid packet or in a restored exact zero block. The previous count-25 and
tiny-owner exceptions in this particular branch are gone.

`polynomialCentralRemaining_eq_sum_sdiff` deletes the old interiors and
new restored blocks directly from the same original central owner atoms.
The large-owner, closed-row and polynomial-cutoff credits keep their
original supports, each once. The comparison budget is unchanged; this
zero payment adds no positive allowance.

Ownership-safe cutoff crossings beyond `N^2`, genuine reflected
Riesz-hinge crossings and other unselected original signed rows remain
unpaid. A cutoff crossing surviving restoration satisfies
`log(p)>161N/6000`; that lower bound is support information, not a norm or
numerical floor. **The whole `-79/1000` floor, ceiling and zero exclusion
remain open. No proportion of the global deficit is certified.**

The optional `probe_riesz_crossing_orbits.py` preserves the preceding
negative numerical regression: its two clipped canonical-6 blocks on the
same 36-prime original label reinforce, giving about `-33.28000122314927`.
Restoring the full original orbits supplies the matching opposite terms,
and each complete block is zero separately. A fully rough 36-prime label
with canonical pair `(65537,65539)`, beyond `N^2` at `N=256`, gives the same
full-block cancellation while retaining every original mask. Those
regressions illustrate the identity; the Lean population theorem proves it.
Neither floating zeros nor underflow certify a whole floor. The script is
outside ordinary builds and CI. The restored-crossing slice initially had
496 public theorem records. Its enlarged affine extension is described below.

## Zero cost beyond the artificial cutoff

The same module now proves an independent exact zero bound for a larger
original unpaid population. It no longer requires an orbit to cross the
artificial cutoff. `UnpaidAffineOrbit` selects complete original blocks with

\[
 \log(eR)\le T-L,\qquad
 \bigl(T-L-\log e\le\log p\bigr)
 \ \lor\ \bigl(\log p+\log(eR)\le T-L\bigr),
\]

and with the original owner ceiling and failed based-owner gap

\[
 \log p<\frac{243}{200}N,\qquad
 T-\log e+\log p\le\frac{203}{100}N.
\]

The selector excludes the previously removed short interiors. These
conditions keep both original hinges in one affine region throughout
the whole four-member block; Möbius cancellation is then exact, even far
beyond the artificial short cutoff. All members are incidences of the same
original label. The complex phase, factorial kernel, owner allocation and
every physical/count/radial mask remain unchanged.

`source_scaled_affine_population_norm_eq_zero` bounds the norm of the
ENTIRE selected population by **zero**, independently of a zero hypothesis,
at every order, height and count cutoff. `crossingDivisors_subset_affine`
includes the preceding restored-crossing population, so its credit is
replaced rather than added. The new population is disjoint from the old
interiors, whole large-owner payment, closed owner-gap rows and literal
canonical polynomial-cutoff packet.

`polynomialCentralRemaining_eq_affine_sdiff` removes the enlarged population
directly from the SAME current floor ledger, with no new carrier, budget or
positive allowance. The existing full-support comparison credits and
lower radial payment are each charged once. No partial-row decay is inferred.

The optional same-label probes also contain complete blocks beyond both
earlier selectors. At `N=256` their individual signed coefficients have
magnitude about `16.64` and cancel jointly, including in the fully rough
case. Floating roundoff is explicitly diagnostic; only Lean establishes
population-wide cancellation.

`remaining_affine_hinge_crossing` confines a surviving failed-owner block,
under its stated full-hinge conditions, to the actual Riesz-hinge interval.
That statement is support information. Ownership-safe rough cutoff edges,
actual hinge crossings and other unselected signed geometries still need a
joint bound. **The independent whole `-79/1000` floor, ceiling and zero
exclusion remain open.** No certified deficit percentage is available.

The accumulated batch has 511 public theorem axiom records in 21 modules.
All 59 affected public proofs pass scoped axiom and namespace-lint checks;
the authorized publication also runs ordinary-root and presentation gates.
The published conditional endpoint is retained, with Latest Update recording
these supporting savings and the still-open numerical floor.
