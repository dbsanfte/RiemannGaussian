# Geometric payment with the ordered cofactor retained

[ZetaRieszExposedModeCoupling](../RiemannGaussian/ZetaRieszExposedModeCoupling.lean)
bounds genuine separated-zero components of the existing marked Riesz
response. [ZetaRieszCompletionPayment](../RiemannGaussian/ZetaRieszCompletionPayment.lean)
also pays its full Gamma completion contribution. The subsequent
[unshifted payment](../RiemannGaussian/ZetaRieszUnshiftedPayment.lean)
pays the unshifted part of the selected mode itself. Its shifted resonance
remains open. The
[audit](riesz-exposed-mode-coupling-audit.json) records the exact scope.

For a fixed finite genuine zero divisor `W`, retain all multiplicities and
select only zeros satisfying

```math
|\tau-(3/2+iy)|\ge501/1000,\qquad |\xi|\le1/2000.
```

Both marked denominators then have modulus at least `1001/2000`.
`modeDifference_bound` keeps their subtraction together and obtains

```math
\left|\frac{(-z)^{-j}-(i\xi-z)^{-j}}j\right|
\le |\xi|(1001/2000)^{-(j+1)}.
```

The exact ordered cofactor supplies its second Fourier zero. Its existing
Cauchy radius is `a=1/2-1/262144`; it still includes the least prime, the
entire ordered middle-prime product and the correlated complementary
order `N+1-j`. On every original rectangle order, `j>=N/2`. With
`U=10001/20000`, Lean checks the rational inequality

```math
(U/a)^2\frac{a}{1001/2000}\le(9999/10000)^2.
```

Consequently `coupled_order_bound` gives

```math
u^{N+1}(1001/2000)^{-j}a^{-(N+1-j)}
\le2(9999/10000)^N,\qquad 0\le u\le U.
```

This pays the cofactor amplification as well as the marked leg. It is not
an inference from separately converging complete prime legs.

## Integrated bound and exact signed ledger

Write `M_W` for the sum of actual analytic multiplicities in this separated
sector, and

```math
B=4\exp(4\operatorname{mass}(3/2-a))
      \operatorname{logMass}(3/2-a).
```

The theorem `farResponse_bound` proves, for every finite prime set whose
elements are at least 16 and every moving Riesz length `L>=1`,

```math
\|u^{N+1}\operatorname{farResponse}_N\|
\le2M_W B(N+2)^3(9999/10000)^N.
```

The response integrates both signed Fourier frequencies on
`0<xi<=1/2000`, with the original `xi^-2` and Riesz prefactor.
`integrable_scaled_farPair` proves genuine integrability at zero using the
two retained Fourier zeros. `tendsto_farResponse` proves geometric decay
up to the displayed polynomial, uniformly over arbitrary moving prime sets
and admissible moving lengths. The constant may be large and depends on
the fixed divisor; no useful numerical starting order is asserted.

`moment_principal_split` and `logDifference_principal_split` identify the
component in the actual logarithmic derivative. For the repository's local
genuine divisor, `regularPart_local` keeps exactly the zeta pole,
completion correction and analytic xi remainder. There are no reflected
artificial modes or infinite-divisor passage. The checked identity is

```math
\operatorname{logSymbol}
=\operatorname{retainedSymbol}-\operatorname{farSymbol}.
```

Here the retained symbol contains the regular part and all nearby zeros,
with the unchanged cofactor and factorial rectangle. Only the stated
Fourier band is subtracted at integral level; exterior frequencies remain.
`selected_not_far` proves that the selected source, at distance
`u<=0.50005`, is never included in this payment.

`logMain_retained_bound` gives the explicit geometric cost for this
subtraction in the current main. `tendsto_retained_sub_current` retains the
existing source equivalence to the literal
`lowerThresholdPacket-shortOverflowPacket`, along the original dyadic
orders and prime-count cutoffs. Its proof reuses every earlier completion
and proper-prime-power error payment.

## Full-frequency extension and disjoint combined payment

Horizontal separation gives a second, larger payment.
`horizontal_radius` proves that if `Re(z)<=-501/1000`, both denominators
stay outside `1001/2000` for **every** real Fourier frequency.
For actual zero coordinates this holds whenever `Re(tau)<=999/1000`.

The small-frequency bound above and a separate large-frequency bound give
`horizontal_pair_profile`, an integrable envelope proportional to
`(1+xi^2)^(-1)`. Thus `horizontalResponse_bound` pays the entire Fourier
integral for each such genuine local zero, with the same geometric rate
and no omitted exterior-frequency boundary. The selected source is excluded
by `selected_not_horizontal`.

`horizontalContribution_eq_integral` proves integrability and the exact
finite multiplicity-weighted sum/integral exchange. These are the same
principal parts appearing in `logSymbol_retained_split`.

The combined `reducedMain` first removes the horizontally separated modes
on the whole axis, then removes the small-band far modes from the remaining
divisor. These two sectors are disjoint. `logMain_reduced_bound` proves

```math
\|u^{N+1}(\operatorname{logMain}_N-
                 \operatorname{reducedMain}_N)\|
\le D_{W,y}(N+2)^3(9999/10000)^N.
```

`paidConstant` defines the explicit finite constant `D`. The theorem
`tendsto_reduced_sub_current` keeps source equivalence to the unchanged
literal packet, including every earlier paid error. This applies to any
fixed finite genuine divisor; it does not pass to the infinite zero set.

## Full Gamma completion payment

The Gamma completion is the exact term

```math
R(s)=\frac1s-\frac{\log\pi}{2}+\frac12\psi(s/2)
    =\frac12\psi(s/2+1)-\frac{\log\pi}{2}.
```

The already proved recurrence cancels the apparent reciprocal at zero.
`norm_deriv_zetaGlobalRegularCorrection_le` gives `|R'(s)|<=1` on
`Re(s)>0`, uniformly in height. Cauchy's radius `3/4` at `3/2+iy`
therefore controls both the marked Fourier difference and the nonconstant
moments of this actual correction. The original factorial rectangle has
marked order at least two when `N>=2`; no middle or least-prime order is
discarded.

`completionSymbol_small` couples this bound to the unchanged ordered
cofactor and retains two Fourier zeros. `completionSymbol_large` bounds
the same symbol at arbitrary frequencies. Their joint envelope is a
constant times `(N+2)^2*(9999/10000)^N/(1+xi^2)`.
`integrable_completionPair` proves actual integrability on the full axis,
including the origin and every exterior frequency.

Writing `B= couplingConstant` and `B_m= couplingMassConstant`,
`completionResponse_bound` proves

```math
\|u^{N+1}\operatorname{completionResponse}_N\|
\le\pi(B+B_m)(N+2)^3(9999/10000)^N.
```

This holds for `N>=2`, `0<=u<=10001/20000`, every finite prime set with
elements at least 16, and every `L>=1`. It is uniform in height and does
not use a hypothetical zero. `tendsto_completionResponse` permits the
height, length, radius and prime set to move with `N`. The constant is
explicit but large; this is an asymptotic saving, not a practical evaluated
starting order.

The exact identity `logSymbol_sub_completionSymbol` leaves the pole
minus the **full** xi logarithmic derivative, with all signs, cofactors
and rectangle orders intact. `logResponse_sub_completionResponse`
justifies the subtraction inside the integral using integrability of both
terms. `eventually_logMain_sub_completionResponse` discharges its support
premises for the original moving physical prime set.

`completionReducedMain` combines this subtraction with both previous
disjoint mode payments. Its explicit error bound is

```math
\|u^{N+1}(\operatorname{logMain}_N-
             \operatorname{completionReducedMain}_N)\|
\le [D_{W,y}+\pi(B+B_m)](N+2)^3(9999/10000)^N.
```

`tendsto_completionReduced_sub_current` preserves the exact original
`lowerThresholdPacket-shortOverflowPacket` source ledger and every
previously paid error. The Gamma correction is now paid globally; the
analytic xi remainder in a local principal-part expansion is a different
term and remains retained.

## Unshifted selected mode: exact saturation and paid transfer

Write the marked principal-part difference as

```math
\frac{(-z)^{-j}-(i\xi-z)^{-j}}j.
```

The first term is independent of frequency. After the exact finite
least-prime reindexing, its Fourier integral is the composite cofactor's
original signed Riesz hinge. For a squarefree composite `a`, that hinge
is zero when `log(a)<=L`. The ordinary-prime cofactor contributes zero
as well: its empty middle product cannot fill the actual complementary
factorial order. This uses the joined orders, not bare prime completion.

[ZetaRieszUnshiftedCofactor](../RiemannGaussian/ZetaRieszUnshiftedCofactor.lean)
keeps the precise least-prime rectangle and every allowed zero order.
The complementary total order satisfies `k=N+1-j<=19N/40+1`.
For `L>=11N/8` and `0<u<=10001/20000`, `complementary_rate` proves

```math
u^k(1024/255)^k e^{-L/4}\le3e^{-N/100}.
```

The existing divisor-square majorant therefore bounds the remaining
oversized-cofactor sum by

```math
\|u^{N+1}\operatorname{unshiftedResponse}_N\|
\le3\operatorname{divisorSquareDirichletMass}(1025/1024)
       (N+1)(N+2)e^{-N/100}.
```

This requires only `|z|>=u`, so it includes the selected mode `z=-u`.
Saturation is applied before taking norms; no Fourier absolute cost is
charged to its resonant marked factor.

[ZetaRieszUnshiftedCharacter](../RiemannGaussian/ZetaRieszUnshiftedCharacter.lean)
proves the exact label bijection, factorial identity, genuine integrability
and integral identification. The current carrier uses an Euler quotient,
so the finite character identity alone is insufficient.
[ZetaRieszUnshiftedEulerError](../RiemannGaussian/ZetaRieszUnshiftedEulerError.lean)
pays this precise difference. The full middle correction retains a
Fourier zero, and the least-prime leg supplies another. Their paired
profile is integrable on the entire axis. The exponential prime head
`log(p)>=N/110` supplies `exp(-N/220)`, which beats the complete
complementary source amplification and leaves `exp(-N/300)`.

`quotientResponse_eq` is an exact identity with that paid error.
`quotientResponse_single_rate` bounds the **actual unshifted Euler
quotient response** by

```math
\|u^{N+1}\operatorname{quotientResponse}_N\|
\le C(N+2)^3e^{-N/300}.
```

The constant `paymentConstant` is explicit, finite and independent of
height, the finite prime set and length. The hypotheses are `p>=16`,
`log(p)>=N/110`, `L>=max(1,11N/8)`, `0<u<=10001/20000` and `|z|>=u`.
The actual `roughPrimes` and moving Riesz length satisfy them eventually.
No numerical starting order is evaluated; the constant is large.

`tendsto_selected_unshifted` includes every fixed analytic multiplicity.
`selected_principal_split` checks the genuine zero coordinate and negative
residue sign. Accordingly `selectedReducedMain` adds back this paid
negative contribution. `tendsto_selectedReduced_sub_current` preserves
the unchanged literal `lowerThresholdPacket-shortOverflowPacket`, all
earlier paid errors and the original dyadic orders and prime counts.
Only the unshifted component is removed: the shifted denominator remains
coupled to the cofactor and is not bounded by this theorem.

## The entire unshifted logarithmic derivative

[ZetaRieszUnshiftedLogPayment](../RiemannGaussian/ZetaRieszUnshiftedLogPayment.lean)
uses the existing complete-moment bound at an exposed right-half zero.
For the actual marked coefficient

```math
M_j(s_0)=\frac{\operatorname{zetaPrimeLogMoment}_{j-1}(s_0)}{j},
\qquad s_0=\tfrac32+i\operatorname{Im}\rho,
```

`exists_normalized_mark_bound` proves `|u^j M_j(s0)|<=C_rho` for every
positive marked order. This is a bound on the complete scalar moment,
including all zeros, pole and regular terms. It is not a separate-leg
phase limit passed through a mask. The actual cofactor is then integrated
exactly, and composite saturation is applied before taking its norm.

`unshiftedResponse_eq` proves the exact finite-character-minus-Euler-error
identity with genuine integrability. The resulting bound is

```math
\left\|u^{N+1}\operatorname{unshiftedResponse}_N\right\|
\le C_\rho\,\operatorname{paymentConstant}\,(N+2)^3 e^{-N/300}.
```

`exists_exposed_unshifted_bound` discharges the moment budget, physical
rough-prime support and moving-length premises. `tendsto_exposed_unshifted`
pays the entire term. These theorems require the original exposure
hypothesis and `u<=10001/20000`; they impose no simplicity or global
rightmost-zero assumption. The constant and eventual starting order
depend on the zero and have not been numerically evaluated.

The exact split is `logResponse=unshiftedResponse-shiftedResponse`.
The negative shifted term retains the full logarithmic moment at
`s0+i*xi`, both Fourier phases, ordered cofactor, least-prime rectangle
and moving length. `tendsto_shifted_sub_current` proves its source
equivalence to the unchanged literal `lowerThresholdPacket-shortOverflowPacket`
along the original dyadic orders and prime counts. All previously paid
transfer errors are included. Earlier zero-sector and Gamma estimates
remain available; this theorem does not discard their remaining shifted
parts or count any of these payments as a positive reserve.

## The complete horizontal zero divisor

[`ZetaRieszGlobalHorizontal`](../RiemannGaussian/ZetaRieszGlobalHorizontal.lean)
extends the full-frequency payment from a chosen finite list to **every**
genuine zero with `Re(tau)<=999/1000`. It requires no exposure, simplicity
or rightmost-zero hypothesis. The height `y` is fixed; the constant below
may depend on it.

The decisive estimate retains the distance of the zero throughout the
coupled Fourier integral. With `z=tau-(3/2+i*y)`, Lean proves

\[
\left\|u^{N+1}\operatorname{Response}_N(z)\right\|
\le \frac{C\,(N+2)^3(9999/10000)^N}{|z|^2}.
\]

At small frequencies the inverse-node difference retains both its Fourier
zero and `1/|z|^2`. At large frequencies, the joint kernel is bounded by
`1/|z|^2` times three translated Cauchy kernels. Their full-line integral
is exactly `3*pi`, independent of the zero's ordinate. Thus shifted
resonances at large frequency are included, rather than excluded by a
finite frequency window. The rectangle itself forces marked order at
least two, supplying the summable inverse-square weight. No cofactor
order is discarded.

The existing global multiplicity-weighted inverse-square theorem gives

\[
M_y=\sum_{\tau}
 \frac{m_\tau}{|\tau-(3/2+iy)|^2}<\infty,
\qquad
\left\|u^{N+1}G_N\right\|
\le C M_y(N+2)^3(9999/10000)^N.
\]

`globalPair_L1`, `integrable_globalPair` and `hasSum_globalResponse`
justify summing inside the actual full-frequency integral. This is a
convergent **logarithmic-derivative series**, not an inverse of the global
infinite zero product. The Gamma-growth no-go for that inverse is unchanged.
`hasSum_xiDifference` and `logSymbol_split` identify this series as the
actual negative zero contribution. Both frequencies, all multiplicities,
the ordered least-prime cofactor and the finite rectangle remain exact.

The selected zero is outside this sector: `u<=10001/20000` implies
`Re(rho)>=19999/20000>999/1000`. No selected source is paid by this bound.

Combining the global sector with the **disjoint** Gamma payment gives
`poleEdgeMain`. The theorem `logMain_poleEdge_bound` proves, for `N>=2`,

\[
\left\|u^{N+1}
 (\operatorname{logMain}_N-\operatorname{poleEdgeMain}_N)\right\|
\le \bigl(C M_y+C_\Gamma\bigr)(N+2)^3(9999/10000)^N.
\]

`tendsto_poleEdge_sub_current` connects it to the unchanged literal
`lowerThresholdPacket-shortOverflowPacket` on the original dyadic orders
and count cutoffs, including all earlier paid transfer errors. The
remaining signed spectral expression is the zeta pole minus the full
right-edge zero sum, `Re(tau)>999/1000`. There is no separate unknown local
xi remainder in this global derivative decomposition. The older finite
horizontal payment is included in this global payment and must not be
charged a second time. The earlier exposed whole-unshifted theorem remains
available as a separate exact reduction.

Neither `M_y`, the other constants nor a numerical starting order is
estimated here. This is an asymptotic component payment, not a measured
percentage of the source removed and not an independent whole-sum bound.

## Shifted pole and right-edge exteriors

[`ZetaRieszShiftedExterior`](../RiemannGaussian/ZetaRieszShiftedExterior.lean)
pays a further part of the **remaining** expression. For a mode coordinate
`z=tau-(3/2+i*y)`, its exterior test is exactly

\[
|\xi|\ge\frac1{2000}
\quad\text{and}\quad
|\xi-\Im z|\ge\frac1{40}.
\]

The pole uses its genuine coordinate `z=1-(3/2+i*y)`. Both signed Fourier
frequencies are tested separately; the original phases remain. All genuine
zeros and the pole satisfy `Re(z)<=-1/2`. On the second exterior condition,

\[
|i\xi-z|^2\ge\frac14+\frac1{1600}
>\left(\frac{1001}{2000}\right)^2.
\]

Thus the already checked joint-order rate applies even to the right-edge
zeros. The inverse-square mode distance survives the frequency estimate,
and its global multiplicity-weighted sum is finite. `exteriorResponse_bound`
and `edgeExteriorResponse_bound` give `C_y*(N+2)^3*(9999/10000)^N` for the
pole and entire right-edge exterior. `hasSum_edgeExteriorResponse` and
`integrable_edgeExteriorPair` justify the global sum and actual integral.
The constants are explicit expressions but are not numerically evaluated.

The numerical rate audit motivated the rational choice. Using the weaker
marked fraction `1/2`, the leading envelope log-rate is approximately
`+0.00010381` at zero vertical separation and `-0.00052041` at separation
`1/40`. These floating values are diagnostics, not certificates. The Lean
proof uses the exact rational radius and existing `(9999/10000)^N` theorem.
No estimate for the central resonance is inferred from that test.

`poleEdgeSymbol_split` checks the exact signed subtraction inside the
original rectangle and cofactor. `resonantMain` adds the pole exterior and
subtracts the right-edge-zero exterior with their genuine signs.
`logMain_resonant_bound` combines four disjoint payments: the old horizontal
zero sector, Gamma correction, shifted pole exterior, and shifted right-edge
exterior. Its total cost still tends geometrically to zero. The theorem
`tendsto_resonant_sub_current` preserves the unchanged literal packet and
every previous transfer error.

Only the **shifted parts** of the retained modal terms are confined to

\[
|\xi|<\frac1{2000}
\quad\text{or}\quad
|\xi-\Im z|<\frac1{40}.
\]

`retained_shift_support` proves this statement, and
`exteriorSymbol_zero_of_resonance` verifies that no such term is charged to
the norm payment. The algebraic ledger still includes the unshifted
pole/right-edge terms; the earlier complete-unshifted theorem under
exposure remains a separate available reduction. Do not describe the
entire retained integrand as supported only on these intervals. The
selected resonance, correlations within these intervals and both
independent whole-sum inequalities remain open. This is neither a zero
exclusion nor a numerical fraction of the needed margin recovered.

## What this does not pay

The general [moving-mode lemma](zeta-exposed-moving-modes.md) permits every
strict exposed gap, provided the moving coefficients have a polynomial
budget. The literal cofactor has not been shown to satisfy that budget.
The mode-sector estimates pay their concrete sectors without assuming it.
The complete unshifted payment instead uses exact composite saturation;
it does not establish that missing budget for the shifted expression.

A diagnostic rate calculation explains the distinction: retaining the
sharper marked fraction `21/40` gives the envelope exponent
`log(U/a)+(21/40)*log(a/R_eff)`. Its numerical break-even effective radius
is approximately `0.5000986945`, above `U`. This diagnostic is not a Lean
zero-location theorem or a counterexample to cancellation in the actual
cofactor. The proof above uses only the exact rational rate check.

Across the full genuine divisor, only zeros with `Re(tau)>999/1000`
remain unpaid. Their previously paid local small-band sectors remain
available, but the pole and the right-edge zero response still need a
joint signed estimate. The selected resonance remains in this expression.
Under exposure, the whole unshifted logarithmic-derivative component is
now paid. The selected shifted resonance and the other retained central/resonant
channels remain coupled and signed after the new exterior payment. Neither the cofinal floor `-79/1000-o(1)` nor
ceiling `3/2+o(1)` is proved. No RH or zero-free-region claim follows.

## Supporting sharp-share estimate

[ZetaRieszSharpShifted](../RiemannGaussian/ZetaRieszSharpShifted.lean)
uses the exact marked-order constraint `21N<=40j` to pay an additional
separated shifted sector. Its rational `sharp_rate_check` gives the
denominator radius `5001/10000` and geometric rate `999999/1000000`;
`half_order_rate_gt_one` verifies that the older half-order envelope grows
at that radius. These statements concern the coupled estimates, not a new
zero-free region.

`joint_sharp_bounds` retains an arbitrary unchanged signed complement on
both sides of the comparison. `logMain_sharp_bound` and
`tendsto_sharp_sub_current` keep the literal packet source and all earlier
payments. The remaining central/resonant contribution is not bounded by
these theorems. This module is included in the ordinary root and its
terminal axioms are recorded in the existing audit; the public endpoint
and both open whole-sum inequalities remain unchanged.
