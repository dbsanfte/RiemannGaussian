# Reproducing the published zero-free regions

The user reaffirmed the order on 23 September 2026: **formalize the published
arguments and reproduce their actual regions first; improve them afterwards.**
Comparing width functions, proving the same asymptotic shape with a weaker
constant, and proving conditional transport do not complete a reproduction.
The full objective remains the union of the literature frameworks, followed
by an improvement over that frontier.

The immediate VK source is
[Bellotti, arXiv:2306.10680v1](https://arxiv.org/html/2306.10680v1), with
[Ford, arXiv:1910.08209v1](https://arxiv.org/pdf/1910.08209) supplying the
detailed mixed-system argument. Keep the v1 targets distinct from later
reported constants in the [literature audit](zero-free-literature-frontier.md).

| Published milestone | Reproduction obligation | Local status |
| --- | --- | --- |
| Bellotti 2.1 / Ford 3.2' | Conditioning with an actual short prime packet | General packet bound proved; required packet existence remains open |
| Bellotti 2.2 / Ford 3.3' | Differencing into the next literal mixed count | Proved for integer endpoints, including the diagonal case |
| Bellotti 2.4 / Ford 3.4 | Original mixed iteration with its stated coefficients and thresholds | Original coefficient, defect and starting height proved with constructed scales and integer cutoffs under Ford's stationary-scale criterion; only the dense prime supply remains an arithmetic input at this step |
| Ford 3.5 | Repeated original iteration from the diagonal moment at every positive endpoint | Proved with the published coefficient recurrence; the concrete rank and maximal depth are now constructed, leaving short-prime supply as the arithmetic premise |
| Ford 3.6 | Quantitative original iteration for `k>=1000` | Closed defect bound proved with the original `1.69/k` constant and full upper order range; the `W=k^(4.11*k)` height bound and early coefficient-step estimates are proved; the closed coefficient product remains open |
| Bellotti 2.3 and 2.5 | Sharper scales and repeated moment-order iteration | Sharper scale normalization under audit; full quantitative iteration open |
| Bellotti 1.4 and 2.8 | Complete and smooth incomplete moment estimates | Published numerical bounds open |
| Bellotti 1.5 | Block coefficient `8.7979`, exponent denominator `132.94357` | Open |
| Bellotti 1.1 | Zeta growth with `A=70.6995`, `B=4.43795` | Open |
| Bellotti 1.2 and 1.3 | VK denominators `54.004` for `|t|>=3`, `48.0718` eventually | Open |

## The literal mixed-system interface

[`VinogradovLiteratureStep`](../RiemannGaussian/VinogradovLiteratureStep.lean)
puts the existing differencing result into the form needed for iteration.
Writing `a=k-d` for the active tuple order, its unconditional
`exists_difference_step` proves

```math
L_{s,d}(P,Q)\le(2P)^a\max\left\{
k^aJ_{s,k}(Q),\;
2p^{-ra}J_{s,k}(Q)^{(a-2)/(2(a-1))}
K_{s,d+1}(P,Q;pq)^{a/(2(a-1))}
\right\}.
```

The next system is attained, has the proved type parameter
`T<=T'<=P*T`, and retains every original tail equation. No moment bound
is assumed. `next_moment_eq_count` proves this is the actual next `K`;
`stepEquiv` moves the constant polynomial coordinate into the inactive
block while preserving its tail coordinate. The case `P<p^r` is handled
by the exact diagonal identity.

`exists_mixed_step_of_packet` composes this with unrestricted conditioning.
It retains `floor(Q/p)`, dilation `p*q`, prime regularity, the chosen
packet's cardinality and endpoint, and both numerical branches. Its
explicit hypotheses include `P>=4a^4` and `16s^2 U<=Q`. Those endpoint
conditions must be discharged at every stage of the literature iteration;
this theorem does not assert all of Bellotti 2.1's continuous-parameter
scope. `literature_packet_budget` removes the discriminant-product premise
for a supplied packet of `k^3` primes above `M`, when `P<=M^(k+1)`.
`literature_packet_budget_real` now proves the same implication for real
`M>=1`, including the exact root endpoint; it does not round `M` down
before taking that power.
It does **not** prove that such a packet lies below `(1+omega)M`.

## Finite backward iteration and the sharper scale audit

[`VinogradovResidueMonotone`](../RiemannGaussian/VinogradovResidueMonotone.lean)
proves monotonicity of the original residue mixed moment in its tail
endpoint. It decomposes that integral into complete mixed counts on the
original residue fibres and injects the smaller tail into the larger one.
There is no pointwise comparison of oscillating sums and no multiplicative
loss. `quotient_floor_le` also proves `floor(X)/p<=floor(X/M)` for
`X>=0` and `p>=M>0`.

[`VinogradovLiteratureIteration`](../RiemannGaussian/VinogradovLiteratureIteration.lean)
retains the sharper conditioning coefficient already proved upstream:

```math
4|\mathcal P|d!(k-d)!p^{e_d},\qquad
e_d=2s-d+\frac{(r-d)(r-d-1)}2.
```

`backward_step_of_packet` proves the actual `L -> K -> L` inequality,
including the changed type parameter and quotient endpoint.
`iterated_residue_bound` performs the finite backward induction from the
exact diagonal case. `iterated_moment_bound` starts that induction at the
literal homogeneous moment `J_(s+k),k(P)`. Its numerical result is the
explicit `backwardAllowance` recursion in source moment bounds `J_s,k(Q)`;
no intermediate mixed-count estimate is supplied as a premise. Actual
finite prime packets, all size conditions and source moment bounds remain
explicit hypotheses. This does not yet reproduce the published constants.

The scale substitution needs a further argument. For the current
normalization `L_d <= E_d*C*P^(k-d)*Q^lambda`, put
`lambda=2s-k(k+1)/2+Delta`. Substituting Bellotti 2.3's displayed scale
recurrence gives the exact identity, proved by `published_scale_balance`:

```math
\frac12-r\phi_d+
 \frac{e_d-\lambda}{2(k-d)}\phi_{d+1}
 =\frac{d(d-1)}{4(k-d)}\phi_{d+1}.
```

`published_scale_residual_pos` proves this residual positive for `d>=2`,
`d<k`, and `phi_(d+1)>0`. It vanishes at the first depth. This is an audit
of **our present conditioning estimate and normalization**, not a
disproof of the published final bound. Do not drop the triangular term,
weaken a constant and call it reproduction, or infer that the one-step
lemma alone supplies the published recurrence. The sharper recurrence
remains open. The original recurrence, which retains the triangular depth
term, now gives a separate verified way forward.

## Original Ford scales: actual moment bound proved

[`VinogradovFordScales.scale_balance`](../RiemannGaussian/VinogradovFordScales.lean)
uses the original Ford 3.4 / Bellotti 2.4 recurrence, with local index
`phi d` corresponding to the paper's `phi_(d+1)`. At the next depth `d`,
write `psi=phi d` and

```math
\Phi=\frac1{2r}+
 \frac{k^2+k+r^2-r+d^2-d-2\Delta}{4kr}\psi.
```

The exact normalized exponent remainder is

```math
\frac12-r\Phi+\frac{e_d-\lambda}{2(k-d)}\psi
 =\frac{d\,[d(d-1)+(k-r)(k-r+1)-2\Delta]\psi}{4k(k-d)}.
```

`scale_balance_nonpos` proves it nonpositive under the published depth
restriction. Thus the original recurrence pays the shrinking-tuple
estimate, without deleting the triangular term. `previousScale_pos` and
`previousScale_le` prove positivity and the upper bound `1/r` under their
displayed defect and depth hypotheses.

[`VinogradovPowerConditioning.typeCount_le_of_power_bound`](../RiemannGaussian/VinogradovPowerConditioning.lean)
retains the chosen prime together with its literal quotient endpoint:

```math
p^{e_d}\lfloor Q/p\rfloor^\lambda
 \le p^{e_d-\lambda}Q^\lambda
 \le U^{e_d-\lambda}Q^\lambda
 \qquad(0\le\lambda\le e_d).
```

For a packet with `U<=eta*P^psi`, its width therefore pays `eta^(e_d-lambda)`.
The next mixed bound is uniform in the actual integer tail endpoint;
the quotient is not enlarged before this cancellation.

[`VinogradovFordStep.backward_power_step`](../RiemannGaussian/VinogradovFordStep.lean)
combines these facts with actual differencing and conditioning.
[`VinogradovFordIteration.residue_power_bound`](../RiemannGaussian/VinogradovFordIteration.lean)
performs the entire backward induction from the proved diagonal case.
`moment_power_bound` then starts at the literal homogeneous moment and proves

```math
J_{s+k,k}(P)\le
 C\,\bigl[4k^3k!\,B_{0,n}\,\eta^{e_0-\lambda}\bigr]
 P^{2(s+k)-k(k+1)/2+\Delta'},
\qquad
\Delta'=\Delta(1-\phi_0)-k+
 \frac{\phi_0}{2}(k^2+k+r^2-r).
```

Here `b+n=k`, and `B` is the explicit `coefficient` recursion with terminal
value one. It depends on neither physical endpoint `P,Q`. Both the
diagonal and off-diagonal branches, the factorials and the packet width
are retained. The theorem assumes the ordinary source bound
`J_s,k(X)<=C*X^lambda` for every positive integer endpoint, actual finite
prime packets, admissible scales, and the explicit recursive minimum
tail conditions. It assumes no intermediate mixed-count estimate.

## Published coefficient and quotient-size conditions proved

[`VinogradovFordCoefficient.source_exponent_ge`](../RiemannGaussian/VinogradovFordCoefficient.lean)
derives `lambda>=s` from the actual source moment bound: the literal
moment contains all `X^s` diagonal tuples, so a global upper power with
smaller exponent would contradict growth along integer endpoints. This
reserve is proved from the existing source premise, not added as an
independent hypothesis.

`full_coefficient_bound` now proves the exact requested numerical bound

```math
4k^3k!\,B_{0,n}\,\eta^{e_0-\lambda}
 \le k^{3k}\eta^{4s+k^2}.
```

The proof keeps both branches of the coefficient recursion. An elementary
factorial induction gives `1024*k!<=k^(k-3)` for `k>=26`, hence
`256*(4*k^3*d!*(k-d)!)<=k^k`. The intermediate supersolution is

```math
B_{d,n}\le k^{2k}\eta^{H_d},\qquad
H_d=2s+\frac{k^2-k+d^2-d}{2}+2.
```

Its shrinking Holder exponent is paid by `lambda>=s`; its binary and
factorial factors fit `k^(2k)`. The required terminal active dimension
`b>=3` follows from the original `j<=9r/10`, `r<=k`, `k>=26` restrictions.
[`VinogradovFordMoment.published_moment_bound`](../RiemannGaussian/VinogradovFordMoment.lean)
applies this bound to the actual homogeneous moment. It has no assumed
intermediate mixed estimate or numerical coefficient bound.

[`VinogradovFordTailThreshold.published_height_bound`](../RiemannGaussian/VinogradovFordTailThreshold.lean)
also removes the separate minimum-tail and repeated-tuple size hypotheses
using exactly the paper's base and starting height:

```math
V=\max\left\{e^{3/2+3/(2\omega)},
 \frac{18}{\omega}k^3\log k\right\},\qquad P\ge V^{k+1}.
```

The recursive tail threshold costs only one factor `16*s^2`, followed by
the product of the packet endpoints. With `j=n+1<=9r/10`, `phi_i<=1/r`
and `U_i<=eta*P^phi_i`, their product is at most
`eta^j*P^(j/r)`. Lean proves `V>=64*k^3` and
`16*s^2*eta^j<=P^(1/10)` for `s<=k^3` and `eta<=3/2`. The key finite
inequality is `eta^10<=64`; no width-two replacement is made. Thus the
whole product is at most `P`, paying all literal integer quotient sizes.

The resulting actual-moment theorem has the exact coefficient
`k^(3k)*eta^(4s+k^2)`, the original updated defect and `P>=V^(k+1)`.
The following construction now discharges its scale/type conditions in
the repeated iteration's stationary-scale range.

## Constructed scales, integer cutoffs and all-endpoint iteration

[`VinogradovFordSchedule.schedule_bounds`](../RiemannGaussian/VinogradovFordSchedule.lean)
constructs the finite backward schedule, ending at `1/r`. Put

```math
y=2\Delta-(k-r)(k-r+1),\qquad
\phi^*=\frac{2k}{2rk+y}.
```

With terminal depth `n`, the original depth condition `n(n-1)<=y`,
`Delta<=k*(k-1)/2` and Ford 3.5's scalar criterion
`phi^*>=1/(k+1)` imply, at every depth,

```math
0<\phi_d,\qquad \frac1{k+1}\le\phi^*\le\phi_d\le\frac1r.
```

The construction proves the literal recurrence and terminal value. This
uses the stationary sufficient criterion from Lemma 3.5; it does not assert
that criterion is necessary for every admissible scale in Lemma 3.4.

[`VinogradovFordParameters.moment_bound_of_packets`](../RiemannGaussian/VinogradovFordParameters.lean)
takes `M_d=floor(P^phi_d)` and `U_d=floor(eta*P^phi_d)`.
At the original starting height, every real prime scale is at least `V`.
The supplied `k^3` primes in `(P^phi_d,eta*P^phi_d]` then pay the degree
lower bound and complete discriminant-product budget, including the unused
dimensions zero and one. Root comparisons use the real scale before
rounding. The strict next-integer inequality proves the terminal condition
`P<(M_n+1)^r` even when the real root is an integer. No independent scale,
product-budget, degree, diagonal or quotient-size assumption survives in
this theorem.

[`VinogradovFordGlobalStep.ShortPrimeSupply`](../RiemannGaussian/VinogradovFordGlobalStep.lean)
states the remaining arithmetic input literally: every real `M>=V`
admits a finite set of exactly `k^3` primes in `(M,eta*M]`. It is an
**unproved proposition supplied as a hypothesis**, not an axiom or a
replacement moment estimate.

`all_endpoint_bound` covers every positive integer endpoint. The small
endpoint uses the proved comparison `J_(s+k),k(P)<=P^(2k)*J_s,k(P)`.
The exact identity

```math
\Delta-\Delta'=k(1-r\phi_0)+\frac{\phi_0 y}{2}\ge0
```

pays its exponent by the same published threshold. Thus the next moment
coefficient is precisely

```math
C'=C\max\left\{k^{3k}\eta^{4s+k^2},
 V^{(k+1)(\Delta-\Delta')}\right\}.
```

[`VinogradovFordMomentSequence.iterated_moment_bound`](../RiemannGaussian/VinogradovFordMomentSequence.lean)
then starts at the proved diagonal bound `J_k,k(P)<=k!*P^k` and iterates
this formula. After `J` steps, for `J+1<=k^2`, it bounds the actual moment
of order `(J+1)k` at **every** positive integer endpoint. Its coefficient
and defect are explicit finite recurrences. The initial defect range is
preserved by proof, and no source or intermediate moment bound remains a
premise. This general theorem retains the short-prime supply and the
displayed scalar restrictions on arbitrary rank/depth schedules. The
published selection below now discharges those scalar restrictions.

## Published rank selection and quantitative defect decrease

[`VinogradovFordRank`](../RiemannGaussian/VinogradovFordRank.lean)
constructs the paper's rank and largest permitted depth:

```math
r=\left\lfloor k-\frac{\Delta}{k}+1\right\rfloor,\qquad
n=\max\left\{d:\ 10(d+1)\le9r,\ d(d-1)\le y\right\}.
```

Here the local depth `n` is the paper's `j-1`. For
`k<=Delta<=k(k-1)/2`, `admissible` proves every scalar condition of the
actual moment step, including `4<=r<=k`, a nonempty depth set and
`phi^*>=1/(k+1)`. The reserve satisfies `y>=2k-2`; no depth or stationary
condition is supplied as an extra hypothesis. `admissible_to_boundary`
also covers `k-1<=Delta<=k`, where the rounded rank is exactly `k`.

[`VinogradovFordSelectedIteration.selected_moment_bound`](../RiemannGaussian/VinogradovFordSelectedIteration.lean)
uses these choices in the actual all-endpoint moment sequence, starting
from the diagonal count. It uses the original recurrence while `Delta>k-1`.
The final rank-`k` step from `k-1<Delta<=k` lands at `Delta'<=k-1`.
It then keeps that defect and raises the moment order by the proved trivial
comparison, with no further coefficient loss. Stopping at `Delta<=k`
would be premature for the top of the paper's stated order range, where
the requested closed bound can be below `k`. Short-prime supply remains
explicit; no scalar admissibility
hypothesis remains in this selected moment theorem.

[`VinogradovFordScaleError`](../RiemannGaussian/VinogradovFordScaleError.lean)
proves the half-contraction in (3.12) and sums every triangular forcing
term with a finite quadratic supersolution. The actual first scale obeys

```math
\phi_0-\phi^*\le \frac{2^{-n}}r+\frac{2\phi^*}{kr}.
```

[`VinogradovFordQuantitativeScale`](../RiemannGaussian/VinogradovFordQuantitativeScale.lean)
then proves the paper's numerical error budget for **every** `k>=1000`,
through an integer square-root depth candidate and exact polynomial
induction:

```math
2^{-n}\le\frac{0.071}{k^4},\qquad
\phi^*\le\frac8{7k}-\frac{0.16}{k^3},\qquad
\phi_0-\phi^*\le\frac{16}{7k^2r}.
```

[`VinogradovFordDefectRate.selectedDefect_rate`](../RiemannGaussian/VinogradovFordDefectRate.lean)
applies this to the literal selected sequence. With
`d=Delta/k^2` and `d'=Delta'/k^2`, it proves Ford's exact (3.14):

```math
d'\le d\left[1-\frac{2-d}{2-d^2}
 \left(\frac2k-\frac{32}{21k^2}-\frac{16}{7dk^3}\right)\right].
```

The proof retains the rank-rounding information in (3.16). A quadratic
denominator interpolation proves the upper bound in (3.17) from its two
endpoints; their exact margins have numerators
`d^2*((2-d^2)*k-1)` and `d*(2+d)`. No calculus or unexplained numerical
optimization is assumed.

[`VinogradovFordLowerDefect`](../RiemannGaussian/VinogradovFordLowerDefect.lean)
proves strict positivity and the lower recurrence
`Delta_(j+1)>=Delta_j*(1-2/k)`, including boundary and stopped steps.
Thus the logarithms used below are well-defined on the actual selected
sequence, rather than on an assumed positive comparison sequence.

[`VinogradovFordPotential`](../RiemannGaussian/VinogradovFordPotential.lean)
retains the signed cubic logarithm remainder. For the actual comparison
step it proves the potential decrease `-b-(2/5)b^2`; the quadratic gain
recovers the full `2/k` rate. Then
[`VinogradovFordPotentialIteration.potential_cumulative`](../RiemannGaussian/VinogradovFordPotentialIteration.lean)
pays the complete reciprocal-defect sum and gives

```math
H(d_J)\le H(d_0)-\frac{2J}{k}+\frac{67}{50k},\qquad
H(d)=d+\log d+\log(2-d),\qquad d_j=\frac{\Delta_j}{k^2}.
```

This holds for `k>=1000` while every preceding `Delta_i>k`.
`active_prefix` derives that condition whenever the endpoint satisfies
`Delta_J>k-1`. The error allowance is the paper's exact `1.34/k`;
none of these scalar estimates assumes short-prime supply.

## Closed defect and early coefficient costs

[`VinogradovFordClosedDefect.selected_defect_bound`](../RiemannGaussian/VinogradovFordClosedDefect.lean)
now proves the closed defect estimate, writing the paper's index as `n=J+1`:

```math
\Delta_J\le\frac38 k^2\exp\!\left(\frac12-\frac{2(J+1)}k+\frac{169}{100k}\right),
\qquad k\ge1000,\quad
J+1\le\frac{k}{2}\left(\frac12+\log\frac{3k}{8}\right)+1.
```

The initial potential retains `7/(6k)` of reserve; the terminal potential
retains `49/(100k)`. The final rank-`k` step pays the stopped case at the
full upper order ceiling. `paper_order_le` derives the natural iteration
cap from that ceiling, so no extra cap is assumed.
`selected_moment_closed_defect` inserts this allowance into the actual
homogeneous moment at every positive integer endpoint. It still requires
`ShortPrimeSupply` and retains the recursive coefficient. The scalar defect
estimate itself has no prime-supply premise.

For the paper's `omega=3/50`,
[`VinogradovFordCoefficientScale.published_height_le`](../RiemannGaussian/VinogradovFordCoefficientScale.lean)
proves `V^(k+1)<=W=k^(4.11*k)` for every `k>=1000`, including both branches
of the original base `V`. Its logarithmic and exponential constants are
proved from exact rational Taylor estimates. On `j+1<=1.97*k`,
[`VinogradovFordEarlyDefect.early_defect_drop`](../RiemannGaussian/VinogradovFordEarlyDefect.lean)
proves `Delta_j-Delta_(j+1)>=0.01916*k`. It retains the defect-dependent
rate ratio instead of discarding it for a uniform contraction factor.

[`VinogradovFordCoefficientStep.early_packet_lt_scale`](../RiemannGaussian/VinogradovFordCoefficientStep.lean)
then proves the paper's strict early comparison (3.20): the literal packet
cost is less than `W^(Delta_j-Delta_(j+1))`. `early_step_le` pays the entire
original maximum in this range, while `step_le_product` retains both
factors at all later steps. None of these coefficient estimates assumes
prime supply or an independent moment bound.

The coefficient product still needs to be telescoped and bounded with
the original `2.055`, `5.91` and `9.7278` constants. The full coefficient
bound, short-prime supply and subsequent zeta/VK transport remain open;
this is not yet all of Lemma 3.6 or a new zero-free region.

The required dense prime-packet estimate must also be proved. The existing
`(M,8M]` packet cannot silently replace the paper's narrower interval while
retaining its constants.
Ford's Lemma 2.1 obtains that packet from explicit Rosser–Schoenfeld
prime-counting estimates; Bertrand's postulate alone does not provide it.
The precise source input to reproduce is, for real `x>67`,

```math
\frac{x}{\log x-1/2}<\pi(x)<
\frac{x}{\log x}\left(1+\frac{3}{2\log x}\right).
```

Its short-interval consequence gives `N` primes when
`N/log(N)>=6/omega`, `x>=exp(3/2+3/(2*omega))` and
`x>=(6/omega)*N*log(N)`. Substituting `N=k^3` yields precisely the two
terms in `V`; the paper also restricts `omega>=1/(3*log(k))`.
The quantitative prime-count bounds themselves are not present in the
current imported chain. Proving only a conditional implication from them
must not be reported as proving `ShortPrimeSupply`.
The full-width conditional transport is now compiled in
[`VinogradovRosserPrimeSupply`](../RiemannGaussian/VinogradovRosserPrimeSupply.lean).
The actual anchor, three J-comparisons, exact source zero-free input and
last scalar error comparison are also proved. The detailed
[Rosser–Schoenfeld dependency audit](rosser-schoenfeld-reproduction.md)
records the remaining theta/psi and low-zero verification obligations.
The new arbitrary-order Euler–Maclaurin evaluator has a checked uniform
error below 10^(-12) through height 22000 on the right half-strip, excluding
the pole. This is an evaluation bound, not a low-zero certificate.
This is now the principal external arithmetic input left at the original
mixed-iteration stage. The sharper Bellotti 2.3 scale audit, closed
numerical complete/incomplete moments, and block/zero-detector
transport remain open. No published zeta-region benchmark is reproduced by
the conditional moment sequence alone.

The two wrapped-Gaussian modules developed before this reorientation are
retained as checked auxiliary estimates. Their further optimization and
transport are deferred until the published benchmark chain is reproduced.
They do not change the stated VK region or any RH arithmetic floor.
