# Arithmetic supply for exact cycles of the whole carrier

Lean now gives the full original carrier a specified arithmetic upper
bound: its absolute mass minus an accumulated budget of exact-cycle
savings. Each budget follows from local cofactor estimates, the actual
complex directions, and each vertex's remaining capacity. No unproved
aggregate cancellation assumption enters this finite bound.

It applies to **every complex polynomial filter**, all original moment
orders and ordinates. Prime and composite shared cofactors are included,
and the central atom may belong to a different prime-count class from
its two partners. The full pole-jet source is preserved without exposure
or simplicity.

**Sufficient aggregate saving at source scale remains open. No new
zero-free region or RH proof follows yet.**

## Retain the exact target profile

For the signed Riesz divisor profile R, define

```math
F_{L,n}(x)=R_L(n)-R_{L-x}(n).
```

At an inserted prime q not dividing n, this equals R_L(qn) when x=log q.
An ideal opposite phase or the midpoint of two flanking prime logarithms
can be used as the exact real target. The error estimate then charges
only the small target-to-prime gap, retaining the signed change across
the half-turn itself.

For each nonunit squarefree cofactor, the proved error is

```math
|R_L(qn)-F_{L,n}(x)|\le E_n(x,q),\qquad
E_n(x,q)=|\log q-x|\,M(n)
\begin{cases}
1/2,&n\text{ prime},\\
1/4,&n\text{ composite},
\end{cases}
```

where M(n) is the sum of absolute Mobius divisor weights. The prime case
uses the existing centered half-slope estimate; the composite case uses
the coupled two-prime tent. All hypotheses are discharged from the actual
cofactor tests in the final bound.

Consequently an actual partner's full-filter norm is at least

```math
|A_{L,P,N,t}(qn)|\,
\max\!\left(0,|F_{L,n}(x)|-E_n(x,q)\right).
```

Here A is the exact non-Riesz amplitude, including the original support
mask, normalization and complete polynomial kernel. This does not replace
the filter by one or discard its complex direction.

## Keep three separate capacities

Every earlier exact cycle leaves an original atom multiplied by a proved
scalar eta in [0,1]. `cycleResidual_eq_retainedFraction` retains this exact
identity, even for repeatedly used vertices.

For three unit rays z,w,v with positive oriented areas
alpha=[w,v], beta=[v,z], gamma=[z,w], separately proved lower masses a,b,c
supply the cycle parameter

```math
\lambda=\min(a/\alpha,b/\beta,c/\gamma).
```

`cycleSaving_ge_rayCapacity` proves a saving of at least
lambda(alpha+beta+gamma). Each lower mass is multiplied by its own actual
remaining fraction. Neither the three sine capacities nor their remaining
fractions are collapsed to one common minimum.

`full_cycle_after_previous_ge_cofactor_target` puts the actual partner
floors into this estimate, retaining all full-polynomial rays. The central
atom is unrestricted. Earlier unfiltered sign and sine identities remain
available as more explicit ways to verify the complex orientation; they
are not imposed on the general full-filter theorem.

## A fully defined whole-carrier budget

For an original triple (i,j,k), the partner gcd g=gcd(j,k) determines its
literal quotients q=j/g and r=k/g. `partnerArithmeticTest` checks that q,r
are prime, neither divides g, and g is nonunit and squarefree. The target
is the midpoint of log q and log r. The original complex area test retains
the complete polynomial phases and arithmetic signs.

`arithmeticCycleBudget` uses these actual data and all previous retained
fractions. Failed tests earn zero claimed saving. Every original term
remains accounted for. `arithmeticCycleBudget_le_saving` proves the local
budget unconditionally, and `arithmeticSavings_le_totalSaving` accumulates
it along the actual processed list without spending mass twice.

The canonical `availableArithmeticCycles` tests every original triple
and processes only those whose proved initial arithmetic budget is
strictly positive. This prevents an uncredited geometric step from
consuming a later partner's supply. It does **not** prove that enough
eligible triples exist or that their total budget is sufficient.

The whole-bound endpoint is
[`norm_actual_band_le_available_arithmetic_cycles`](../RiemannGaussian/ZetaRieszArithmeticCycles.lean):

```math
|\mathcal B_{L,P,N}(t)|\le
\sum_{n\in\mathcal B_N}|B_{L,P,N,t}(n)|-
\operatorname{arithmeticSavings}_{L,P,N,t}.
```

Variants cover every supported finite cycle list and original support
slice. They assume only checked finite membership for that list, not a
cancellation estimate. All inactive and unselected terms stay in the
upper allowance.

The terminal `tendsto_available_arithmetic_cycle_source` preserves

```math
u^{N+1}\sum_n B_N^{\mathrm{remaining}}(n)\longrightarrow-m(\rho),
\qquad u=\frac32-\Re\rho,
```

for the full pole-jet filter at every hypothetical right-half zero.
The arithmetic bound and the source now refer to the same complete
carrier. An independent cofinal upper allowance strictly below the source
would suffice for a contradiction; decay to zero is a stronger target
than necessary. Neither sufficient bound is proved here.

## Scope of the evidence

The eight arithmetic modules are imported by the ordinary root and use
only the permitted standard axioms. Default RH, zero-free and numerical
certificate endpoints and both top-ten lists remain unchanged.

Small floating-point tests evaluate selected greedy lists for P=1 in the
physical annulus, with their cutoffs tied to the moment order. These are
exploration only, not full original-band certificates or an asymptotic
rate. Orders below an unevaluated source-error threshold cannot establish
a zero contradiction merely because an allowance is below one. The tests
do not run in ordinary CI. No historical novelty claim is made for the
underlying geometric or trigonometric identities.
