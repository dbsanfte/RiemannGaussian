# General tilts now bound the actual composite-cofactor class

[Explore the arithmetic bound and retained source](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=general-tilt-decay).

The exact scalar optimizer now has an arithmetic application. Lean proves
its required spatial estimate, pays the complete cofactor cost, and bounds
the original filtered contribution in an explicitly growing cofactor range.
The earlier restriction `2/3<u<1` is replaced by `1/2<u<1`, except for one
scalar contact covered by the previous polynomial decay theorem.
**The joint signed floor for the surviving tail remains open.**

## The controlled quantity

Keep the [original carrier definitions](zeta-riesz-signed-fourier-tail.md#the-exact-target):
`u=3/2-Re(rho)`, the damped cutoff `D_N`, physical length `L_N`, signed
coefficient `C_L`, original band, and complete fixed factorial filter `K`.
The following component estimate itself uses no hypothetical-zero assumption.

For any fixed `0<u<=1`, tilt `q>1/2`, and complex polynomial `P`, put

```text
alpha = q-1/2,
S_q(P) = sum_j |P_j| q^(-j),
r(u,q) = exp((2-2q) log u)/q,
C(P,u,q) = 2(1+1/log 4) S_q(P) (1+1/alpha) 3^(2alpha) u.
```

When `r(u,q)<1`, choose the literal integer schedule

```text
g(u,q) = exp(-log(r(u,q))/(2(q+5/2))),
A_N = min(floor(g(u,q)^N), D_N+1).
```

Let `T_N` consist of the original band labels admitting `n=p*a`, with `p`
prime, `p` not dividing `a`, and `a` squarefree, nonunit, composite and
at most `A_N`. Each label is counted once, regardless of how many eligible
factorizations it has. At **every order**, Lean proves

```text
|u^(N+1) sum_(n in T_N) C_(L_N)(n) K_(P,N,y)(n)|
  <= C(P,u,q) sqrt(r(u,q)^N).
```

The allowance tends geometrically to zero, uniformly in height `y` for
fixed `P,u,q`. Every factorial shift keeps the base order's band and cutoff.
The fixed multiplicative constant is explicit; no numerical threshold or
uniform constant as `u` approaches an endpoint is asserted.

## Why this is an arithmetic bound

Discrete concavity and telescoping prove the real-power prefix estimate

```text
sum_(n=1..X) n^(alpha-1) <= (1+1/alpha) X^alpha,  alpha>0.
```

The general factorial tilt bounds the full kernel by
`q^(-N) S_q(P) n^(q-3/2)`. Apply the prefix estimate on the compact
range `n<=A_N(D_N+2)^2`, with the actual coefficient cost
`2 A_N log(A_N)(1+log(A_N)/log 4)`. Normalization leaves precisely
`r(u,q)^N`. The complete range cost is bounded by a constant times
`A_N^(q+5/2)`; the schedule pays that cost and leaves the displayed
square-root geometric saving.

All rounding and cutoff inclusions are proved. Complete composite-cofactor
mass and logarithmic-moment cancellation make the contribution outside
that compact range **exactly zero**. The estimate therefore covers the
whole selected original-band class, not a truncated part with an unpaid
boundary. For `0<u<1`, the schedule eventually exceeds `N^k` for each fixed
natural `k`, even after taking the minimum with the damped physical cutoff.

## The analytic choice and its limits

For every actual source scale `1/2<u<1`, the already proved unique scalar
optimizer is admissible:

```text
q_opt(u) = 1/(-2 log u) > 1/2,
r_min(u) = (-2 log u) exp(1+2 log u).
```

The minimum is strictly below one exactly when `u!=exp(-1/2)`. Substitution
in the new arithmetic bound pays a cofactor range beyond every fixed
polynomial at each such scale. At the exceptional contact, the earlier
universal eighth-root schedule still gives independent decay. This is a
contact of the bounding envelope, with no conclusion about zeta zeros.
The optimizer minimizes the scalar rate; it does **not** claim to maximize
the cofactor range after all constants and costs are included.

The optimized class and its literal complement partition the original
signed carrier at every order. Under each hypothetical right-half zero,
the complementary normalized sum still tends to `-multiplicity(rho)`,
including at the exceptional contact.

| Terms | What has been bounded | What is still needed |
| --- | --- | --- |
| Composite cofactors in the exact-tilt schedule | Explicit geometric allowance, away from the scalar contact | Nothing further for this selected class |
| Composite cofactors in the earlier polynomial schedule at contact | A vanishing allowance | Nothing further for this selected class |
| Semiprimes | The exact coefficient and phase are retained | Their contribution coupled with larger composite cofactors |
| Surviving composite cofactors | Every eligible cofactor exceeds the selected threshold | A joint signed lower floor with the semiprimes |

These are component statements, not percentages of the original carrier.
A fixed cofinal floor strictly above minus one for the combined remaining
normalized sum would contradict its source. That independent arithmetic
estimate is unproved. No new zero-free region, numerical certificate or
historical novelty is claimed here.

## Checked endpoints

All 41 declarations in
[ZetaRieszGeneralCofactorTilt](../RiemannGaussian/ZetaRieszGeneralCofactorTilt.lean)
belong to the ordinary root and its full transitive axiom audit. Main
endpoints are `norm_tilted_composite_band_le`,
`norm_optimal_composite_band_le`, `eventually_pow_le_optimalSchedule`, and
`tendsto_optimized_reduced_source`. The
[explorer audit](rh-proof-explorer/audit.json) supplies compiled statements,
dependencies and exact source lines. The default whole-carrier endpoint
remains `ZetaRieszCriticalProfile.exists_original_band_critical_profile`.
