# Growing cofactor decay and the retained arithmetic source

[Explore the checked bounds and remaining premises](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=growing-cofactor-decay).

Lean proves that an explicitly growing class of squarefree composites has
vanishing contribution at the original source scale. Deleting that class
preserves the hypothetical-zero source. This is an arithmetic component
bound; the joint signed lower bound for its complement remains open.

## The bound

Use the original quantities and full fixed factorial filter from the
[fixed-cofactor audit](zeta-riesz-fixed-cofactor-decay.md). Put

```text
A_N = sqrtNat(sqrtNat(sqrtNat(N+1))),
C(A) = 2*A*log(A)*(1+log(A)/log(4)),
S(P) = sum_j |P_j|.
```

Every rounding is retained: Lean proves `1<=A_N`, `A_N^8<=N+1` and
`A_N -> infinity`. The eighth-root exponent is a conservative admissible
choice, not an optimum.

For any original subband whose labels admit `n=p*a`, with `p` prime,
`p` not dividing `a`, `1<a<=A` and `n<=A*(D_N+2)^2`, the complete filtered
contribution obeys

```text
|u^(N+1) sum_n C_(L_N)(n) K_(P,N,y)(n)|
 <= 2*C(A)*S(P)*sqrt(A) * [u/(N+1)+2*u^(N+1)].
```

For the explicit schedule this is at most

```text
4*(1+1/log(4))*S(P)
  * [u/sqrt(N+1)+2*(N+1)*u^(N+1)] -> 0,     0<u<1.
```

The proof uses the signed cofactor cancellation before bounding its
remaining divisor cost by `a*log(a)`. It holds for every fixed polynomial
`P` and every real height `y`, with a bound independent of `y`.

When `a` is squarefree, nonunit and composite, its complete divisor mass
and logarithmic moment both vanish. Once `log(A_N)<=L_N`, every label
above the displayed compact range therefore has coefficient exactly zero.
Lean proves this cutoff inclusion eventually. The **whole** original-band
class with such a cofactor `a<=A_N` consequently tends to zero. No estimate
on an omitted boundary is assumed.

## What remains

The original band splits exactly into this paid class and its literal
complement. Their common physical cutoff, arithmetic coefficients, phases,
base band and polynomial factorial filter are unchanged. Under a
hypothetical right-half zero `rho`, the complementary sum still converges
to `-multiplicity(rho)` after source normalization.

| Actual arithmetic labels | Checked status |
| --- | --- |
| All prime factors below 16 | Absent from the original band for `N>=60` |
| A composite cofactor dividing 30030 | The complete finite union decays; its deletion and reduced source are assembled without counting overlaps twice |
| A squarefree nonunit composite cofactor `a<=A_N` | The entire growing class decays with the explicit allowance above |
| Semiprimes | Still require a signed bound; prime cofactors are excluded from the whole-class decay theorem |
| Surviving composites with composite cofactors | Every eligible cofactor exceeds `A_N`; their joint signed contribution with the semiprimes is unpaid |

These rows describe nested reductions, not additive proportions of the
carrier. The numerical constant 30030 is the product of the six primes
below 16. No percentage of RH progress or new numerical zero bound follows.

## What a successful remaining estimate would prove

For each hypothetical right-half zero it suffices to prove a fixed real
floor `Re B_N >= -c`, with `c<1`, at arbitrarily large orders for the
complete remaining normalized carrier. Constants and subsequences may
depend on the zero. Its source limit is at most `-1`, so that floor gives
a contradiction; reflection then places every nontrivial zero on the
critical line.

`rh_of_reduced_cofinal_floors` checks that logical closure to Mathlib's
`RiemannHypothesis` for the finite-head reduction. **Its arithmetic floor
is an unproved hypothesis.** The growing reduction also retains the same
source, but neither reduction supplies the independent floor. Isolated
`1/L` factors, bounds on a separately completed Euler response, or a small
nonlinear multiplier do not establish the joint inequality.

## Compiled endpoints

| Module | Main declarations |
| --- | --- |
| [ZetaRieszReducedCofactorSource](../RiemannGaussian/ZetaRieszReducedCofactorSource.lean) | `tendsto_composite_head_band`, `tendsto_reduced_source`, `reduced_support`, `rh_of_reduced_cofinal_floors` |
| [ZetaRieszGrowingCofactor](../RiemannGaussian/ZetaRieszGrowingCofactor.lean) | `norm_clipped_range_band_le`, `tendsto_eighth_power_clipped_band`, `eighthRootSchedule_tendsto`, `tendsto_growing_composite_band`, `tendsto_growing_reduced_source`, `surviving_composite_cofactor_gt` |

Both modules belong to the ordinary root and its transitive axiom audit.
The [supporting explorer audit](rh-proof-explorer/audit.json) links their
compiled statements and exact source locations. The default RH explorer
continues to show the furthest bound on the complete carrier,
`ZetaRieszCriticalProfile.exists_original_band_critical_profile`.
The zero-free region and optional numerical certificate are unchanged.
