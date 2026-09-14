# Exponential cofactor decay and the adaptive source

[Explore the geometric bound and retained source](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=exponential-cofactor-decay).

Lean now proves geometric decay of the entire original-band contribution
from an explicit composite-cofactor range that eventually exceeds every
fixed polynomial in the order. This stronger estimate holds for
`2/3<u<1`, corresponding to hypothetical zeros with `1/2<Re(rho)<5/6`.
An adaptive deletion combines it with the earlier universal polynomial
range. Its exact complement retains the original source throughout the
right half-strip. The joint signed floor remains open.

## The full arithmetic bound

Retain `D_N`, `L_N`, the signed coefficient `C_L`, original band and full
fixed factorial filter from the [growing-cofactor audit](zeta-riesz-growing-cofactor-decay.md).
Define

```text
S(P) = sum_j |P_j|*(2/3)^j,
E_N = min(sqrtNat(sqrtNat(sqrtNat(floor((3*u/2)^N)))), D_N+1).
```

Let `T_N` be the original band restricted to labels `n=p*a`, where `p` is
prime, `p` does not divide `a`, and `a` is squarefree, nonunit, composite
and at most `E_N`. At every order, for `2/3<u<=1`, Lean proves

```text
|u^(N+1) sum_(n in T_N) C_(L_N)(n)*K_(P,N,y)(n)|
 <= 18*u*(1+1/log(4))*S(P)*sqrt((2/(3*u))^N).
```

The right side tends geometrically to zero for `2/3<u<1`. This holds for
every fixed complex polynomial `P` and uniformly in the height `y`.
No hypothetical-zero assumption is used for the estimate.

The three-halves exponential tilt bounds the complete factorial kernel by
`(2/3)^N*S(P)`. The cofactor coefficient has its earlier range cost
`2*A*log(A)*(1+log(A)/log(4))`; counting the compact support preserves the
geometric base `2/(3*u)`. Lean proves `E_N^8<=(3*u/2)^N`, including all
integer rounding, and `log(E_N)<=L_N` at every order. Complete cofactor
mass and logarithmic-moment cancellation make every term above the compact
range exactly zero. Thus the bound covers the whole selected class.

`eventually_pow_le_exponentialSchedule` proves that, for each fixed natural
`k`, eventually `N^k<=E_N`. The stronger range is established in Lean,
not inferred from an unverified asymptotic approximation to the floor.

## The remaining arithmetic

The adaptive deletion selects this class when `u>2/3` and the earlier
growing polynomial class otherwise. Its exact complementary source
converges to `-multiplicity(rho)` for every hypothetical right-half zero.
The original signs, phases, support, common physical cutoff and full fixed
factorial filter survive the partition.

| Actual terms | Status |
| --- | --- |
| Composite cofactors in the universal eighth-root range | Independently paid for every `0<u<1` |
| Composite cofactors in `E_N` | Stronger geometric bound for `2/3<u<1`; the range eventually exceeds every fixed polynomial |
| Semiprimes | Their prime cofactors do not have the two complete moment cancellations; their signed tails remain |
| Surviving larger composite cofactors | Every eligible cofactor exceeds the selected threshold; a joint lower bound with the semiprimes remains unproved |

The rows describe nested reductions, not additive percentages of the
carrier. A fixed cofinal floor strictly above minus one for the combined
remaining normalized sum would contradict the source. No new zero-free
region or numerical certificate follows from the component estimates.

## Exact tilt optimization: a separate scalar audit

The proposed geometric base for an arbitrary positive tilt is

```text
r(u,q) = exp((2-2*q)*log(u))/q.
q_opt(u) = 1/(-2*log(u)),
min_q r(u,q) = (-2*log(u))*exp(1+2*log(u)).
```

For `0<u<1`, Lean proves that this is the unique positive optimizer.
A scalar rate strictly below one exists exactly when `u!=exp(-1/2)`.
At that exceptional value every positive tilt has rate at least one.
This is an exact test of all positive tilts, using elementary exponential
convexity. It is not a claim of historical novelty.

The unit tilt gives rate one, and the three-halves tilt gives precisely
the proved arithmetic base `2/(3*u)`. For actual `1/2<u<1`, the optimum
is above one half. **A general-tilt spatial estimate is still required**
before the other scalar rates become arithmetic bounds. The exceptional
scalar contact does not assert the presence or absence of zeta zeros.
Optimizing this envelope also does not pay the joint remaining signed sum.

## Checked endpoints

| Module | Main declarations |
| --- | --- |
| [ZetaRieszExponentialCofactor](../RiemannGaussian/ZetaRieszExponentialCofactor.lean) | `norm_exponential_composite_band_le`, `eventually_pow_le_exponentialSchedule`, `tendsto_exponential_composite_band`, `tendsto_adaptive_reduced_source` |
| [ZetaRieszCofactorTiltRate](../RiemannGaussian/ZetaRieszCofactorTiltRate.lean) | `minimumRate_eq_tiltRate_iff`, `exists_improving_tilt_iff`, `optimalTilt_gt_half` |

Both belong to the ordinary root and its full transitive axiom audit.
The [explorer audit](rh-proof-explorer/audit.json) links compiled statements,
dependencies and exact source locations. The default whole-carrier
endpoint remains `ZetaRieszCriticalProfile.exists_original_band_critical_profile`.
