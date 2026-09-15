# Removing the complete Euler correction from the original arithmetic band

[Explore the actual-band deletion and its explicit residual](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=euler-correction-deletion).

Lean now proves that removing the **standalone full Euler correction** changes
the original normalized arithmetic band by a quantity tending to zero. This
retains the actual growing physical cutoff, both Fourier phases, every
factorial order and every fixed polynomial filter. It uses no hypothetical-zero
premise. **The independent joint floor for the remaining signed response is open.**

## The physical phase and its cost

Use the full correction product from the
[finite Euler-quotient factorization](zeta-riesz-euler-correction-energy.md):

```text
w(q,z) = q^2 (z-1)/(1-q*z),
H_Q(s,xi) = prod_Q [1+w(p^(-s),exp(i log(p) xi))].
```

All labels in this correction satisfy `p>=16`. The finite smaller-prime head
is retained in the leading response. For arbitrary quarter-disk complex
weights and real frequencies, put

```text
M = sum_Q |q_p|^2,
J = sum_Q |q_p|^2 |ell_p|,
C = 2+exp(8M),
B = 32+64MC.

S_L(s,xi) = exp(i L xi)(H_Q(s,xi)-1)
          + exp(-i L xi)(H_Q(s,-xi)-1).
```

The even and odd channels stay coupled before taking a norm. Weighted Young
inequality and the exact cosine integral prove genuine integrability and

```text
integral_0^infinity |S_L(s,xi)/xi^2| dxi
 <= (B+4C)(pi/2)J + 4 pi C M |L|.
```

This covers every product interaction order. Its dependence on the physical
length is linear. For literal prime weights on a fixed closed half-plane
`Re(s)>=sigma>1/2`, the allowance is at most
`phaseTailCost sigma L * squareLogTail sigma K` above the chosen threshold.
Constants may depend on the fixed half-plane; no uniform limit as `sigma`
approaches one half is asserted.

The original carrier already contains `1/L`. Lean proves that, for every
`L>=a>0`,

```text
phaseTailCost(sigma,L)/L <= phaseTailCost(sigma,a)/a.
```

Thus restoring the physical phase does not introduce an unbounded cutoff cost
after the original normalization. No bounded-length assumption is imposed.

## Every factorial moment and fixed filter

The complete correction is analytic in the arithmetic parameter. A pointwise
cosine majorant is uniform throughout the closed half-plane, so Cauchy's
estimate on a radius `R>0` preserves that same integrable majorant, divided
by `R^n`, for the signed factorial moment of order `n`.

The proof separately establishes joint measurability through an exact
parameterized Cauchy-circle formula and ordinary frequency integrability of
each moment. It does not exchange a derivative and an improper integral
without justification.

For a fixed polynomial `P`, the original logarithmic mark shifts the moment
to `N+k+1` and multiplies it by `N+k+1`. Every such offset is retained. Set

```text
filterRadiusCost(P,R) = sum_(k in P.support) |P_k| (k+1)/R^k,
C_sigma,a,K = [phaseTailCost(sigma,a)/a] squareLogTail(sigma,K).
```

The integrated, correctly oriented correction satisfies

```text
|u^(N+1) filteredResponse(Q,P,N,s,L)|
 <= C_sigma,a,K filterRadiusCost(P,R) (N+1)(u/R)^(N+1),
sigma = Re(s)-R > 1/2,  L>=a>0.
```

This decays whenever `0<=u<R`. At the original center `s=3/2+i*y` and every
source scale `0<u<1`, choose `R=(u+1)/2`. The actual physical length
`SquarefreeVaughanLogSource.length u N` is always at least `log 4`.
The selected prime universe is exactly the primes at least 16 in the
primorial completion of the original endpoint `2^(32N)`. The prime selection
may grow with `N`; the proof does not fix it before taking the limit.

## What remains after the deletion

Write the complete finite character as `V H`, where `V` retains the entire
small-prime head and the leading Euler quotient. Let `A` be the complete
ordinary-prime compensation. The exact identity is

```text
V H - 1 - A = (V-1-A) + (H-1) + (V-1)(H-1).
```

Lean keeps this identity through the signed band completion, every factorial
shift, the fixed filter, both physical phases and the ordinary frequency
integral. The resulting terminal theorem proves, independently of any zero
hypothesis,

```text
u^(N+1) [actualArithmeticBand_N - residualResponse_N] -> 0.
```

The residual is explicit, rather than an assumed bound:

| Term retained in the residual | What still needs control |
| --- | --- |
| Leading Euler quotient and finite small-prime head | Its contribution at the original source scale |
| Ordinary-prime compensation | Its signed cancellation with the other terms |
| Mixed term `(V-1)(H-1)` | Its interaction with the leading response; standalone correction decay does not bound it |
| Entire signed off-band completion boundary | Its correlation with the completed terms |

These terms remain coupled. The target is a joint cofinal real lower bound
strictly above minus one at a hypothetical right-half zero. The deletion does
not establish that floor, a new zero-free region, or RH. It does not assert an
infinite Euler-product identity outside a proved convergence domain.

## Checked sources

- [ZetaRieszEulerCutoff](../RiemannGaussian/ZetaRieszEulerCutoff.lean): the physical-phase integral and its arithmetic tail allowance.
- [ZetaRieszEulerMoments](../RiemannGaussian/ZetaRieszEulerMoments.lean): all factorial moments, the full fixed filter, and decay at the original physical cutoff.
- [ZetaRieszEulerCorrectionDeletion](../RiemannGaussian/ZetaRieszEulerCorrectionDeletion.lean): the exact original-band decomposition and `tendsto_actual_band_sub_residual`.

The three ordinary modules contain 87 declarations, including 67 theorems.
The [explorer audit](rh-proof-explorer/audit.json) links compiled statements,
dependency paths, source lines and transitive axiom checks. The default
whole-carrier endpoint remains
`ZetaRieszCriticalProfile.exists_original_band_critical_profile`.

The [growing-head correction deletion](zeta-riesz-euler-growing-head.md) now pays
the full correction multiplied by actual primes up to n+16 along a cofinal
stride of original factorial orders. Its explicit compensated-leading, mixed
and signed-boundary residual retains the source; the joint floor remains open.
