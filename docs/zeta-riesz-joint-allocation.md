# Exact allocation cancellation in the harmonic remainder

This local theorem batch pays the complete infinite boundary of the composite
companion, a sector of the actual signed remainder, and the entire correction
outside the original arithmetic mask. The remaining target is one sum of the
original signed atoms with multipliers between zero and one. The independent
cofinal floor and restricted zero exclusion remain open.

Write M=N+1, let U_N be the original unpaid wing orders, A_N the original
intermediate-prime set, S_N the original masked lower-count window, and
W_N={n: 7N/4 < log n <= 9N/4}. All old masks remain in S_N.
For squarefree composite n>1, define

$$
\theta_N(n)=\sum_{\substack{p\mid n,\ p\in A_N\\n/p\text{ composite}}}
\sum_{k\in U_N}{M\choose k}
\left(\frac{\log(n/p)}{\log n}\right)^k
\left(\frac{\log p}{\log n}\right)^{M-k}.
$$

It is zero outside this arithmetic support. `boundedShare` retains the
explicit squarefree and coprimality guards as well. The full multinomial
allocation proves 0 <= theta_N(n) <= 1: a single derivative allocation
cannot give a strict majority to two different primes. Thus the prime
incidences do not introduce a factor of the number of prime divisors.

`hasSum_assignedAtom` proves that the complete companion is genuinely the
sum of theta_N(n) times the original signed atom. `exists_finiteResponse_error`
then proves, uniformly in height, prime-count cutoff and 0 <= u <= exp(-11/16),

$$
 u^{N+1}(F_N-T_N)=u^{N+1}\sum_{n\in W_N}
 \bigl(\mathbf1_{S_N}(n)-\theta_N(n)\bigr)c_{L_N}(n)b_N(n)+E_N,
 \qquad |E_N|\le C r^N,\quad 0\le r<1.
$$

The multiplier lies between -1 and 1. In particular, the terms outside S_N
are retained with multiplier -theta_N(n); the companion is not declared
to be a finite subfamily of F_N.

## A quantitatively paid sector

For N>=320 the unpaid orders are exactly

$$
 k\le\lfloor13N/32\rfloor,\qquad5(N+1-k)<4N.
$$

If an eligible prime p in A_N divides a retained squarefree composite n and

$$
 \frac{17}{64}\le\frac{\log(n/p)}{\log n}\le\frac{11}{32},
 \quad\text{equivalently}\quad
 \frac{21}{32}\le\frac{\log p}{\log n}\le\frac{47}{64},
$$

then `allocation_missing_exponential` proves

$$
 0\le1-\theta_N(n)\le3e^{-N/140}.
$$

This uses both binomial tails, with tilts 5/4 and 4/5, against the exact
integer endpoints. It does not assume a zeta zero or arithmetic cancellation.
The original signed coefficient and complex product phase survive the
pointwise identity before this estimate is taken.

The actual finite subset is `cancellingSector`. Its whole source-normalized
sum has the checked bound `actual_sector_geometric`:

$$
 \left|u^{N+1}\sum_{n\in\mathcal C_N}
   (1-\theta_N(n))c_{L_N}(n)b_N(n)\right|
 \le r_*^N\frac{1509}{1000}\mathcal M(2049/2048),
 \qquad
 r_* =\frac{503}{1000}\frac{2048}{1023}e^{-1/140}<1.
$$

Here Mcal(sigma) is the existing convergent divisor-majorant Dirichlet mass.
The bound is uniform in height, count threshold, and 0 <= u <= exp(-11/16).
The constant is a defined convergent series, not a numerical evaluation.
There is no empirical or floating-point certificate in the proof.

## The entire mask correction is paid

The intermediate multiplier `1_S-theta` above is essential; replacing it
pointwise by `1-theta` would be incorrect. The following estimates and exact
support comparisons now discharge its complete off-mask correction:

- `ZetaRieszWeightedCount.tendsto_remaining_sub_lowCount` pays every high-count
  term, including the companion correction. It proves the count estimate for
  arbitrary coefficients dominated by the original absolute divisor majorant;
  it does not transfer an unweighted signed estimate through a new multiplier.
- `ZetaRieszBalancedCompanion.unpaid_mass_balanced_le` proves a bound
  `exp(-N/64)` for each eligible selected prime whose logarithm is at most half
  the product logarithm. The whole balanced companion has the bound
  `balanced_companion_bound`, at most `4(N+1)/3` times the geometric sector
  allowance above. This bounds the companion, not the original balanced sum.
- `ZetaRieszMaskSupport.window_mem_originalMask` proves every old mask for a
  lower-count squarefree integer in the literal window with at least three
  prime factors, all below the physical cutoff. The actual small-cofactor
  schedule and every quadratic-head divisor have logarithm at most `N/4`.
  The physical length is eventually at least `5N/4`.
- If an off-mask integer survives those tests, it must have an unselected
  prime above the physical cutoff. Its logarithm exceeds half the total,
  forcing all selected primes into the already paid balanced case. Counts
  below three and nonsquarefree labels vanish exactly.

Consequently `residualMask_eq_retained` proves exact eventual equality with
the retained sum on the **original** mask. No independent off-mask term is
left. Write

$$
 R_j^{\rm ret}=u^{N_j+1}
 \sum_{n\in S_{N_j}\setminus\mathcal C_{N_j}}
 (1-\theta_{N_j}(n))c_{L_{N_j}}(n)b_{N_j}(n).
$$

The actual schedules remain `K_j=2^(j+3)` and `N_j=8(j+4)K_j`.
`tendsto_arithmetic_sub_retained_moving` combines **all** corrections into
one independently vanishing difference, with no zero hypothesis, even for
an arbitrary height sequence `y_j`. The stronger uniform formulation
`eventually_all_heights_arithmetic_error` states that, for fixed
`1/2<u<=exp(-11/16)` and each positive tolerance, one starting index controls
the complete error at **every real height**. Neither theorem says the
retained sum itself tends to zero. The threshold is not numerically evaluated.

## The surviving obligation

`ZetaRieszMaskSupport.tendsto_retained_add_reserve` carries the exact old source
to this single retained carrier:

$$
 R_j^{\rm ret}+u^{N_j+1}V_{N_j}^+
 \longrightarrow -m+m^2c(u).
$$

The follow-up now evaluates the **whole** positive reserve, improving the
earlier coarse lower bound `15m^2/544`. The actual reciprocal interval
masses are `log(15/13)` and `log(19/17)`. Keeping the endpoint subtraction
gives

$$
 v(u)=\log(19/17)+\left(1-\frac1{-2u\log u}\right)\log(15/13),
 \qquad u^{N+1}V_N^+\longrightarrow m^2v(u).
$$

`ZetaRieszWingReserve.tendsto_reserve_exact` proves this complex limit with
the original finite prime sets, derivative successor and integer orders.
`ZetaRieszMaskSupport.tendsto_retained_exact_source` therefore proves

$$
 R_j^{\rm ret}\longrightarrow -m+m^2c_{\rm ret}(u),\qquad
 c_{\rm ret}(u)=\frac{\log(32/13)}{-2u\log u}-\log(19/13).
$$

The source assumptions and `1/2<u<exp(-11/16)` remain explicit. The
independent elementary estimate `retainedCost_lt_thirtyseven_fortieths`
proves `c_ret(u)<37/40` throughout the closed radius interval. Thus, for a
simple exposed zero, the real retained sum is eventually **strictly below
`-3/40`**. A cofinal independently proved floor

$$
 \Re R_j^{\rm ret}\ge-\frac3{40}
$$

would contradict this. More generally any floor `-eta` with
`eta<1-c_ret(u)` suffices. This exact deficit is approximately 0.0766 near
the upper endpoint; the old coarse allowance there was approximately
0.0569. These decimals explain the scale; the proved rational threshold
is `3/40=0.075`.

No theorem in this batch proves the independent floor. What remains inside it is the
signed Riesz divisor sum, the factorial envelope, the full product phase
`exp(-i*y*log n)`, and the nonnegative unassigned fraction, summed over all
retained prime counts together. Balanced products are among the surviving
configurations. The independent balanced bound above makes their assigned
fraction small, so it cannot justify a small unassigned fraction. There is
no remaining off-mask companion correction to pay.

The [dominant-prime follow-up](zeta-riesz-dominant-sector.md) further
reduces this target. It independently pays the whole unassigned contribution
whenever an eligible prime carries at least `13/20` of the logarithm, with
no upper prime-log endpoint. All nonzero surviving labels have every prime
below that fraction, and their carrier `nondominantRemainder` keeps the same
exact source and rational deficit. Its signed cofinal floor is still open.

The pointwise bound `0<=theta<=1` does not control the joint oscillatory sign.
Nor does completing the full divisor/Euler identity produce a second
independent inequality: that identity is already compatible with the
negative source. The next advance must control this retained signed sum,
not rederive its source or bound the companion alone.

Sources:
[allocation weights](../RiemannGaussian/ZetaRieszAllocationWeights.lean),
[assigned companion](../RiemannGaussian/ZetaRieszAssignedCompanion.lean),
[complete boundary and finite sum](../RiemannGaussian/ZetaRieszCompanionWindow.lean),
[binomial concentration](../RiemannGaussian/ZetaRieszAllocationConcentration.lean),
[paid sector](../RiemannGaussian/ZetaRieszCancellingSector.lean),
[weighted count estimate](../RiemannGaussian/ZetaRieszWeightedCount.lean),
[balanced companion](../RiemannGaussian/ZetaRieszBalancedCompanion.lean),
[off-mask correction](../RiemannGaussian/ZetaRieszCompanionMask.lean),
[support size estimates](../RiemannGaussian/ZetaRieszMaskSizeBounds.lean),
[complete mask comparison](../RiemannGaussian/ZetaRieszMaskSupport.lean),
[single retained carrier](../RiemannGaussian/ZetaRieszRetainedCarrier.lean),
[exact reserve weights](../RiemannGaussian/ZetaRieszReserveWeights.lean),
[complete reserve evaluation](../RiemannGaussian/ZetaRieszReserveExact.lean),
[exact retained source and rational deficit](../RiemannGaussian/ZetaRieszRetainedSource.lean).

The [allocation explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=joint-allocation)
and [exact-reserve view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=exact-wing-reserve)
show these checked chains, including their hypotheses and exact source lines.
The [compiled proof audit](rh-proof-explorer/audit.json) records the transitive
axioms. The current default continues through the
[dominant-prime deletion](zeta-riesz-dominant-sector.md); its independent
signed floor remains open.
