# Zero-free logarithmic regions for every fixed coefficient

The actual zeta function now has a proved eventual zero-free region for
every fixed positive logarithmic coefficient. All analytic and arithmetic
premises are discharged. The theorem has the quantifier order

```text
for every A > 0,
  there exists a finite T(A) >= 2,
    for every nontrivial zeta zero rho = beta+i*t with abs(t) >= T(A),
      A/log(abs(t)) < beta < 1-A/log(abs(t)).
```

[exists_eventual_strip](../RiemannGaussian/ZetaArbitraryLogZeroFree.lean#L51)
proves both edges. `exists_eventual_nonvanishing` also proves literal
`zeta(s) != 0` on the closed right edge at sufficiently large height.
Each threshold is existential, depends on the coefficient, and has not
been numerically evaluated. No common threshold for all coefficients is
asserted. In particular, one cannot increase `A` indefinitely at a fixed
height to exclude every off-line zero.

## Full local source with its correction retained

Use the already proved [Gaussian strip bound](zeta-gaussian-local-jensen.md):

```text
alpha_k = 1/(2^(k+2)-2),     delta_k = (k+2)*alpha_k,
H(t) = abs(t)+2,
M_k(t) = log(32768/delta_k)+alpha_k*log(H(t))+log(log(H(t))),
E_k(x,t) = M_k(t)+14+log(1+1/x).
```

For `k >= 1`, `abs(t) >= 2`, `0 < x <= delta_k/4`, put `c=1+x+i*t`.
The complete closed disc of radius `delta_k/2` is analytic for actual
zeta, and its center is nonzero by Euler nonvanishing. A finite-divisor
argument selects a zero-free boundary radius

```text
delta_k/4 < r < 3*delta_k/8.
```

Translate the center to zero and remove the entire local divisor with
canonical factors. The resulting residual `g` is analytic and nonzero
on the disc. Canonical removal preserves the boundary norm exactly and
increases the center norm. The maximum principle, an actual analytic
logarithm, Borel--Caratheodory and Cauchy give

```text
norm(g'(0)/g(0)) <= 2*E_k(x,t)/r <= 8*E_k(x,t)/delta_k.
```

The logarithmic derivative retains the full complex identity

```text
zeta'(c)/zeta(c)
  = g'(0)/g(0) + sum_a multiplicity(a)*(-1/a+conj(a)/r^2),

Re(-1/a+conj(a)/r^2)
  = (-Re(a)/normSq(a)) * (1-normSq(a)/r^2).
```

Here `a` is the displacement of an actual zero from `c`; the sum is the
complete finite local divisor. Each `a` is nonzero and lies to the left
of the center. Each coupled term is consequently nonnegative. Keeping
the correction attached to its pole avoids a separate error proportional
to the number of local zeros.

For a selected actual zero `rho=beta+i*t`, let `d=x+1-beta` and let
`m_rho` be its full analytic multiplicity. If `d<delta_k/4`, the actual
signed bound is

```text
Re(-zeta'(c)/zeta(c))
  <= 8*E_k(x,t)/delta_k
       - m_rho*(1/d-16*d/delta_k^2).
```

The [full complex identity](../RiemannGaussian/AnalyticDiscSignedDerivative.lean#L48)
and [actual selected-zero bound](../RiemannGaussian/ZetaNearOneSignedBound.lean#L139)
remain separate named theorems. No simple-zero assumption or absolute-value
replacement of the selected source is used.

## Actual prime positivity and the complete budget

The genuine von Mangoldt series supplies the usual three-height
nonnegative combination, with coefficients `3,4,1`. Its real-axis pole
is bounded separately, and the doubled-height term receives the same
local residual bound. Define

```text
B_k(x,t) = 1344*log(22)
             + (32*E_k(x,t)+8*E_k(x,2*t))/delta_k.
```

Lean proves, with all prime and analytic premises discharged,

```text
4*m_rho*(1/d-16*d/delta_k^2) <= 3/x+B_k(x,t).
```

For any target `C>0`, write

```text
u(t) = C/log(H(t)),     x(t) = 6*u(t),
cost_k,C(t) = 14*u(t)*B_k(x(t),t)+6272*u(t)^2/delta_k^2.
```

If a genuine zero satisfies `1-beta <= u(t)` and `28*u(t)<delta_k`,
then `d<=7*u(t)<delta_k/4`. The coupled selected source is nonnegative,
its multiplicity is at least one, and the preceding inequality forces

```text
1 <= cost_k,C(t).
```

This is a contradiction threshold for the whole allowance. It requires
only a strict bound below one, rather than decay of every unnormalized
term. See [source_le_budget](../RiemannGaussian/ZetaNearOnePhaseConstraint.lean#L31)
and [one_le_cost_of_zero_near](../RiemannGaussian/ZetaNearOneExclusion.lean).

## Fix the order before taking the height limit

The complete [budget limit](../RiemannGaussian/ZetaNearOneBudgetLimit.lean)
includes the moving Euler center cost `log(1+1/x(t))`. For every fixed
order `k` and coefficient `C>0`,

```text
B_k(x(t),t)/log(H(t)) -> 40/(k+2),
cost_k,C(t) -> 560*C/(k+2).
```

The other terms are proved lower order, including `log(1/delta_k)`,
the logarithmic height correction, the doubled-height ratio, the
shrinking center cost and the canonical radial correction. Given `C`,
choose one fixed natural `k>=1` with `k+2>560*C`. The cost is eventually
strictly below one, while the geometric conditions eventually hold.
The hypothetical zero would force the opposite bound, so
`C/log(H(t)) < 1-beta` eventually.

To obtain any ordinary-logarithm coefficient `A`, use `C=2*A` and the
proved inequality `log(abs(t)+2)<=2*log(abs(t))` for `abs(t)>=2`.
Reflection across the critical line gives the left edge. No exchange of
the order and height limits is made.

This fixed-order argument proves every fixed coefficient eventually.
The downstream [joint-order proof](zeta-log-log-zero-free.md) now controls
all width and center costs at a growing order and supplies a specified
`log(log(abs(t)))/log(abs(t))` region. That stronger statement uses
additional uniform estimates rather than exchanging these fixed-order
limits.

## Consequence for the original arithmetic response

The complete-band theorem covers every zero below `H`, including those
below the initial asymptotic threshold. For each fixed `A>0`, the margin
`A/log(H)` is positive and below `1/4` at sufficiently large `H`.
At `c=3/2+i*y`, set `H=2*abs(y)+3`. The literal quotient
`Q(s)=zeta(s)/zeta(2*s)` is then analytic on a neighborhood of the entire
closed disc of radius

```text
R_A(y) = 1+A/(2*log(2*abs(y)+3)).
```

Both pole exclusions and every doubled-denominator zero are checked.
The [actual radius and Cauchy bound](../RiemannGaussian/ZetaSquarefreeArbitraryLogRadius.lean)
give one constant, independent of the excluded prime set, squarefree mark,
complex polynomial and moment order, in

```text
norm(response(p,S,P,N,c))
  <= K(A,y)*envelope_2(S,c,r)*r^(-N)*sum_k norm(p_k)*r^(-k),
0 < r <= R_A(y).
```

The envelope retains the signed first and doubled prime harmonics on
the chosen disc. It is not replaced by a bound uniform in growing `S`.
For every two fixed coefficients `0<=A<B`, sufficiently large `abs(y)`,
and fixed valid `S,P,p`, Lean also proves

```text
R_A(y) < R_B(y),
R_A(y)^N * response(p,S,P,N,c) -> 0.
```

The height threshold in this comparison depends on the coefficients.
The full squarefree response is different from the separate ordinary-prime
source in the RH contradiction. This stronger decay does not supply that
source's independent signed lower bound.

## Entry points

| Module | Principal results |
| --- | --- |
| [AnalyticDiscCanonicalBounds](../RiemannGaussian/AnalyticDiscCanonicalBounds.lean) | `exists_zeroFree_sphere`, `norm_eq_on_sphere`, `norm_le`, `center_norm_le`. |
| [AnalyticDiscLogarithm](../RiemannGaussian/AnalyticDiscLogarithm.lean) | `exists_logarithm`, `exp_mul_center`, `norm_logDeriv_center_le`. |
| [AnalyticDiscSignedDerivative](../RiemannGaussian/AnalyticDiscSignedDerivative.lean) | `logDeriv_center_eq`, `kernel_re`, `kernel_re_nonneg`. |
| [ZetaNearOneCanonical](../RiemannGaussian/ZetaNearOneCanonical.lean) | `analyticOnNhd_translated`, `exists_controlled_decomp`. |
| [ZetaNearOneSignedBound](../RiemannGaussian/ZetaNearOneSignedBound.lean) | `divisor_at_zero`, `source_le_sum`, `neg_logDeriv_re_le_sub_zero`. |
| [ZetaNearOnePhaseConstraint](../RiemannGaussian/ZetaNearOnePhaseConstraint.lean) | `source_le_budget`, `zero_gap_constraint`. |
| [ZetaNearOneBudgetLimit](../RiemannGaussian/ZetaNearOneBudgetLimit.lean) | `center_cost_div_scale`, `budget_div_scale`. |
| [ZetaNearOneExclusion](../RiemannGaussian/ZetaNearOneExclusion.lean) | `cost_tendsto`, `one_le_cost_of_zero_near`, `exists_eventual_margin`. |
| [ZetaArbitraryLogZeroFree](../RiemannGaussian/ZetaArbitraryLogZeroFree.lean) | `exists_eventual_strip`, `exists_eventual_common_margin`, `exists_eventual_nonvanishing`. |
| [ZetaSquarefreeArbitraryLogRadius](../RiemannGaussian/ZetaSquarefreeArbitraryLogRadius.lean) | `exists_eventual_radius_spec`, `exists_eventual_response_bound`, `exists_eventual_coefficient_scaled_decay`. |

## Literature and remaining frontier

The changing-order strategy is motivated by
[Yang, JMAA 2024](https://arxiv.org/html/2301.03165v2).
The higher-derivative bounds, canonical factorization and
Borel--Caratheodory argument are classical techniques. No historical
novelty or reproduction of optimized published constants is claimed.
The [literature survey](zero-free-region-transport.md) records stronger
explicit Littlewood and Vinogradov--Korobov widths, their actual boundary
conventions, and rigorous finite-height verification.

The [joint order-height argument](zeta-log-log-zero-free.md) now proves
the specified log-log width, retains its open coefficient range under
smoothing, and transports it to actual larger arithmetic discs.
Independent control of the signed ordinary-prime
source at a hypothetical fixed right-half zero is still required by the
current RH contradiction. RH remains open.

## Validation of the fixed-coefficient slice

All ten modules pass direct elaboration with warnings treated as errors.
The focused build passes 4,892 jobs; the full library passes 10,254 jobs.
Whole-project declaration lint and verbose lint of the ten modules pass.
All 62 new public theorems have explicit axiom audits using only
`propext`, `Classical.choice` and `Quot.sound`.

The strict generated inventory contains 1,407 project modules and 26,449
project theorems, with no project axioms or placeholder-dependent
declarations. It reports `rhImplied = false`. The source scan covers
1,550 Lean files. The README and related documentation pass 643 local-link
checks, and the Current Direction remains one 402-character paragraph.
All changes remain local and uncommitted under the user's hold.
