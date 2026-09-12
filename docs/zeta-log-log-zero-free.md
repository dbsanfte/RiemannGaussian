# A proved log-log zero-free region

For every fixed coefficient

```text
0 < A < 1/(140*log(2)),
```

Lean now proves the following statement for actual nontrivial zeta zeros:

```text
there exists a finite T(A) >= 2 such that
  abs(t) >= T(A), rho = beta+i*t
    => A*log(log(abs(t)))/log(abs(t)) < beta
       < 1-A*log(log(abs(t)))/log(abs(t)).
```

[exists_eventual_strip](../RiemannGaussian/ZetaLogLogZeroFree.lean#L62)
proves both edges. The same module proves literal zeta nonvanishing on
the closed right edge and a common margin for the complete divisor below
every sufficiently large height. All analytic and arithmetic premises
are discharged. The threshold depends on the coefficient and has not
been numerically evaluated.

The coefficient range is supplied by the proved budget; no optimality
claim is made. The width has Littlewood shape, with coarse constants and
an existential threshold. It does not reproduce the optimized constant
or finite starting height in [Yang's published theorem](https://arxiv.org/html/2301.03165v2).

## The same order and height in every estimate

Write

```text
H(t) = abs(t)+2,       L(t) = log(H(t)),       ell(t) = log(L(t)),
k(t) = floor(ell(t)/b),                      b > log(2),
alpha_k = 1/(2^(k+2)-2),                     delta_k = (k+2)*alpha_k,
u(t) = C*ell(t)/L(t),                        x(t) = 6*u(t).
```

The exact exponent ratio `alpha_k/delta_k=1/(k+2)` is preserved in the
leading term. For the other terms, the natural floor and the complete
inverse width have the uniform bounds

```text
1/delta_(k(t)) <= 4*L(t)^p,       p=log(2)/b < 1,
ell(t)/(k(t)+2) -> b,
ell(t)^n/(L(t)*delta_(k(t))) -> 0    for every fixed natural n.
```

The positive power saving `1-p` absorbs every fixed logarithmic power.
These are moving-order theorems: no fixed-order limit is substituted
at a height-dependent index. See
[pow_log_div_width_tendsto](../RiemannGaussian/LogLogDerivativeSchedule.lean#L123)
and the [actual zeta schedule](../RiemannGaussian/ZetaLogLogScale.lean).

## The whole center and width correction vanishes

The [earlier full signed local source](zeta-arbitrary-log-zero-free.md)
uses the actual allowance

```text
E_k(x,v) = alpha_k*L(v) + R_k(x,v),
R_k(x,v) = log(32768/delta_k)+14+log(L(v))+log(1+1/x).
```

This is retained as an exact identity before taking a bound or limit.
At `x(t)=6*u(t)`, the full moving Euler center cost satisfies

```text
log(1+1/x(t)) <= log(1+1/(6*C))+ell(t)
```

once `L(t)>=1` and `ell(t)>=1`. The complete width logarithm satisfies

```text
log(32768/delta_(k(t))) <= log(131072)+p*ell(t).
```

More generally, let `v(t)` be any evaluation-height function such that,
eventually, `log(L(v(t)))>=0` and `L(v(t))<=D*L(t)` for a fixed `D>0`.
The entire correction is then bounded by

```text
0 <= R_(k(t))(x(t),v(t))
  <= log(131072)+14+log(D)+log(1+1/(6*C))+(p+2)*ell(t).
```

Consequently

```text
u(t)*R_(k(t))(x(t),v(t))/delta_(k(t)) -> 0.
```

The [correction theorem](../RiemannGaussian/ZetaLogLogCorrection.lean)
includes the whole moving center, radius and evaluation-height cost.
If the additional logarithmic ratio `L(v(t))/L(t)->q` is proved, the full
allowance has limit

```text
u(t)*E_(k(t))(x(t),v(t))/delta_(k(t)) -> C*b*q.
```

The actual prime phase inequality uses `v(t)=t` and `v(t)=2*t`; both have
ratio one. Their height comparisons and corrections are discharged in
[ZetaLogLogBudget](../RiemannGaussian/ZetaLogLogBudget.lean).

## The actual prime contradiction

The full-radius prime budget is now

provided by [ZetaFullRadiusPrimeBudget](../RiemannGaussian/ZetaFullRadiusPrimeBudget.lean).
Its analytic input uses the entire radius `delta_k` and retains the exact
selected correction `d/delta_k^2`, including its multiplicity.

```text
B_k(x,t) = 1344*log(22)+(8*E_k(x,t)+2*E_k(x,2*t))/delta_k.
```

The full moving-order limit is

```text
u(t)*B_(k(t))(x(t),t) -> 10*C*b,

cost(t) = 14*u(t)*B_(k(t))(x(t),t)
            +392*(u(t)/delta_(k(t)))^2 -> 140*C*b.
```

The second term is the canonical radial correction; its decay is proved
on the same schedule. The exact local pole and canonical correction
remain coupled. Every other local zero contributes nonnegatively,
while the selected zero retains its complete multiplicity and
reciprocal-distance source.

An actual zero with `1-beta<=u(t)` forces `cost(t)>=1`, once the
geometric conditions hold. Those conditions now hold eventually:
`k(t)>=2`, `u(t)>0`, and `28*u(t)<delta_(k(t))`. For every
`140*C*log(2)<1`, choose one fixed

```text
log(2) < b < 1/(140*C).
```

The actual cost is eventually below one. This proves the contradiction
for the specified smoothed log-log width, with no missing prime-bound
hypothesis. See the [complete budget limit](../RiemannGaussian/ZetaLogLogBudget.lean#L103)
and [actual growing-order exclusion](../RiemannGaussian/ZetaLogLogExclusion.lean).

## Ordinary height, reflection and the full lower divisor

The smoothed logarithm satisfies `L(t)/log(t)->1`. For any `A<C`, the
ordinary width `A*log(log(t))/log(t)` is eventually at most the smoothed
width `C*ell(t)/L(t)`. Given `A` in the open coefficient range, choose
`A<C<1/(140*log(2))`. This retains the whole stated range rather than
imposing a fixed fractional loss. Reflection gives the other strip edge.

The ordinary width is positive and antitone for
`H>=exp(exp(1))`, and tends to zero. This elementary height marks where
the width has those properties; it is not the zero-exclusion threshold.
The [general complete-band theorem](zero-free-region-transport.md) uses
these properties and the existing unconditional low-height margin to
cover every zero below `H`, including the divisor below the initial
asymptotic threshold.

For every fixed `A>0`, this width eventually exceeds `B/log(H)` for
every fixed `B`. That comparison is itself a
[proved theorem](../RiemannGaussian/ZetaLogLogWidth.lean).
It does not assert a single threshold covering all `B`.

## Consequence for the actual squarefree response

At `c=3/2+i*y`, put `H=2*abs(y)+3`. Each eligible coefficient gives
the actual quotient `zeta(s)/zeta(2*s)` the complete analytic disc radius

```text
R_A(y) = 1+A*log(log(H))/(2*log(H))
```

at sufficiently large `abs(y)`. Both poles and every doubled-denominator
zero are excluded before Cauchy's estimate is applied. For every finite
excluded prime set, valid squarefree mark, complex polynomial and order,

```text
norm(response(p,S,P,N,c))
  <= K(A,y)*envelope_2(S,c,r)*r^(-N)*sum_k norm(p_k)*r^(-k),
0 < r <= R_A(y).
```

The signed first and doubled prime harmonics remain in the actual
envelope on the selected disc. No uniform growing-prime-set bound is
asserted. For fixed `0<=A<B<1/(140*log(2))`, sufficiently large `abs(y)`,
and every fixed valid `S,P,p`,

```text
R_A(y) < R_B(y),
R_A(y)^N * response(p,S,P,N,c) -> 0.
```

These are [actual arithmetic theorems](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean),
with every zero-free and analytic premise discharged. Constants and the
phase envelope can increase with radius; a stronger asymptotic rate is
not a claim that every finite-order estimate improves.

## Entry points and remaining frontier

The current coefficient range uses the
[full strip-width radius and its complete signed endpoint limit](zeta-full-radius-zero-free.md).
The sharp Carathéodory estimate remains part of that proof.

| Module | Principal results |
| --- | --- |
| [LogLogDerivativeSchedule](../RiemannGaussian/LogLogDerivativeSchedule.lean) | `log_div_index`, `inverse_delta_le`, `log_width_le`, `pow_log_div_width_tendsto`. |
| [ZetaLogLogScale](../RiemannGaussian/ZetaLogLogScale.lean) | `order_atTop`, `width_div_delta_tendsto`, `width_mul_level_div_delta_tendsto`. |
| [ZetaLogLogCorrection](../RiemannGaussian/ZetaLogLogCorrection.lean) | `allowance_eq`, `center_log_le`, `normalized_correction_tendsto`. |
| [ZetaLogLogBudget](../RiemannGaussian/ZetaLogLogBudget.lean) | `leading_identity`, `normalized_allowance_tendsto`, `cost_tendsto`. |
| [ZetaLogLogExclusion](../RiemannGaussian/ZetaLogLogExclusion.lean) | `exists_schedule`, `exists_eventual_margin`. |
| [ZetaLogLogWidth](../RiemannGaussian/ZetaLogLogWidth.lean) | `width_antitone`, `eventually_le_smoothed`, `eventually_dominates_logarithmic`. |
| [ZetaLogLogZeroFree](../RiemannGaussian/ZetaLogLogZeroFree.lean) | `exists_eventual_strip`, `exists_eventual_common_margin`, `exists_eventual_nonvanishing`. |
| [ZetaSquarefreeLogLogRadius](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean) | `exists_eventual_radius_spec`, `exists_eventual_response_bound`, `exists_eventual_coefficient_scaled_decay`. |

The higher-derivative and Littlewood strategy is classical. No historical
novelty, optimized published coefficient or numerical threshold is
claimed. Stronger explicit published regions remain in the
[literature survey](zero-free-region-transport.md).

The enlarged discs apply to the complete squarefree quotient. The
separate signed ordinary-prime source at a hypothetical fixed right-half
zero still needs its independent cofinal lower bound. The larger region
does not establish that bound or exclude every point of the remaining
interior strip. RH remains open.

## Original schedule-slice validation

All eight modules pass direct elaboration with warnings treated as
errors. The focused build passes 4,893 jobs and the full library passes
10,262 jobs. Whole-project declaration lint and verbose lint of the
eight modules pass. All 52 new public theorems have explicit axiom
audits using only `propext`, `Classical.choice` and `Quot.sound`.

The strict inventory contains 1,415 compiled project modules and 26,528
project theorems, with no project axioms or placeholder-dependent
declarations. It continues to report `rhImplied = false`. The source
scan covers 1,558 Lean files. The README and related documentation pass
673 local-link checks; Current Direction remains one 419-character
paragraph at that checkpoint.

Those counts record the original eight-module schedule slice. The
subsequent sharp derivative improvement and revalidation of the complete
chain are recorded in the [current full-radius slice](zeta-full-radius-zero-free.md).
