# A signed bound for the whole five-prime class

The later [exact five-prime reserve](zeta-riesz-five-prime-reserve.md)
evaluates the positive coefficient and proves its debit never exceeds the
clipped bound below. It is integrated into the same compensated joint
inequality; the weighted aggregate estimate remains open.

[`ZetaRieszFivePrimeFloor`](../RiemannGaussian/ZetaRieszFivePrimeFloor.lean)
proves an independent upper bound for the actual five-prime coefficient.
It applies to the entire class in the core, including small prime factors.
It uses no zero hypothesis, prime-density approximation, or completed
cofactor. The whole joint arithmetic floor remains open.

Write `T=log n`, let `P=largestPrime n`, let
`Q=largestPrime (n/P)`, and let `r=minFac n`. Put

\[
A=2\log P+T-3L,\qquad B=\log P-\log Q+T-2L.
\]

For every integer with exactly five distinct prime factors, `0<L`, and
`2T/3<=L<=3T/4`, `actual_five_upper_gap` proves

\[
\boxed{\quad \Re c_L(n)\le\frac TL\max(0,\min(A,B)).\quad}
\]

`actual_five_upper_clipped` sharpens this using the existing antichain
estimate, retaining the least prime instead of replacing it by a mean:

\[
\boxed{\quad
\Re c_L(n)\le\frac TL H_L(n),\qquad
H_L(n)=\min\{3\log r,\ \max(0,\min(A,B))\}.
\quad}
\]

Nonsquarefree labels have coefficient zero, exactly as before. These are
upper bounds, not assertions that the coefficient itself is nonnegative.
The least-prime cap is optional strengthening of the same inequality;
it is not an absolute-value replacement for the signed carrier.

## The sign restriction is now proved

`coefficient_five_nonpos` proves the complete coefficient nonpositive if
either `A<=0` or `B<=0`. Consequently a positive coefficient requires both
strict gaps. On the original eventual length and core window,

\[
137N/100\le L\le7N/5,\qquad39N/20<T\le203N/100,
\]

`positive_five_core_geometry` gives the uniform necessary conditions

\[
\log P>\frac{104}{203}T,\qquad
\log P-\log Q>\frac{71}{203}T.
\]

In particular all balanced five-prime labels with `log P<=T/2` have
nonpositive arithmetic coefficient. They are favorable on negative-cosine
observations, the same observations on which positive triple coefficients
are adverse. This proves a sign relation, **not** that the favorable
population has sufficient weighted mass to pay the triples.

## Why it holds

Reflect to `D=T-L`. Five-prime parity gives `-R_L(n)=R_D(n)`.
If `log P>=D`, exact prime insertion leaves the four-prime cofactor at
the same cutoff. The new four-prime inequality bounds its response by
both its radial gap and its largest-prime gap. Those become `A` and `B`.

The central four-prime chamber is nonpositive. When all five prime logs
are below `D`, only the unit, single-prime and pair divisors can survive;
their complete signed sum is nonpositive as well. Finite hinge budgets
prove these statements with all boundary equalities retained. No sign is
inferred from the numerical samples.

The least-prime cap reuses the existing two-smallest-prime Sperner bound.
For five primes the remaining three-factor middle layer has size three,
so the response costs at most `3*log r`. Only the resulting upper bound
is used; the actual negative coefficient and favorable observation remain.

## The combined core inequality

Let `f_N(n)` be the original complex residual atom and `w_N(n)` its
nonnegative factorial weight including `1-boundedShare`. On `cos(yT)<=0`,
`re_five_atom_ge_keep_positive` proves

\[
\Re f_N(n)\ge
\max(\Re f_N(n),0)-w_N(n)\frac TL H_L(n)(-\cos(yT)).
\]

`eventually_re_core_ge_four_five_credit` applies this together with the
existing four-prime gap bound to the **same complete core sum**, uniformly
in the height and count endpoint. It retains:

- every positive four-prime and negative-cosine five-prime observation;
- the signed five-prime observations at positive cosine;
- the entire signed sum of all other prime counts.

The comparisons introduce no completion error and spend no compensation
supply. The displayed debits have not been bounded after source
normalization. The sufficient target remains the cofinal joint
`-79/1000-o(1)` floor for `J_N+C_N`; separate decay is unnecessary.

## Quantitative diagnostic, not a source estimate

The optional [capacity probe](../scripts/probe_riesz_joint_capacity.py)
and [recorded output](riesz-joint-capacity-probe.json) now compare the
proved two-gap allowance and its least-prime cap in the same exploratory
rough-sector density model. At `N=65536`, two Sobol scrambles give:

| Quantity | Seed 17 | Seed 29 |
| --- | ---: | ---: |
| Actual positive coefficient mass in the model | 0.00629 | 0.00638 |
| Two-gap upper cost | 0.02716 | 0.02375 |
| Upper cost after least-prime cap | 0.01686 | 0.01586 |
| Negative coefficient mass in the model | 0.43133 | 0.43075 |

These quantities omit the common radial factor and precede the phase.
The model fixes `T=2N`, replaces prime counts by densities, and omits small
primes and counts above nine without a tail bound. It is neither a literal
signed-sum bound nor a certified numerical integral. The Lean proof uses
none of these numbers. Comparing the actual signed populations, with all
remaining counts and observations present, is still the arithmetic task.
