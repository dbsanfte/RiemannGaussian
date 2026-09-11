# Global control of the Gaussian Fermi zero side

This slice extends the [ideal Fermi reflection theorem](fermi-reflection-zero-free-plan.md)
from a positive finite band to an absolutely convergent lower bound for the
complete paired real zeta zero sum, with a quantitative allowance that
vanishes uniformly over every admissible moving Gaussian scale. It does not prove the smoothed prime
explicit formula, a new numerical zero-free region, the external `4.896`
constant, or RH.

The new root-imported modules are
[GaussianFermiDerivativeBounds](../RiemannGaussian/GaussianFermiDerivativeBounds.lean),
[GaussianFermiPairDecay](../RiemannGaussian/GaussianFermiPairDecay.lean),
[GaussianFermiZeroTail](../RiemannGaussian/GaussianFermiZeroTail.lean),
[GaussianFermiZeroTailRate](../RiemannGaussian/GaussianFermiZeroTailRate.lean), and
[GaussianFermiMovingAllowance](../RiemannGaussian/GaussianFermiMovingAllowance.lean).

## Retaining the Fermi factor avoids an exponential loss

For `a >= 0`, `b > 0`, write

```text
f(u) = exp(-b*u^2)/(1+exp(-a*u)),
F(z) = integral_(u>0) f(u)*exp(-z*u) du,
h_x(u) = exp(-b*u^2-x*u)/(1+exp(-a*u)).
```

Let `delta >= 0`, `delta^2 <= b`, and `-delta <= x <= a+delta`.
The Fermi factor bounds the negative half-line as well as the positive one:

```text
0 < h_x(u) <= exp(-b*u^2+delta*abs(u))
          <= exp(1/2)*exp(-(b/2)*u^2).
```

The exact first two derivatives are retained before taking absolute values.
For the original Fermi function `q(v)=1/(1+exp(v))`, both
`abs(q'(v)) <= q(v)` and `abs(q''(v)) <= q(v)` are proved. Thus the
negative-time decay remains present in each derivative estimate. Replacing
the Fermi factor by `1` too early would instead introduce a large
exponential cost in `1/b`.

`abs_damped_orders_le_envelope` gives one common envelope for the actual
amplitude and its two derivatives. `envelope_le_simple` replaces that
polynomial envelope by the simpler Gaussian

```text
A(a,b,delta)*exp(-(b/4)*u^2),
A(a,b,delta)=exp(1/2)*(34*b+2*(2*a+delta)^2+1).
```

All three orders are genuinely integrable on the full real line. The
second derivative has the explicit absolute-integral bound

```text
integral_R abs(h_x''(u)) du <= C(a,b,delta),
C(a,b,delta)=A(a,b,delta)*sqrt(pi/(b/4)).
```

The cost is explicit and algebraic in the inverse Gaussian scale; there is
no exponential factor depending on `a^2/b`.

## Two exact integrations by parts

For the angular-frequency transform

```text
J(h,y)=integral_R h(u)*exp(-i*y*u) du,
```

Lean proves `J(h'',y)=(i*y)^2*J(h,y)`. Integrability of the original signal
and derivatives discharges both endpoint limits through the full-line
fundamental theorem of calculus. No boundary terms are assumed to vanish.

The previous complex reflection identity identifies

```text
F(z)+F(a-z)=J(h_(Re(z)),Im(z)).
```

Therefore `im_sq_mul_norm_pair_le` proves

```text
Im(z)^2 * norm(F(z)+F(a-z)) <= C(a,b,delta).
```

For the physical same-phase pair, the checked identity
`F(a-conj(z))=conj(F(a-z))` identifies only the real parts of the two pairs.
For `Im(z) != 0`, the actual conclusion is

```text
abs(Re(F(z)+F(a-conj(z)))) <= C(a,b,delta)/Im(z)^2.
```

The module does not assert this inverse-square bound for the complex norm
of the physical same-phase pair.

## Actual zeta zeros and analytic multiplicities

For `1/2 <= sigma <= 1`, choose `a=2*sigma-1`, `delta=1-sigma`, with
`delta^2 <= b`. Every genuine nontrivial zero `rho=beta+i*gamma` satisfies

```text
-delta < Re(s-rho) < a+delta,       s=sigma+i*t.
```

Define the real contribution

```text
Q(rho)=m(rho)/2 * Re(F(s-rho)+F(s-(1-conj(rho)))),
```

where `m(rho)` is the actual analytic multiplicity. The factor `1/2` records
the normalization for summing pairs over the entire zero divisor. No
identity with an unpaired complex sum or with the prime side is assumed.

If `H >= max(2*abs(t),1)` and `abs(gamma)>H`, elementary separation gives

```text
1+gamma^2 <= 8*(t-gamma)^2,
abs(Q(rho)) <= 4*C(a,b,delta)*m(rho)/(1+gamma^2).
```

The repository's existing unconditional inverse-square divisor theorem
proves that the majorant is summable, with multiplicities. Consequently
the genuine outside-band contribution is absolutely summable and

```text
abs(sum_(abs(gamma)>H) Q(rho)) <= 4*C(a,b,delta)*W(H),
W(H)=sum_(abs(gamma)>H) m(rho)/(1+gamma^2).
```

`tendsto_divisorTail` proves `W(H)->0`. The bounded-height contribution has
finite support in the actual analytic divisor, so the full paired real
sum is also absolutely convergent.

## Global bound on the interior evaluation line

Let `m(H)=zetaPoleReserveZeroMargin H` be the existing proved zero-free
width and put `sigma_H=1-m(H)`. The prior reflection theorem proves
`Q(rho)>=0` for every `abs(gamma)<=H`. Combining both pieces,
`global_zero_side_lower_bound` proves the actual full lower bound

```text
sum_rho Q(rho) >= -4*C(2*sigma_H-1,b,1-sigma_H)*W(H),
```

under the explicit conditions `b>0`, `H>=max(2*abs(t),1)` and `m(H)^2<=b`.
Every zero is included. This is a causal transport from the repository's
known zero-free region to a global smoothed zero-side estimate.

## Quantitative tail from the actual xi-growth bound

`W(H)->0` alone does not prove that the full error allowance vanishes when
`b` also shrinks: its coefficient contains an inverse square root of `b`.
The existing
[dyadic inverse-square estimate](../RiemannGaussian/GaussianXiInverseSquareSummability.lean)
has a multiplicity count of exponent `3/2`. The new `divisorTail_le_majorant_tail`
partitions the actual height tail over complete norm shells, retaining every
analytic multiplicity. For `2^N <= H`, the genuine height condition forces
the norm shell index to be strictly greater than `N`. The old geometric
majorant therefore yields

```text
W(H) <= C0 * exp(-(log(2)/2)*N),       2^N <= H.
```

`majorant_tail_geometric` extracts this exact factor from the complete
infinite shell sum. Choosing adjacent dyadic bounds around each real height,
`exists_divisorTail_sqrt_bound` proves

```text
there exists C > 0 such that W(H) <= C/sqrt(H) for every H >= 1.
```

The constant is independent of the Gaussian scale and evaluation ordinate.
It comes from the repository's unconditional `riemannXi_threeHalvesGrowth`
theorem, not an assumption on zero locations or on the prime-tail frontier.

## The full allowance vanishes uniformly

Put `delta=m(H)`, `sigma_H=1-delta`, and `a=1-2*delta`. The existing margin
satisfies `0<delta<1/4`. For every scale `delta^2 <= b <= 1`,
`integralCost_le_inverse_margin` proves

```text
C(1-2*delta,b,delta) <= 86*exp(1/2)*sqrt(pi)/delta.
```

This follows from `2*a+delta=2-3*delta`, the explicit derivative polynomial,
and `sqrt(b)>=delta`. The old proved zero-free width gives

```text
1/m(H) <= (7625/792)*log(H+2),        H >= 1.
```

Combining these with the actual tail rate, `exists_uniform_allowance_bound`
gives a single constant `K>0` such that

```text
E(b,H) = 4*C(1-2*m(H),b,m(H))*W(H)
       <= K*log(H+2)/sqrt(H) -> 0,
```

uniformly for every `m(H)^2 <= b <= 1`. The theorem
`tendsto_allowance_of_admissible` covers every moving choice `b(H)` eventually
inside that range; it assumes no continuity or other regularity of the choice.
Here decreasing `b` broadens the real-time Gaussian `exp(-b*u^2)`.

Finally, `exists_uniform_zero_side_bound` transports the same rate to
the actual signed sum:

```text
abs(sum_(abs(gamma)>H) Q(rho)) <= K*log(H+2)/sqrt(H),
sum_rho Q(rho) >= -K*log(H+2)/sqrt(H),
```

uniformly also in all ordinates satisfying `2*abs(t)<=H`.
`eventually_zero_side_ge_neg` proves that, for each `epsilon>0`, every
admissible scale and ordinate eventually has full zero side at least
`-epsilon`. No zero is dropped without paying its allowance. The evaluation
line is still `sigma_H=1-m(H)`; this statement does not exclude a further
zero or move the line to `1/2`.

## Precise remaining work

The moving-scale zero-side allowance is now closed. A numerical use of its
rate would also need an explicit numerical value for the xi-growth constant.

The [subsequent exact-mixture slice](gaussian-fermi-explicit-mixture.md)
now identifies the Fermi zero side with an absolutely convergent spectral
average of the unconditional Gaussian arithmetic explicit formula. The
kernel representation and whole-zero interchange are proved, and this
vanishing lower allowance transfers to that arithmetic average.

The [literal-prime and phase continuation](gaussian-fermi-prime-phase-budget.md)
now proves prime-series convergence and evaluation, exact pole and constant
terms, and an integrable gamma average. Every admissible finite cosine test
gives the whole prime series the favorable sign and retains a selected
finite zero set in the budget. The [gamma continuation](gaussian-fermi-gamma-bound.md)
now supplies an explicit quarter-logarithm upper bound, uniform over all
admissible shrinking scales. The [resonant continuation](gaussian-fermi-resonant-budget.md)
also proves Gaussian pole and target-pair bounds. The
[independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now proves a stronger eventual exclusion, with exact coefficient `3/20`
and an existential height threshold. The independent signed ordinary-prime-tail
bound in the original RH reduction is a different, still open arithmetic
obligation.

## Local verification

All local gates passed for the quantitative-tail checkpoint: strict direct
elaboration of both new modules, focused builds, the full warning-as-error
build (10,119 jobs), all 14 declaration linters, 13 terminal axiom audits,
the whole-project declaration lint, the compiled-environment soundness
generator, and source/whitespace checks. Its inventory contained 1,272 modules,
zero project axioms and zero declarations depending on placeholders.
Audited theorems use only `propext`, `Classical.choice` and `Quot.sound`.
README links, table formatting and the 500-character direction limit also
pass. These are local validation results; remote CI is checked separately on the exact commit.
