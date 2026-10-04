# Full Selberg convolution: a strict continuous countertest

The unchanged target is an independent cofinal
`Re prefixPairDefect <=399/5000+o(1)` for the actual ordinary-prime sum.
This slice proves **no new arithmetic floor saving**. It checks whether
positivity, common-phase factorial moments and the full second logarithmic
convolution would suffice. They do not suffice without additional
arithmetic restrictions.

The checked leaf is
[`ZetaRieszSelbergRenewalAudit.lean`](../RiemannGaussian/ZetaRieszSelbergRenewalAudit.lean).
It contains a continuous rational test, not a replacement carrier or an
ordinary-prime counterexample. Every preceding payment, no-go and proof
snapshot remains available.

## Algebra before numerical sampling

Put `beta=3/2-u`, `alpha=2-2u`, and define

\[
f(T)=e^T+e^{\alpha T}-2e^{\beta T}\cos(yT).
\]

The exact square identity is

\[
f(T)=\left(e^{T/2}-e^{(1-u)T}\right)^2
     +2e^{\beta T}(1-\cos(yT))\ge0.
\]

Its prime-density interpretation is the continuous measure
`f(T)dT/T` on `T>0`; no ordinary primes are assigned to it.
`numerator_laplace_expansion`, `phaseMoment_eq` and
`array_eq_phaseMoment` prove genuine integrability and the exact
common-phase logged factorial moments at every order, including zero:

\[
a_k=u^{k+1}\int_0^\infty
 \frac{T^k}{k!}e^{-(3/2+iy)T}f(T)\,dT
 =\left(\frac{u}{1/2+iy}\right)^{k+1}
 +\left(\frac{u}{2u-1/2+iy}\right)^{k+1}
 -1-\left(\frac{u}{u+2iy}\right)^{k+1}.
\]

The four original factorial slots are retained: central, successor,
logged prefix and full trace. The optional probe compares those slots
with their exact harmonic collection before inspecting values. Swapped
incidences use complementary indices of the same array; there is no
independent per-leg phase substitution.

## Full second convolution, not just a normalized trace

The rational count transform and its logarithmic derivative are

\[
F(s)=\frac{(s-\beta-iy)(s-\beta+iy)}{(s-1)(s-\alpha)},
\qquad
Z(s)=-\frac{F'(s)}{F(s)}
 =\frac1{s-1}+\frac1{s-\alpha}
   -\frac1{s-\beta-iy}-\frac1{s-\beta+iy}.
\]

`neg_logDeriv_countSymbol` proves this exact logarithmic-derivative
identity. `selbergKernel_laplace` proves, with integrability before
interchanging integrals,

\[
Z(s)^2-Z'(s)=\int_0^\infty e^{-sT}
 \left[Tf(T)+\int_0^T f(v)f(T-v)\,dv\right]dT.
\]

The joined real kernel is nonnegative. The selected double pole in
`Z^2-Z'` cancels exactly, as shown by
`selberg_selected_double_pole_cancels`. Its remaining simple pole is
`-2h(s)/(s-beta-iy)`, with

\[
h(s)=\frac1{s-1}+\frac1{s-\alpha}-\frac1{s-\beta+iy}.
\]

These are full continuous convolution identities. They are **not** the
literal integer identity `mu*log^2=Lambda*log+Lambda*Lambda`.

## The weighted joined residue still exceeds the target

For `1/2<=u<=10001/20000` and every fixed `abs(y)>=54`, Lean proves
`a_k -> -1`. Applying the already-checked continuity theorem to the
whole joined functional gives

\[
Q_N(a)\longrightarrow1-c_{\rm ret}(u)>399/5000.
\]

`eventually_joined_gt_target` proves the eventual strict inequality.
`cofinal_generic_floor_impossible` also rules out a cofinal
`399/5000+err_N` upper bound for this model when `err_N -> 0`.
The proof does not rely on numerical threshold crossings.

At `u=10001/20000`, `y=54`, the optional 100-digit regression gives:

| Order N | Re of joined model |
| ---: | ---: |
| 640 | 0.057372765927263925 |
| 8192 | 0.077551988267263505 |
| 65536 | 0.079522689496597419 |
| 196608 | 0.079744966250948827 |
| 425984 | 0.079809858576337171 |
| 1048576 | 0.079845024199341731 |
| Limit | 0.079871797034944178 |

The sampled violation at 425984 is not a certified first crossing or an
entry order for literal primes. The unchanged `0.000071797...` is the
contradiction margin, not measured unpaid mass or progress toward the
floor. Larger orders use the explicit moving-length interval

\[
0\le L_N-[-2N\log u-2\log(N+1)]\le4(N+1)u^N;
\]

the report labels this approximation and its effect on the evaluation.
It separately bounds the omitted geometric channels and does not present
that bound as a certification of finite-precision roundoff. Small-order
regressions compute all original factorial slots directly.

## Exact difference from ordinary arithmetic

The model has an extra real pole at `alpha`, which ordinary zeta does not
have. Its count transform is exactly

\[
F(s)=1+\frac{y^2+(u-1/2)^2}{(s-1)(s-\alpha)}.
\]

Its residue at one is

\[
\frac{y^2+(u-1/2)^2}{2u-1}\ge29160000
\]

on the strict requested radius/height range; at the probe endpoint it is
`29160000.000025`. `countSymbol_eq_one_add` and
`count_normalization_mismatch` prove these distinctions. Ordinary integer
counting has residue one. This synthetic failure does not refute a bound
which uses those missing literal arithmetic properties, the absence of
the extra pole, or the already-proved zero-free regions. Normalizing one
constant alone is not proved to yield the floor either.

There is a relevant classical route using more than generic positivity.
The formal Selberg proof in Isabelle/AFP keeps exact integer divisor
counting and factorial identities before deriving the asymptotic
convolution formula. Its final `O(x)` error is not the fixed-power saving
needed by our source normalization. This is literature context, not an
imported Lean estimate or a proof that its weighted version closes our
floor. [Selberg asymptotic formula, Isabelle/AFP](https://isa-afp.org/browser_info/current/AFP/Prime_Distribution_Elementary/Selberg_Asymptotic_Formula.html).

## What this test permits next

Stop the generic continuous Selberg-positivity route. Any next bound must
retain a further **proved constraint on the actual ordinary-prime or
ordinary-integer convolution**, with the current correlated factorial
weights. An unweighted trace cancellation, count-by-count allowance or
another equivalent formula does not fund the missing weighted residue.
The current full-prime-power bridge permits the literal integer Selberg
identity to be used; it does not itself estimate its signed, weighted
central/successor remainder.

The absolute all-height floor and higher-multiplicity ceiling remain
open. No new zero exclusion is claimed. Validation is limited to the
leaf, namespace lint, transitive axiom audit and this optional synthetic
probe. There is no root registration, commit, push or wider CI gate.
