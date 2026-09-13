# Exact Vaughan averaging and Möbius reflection

[Averaging and reflection proofs](../RiemannGaussian/ZetaVaughanLogAverage.lean)
· [Actual finite-band source](../RiemannGaussian/ZetaSquarefreeVaughanLogSource.lean)
· [Independent cutoff budget](zeta-squarefree-vaughan-budget.md)
· [Theorem explorer](theorem-explorer/)

The genuine logarithmic average of the original two-cutoff Vaughan
coefficient now equals one explicit signed Möbius divisor sum. Its
measurable floor cells, normalization, prime correction and independent
error budget are proved. The entire original finite band retains the
conditional source `-m_rho`. The independent signed lower bound and RH
remain open; this slice gives no larger zero-free region.

## An identity for every arithmetic profile

For every function `w : Nat -> Real`, Lean proves

\[
\sum_{d\mid n}\ \sum_{ab=d}\mu(a)\Lambda(b)
 [w(d)-w(a)-w(b)]
=-\log n\sum_{d\mid n}\mu(d)w(d)-\Lambda(n)w(n).
\]

`sum_profile_eq` has no positivity, smoothness or chosen-family hypothesis
on `w`. It follows from the complete identities
`mu*Lambda = -mu log`, `Lambda*1 = log` and `mu*1 = delta`, where `*`
means Dirichlet convolution. All ordered factors and signs are retained.
This general interface permits other profiles without a coefficient search;
it supplies an identity, not an estimate of its signed terms. No historical
novelty is claimed for these convolution identities.

## The actual cutoff integral

Write `b(U,V;n)` for the existing Vaughan bilinear coefficient and put

\[
\begin{aligned}
\mathcal A_L(n)
 &=\int_0^L b(\lfloor e^t\rfloor,\lfloor e^{L-t}\rfloor;n)\,dt,\\
R_L(n)&=\sum_{d\mid n}\mu(d)(L-\log d)_+.
\end{aligned}
\]

Here `x_+ = max(0,x)` and `L >= 0`. The formal integral is over the
closed real interval. Its strict factor-cutoff fibres are open intervals;
their endpoint equivalence under Lebesgue measure is proved, not sampled.
`integral_cutoff_pair` evaluates each entire clipped fibre. The resulting
coefficient identity is

\[
\boxed{\mathcal A_L(n)
 =-\log n\,R_L(n)+\Lambda(n)\min(L,\log n).}
\]

`logarithmicAverage_eq_riesz` includes zero, the unit and every prime
power. On squarefree composites, `Lambda(n)=0` and only the signed Riesz
term remains. On primes the two displayed terms cancel exactly.

The cells are the literal sets

\[
E_{L,U,V}=\{t\in[0,L]:
 \lfloor e^t\rfloor=U,\ \lfloor e^{L-t}\rfloor=V\}.
\]

They form a finite measurable partition independent of `n`.
For `L>0`, their exact weights `|E_(L,U,V)|/L` are nonnegative and sum
to one. `integral_eq_cell_sum` and `logarithmicAverage_div_eq_mixture`
identify the continuous average with this finite mixture. Neither an edge
cell nor an integer at a floor boundary is omitted.

## Independent budget and the original source

Each nonempty cell obeys

\[
(U+1)(V+1)\le 2(e^L+1).
\]

For `0<u<1`, use the concrete schedule

\[
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
\qquad L_N=\log((D_N+2)^2).
\]

Every length is positive, including the early orders. Each cell's
square-root product budget is at most `2*(D_N+2)`. The weighted average
budget, multiplied by `u^(N+1)`, tends to zero independently of any zero
hypothesis (`tendsto_average_budget`). This uses the general paid-mixture
theorem; it does not assert that these cells lie in the smaller previously
displayed region `(U+1)*(V+1)<=(D_N+1)^2`.

Define the actual composite coefficient

\[
c_L(n)=\mathbf1_{n\ {\rm squarefree},\ n\ {\rm composite}}
       \frac{-\log n\,R_L(n)}{L}.
\]

The Lean definition also permits the unit, whose logarithm is zero.
`coefficient_eq_mixture` identifies it with the entire squarefree Vaughan
mixture; its original divisor-log majorant remains valid.
At a hypothetical nontrivial right-half zero `rho=beta+i*gamma`, with
`u=3/2-beta` and the original fixed pole-jet polynomial `p`, Lean proves

\[
u^{N+1}\sum_{n\in\mathrm{original\ band}_N}
c_{L_N}(n)K_{p,N}(3/2+i\gamma,n)\longrightarrow-m_\rho.
\]

This is `tendsto_actual_riesz_band`. The band, complex phases,
normalization and analytic multiplicity are unchanged. The negative limit
is conditional on the hypothetical zero and is not an independent lower
bound.

## The surviving prime structure

Divisor reflection retains the full squarefree parity:

\[
\boxed{R_{\log n-L}(n)=\mu(n)R_L(n)}
\]

for every nonunit squarefree composite (`riesz_reflection`). Thus odd
Möbius parity makes the profile antisymmetric about `log(n)/2` and forces
exact cancellation there. More strongly, for every `0<L<=log(2)`,

\[
\mu(n)=-1\quad\Longrightarrow\quad
R_L(n)=L,\qquad R_{\log n-L}(n)=-L.
\]

`riesz_opposite_edges` proves these exact opposite values for the entire
odd-parity squarefree composite class. The remaining signs are therefore
structural, even before multiplication by the complex zeta kernel.
This rules out a pointwise one-sign argument for the whole Riesz profile.
It does not rule out cancellation in the complete arithmetic sum.

The reflection is `B -> n/B`: it depends on the integer being tested.
Replacing the common `L_N` by `log(n)/2` inside the source sum is **not**
licensed by the mixture theorem, whose weights must act on whole cutoff
pairs independently of `n`. Such a replacement needs a new source-error
estimate before its midpoint cancellation can be used.

Completing the squarefree composite sum restores exactly

\[
\mathbf1_{n\ {\rm prime}}\,
\frac{\log n\,\min(L,\log n)}{L}.
\]

`coefficient_eq_completed_with_prime` keeps this endpoint explicitly. A
bound for the completed divisor sum alone is not a bound for the
composite restriction. The remaining sufficient target is still only a
cofinal real lower bound with a fixed positive margin above `-m_rho` for
the full normalized signed band. Pointwise positivity, the conditional
source limit and an unpaid integer-dependent reflection do not supply it.

| Compiled theorem | Role |
|---|---|
| `VaughanLogAverage.sum_profile_eq` | Complete signed identity for every arithmetic profile |
| `VaughanLogAverage.logarithmicAverage_eq_riesz` | Exact floor integral and full prime-power correction |
| `VaughanLogAverage.integral_eq_cell_sum` | Measurable finite partition, independent of the tested integer |
| `VaughanLogAverage.riesz_reflection` | Full Möbius parity under divisor reflection |
| `VaughanLogAverage.riesz_opposite_edges` | Exact opposite values throughout the odd-parity class |
| `SquarefreeVaughanLogSource.coefficient_eq_completed_with_prime` | Ordinary-prime correction under completion |
| `SquarefreeVaughanLogSource.tendsto_average_budget` | Independent decay of the complete average budget |
| `SquarefreeVaughanLogSource.tendsto_actual_riesz_band` | Original finite-band source with every averaging premise discharged |
