# All squarefree-divisor families and exact Möbius compensation

The new modules are
[`ZetaRoughDivisorIncidence.lean`](../RiemannGaussian/ZetaRoughDivisorIncidence.lean)
and
[`ZetaRoughMoebiusIncidenceSource.lean`](../RiemannGaussian/ZetaRoughMoebiusIncidenceSource.lean).
They extend the checked prime-incidence bound to every nontrivial
squarefree divisor mark, and use the full truncated Möbius sum as an exact
source-preserving weight. The independent signed inequality for RH is open.

## Every bounded divisor family

Keep the original parameters

\[
u=\tfrac32-\Re\rho\in(\tfrac12,1),\quad q=u^{-1/4},\quad
D_N=\lfloor q^N\rfloor,\quad
R_N=\lfloor N\log(q)/8\rfloor^2,
\]

and the original small-prime set `S_N`, rough squarefree composite
coefficient `A_N(n)` and full complex polynomial kernel `K_N(n)`.
For each divisor mark `P`, let

\[
F_{N,P}=u^{N+1}\sum_{P\mid n}A_N(n)K_N(n).
\]

For **every** finite family of squarefree `1<P<=D_N^4` whose primes avoid
`S_N`, Lean proves

\[
\sum_{P\in T_N}|F_{N,P}|
\le C_\rho(1+N)\eta_\rho^N\longrightarrow0,
\qquad\eta_\rho=\frac{2u^{1/8}}{1+u^{1/8}}<1.
\]

The constant is uniform in the whole family. Thus every moving complex
weight family of norm at most one is controlled simultaneously. There is
no restriction on the number of distinct prime factors of a mark. The
bound concerns complete arithmetic series, with all roughness, squarefree
restrictions and phases retained.

The terminal theorems in `RoughDivisorIncidence` are
`exists_actual_sum_norm_bound` and `tendsto_actual_incidence`.

## Why all prime intersections fit

The complete squarefree intersection correction is bounded by the existing
least-common-multiple mass

\[
\mathcal L(P)=\frac1{\sqrt P}\sum_{d\mid P}\frac1{\sqrt d}.
\]

The new `sum_lcmSqrtFactorMass_le` proves

\[
\sum_{1\le P\le X}\mathcal L(P)
\le2\sqrt X\sum_{d\ge0}\exp\!\left(-\tfrac32\log d\right).
\]

The last sum is a fixed convergent constant. Lean uses `log(0)=0`, so the
displayed convention includes one harmless extra unit at `d=0`.
The proof interchanges the finite divisor sums and retains the divided
cutoff in each progression. Summing the full divisor correction first
avoids a worst-case divisor-count loss.

At every fixed Cauchy radius `r<1`, the complete general family bound is

\[
C_{y,r}D e^{4\sqrt R}\sqrt X(1+\log X)r^{-N}
\sum_{k\in\operatorname{supp}P}|P_k|r^{-k}.
\]

Only prime marks have an ordinary-prime correction. Its entire finite
absolute mass is included. Taking `X=D_N^4` and the existing radius
`r=(1+u^(1/8))/2` gives the displayed normalized rate.

## A mathematically fixed mask

Define

\[
M_Y(n)=\sum_{\substack{d\mid n\\d\le Y}}\mu(d),\qquad
\widehat A_{N,Y}(n)=M_Y(n)A_N(n).
\]

On the original nonzero support, every divisor is squarefree and avoids
`S_N`. Hence `M_Y` is exactly one plus the full bounded Möbius incidence
family. `coefficient_eq_add_fibres` and `hasSum_coefficient` establish the
coefficient identity and genuine convergence.

For **every moving cutoff** `1<=Y_N<=D_N^4`,

\[
\widehat C_N=u^{N+1}\sum_n M_{Y_N}(n)A_N(n)K_N(n)
\longrightarrow-m_\rho.
\]

The exact source comparison retains all signs. At every order,
`exists_response_error_bound` proves

\[
|\widehat C_N-\text{original full rough response}_N|
\le C_\rho(1+N)\eta_\rho^N\longrightarrow0.
\]

No numerical coefficients are chosen. The full Möbius divisor identity
proves that every compensated `n<=Y_N` vanishes exactly. In particular,
`Y_N=D_N^4` places this source beyond the fourth-power product cutoff.
The remaining integers keep their explicit mask; their weights are changed.

Lean also proves `M_Y(p*m)=M_Y(m)` whenever `p` is prime and `p>Y`.
Consequently every nontrivial complete cofactor `1<m<=Y` disappears.
These are exact algebraic cancellations, not separate decay assertions for
the old unweighted sectors.

## The square and logarithmic companion

At the original cutoff `Y=D`, put

\[
L_D(n)=\sum_{\substack{d\mid n\\d\le D}}\mu(d)\log d.
\]

On rough squarefree composites, Lean proves exactly

\[
A_{D,S}(n)=-M_D(n)\log n+L_D(n),
\]
\[
\boxed{M_D(n)A_{D,S}(n)
=-M_D(n)^2\log n+M_D(n)L_D(n).}
\]

The mask is real, so `M_D(n)^2` is a nonnegative real coefficient. The
whole expression still multiplies the original complex kernel. The mixed
logarithmic term remains explicit. The subsequent
[mixed-term decay theorem](zeta-rough-moebius-mixed-decay.md) independently
bounds it and transfers the full source to the square. The strict signed
upper bound on that remaining oscillatory sum is still open.

This is an exact use of classical Möbius/divisor algebra; no mathematical
priority claim is made.

## Remaining obligation

For any admissible cutoff sequence, an independent bound
`Re(response_N)>=-1+epsilon` for a fixed `epsilon>0` on a cofinal subsequence
would contradict the proved limit. `false_of_cofinal_response_bound`
formalizes that implication, with the arithmetic premise still open.

The earlier [balanced source with weight `1-k_N`](zeta-rough-prime-incidence.md)
remains separately available. Its factor support and error estimates are
not automatically inherited by the new Möbius mask. Nor is an additional
physical-window restriction free.

No additional zero is excluded. The all-height edge width remains
`1/(10 log(|t|+2))`, and RH is open.
