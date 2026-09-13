# Removing the entire nonsquarefree Vaughan band

[Lean module](../RiemannGaussian/ZetaSquarefreeVaughanProjection.lean)
· [Larger cutoff budget](zeta-vaughan-cutoff-budget.md)
· [Theorem explorer](theorem-explorer/)

The complete signed contribution from nonsquarefree integers in the
original finite Vaughan band has independently vanishing source-normalized
size. The cutoff remains `D_N=floor(u^(-N)/(N+1))`. The surviving squarefree
band retains the full conditional zero source. Its independent cofinal
signed lower bound and RH remain open.

## The actual deletion

Let `b(U,V)=mu_(>U)*kappa_V` be the original Vaughan coefficient and
`B_N=zetaPrimeLogBand N`. For every fixed complex polynomial `p`, real
`0<u<1` and fixed ordinate `abs(y)>1`, Lean proves

\[
 u^{N+1}\sum_{\substack{n\in B_N\\n\text{ not squarefree}}}
 b(D_N,D_N;n)K_{p,N}(3/2+iy,n)\longrightarrow0.
\]

`tendsto_nonsquarefree_band` assumes no zero. It concerns the entire moving
band, including its original endpoints. It bounds the absolute value of
the signed sum through independently vanishing allowances; it does not
assert decay of the sum of absolute values. No term is deleted because
its phase is inconvenient.

For any hypothetical nontrivial zero `rho=beta+i*gamma`, `beta>1/2`, take
`u=3/2-beta` and the original `zetaRightHalfPoleJetFilter`. Then
`tendsto_actual_squarefree_band` proves

\[
 u^{N+1}\sum_{\substack{n\in B_N\\n\text{ squarefree}}}
 b(D_N,D_N;n)K_{p,N}(3/2+i\gamma,n)\longrightarrow-m_\rho.
\]

All Möbius signs and product phases remain. A factorization of a surviving
squarefree integer has squarefree, coprime factors. The negative source
still requires the hypothetical zero; it is not an independent lower bound.

## Paying the complete reciprocal Euler correction

The actual squarefree quotient is `Q(s)=zeta(s)/zeta(2*s)`. Its marked
Euler atom is

\[
 A_s(a)=\prod_{p\mid a}\frac{p^{-s}}{1+p^{-s}}.
\]

For squarefree `a` and `Re(s)>=1/2`, Lean expands every reciprocal-factor
correction before averaging:

\[
 |A_s(a)|\leq\frac1{\sqrt a}
   \sum_{d\mid a}\frac{\tau(d)^2}{\sqrt d},\qquad
 \sum_{\substack{a\leq U\\a\text{ squarefree}}}|A_s(a)|
 \leq2\sqrt U\,\mathcal D(3/2),
 \quad \mathcal D(3/2)=\sum_{d\geq1}\frac{\tau(d)^2}{d^{3/2}}<\infty.
\]

The existing divisor-square Dirichlet theorem supplies genuine convergence.
The finite divisor expansion and the bound for multiples supply the
square-root cutoff scale. No pointwise `a^epsilon` loss is introduced.
Chebyshev prime density also gives
`sum_(p<=V) log(p)*norm(A_s(p)) <= 12*sqrt(V)`.

`coprimeCoefficient_eq_projected_convolution` identifies the exact
squarefree projection of `mu_(<=U)*Lambda_(<=V)*1` with the full coprime
marked family. Its analytic multiplier is

\[
 \sum_{\substack{a\leq U,\ a\text{ squarefree}\\
                   p\leq V,\ p\text{ prime},\ (a,p)=1}}
     \mu(a)\log p\,A_s(ap).
\]

The equality retains coprimality, divisibility, signs and complex phases.
Only the subsequent upper bound drops the coprimality constraint. The
multiplier has bound `24*D(3/2)*sqrt(U)*sqrt(V)` on the closed half-plane.
Cauchy estimates for the actual analytic quotient on the unit disc at
`3/2+iy` give the full filtered square-root product budget. Absolute
convergence and the arithmetic-to-analytic equality are proved before
this estimate is applied.

## The other projected terms and the finite band

The squarefree projection of `mu_(<=U)*log` is exactly a sum of marked
responses weighted by `log(n)-log(a)`. Uniform marked Euler bounds give

\[
 |\text{projected head-log filter}|
 \leq C_{p,y}\,U\bigl(N+1+\log(U+1)\bigr)r_y^{-N},\qquad r_y>1.
\]

It decays after normalization even when `U<=u^(-N)`. That larger allowance
belongs to this term alone; the full cross term still uses the damped
cutoff. The finite projected prime head has bound
`3*sqrt(V)*sum_k norm(p_k)`.

All three projected small terms therefore decay independently at `D_N`.
Together with the already proved full Vaughan small-term decay and proper
prime-power decay, this removes the whole nonsquarefree response. The
existing uniform divisor-log majorant transports the conclusion to the
same finite band with its original vanishing tail error.

## Scope and remaining target

This applies classical Euler products, divisor expansions, Chebyshev
density and Cauchy estimates. No historical novelty, larger zero-free
region, arbitrary-coefficient Type II estimate, or height-uniform
constant is claimed. The averaged atom bound is uniform in the full closed
half-plane; the filtered constants may depend on the fixed ordinate and
polynomial. Moving filters require their own budget.

The remaining task is a cofinal real lower bound for the surviving
squarefree signed band strictly above `-m_rho`. Its divisor parity,
coprime factor structure and logarithmic phases are available for that
attack. The deletion theorem does not yet control those correlations.

| Compiled theorem | Role |
|---|---|
| `sum_squarefree_norm_atom_le` | Average all reciprocal local factors |
| `coprimeCoefficient_eq_projected_convolution` | Exact arithmetic cross term |
| `tendsto_projected_cross_linearDampedCutoff` | Independently pay its full cost |
| `tendsto_projected_head_log` | Pay all physical and divisor logarithms |
| `tendsto_projected_small_linearDampedCutoff` | All three projected small terms |
| `tendsto_nonsquarefree_bilinear` | Remove the entire nonsquarefree response |
| `tendsto_nonsquarefree_band` | Independent deletion in the original finite band |
| `tendsto_actual_squarefree_band` | Preserve the full conditional zero source |
