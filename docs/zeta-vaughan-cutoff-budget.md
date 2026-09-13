# A larger independently paid Vaughan cutoff

[Lean module](../RiemannGaussian/ZetaVaughanCutoffBudget.lean)
· [Exact original decomposition](zeta-vaughan-reduction.md)
· [Theorem explorer](theorem-explorer/)

The full small-factor contribution now has a square-root product budget.
This permits larger cutoffs in the **same** finite arithmetic band. The
independent lower bound for the surviving signed band and RH remain open.

## The independent estimate

Write `M_U(s)=sum_(n<=U) mu(n)*n^(-s)` and
`A_V(s)=sum_(n<=V) Lambda(n)*n^(-s)`, with the definitions and positive
integer conventions of `ZetaVaughanReduction`. On `Re(s)>=1/2`, Lean proves

\[
 |M_U(s)|\leq 2\sqrt U,\qquad |A_V(s)|\leq12\sqrt V.
\]

The second inequality uses the actual Chebyshev bound for `psi`, followed
by finite partial summation. It includes all prime powers. Replacing
`Lambda(n)` by `log(n)` before summing would lose this density information.
The prime-density and partial-summation ingredients are classical, not
claimed new mathematics.

The exact small response remains

\[
 A_V+M_U(-\zeta')-M_U A_V\zeta.
\]

At `s0=3/2+i*y`, `abs(y)>1`, its original factorial filter obeys

\[
 \left|\mathrm{smallFilter}_{p,U,V,N}(s_0)\right|
 \leq C_y\sqrt{U+1}\sqrt{V+1}
       \sum_{k\in\operatorname{supp}p}|p_k|.
\]

The constant is independent of the moment order and both cutoffs.
Every fixed complex polynomial is allowed; no filter-root condition or
zero hypothesis enters this bound. The richer three-term signed identity
is retained upstream of this estimate. The product multiplier, both
individual prefixes and every shifted order in the polynomial are paid.

## All cutoff allocations and damping schedules

For arbitrary sequences `U_N,V_N`, the small response tends to zero at
source normalization `u^(N+1)` whenever its explicit budget

\[
 u^{N+1}\sqrt{U_N+1}\sqrt{V_N+1}\longrightarrow0.
\]

An independently discharged class is

\[
 0<u<1,\quad b_N>0,\quad b_N\longrightarrow\infty,
 \qquad U_N,V_N\leq\left\lfloor\frac{u^{-N}}{b_N}\right\rfloor.
\]

For every positive denominator, including each individual finite order,
the full normalized allowance is

\[
 \left|u^{N+1}\mathrm{smallFilter}_{p,U_N,V_N,N}(s_0)\right|
 \leq C_{p,y}\left(\frac{u}{b_N}+u^{N+1}\right).
\]

The second term pays the integer-floor correction. The canonical choice
is `b_N=N+1`. Its cutoff eventually exceeds **every**
`floor(r^N)` with `r>=1` and `u*r<1`, in particular the preceding
`floor(u^(-N/4))` cutoff. These are checked eventual comparisons, not
claims about every small order. No optimality or undamped-cutoff result
is asserted. A faster denominator is permitted but need not give a
growing cutoff.

## The unchanged arithmetic obstruction

The subsequent [squarefree projection](zeta-squarefree-vaughan-projection.md)
independently removes all nonsquarefree terms at this same cutoff. The
full formula below remains valid; its squarefree restriction now retains
the same source. Neither statement supplies the independent signed floor.

For any hypothetical nontrivial zero `rho=beta+i*gamma` with `beta>1/2`,
put `u=3/2-beta`, use the **original** pole-jet polynomial `p`, and set
`D_N=floor(u^(-N)/(N+1))`. Lean proves

\[
 u^{N+1}\!
 \sum_{\substack{ab\in\mathcal B_N\\a>D_N,\ b>D_N}}
 \mu(a)\kappa_{D_N}(b)K_{p,N}(3/2+i\gamma,ab)
 \longrightarrow -m_\rho,
 \qquad
 \kappa_V(b)=\sum_{\substack{d\mid b\\d>V}}\Lambda(d).
\]

Here `B_N` is the original `zetaPrimeLogBand`. Its error bound and full
divisor-log majorant are unchanged and uniform in the moving cutoffs.
Shared prime factors, all product phases and both strict boundaries remain
inside the sum. The factors need not be comparable in size.

The source limit uses the hypothetical zero. It supplies no independent
arithmetic lower bound. The remaining goal is still a cofinal real lower
bound strictly above `-m_rho`; no full complex norm estimate is required.
This slice does not enlarge the zero-free region or establish a Type II
bound for arbitrary coefficients or arbitrary intervals.

## Checked entry points

| Theorem | Scope |
|---|---|
| `sum_vonMangoldt_inv_sqrt_le` | Full prime-power density budget |
| `exists_smallFilter_budget_bound` | Every polynomial and both cutoff budgets |
| `exists_smallFilter_damped_bound` | Explicit normalized error for every positive denominator |
| `tendsto_smallFilter_dampedCutoff` | Every positive divergent damping schedule |
| `tendsto_actual_band_of_budget` | Original source for any paid asymmetric allocation |
| `tendsto_actual_band_linearDampedCutoff` | Actual source at the concrete larger cutoff |
| `eventually_geometricCutoff_lt_linearDampedCutoff` | All strict sub-inverse geometric comparisons |
| `eventually_previous_cutoff_lt` | Strict improvement over the preceding cutoff |
