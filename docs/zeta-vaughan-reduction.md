# Two growing factor cutoffs at the original zero-source scale

The [square-root budget refinement](zeta-vaughan-cutoff-budget.md) now
permits `floor(u^(-N)/(N+1))` in both factors, with independently vanishing
normalized allowance. This page retains the original decomposition and
its earlier geometric-cutoff theorem; all its exact identities remain in use.

The [Lean module](../RiemannGaussian/ZetaVaughanReduction.lean) proves an
independent geometric bound for every small-factor term in Vaughan's
decomposition, and transports the complete hypothetical-zero signal to the
remaining finite bilinear sum. **The independent lower bound for that sum,
and RH, remain open. No larger zero-free region is claimed.**

## Exact arithmetic and its information

Write `*` for Dirichlet convolution, `1` for its constant-one coefficient
sequence, and use subscripts for strict or non-strict size restrictions.
The classical identity is

\[
\Lambda=\Lambda_{\le V}+\mu_{\le U}*\log
  -\mu_{\le U}*\Lambda_{\le V}*1
  +\mu_{>U}*\kappa_V,
\qquad
\kappa_V(n)=\sum_{\substack{d\mid n\\d>V}}\Lambda(d).
\]

This is Vaughan's decomposition, not a new identity or an imported analytic
estimate. See [Vaughan's original paper](https://www.impan.pl/get/doi/10.4064/aa-37-1-111-115)
and [Tao's exposition, Lemma 18](https://terrytao.wordpress.com/2015/01/10/254a-notes-3-the-large-sieve-and-the-bombieri-vinogradov-theorem/).
Lean proves it from the existing exact divisor identities.

The cofactor retains prime powers, their logarithmic weights and the cutoff
on the prime power itself. Lean proves

\[
0\le\kappa_V(n)\le\log n,\qquad
\kappa_V(n)=0\ (n\le V),\qquad
\kappa_V(ab)=\kappa_V(a)+\kappa_V(b)\quad((a,b)=1).
\]

The last identity exposes an additive correlation across coprime factors.
It is not a cancellation estimate. No coprimality condition is imposed on
the two factors in the surviving carrier; shared primes remain included.

## The independently paid terms

For a hypothetical nontrivial zero `rho=beta+i*gamma` with `beta>1/2`, set
`u=3/2-beta`, so `1/2<u<1`. Use the existing fixed pole-jet filter `p` and
the same detector center `s0=3/2+i*gamma`. The natural cutoffs are

\[
D_N=\left\lfloor q^N\right\rfloor,
\qquad q=(\sqrt{\sqrt u})^{-1}>1.
\]

With `M_U(s)=sum_(d<=U) mu(d)d^(-s)` and
`A_V(s)=sum_(d<=V) Lambda(d)d^(-s)`, the full small response is

\[
A_V(s)-M_U(s)\zeta'(s)-M_U(s)A_V(s)\zeta(s).
\]

Its signed filtered factorial moments obey

\[
\left|u^{N+1}\operatorname{Small}_{p,U,V,N}(s_0)\right|
\le C_{p,u,\gamma}(\sqrt u)^N
\quad(0\le U,V\le D_N).
\]

`exists_smallFilter_geometric_bound` proves this for **every fixed complex
polynomial**, without a root or sign hypothesis, and all `0<u<1` and
`abs(gamma)>1`. The latter is available for every actual nontrivial zero.
The constant is independent of `N,U,V`; it may depend on the fixed
polynomial, normalization and ordinate. No moving-filter or height-uniform
constant is asserted.

The proof uses a unit Cauchy circle about the detector. It avoids zeta's
pole and stays in `Re(s)>=1/2`. The finite multipliers have bounds
`|M_U|<=U` and `|A_V|<=2V`. Consequently the complete moment allowance is
`(2V+C_gamma*(U+2UV))*sum_k |p_k|`, and
`u*q^2=sqrt(u)<1` pays for both growing cutoffs. This uses analyticity of
zeta and zeta's derivative, with no zero-avoidance hypothesis for them.

## The full finite-band obstruction

Let `B_N` be the **existing** integer logarithmic band, with the existing
endpoint conventions. `band_eq_product_sum` identifies the remaining sum as

\[
T_N=\sum_{n\in B_N}\ \sum_{\substack{ab=n\\a>D_N,\ b>D_N}}
\mu(a)\kappa_{D_N}(b)K_{p,N}(s_0,ab),
\]

where the original kernel is

\[
K_{p,N}(s,x)=x^{-s}\sum_kp_k\frac{(\log x)^{N+k}}{(N+k)!}.
\]

Every product phase, Möbius sign, prime-power cofactor and original band
boundary is retained. The complete coefficient is bounded uniformly in
both cutoffs by `sum_(ab=n) log b`, the original divisor-log majorant.
Thus the already proved band-tail allowance applies unchanged:
`2^(-N)*zetaMoebiusBandTailConstant(p)`. Its normalization also tends to zero.

The compiled terminal theorem `tendsto_actual_band` proves

\[
u^{N+1}T_N\longrightarrow-m_\rho.
\]

This limit is conditional on the selected zero. The independent decay of
the removed terms is proved separately. The remaining target is only a
cofinal strict lower margin above `-m_rho` for the normalized real part;
bounding all orders, all intervals, arbitrary bilinear coefficients or the
full complex norm would ask for more.

Both factors grow, but they need not have comparable size. In particular,
this decomposition does not establish the general Type II hypotheses of
the [literature audit](prime-tail-literature-audit-2026-09-11.md).
Separating the Mellin phase into one phase per factor supplies an exact
identity, not independent oscillation. Any further estimate must use the
literal Möbius/prime-divisor correlations and the complete product kernel.

## Checked chain

| Theorem | Role |
| --- | --- |
| `vaughan`, `hasSum_smallResponse`, `hasSum_response` | Exact coefficients, convergence and analytic responses |
| `cofactor_mul_of_coprime` | Retained additive prime structure |
| `norm_bilinear_le` | One cutoff-independent divisor majorant |
| `exists_smallFilter_geometric_bound`, `tendsto_smallFilter` | Independent removal of the small-factor terms |
| `responseFilter_sub_band_le`, `band_eq_product_sum` | Quantitative localization and exact two-factor finite sum |
| `tendsto_actual_band` | Original complete zero source in that sum |

All names are in `RiemannGaussian.ZetaVaughanReduction`. This is a local
theorem slice under the user's instruction to hold commits; remote CI for
the existing committed revision does not verify these changes.
