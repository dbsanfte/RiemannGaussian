# The original Riesz carrier meets signed Vinogradov energy

[ZetaRieszConditionedEnergy.actual_band_le_mixed_moments](../RiemannGaussian/ZetaRieszConditionedEnergy.lean)
bounds the **literal original finite Riesz carrier** by actual finer-residue
mixed moments. Its signs, logarithmic phase, full filter polynomial, damping,
prime deletion and original band cutoff are unchanged. The arithmetic
congruence conditions and all integration and sampling costs are proved;
there is no assumed moment budget in this endpoint.

This closes an interface between two existing proof chains. It does not yet
prove that the remaining mixed moments are small enough for the source
contradiction, or enlarge the proved zero-free region.

## Exact lift of the original carrier

Let `X=2^(32*N)`, let `B` denote the original Riesz band, and let

```math
A_n={\mathbf1}_{n\in\mathcal B_N}\,
 c_L(n)\,K_{P,N}(3/2+iy,n),
\qquad
c_L(n)={\mathbf1}_{\substack{n\text{ squarefree}\\n\text{ not prime}}}
 \frac{-\log n}{L}\sum_{d\mid n}\mu(d)(L-\log d)_+.
```

Here `K` is the original complex zeta filter kernel, including every
coefficient of `P`. The indicator retains the original logarithmic band;
its prime and nonsquarefree deletions are not completed or estimated away.
Define the auxiliary frequency vector `v(n)=(n,n^2,...,n^k)` and

```math
R(\theta)=\sum_{n=1}^X A_n e^{2\pi i\langle v(n),\theta\rangle},
\qquad
R_\eta(\theta)=\sum_{\substack{1\le n\le X\\n\equiv\eta\pmod{p^b}}}
 A_n e^{2\pi i\langle v(n),\theta\rangle}.
```

Theorems `fullLift_zero`, `fullLift_partition` and
`actual_band_eq_residue_lifts` prove the exact complex identities

```math
\boxed{R(0)=B,\qquad R(\theta)=\sum_{\eta\bmod p^b}R_\eta(\theta).}
```

The logarithmic zeta phase stays in `A_n`; the auxiliary polynomial phase
is added without pretending that a logarithm is itself a polynomial.
`residueLift_power_eq` retains the original product weights on every full
ordered tail tuple. `residue_moment_eq_gram` identifies its actual moment:

```math
\int |R_\eta(\theta)|^{2r}\,d\theta
=\sum_{\substack{u,v\in\mathcal W_\eta^r\\
 \sum_j v(u_j)=\sum_j v(v_j)}}
 \left(\prod_j A_{u_j}\right)
 \overline{\left(\prod_j A_{v_j}\right)}.
```

All residue restrictions, Riesz signs and the logarithmic product phases
remain coupled to the complete equal-power-sum equations. The companion
`amplified_moment_eq_gram` also retains the full signed block frequencies.
The complex cross terms remain available before the inequalities below.

## The proved finite bound

Take a prime `p`, `1≤k<p`, `a<b`, `r≥1`, and arbitrary block colours
`epsilon`. Let `F_epsilon` sum all positive blocks in coarse class zero
modulo `p^a` with pairwise distinct normalized next digits modulo `p`.
Its value at zero is the literal number `C` of those blocks. Put

```math
\begin{gathered}
\Gamma=r_+!\,r_-!\,p^{(a+b)k(k-1)/2}
 \bigl(p^{kb-a}\bigr)^k,\\
M_\eta=\max_{0\le\zeta\lt p^{kb}}
 \int |f_{p^{kb},\zeta}(\theta)|^{2k}
       |R_\eta(\theta)|^{2r}\,d\theta.
\end{gathered}
```

Here `f` is the literal unweighted positive finer-residue polynomial.
The product factorization and finite Hölder theorem in
[VinogradovProductEnergy](../RiemannGaussian/VinogradovProductEnergy.lean)
prove `int |F_epsilon|^2 |R_eta|^(2r) ≤ Gamma*M_eta`.

A pointwise bound also has to pay for sampling at phase zero.
[VinogradovFourierEvaluation](../RiemannGaussian/VinogradovFourierEvaluation.lean)
first groups every full complex frequency coefficient, then uses exact
orthogonality and finite Cauchy. If `S_eta` is the number of joint
frequencies attained by nonzero original terms of `F_epsilon*R_eta^r`,
`residue_sample_bound` proves

```math
C^2|R_\eta(0)|^{2r}\le S_\eta\Gamma M_\eta.
```

No rectangular frequency box replaces the actual joint support. The exact
residue partition and an explicit finite Hölder cost then give
`actual_band_conditioned_bound`:

```math
\boxed{C^2|B|^{2r}\le
 (p^b)^{2r-1}\Gamma\sum_{\eta\bmod p^b}S_\eta M_\eta.}
```

The multiplied form holds even for empty block windows. If
`p^(a+1)≤X`, the explicit block `p^a,2p^a,...,k*p^a` belongs to the
actual conditioned family. Thus `conditionedWindow_nonempty` and
`blockCount_pos` prove `C>0`. The normalized terminal theorem is

```math
\boxed{|B|^{2r}\le
 \frac{(p^b)^{2r-1}\Gamma}{C^2}
 \sum_{\eta\bmod p^b}S_\eta M_\eta.}
```

Every term on the right is defined from the original finite data. No
independent upper bound on the `M_eta` is assumed or proved by the bridge.

## Constructive mass and actual mixed-moment interpolation

[VinogradovBlockMass](../RiemannGaussian/VinogradovBlockMass.lean)
now counts every injective next-digit choice and every complete higher
quotient block. Both choices are reconstructed from the original positive
integers, giving the literal family the lower bound

```math
\begin{gathered}
C\ge C_0=(p)_k\left\lfloor\frac{X}{p^{a+1}}\right\rfloor^k,\\
(p)_k=p(p-1)\cdots(p-k+1).
\end{gathered}
```

When `p^(a+1)≤X`, this count is positive and also at least
`(p)_k*(X/(2*p^(a+1)))^k`, with the floor loss proved explicitly.
[actual_band_le_explicit_block_mass](../RiemannGaussian/ZetaRieszBlockMass.lean)
therefore replaces the normalization in the carrier bound by the explicit
`C_0^2`. The exact original block count remains available upstream.

[VinogradovInterpolation.mixed_interpolation](../RiemannGaussian/VinogradovInterpolation.lean)
proves, for **arbitrary continuous complex functions** `f,F` and `u≥1`,

```math
\begin{aligned}
\int |f|^{2k}|F|^{2u}
&\le \left(\int |F|^{2u+2}\right)^{1-1/u}\\
&\qquad\cdot\left(\int |F|^2|f|^{2ku}\right)^{1/u}.
\end{aligned}
```

All compactness, continuity and Lp requirements are discharged, including
zero function values and the endpoint `u=1`. This is the interpolation
used in [Wooley (2012), equation (6.8)](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
It is available for both actual conditioned polynomials and Riesz lifts.

[ZetaRieszInterpolation](../RiemannGaussian/ZetaRieszInterpolation.lean)
applies it to the original Riesz tail. Define the actual quantities

```math
\begin{gathered}
H_\eta=\int |R_\eta|^{2r+2},\\
V_\eta=\max_{0\le\zeta\lt p^{kb}}
 \int |R_\eta|^2 |f_{p^{kb},\zeta}|^{2kr}.
\end{gathered}
```

The theorem `rieszMomentMaximum_le_interpolated` proves
`M_eta≤H_eta^(1-1/r)*V_eta^(1/r)` with no supplied moment budget.
The terminal [actual_band_le_interpolated_moments](../RiemannGaussian/ZetaRieszInterpolation.lean)
therefore gives the literal original carrier the bound

```math
\boxed{\begin{aligned}
|B|^{2r}&\le \frac{(p^b)^{2r-1}\Gamma}{C_0^2}\\
&\qquad\cdot\sum_{\eta\bmod p^b}
 S_\eta H_\eta^{1-1/r}V_\eta^{1/r}.
\end{aligned}}
```

The reverse mixed moment contains only a squared original Riesz factor;
its other factor is the literal finer-residue polynomial. All original
weights and logarithmic phases remain in both moments. The estimate
organizes the remaining problem; it does not yet prove a saving for either
factor or a new zero-free region.

## Source and remaining arithmetic work

For a hypothetical right-half zero `rho`, the original theorem chooses
`u=3/2-Re(rho)`, its pole-jet filter, and the exact common length `L_N`.
`tendsto_actual_residue_source` carries its source through the new lift:

```math
u^{N+1}\sum_{\eta\bmod p^b}R_{\eta,N}(0)
 \longrightarrow -m_\rho.
```

The source uses the same entire original band, and the common Riesz length
is not replaced by an integer-dependent reflection midpoint. This remains
a conditional source identity, not an independent arithmetic estimate.

The remaining task is a quantitative bound on the **actual weighted mixed
moments**, together with the explicit sampling, congruence and block-count
costs. Generic mean-value bounds can be applied through this interface,
but taking coefficient absolute values would lose the signed arithmetic
correlations retained by its Gram identities. No saving beyond those costs
has yet been proved. The remaining VK homogeneous-moment comparison, singular conditioning
and high-moment iteration remain open as documented in the
[VK framework](vinogradov-korobov-framework.md).

The finite Fourier and congruencing tools are classical ingredients. This
module connects their proved forms to this repository's actual Riesz source;
no claim of historical novelty or a new zero-free width is made.
