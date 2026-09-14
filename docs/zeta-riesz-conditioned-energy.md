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

## Direct transfer to the finite conditioning recurrence

[ZetaRieszConditioningTransfer](../RiemannGaussian/ZetaRieszConditioningTransfer.lean)
now connects the original carrier to the proved finite conditioning
recurrence. The transfer uses the same configurations as the existing
amplified Riesz lift. For each residue `eta`, a configuration consists of
one original signed conditioned block and `r` original residue-tail entries.
Write `v(z)` for its complete signed power-sum vector and `w(z)` for the
product of the original complex Riesz weights. Define

```math
\begin{gathered}
n_{\eta,c}=\#\{z:v(z)=c\},\qquad
\mu_{\eta,c}=\frac{1}{n_{\eta,c}}\sum_{v(z)=c}w(z),\\
\chi_\eta=\max_{c\in v(\Omega_\eta)}|\mu_{\eta,c}|.
\end{gathered}
```

An empty fibre has average zero, and an empty configuration family has
maximum zero. These conventions are covered by the proof. The averages
retain the actual squarefree coefficients, their signs, logarithmic phases,
filter, damping, and the unchanged common length and finite endpoint.
They use equality of the **whole** frequency vector, with the original
block colour retained.

[VinogradovFibreCorrelation](../RiemannGaussian/VinogradovFibreCorrelation.lean)
proves exact identities before taking a maximum:

```math
\begin{aligned}
F_a(\theta)R_\eta(\theta)^r
 &=\sum_c n_{\eta,c}\mu_{\eta,c}e(c\cdot\theta),\\
\int |F_aR_\eta^r|^2
 &=\sum_c n_{\eta,c}^2|\mu_{\eta,c}|^2,\\
I_{a,b}^{\eta}&=\sum_c n_{\eta,c}^2.
\end{aligned}
```

Here `I` is the literal unweighted mixed moment on the **identical**
configuration family. Thus the compiled integrated comparison is

```math
\int |F_aR_\eta^r|^2\le\chi_\eta^2 I_{a,b}^{\eta}.
```

This does not compare the oscillating polynomials pointwise. In general
such a pointwise domination would be false. The theorem
`correlationMaximum_le_of_weight_bound` also proves that `chi_eta` is at
most any bound for the configuration coefficients `|w(z)|`; cancellations
inside the exact complex fibre averages can make it smaller. No smallness
of these averages is assumed by the terminal carrier theorem.

Set `X=2^(32*N)`, `r=k*u`, and retain the actual sampling cost

```math
\mathcal T=(p^b)^{2ku-1}
 \sum_{\eta\bmod p^b} S_\eta\chi_\eta^2,
\qquad S_\eta=\#\{v(z):w(z)\ne0\}.
```

At the proved elementary exponent `lambda0=k*(2*u+1)`, use the actual
normalized levels and complete conditioning allowance from
[VinogradovNormalizedIteration](../RiemannGaussian/VinogradovNormalizedIteration.lean):

```math
\begin{gathered}
\mathcal N_{a,b}=(X/p^a)^k(X/p^b)^{2ku},\qquad
\widehat Q_{a,j}=Q_{a,j}/\mathcal N_{a,j},\\
\mathcal A_{a,b,H}=p^{-H/2}
 +E\sum_{h=0}^{H-1}S^h p^{-2kuh}\widehat Q_{a,b+h},\\
S=2u\binom{p}{k-1}(k-1)^{2ku},\qquad
E=\big((2ku)_k\big)^{2u}.
\end{gathered}
```

`Q` is the actual maximum over canonical tail residues and induced block
colours, with coarse residue zero and the original coarse block colour
fixed. It is not an assumed energy budget. The terminal theorem
[actual_band_le_conditioned_iteration](../RiemannGaussian/ZetaRieszConditioningTransfer.lean)
proves for the **original arithmetic band**:

```math
\boxed{|B|^{2ku}\le
 \frac{\mathcal T\,\mathcal N_{a,b}\,\mathcal A_{a,b,H}}{C_0^2}.}
```

Its explicit hypotheses are nonzero integer `p`, `k≥2`, `u≥k`, `a≤b`,
`H≥1`, `b-a≤2*H`, `p^(b+H)≤X`, and `(C*D)^2≤p`, where
`C=2^(k*(2*u+1))*k!` and `D=2*u*(k-1)^(2*k*u)`.
The same budget proves `k<p`, and the finite cutoff condition proves
`C0>0`. Primality is not required for this conditioning transfer.
The companion `actual_band_le_geometric_conditioned_iteration` replaces
each retained weight `S^h*p^(-2*k*u*h)` by its proved upper bound
`D^h*p^(-(2*k*u-k+1)*h)`, retaining every actual level.

The new interface lets an improvement to these actual conditioned levels
feed into the literal Riesz bound while the arithmetic correlations remain
explicit. A useful source-scale saving still has to overcome **all** the
sampling, correlation and normalization costs. The small deep remainder
alone does not control the remaining intermediate sum. This is a finite
statement: its cutoff condition prevents sending `H` to infinity at fixed
`X`. It proves no new zero-free width or independent signed arithmetic floor.

## The improved global exponent in the original band

[`exists_original_band_improved_iteration`](../RiemannGaussian/ZetaRieszImprovedMoment.lean)
now inserts the independently proved exponent
`lambda1=k(2u+1)-1/(3k)` into the **complete original-carrier bound**.
For every `k>=2,u>=k`, it constructs one `C>=1` and a finite quotient
threshold `N0`. For nonzero `p`, the displayed conditions are

```math
a\le b,\quad H\ge1,\quad b-a\le2H,\quad
p^{b+H}\le X,\quad N_0\le\lfloor X/p^{b+H}\rfloor+1,\quad
(CD)^2\le p,\qquad X=2^{32N}.
```

They imply positive block mass and discharge **both actual homogeneous
moment estimates**, including all quotient rounding. With the original
correlated sampling cost `S`, lower block mass `B`, and unchanged actual
allowance `A`, the result is

```math
\boxed{|\operatorname{Band}_N|^{2ku}
 \le \frac{S}{B^2}\,
 M_{a,b}(\lambda_1)\mathcal A_{a,b,H}(\lambda_1).}
```

The companion `exists_original_band_improved_moment_bound` supplies the
explicit two-quotient bound

```math
|\operatorname{Band}_N|^{2ku}
 \le \frac{SC}{B^2}
 (X/p^a)^{\lambda_1/(u+1)}
 (X/p^b)^{\lambda_1u/(u+1)}.
```

It requires `k<p`, `a<=b`, `p^(a+1)<=X`, `p^b<=X` and the deep quotient
`floor(X/p^b)+1>=N0`. The constants and thresholds depend on `k,u` and
**are not numerically evaluated**. No missing moment budget is supplied as
an assumption; `S` still contains the actual complex Riesz correlations.

The [exact exponent audit](../RiemannGaussian/VinogradovImprovedNormalization.lean)
identifies the effect without losing the remaining energies. Put
`Q=X/p^a>0` and let `epsilon` be any real exponent change. Then
`allowance_exponent_shift_identity` proves

```math
\begin{aligned}
&M_{a,b}(\lambda-\epsilon)\mathcal A_{a,b,H}(\lambda-\epsilon)\\
&\quad+M_{a,b}(\lambda)(1-Q^{-\epsilon})p^{-H/2}
 =M_{a,b}(\lambda)\mathcal A_{a,b,H}(\lambda).
\end{aligned}
```

For `Q>=1` and `epsilon>=0`, `scaled_allowance_exponent_mono` proves that
the complete right-hand-side allowance cannot increase. **Only the deep
remainder changes; every intermediate energy is identical after restoring
its source scale.** With `epsilon=1/(3k)`, the remainder gains exactly
`Q^(-1/(3k))`. This factor cannot be assigned to the entire retained sum.
A net bound for those energies together with the original correlations and
sampling costs remains necessary for the source contradiction. The proved
zero-free region is unchanged.

## Negative profile in the original initial band

[`exists_original_band_negative_profile`](../RiemannGaussian/ZetaRieszNegativeProfile.lean)
now bounds the complete conditioned-energy allowance at `a=0,b=1`
independently. For every `k>=2,u>=k`, Lean constructs `C>=1`, `B>=1`,
a finite quotient threshold `N0`, depth `S>=2`, and `-1/2<=beta<0`.
For prime `p` with

```math
p^S\le X,\qquad N_0\le\lfloor X/p^S\rfloor+1,\qquad
(CD)^2\le p,\qquad X=2^{32N},
```

the actual original band satisfies

```math
\boxed{|\operatorname{Band}_N|^{2ku}
 \le \frac{\mathcal S_{\rm corr}}{\operatorname{lowerMass}^2}
 M_{0,1}(\lambda_1)\,B p^\beta.}
```

Every homogeneous moment and later conditioned-energy premise is
discharged. The [uniform profile induction](vinogradov-korobov-framework.md#uniform-negative-profiles-and-global-exponent-bootstrap)
pays all descendant cutoffs and preserves the full finite sum through
its geometric factorization. The initial depth-one allowance then includes
both its whole intermediate level and its `p^(-1/2)` remainder; capping
the negative exponent at `-1/2` absorbs both.

The exact original complex fibre averages remain in `S_corr`, together
with attained-frequency and residue-summation costs. The positive lower
block mass and the full source normalization remain in the displayed bound.
The negative factor is therefore a proved saving in this conditioned-energy
component; a net saving after these other costs is still unproved. The
coupled cutoff prevents increasing `p` arbitrarily at fixed `X`. Constants,
depth and the negative exponent are not numerically evaluated. No new
zero-free region or RH contradiction follows from this theorem alone.

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
has yet been proved. The higher conditioned homogeneous comparison and finite
VK congruencing step are now proved, along with an explicit bound for the
singular and nonsingular conditioning contributions. Their explicit one-step
conditioning recurrence is proved, and the direct correlation transfer above
now applies its finite iteration and deep remainder to the original carrier.
The uniform profile iteration now gives an independent initial-energy
saving and improves every admissible global exponent above critical.
Making that improvement uniform near the infimum and proving a net saving
in the remaining actual correlation and sampling costs remain open in the
[VK framework](vinogradov-korobov-framework.md).

The finite Fourier and congruencing tools are classical ingredients. This
module connects their proved forms to this repository's actual Riesz source;
no claim of historical novelty or a new zero-free width is made.
