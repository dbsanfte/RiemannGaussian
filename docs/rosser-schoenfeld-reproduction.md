# Rosser–Schoenfeld input to Ford's prime packets

The actual prime-counting inequalities needed by Ford are **not yet proved
in this repository**. The compiled results below discharge particular
dependencies; none assumes an external numerical prime or zero table.
The published constants, finite starting points and full packet-width range
remain the target.

The sources are [Rosser–Schoenfeld (1962), sections 5–7](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)
and [Ford, Lemma 2.1](https://arxiv.org/pdf/1910.08209). The exact required
input, for every real $x>67$, is

```math
\frac{x}{\log x-1/2}<\pi(x)<
\frac{x}{\log x}\left(1+\frac{3}{2\log x}\right).
```

Here every Lean occurrence of π is `Nat.primeCounting ⌊x⌋₊`.

## Compiled parts

| Part | Actual proved statement | Lean source |
| --- | --- | --- |
| Finite arithmetic anchor | π(1451)=230; 1360<θ(1451)<1410; 7.2≤log(1451)≤7.3 | [RosserSchoenfeldAnchor](../RiemannGaussian/RosserSchoenfeldAnchor.lean) |
| Anchored Abel comparison | Actual π(x) compared with the actual J-function when the corresponding θ inequality is supplied | [RosserSchoenfeldComparison](../RiemannGaussian/RosserSchoenfeldComparison.lean) |
| Section 7, Lemmas 2 and 3 | J(x;0.31)<upper(x) for x≥10⁸; J(x;0.47)<upper(x) for x≥exp(100) | [RosserSchoenfeldBounds](../RiemannGaussian/RosserSchoenfeldBounds.lean) |
| Section 7, Lemma 5 | lower(x)<J(x;−0.47) for every x≥1451, strengthening its stated starting range | [RosserSchoenfeldBounds](../RiemannGaussian/RosserSchoenfeldBounds.lean) |
| Theorem 26 zero-free input | The exact radical constant and height, from the existing stronger signed-pole bound | [RosserSchoenfeldZeroFree](../RiemannGaussian/RosserSchoenfeldZeroFree.lean) |
| Complete reciprocal-square zero mass | Both multiplicity-weighted sums, using squared ordinates or squared norms, are strictly below 0.0463 | [RosserSchoenfeldZeroMass](../RiemannGaussian/RosserSchoenfeldZeroMass.lean) |
| Last numerical error comparison | The paper's ε(x)<0.47/log(x) for every x≥exp(5000) | [RosserSchoenfeldError](../RiemannGaussian/RosserSchoenfeldError.lean) |
| Ford short packet transport | Exact finite prime packet from the two displayed actual prime-count bounds, with every numerical side condition derived | [VinogradovRosserPrimeSupply](../RiemannGaussian/VinogradovRosserPrimeSupply.lean) |

The anchor uses a complete kernel-checked list of the 230 primes and an
exact primorial product. Integer power inequalities and proved exponential
enclosures bound its logarithm. Python-generated candidate data is not a
trusted premise. The J-comparisons use explicit rational barriers and
their proved derivative signs, without assuming decimal values of an
exponential integral.

The zero-free theorem keeps exactly

```math
R=\frac{515}{(\sqrt{546}-\sqrt{322})^2},\qquad A=e^{9.99},\qquad
\beta<1-\frac1{R\log|\gamma|}\quad(|\gamma|\ge A).
```

This containment result does not enlarge the repository's current region.
The scalar error comparison uses the same $R$ in

```math
\epsilon(x)=\sqrt{\log x}\exp\!\left(-\sqrt{\frac{\log x}{R}}\right).
```

It does **not** prove θ(x) or ψ(x) lies within this error of x.

`shortPrimeSupply_of_primeCounting` gives the existing, unchanged
`ShortPrimeSupply k omega` for every $k\ge26$ and

```math
\frac1{3\log k}\le\omega\le\frac12,\qquad
V=\max\left(e^{3/2+3/(2\omega)},\frac{18}{\omega}k^3\log k\right).
```

For every real $M\ge V$, its packet contains exactly $k^3$ primes in
$M<p\le(1+\omega)M$. This remains **conditional** on the two actual
prime-count inequalities. The conditional packet theorem is not a proof of
prime density, of Ford's complete numerical moment theorem, or of a VK
zero-free benchmark.

## Complete reciprocal-square zero mass

[RosserSchoenfeldZeroMass.ordinate_mass_lt](../RiemannGaussian/RosserSchoenfeldZeroMass.lean)
and `norm_square_mass_lt` prove unconditionally

```math
\sum_\rho\frac{m_\rho}{|\rho|^2}
\le\sum_\rho\frac{m_\rho}{(\Im\rho)^2}
\lt\frac{463}{10000}=0.0463.
```

The sums include all nontrivial zeros, both ordinate signs and every
analytic multiplicity. Their summability is proved. The norm-square
constant is the classical Rosser (1941), Lemma 17 value also recorded in
[Helfgott, Appendix A, equation (A.4)](https://arxiv.org/pdf/1312.7748).
Here it follows from an independent proof using the repository's complete
xi expansion and finite verification; no numerical zero table is assumed.

For a zero `rho=beta+i*t`, `hasSum_poisson` evaluates the exact positive mass:

```math
\sum_\rho m_\rho\left(
\frac{1-\beta}{(1-\beta)^2+t^2}+
\frac{\beta}{\beta^2+t^2}\right)
=2+\gamma-2\log2-\log\pi\lt\frac{2311}{50000}.
```

[RosserSchoenfeldEulerConstant](../RiemannGaussian/RosserSchoenfeldEulerConstant.lean)
proves the numerical constants using a corrected harmonic sequence and
rational logarithm bounds. For `|t|<=54`, the complete finite verification
gives `beta=1/2`; above 54 the ordinate alone controls the discrepancy.
Together with `|t|>14`, this proves that the reciprocal ordinate-square
weight is at most `785/784` times its Poisson weight. The exact full-series
identity therefore pays every zero, including those beyond the finite
verification.

This discharges the first reciprocal-power constant. The higher-power
constants `0.00167` and `0.0000744`, the smoothed explicit-formula bounds,
the larger finite verification and the actual prime-count estimates remain
open. No larger zero-free region or independent RH arithmetic floor follows.

## The analytic and finite-verification gap

Rosser–Schoenfeld's section 6 uses the verification of the first 25000
nontrivial zeros, a sharp zero-count estimate, explicit zero sums and
smoothed explicit-formula estimates from Rosser (1941). These justify
Table I and the quantitative θ/ψ estimates. The paper does not reprove
all these inputs in full. Citations to them are not Lean proofs.

Theorem 31's theta bound is assembled across these ranges:

| Range | Source dependency still to formalize |
| --- | --- |
| Up to 16000 | Finite prime tables and monotonic interpolation |
| 16000 to 10⁸ | Theorems 18 and 19 |
| 10⁸ to 10¹⁶ | Theorem 24 and the justified Table I |
| 10¹⁶ to exp(5000) | Corollary of Theorem 14 and the justified Table I |
| Above exp(5000) | Actual Theorem 11 prime-error estimate; its final scalar comparison is now proved |

The narrower 0.31 range and the remaining section 7 comparisons also need
their stated inputs. The existing qualitative PNT gives no numerical
starting point for this chain. The existing 67.31% zero-proportion
certificate verifies neither individual low zeros nor completeness of
their list.

A cross-project check on 2026-09-23 inspected PNT+ at commit
`a5154676af9aa3095150ee410cdda80555aa0642`. Its displayed
[`RS_prime.theorem_a`](https://github.com/alexkontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/TMEEMT.lean#L255)
derives the bound `psi(x)<=1.03883*x` from
[`RS_prime.theorem_12`](https://github.com/alexkontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RosserSchoenfeldPrime.lean#L1015),
whose proof body is unfinished in that snapshot. That displayed result
therefore does not supply a checked substitute for the missing input.
This was a targeted dependency check, not an audit of all PNT+ results;
no external code or assumed estimate was imported.

## Rigorous evaluation for the low-zero verification

[ZetaEulerMaclaurin.zeta_eq](../RiemannGaussian/ZetaEulerMaclaurin.lean)
proves the arbitrary-order expansion for actual zeta at every natural
cutoff $N$, for $\Re(s)>0$, $s\ne1$. The normalized Bernoulli
kernels satisfy an exact integration-by-parts recurrence, and every
signed tail converges absolutely. The theorem keeps the complex phase and
every endpoint before estimating the remainder.

For order $q=M+2$, `norm_error_le` supplies the explicit bound

```math
|\zeta(s)-E_{N,M}(s)|\le
\frac{|s(s+1)\cdots(s+q-1)|\,A_q}
     {\Re(s)+q-1}(N+1)^{1-\Re(s)-q},
\qquad
A_q=\frac1{q!}\sum_{j=0}^q\binom qj|B_{q-j}|.
```

[ZetaEulerMaclaurinBudget.uniform_error](../RiemannGaussian/ZetaEulerMaclaurinBudget.lean)
checks $A_{20}<6\cdot10^{-14}$ by exact rational arithmetic and proves

```math
|\zeta(s)-E_{22020,18}(s)|<10^{-12}
\quad\left(\tfrac12\le\Re(s)\le1,\ |\Im(s)|\le22000,\ s\ne1\right).
```

The same module proves $e^{9.99}<22000$. Its `uniform_error_of_norm`
permits any cutoff $N\le22020$ satisfying $|s|+20\le N+1$, so low-height
checks can use much shorter prefixes without weakening the full-height
error theorem.

[ZetaEulerMaclaurinEnclosure.mem_evaluate](../RiemannGaussian/ZetaEulerMaclaurinEnclosure.lean)
now certifies interval evaluation of the exact finite expression. The
complex rectangle arithmetic keeps both signed coordinates, uses proved
periodicity and twenty-decimal bounds for pi, and scales each rising
factor before multiplication to avoid magnifying rounded coefficients.
All cached Bernoulli coefficients are proved equal to the original
recurrence values. Failed domain checks produce no enclosure.

[ZetaEulerMaclaurinCertificate.nonzero_of_check](../RiemannGaussian/ZetaEulerMaclaurinCertificate.lean)
checks the input geometry and combines the computed enclosure with the
proved analytic remainder. A successful check excludes zeros throughout
the input rectangle, rather than only at its center. The coordinate-bound
theorem also retains the explicit truncation allowance on both sides.

The first actual kernel-reduced computation is
[ZetaEulerMaclaurinValidation.height_fourteen_rectangle](../RiemannGaussian/ZetaEulerMaclaurinValidation.lean):

```math
\zeta(s)\ne0\qquad
\left(\frac12\le\Re(s)\le\frac{50001}{100000},\quad
14\le\Im(s)\le\frac{1400001}{100000}\right).
```

This uses cutoff 34 and order 20. It is a small end-to-end validation
rectangle, **not** a complete finite RH certificate or reproduction of a
published benchmark. The truncation budget covers the required height;
the finite computations do not yet cover it.

## An unconditional isolated critical-line zero

[ZetaLowZeroIsolation.isolated_critical_zero](../RiemannGaussian/ZetaLowZeroIsolation.lean)
proves that the disc

```math
c=\frac12+\frac{14134725141735}{10^{12}}i,\qquad
D=\{s:|s-c|\le10^{-5}\}
```

contains exactly one zero of actual zeta. Its real part is exactly $1/2$
and its analytic multiplicity is one. `zero_distance_lt` further proves
$|\rho-c|<1/50000000$, and `nonzero_on_sphere` proves the entire boundary
of $D$ is zero-free. There is no assumed root-existence or numerical
derivative premise.

[ZetaLowZeroSamples](../RiemannGaussian/ZetaLowZeroSamples.lean) checks two
complete interval computations in Lean's kernel. The actual-value
consequences, including the Euler--Maclaurin remainder, are

```math
h=10^{-6},\qquad a=\frac34+\frac18i,\qquad
|\zeta(c)|<10^{-8},\qquad
|\zeta(c+h)-ah|<\frac1{20000000}.
```

[ZetaLowZeroDisc](../RiemannGaussian/ZetaLowZeroDisc.lean) independently
proves $|\zeta|\le32$ on the surrounding radius-$1/4$ disc and
$|\zeta''|\le4096$ on the radius-$1/8$ disc. The mean-value estimates in
[AnalyticNewtonIsolation](../RiemannGaussian/AnalyticNewtonIsolation.lean)
then give $|\zeta'(c)-a|\le1/14$ and $|\zeta'(s)-a|\le1/8$ throughout
$D$. These bounds prove that $s\mapsto s-\zeta(s)/a$ maps $D$ into itself
and contracts with constant $1/4$. Banach's theorem gives the unique
simple zero; the reflection $s\mapsto1-\overline{s}$ fixes it and hence
places it exactly on the critical line.

This disc theorem certifies **one** isolated zero. The complete counting
theorem below now identifies it as the first positive zero and excludes
other zeros through height 15. The full first 25000 zeros remain unverified.
A list of individually isolated zeros is
not a completeness proof. The Rosser--Schoenfeld prime-count estimates
and full published-region reproduction remain open.

The evaluator follows the classical expansion used in
[Lehmer (1956), equation (1)](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5833-11511_2006_Article_BF02401102.pdf).
The separate [extended computation](https://doi.org/10.1112/S0025579300001753)
is the published 25000-zero verification; its result has not been imported
as a premise.

## Certified continuous phase through height 22000

[DigammaMidpointApproximation.norm_digamma_sub_log_midpoint_le](../RiemannGaussian/DigammaMidpointApproximation.lean)
proves the actual digamma estimate

```math
\left|\psi(z)-\log(z-\tfrac12)\right|
\le\frac1{2(\Re z-\tfrac12)^2}\qquad(\Re z\ge\tfrac32).
```

The proof compares each reciprocal Euler term with its centered logarithmic
cell. Its odd error integrates to zero; the remaining quadratic error has
a proved telescoping inverse-square budget. This bound is uniform in the
imaginary part and has no unproved asymptotic-error hypothesis.

[GammaContinuousPhase.Gamma_eq_amplitude_mul_phase](../RiemannGaussian/GammaContinuousPhase.lean)
identifies the integral of the actual digamma function with a continuous
phase of actual Gamma, normalized on the positive real axis. Its amplitude
is strictly positive. Whole turns are retained, as required for a total
zero count; a principal argument alone would not suffice.

[GammaPhaseApproximation](../RiemannGaussian/GammaPhaseApproximation.lean)
proves the exact finite shift and its error. Put $t=T/2$, $b=M-1/4$. The
finite theta approximation is

```math
Q_M(T)=b\arctan(t/b)+\frac t2\log(b^2+t^2)-t
-\sum_{r=0}^{M-1}\arctan\!\left(\frac{t}{r+1/4}\right)-t\log\pi.
```

For $M=200$, `theta_error_lt_one_seventh` discharges the full bound

```math
|\theta(T)-Q_{200}(T)|
\le\frac{|T|}{4(200-1/4)^2}
\le\frac{88000}{638401}<\frac17
\qquad(|T|\le22000).
```

[ZetaHardyPhase](../RiemannGaussian/ZetaHardyPhase.lean) connects this
approximation to actual zeta. Lean proves Hardy $Z(T)$ real and continuous,
with exactly the critical-line zeros of zeta, and proves

```math
\Re\!\left(e^{iQ_{200}(T)}\zeta(\tfrac12+iT)\right)
=Z(T)\cos\!\left(Q_{200}(T)-\theta(T)\right),
\qquad
\cos\!\left(Q_{200}(T)-\theta(T)\right)>\frac{97}{98}.
```

The cosine bound holds throughout the same height range. Thus rigorously
checked opposite signs of the finite-phase rotation imply an actual
critical-line zero between the endpoints, without a numerical derivative
bound. The terminal theorem is `exists_zero_of_approximate_mul_neg`.
This does not assume the endpoint signs have been checked: their complete
finite verification remains work to do.

## Complete counting and the first verified window

[ZetaFiniteZeroCount](../RiemannGaussian/ZetaFiniteZeroCount.lean) specializes
the existing complete finite-divisor contour theorem with its actual
analytic multiplicities. Its count $C(T)$ includes **both** signs of the
ordinate. [ZetaZeroCountFormula](../RiemannGaussian/ZetaZeroCountFormula.lean)
proves, for positive heights with no boundary zeros,

```math
C(T)=2+\frac{2}{\pi}\left(\theta(T)+A(T)\right),\qquad
A(T)=\int_0^T\Re\frac{\zeta'}{\zeta}(3/2+it)\,dt
-\int_{1/2}^{3/2}\Im\frac{\zeta'}{\zeta}(\sigma+iT)\,d\sigma.
```

Both pole contributions are evaluated exactly, and the actual Gamma path
is exactly the unwrapped theta phase. Replacing theta by $Q_{200}$ changes
the count expression by **less than 1/10** throughout $0<T\le22000$; no
bound on the remaining zeta phase is assumed in that error estimate.

[ZetaRightPhase.zeta_re_pos](../RiemannGaussian/ZetaRightPhase.lean) proves
$\Re\zeta(3/2+it)>0$ at every real height from the complete logarithmic
Euler series and its independent norm bound $\log3<\pi/2$.
[ZetaCountingEndpoint](../RiemannGaussian/ZetaCountingEndpoint.lean) then
proves that positivity on the horizontal segment implies both regularity
of the entire zero boundary and

```math
A(T)=\arg\zeta(1/2+iT).
```

This equality retains the unwrapped path: the positivity checks prove that
no whole turns were lost. `count_eq_of_endpoint` makes the two numerical
obligations explicit. It does not presume they have been checked at every
height.

They **are discharged at height 15**:

- [CertifiedArctan](../RiemannGaussian/CertifiedArctan.lean) checks rational
  angle brackets against certified sine/cosine signs, retaining the tangent
  branch conditions. [GammaThetaFifteen.theta_bounds](../RiemannGaussian/GammaThetaFifteen.lean)
  proves $-3/2<\theta(15)<0$, including the analytic shift-eight error.
- [ZetaHeightFifteen.horizontal_positive](../RiemannGaussian/ZetaHeightFifteen.lean)
  certifies fourteen adjacent **closed** rectangles covering every
  $1/2\le\sigma\le3/2$ at height 15. A separate checked endpoint has positive
  imaginary part. All computations use `decide +kernel`, the complete
  Euler--Maclaurin expression, and the proved analytic error.
- [ZetaFirstZeroCompleteness.count_fifteen](../RiemannGaussian/ZetaFirstZeroCompleteness.lean)
  proves $C(15)=2$. `complete_first_pair` proves the entire finite divisor is
  the isolated simple zero and its conjugate. The positive ordinate remains
  within $1/50000000$ of $14.134725141735$.
- `critical_line_through_fifteen` proves that **every** nontrivial zero with
  $|\Im\rho|\le15$ has $\Re\rho=1/2$; `no_zero_through_fourteen` proves
  $14<|\Im\rho|$ for every nontrivial zero. `nonzero_through_fifteen` states
  actual zeta nonvanishing off the line for $\Re s>0$, $|\Im s|\le15$, with
  the pole at one explicitly excluded.

[ZetaZeroCountCompleteness](../RiemannGaussian/ZetaZeroCountCompleteness.lean)
provides the general list-matching theorem: a verified finite subset whose
cardinality exhausts the total multiplicity count contains every zero in
the window. No simplicity assumption on unseen zeros is used.

## Complete verification extended through height 26

[ZetaThreeZeroCompleteness.critical_line_through_twentySix](../RiemannGaussian/ZetaThreeZeroCompleteness.lean)
extends the complete finite verification:

```math
C(26)=6,\qquad
\zeta(\rho)=0,\quad 0<\Re\rho<1,\quad |\Im\rho|\le26
\quad\Longrightarrow\quad\Re\rho=\tfrac12.
```

The four actual Hardy signs in
[ZetaHardySamples](../RiemannGaussian/ZetaHardySamples.lean) are

```math
Z(14)<0,\qquad Z(15)>0,\qquad Z(22)<0,\qquad Z(26)>0.
```

They supply three distinct positive critical-line zeros in `(14,15)`,
`(15,22)` and `(22,26)`. Their conjugates exhaust the complete count.
[ZetaHardyWindowCompleteness.critical_line_of_sign_windows](../RiemannGaussian/ZetaHardyWindowCompleteness.lean)
proves this matching step for any finite collection of ordered disjoint
positive sign windows, retaining every actual multiplicity.

The count is independently discharged by eight closed horizontal
rectangles in [ZetaHeightTwentySix](../RiemannGaussian/ZetaHeightTwentySix.lean),
the checked positive imaginary part of the endpoint, and the unwrapped
phase bound `49/10 < theta(26) < 53/10` in
[GammaThetaTwentySix](../RiemannGaussian/GammaThetaTwentySix.lean).
`count_eq_of_phase_sector` in
[ZetaCountingEndpoint](../RiemannGaussian/ZetaCountingEndpoint.lean) retains
the integer phase-sector index; no principal argument replaces an
untracked whole turn. `nonzero_through_twentySix` states the actual
off-critical-line nonvanishing result for `Re(s)>0`, with the pole at one
excluded.

The new sign evaluator uses a proved exact algebraic reduction:

```math
P(T)=\prod_{r=0}^{199}(r+\tfrac14-iT/2),\quad
S(T)=|\Re P(T)|+|\Im P(T)|>0,\quad
W(T)=\frac{P(T)}{S(T)}e^{i\Phi(T)},\qquad |W(T)|\le1,
```

where `Phi` is the single leading phase in
[ZetaHardyProduct](../RiemannGaussian/ZetaHardyProduct.lean). Lean proves

```math
\Re\bigl(W(T)\zeta(\tfrac12+iT)\bigr)
=\frac{|P(T)|}{S(T)}Z(T)\cos\bigl(Q_{200}(T)-\theta(T)\bigr).
```

Thus rational product arithmetic replaces two hundred separate angle
evaluations. The positive normalization cannot amplify the zeta error.
[ZetaHardyProductCertificate.hardy_sign_of_check](../RiemannGaussian/ZetaHardyProductCertificate.lean)
checks the remaining angle, both signed coordinates, the analytic domain,
the full truncation allowance and the height restriction. All four sample
checks use `decide +kernel`. This rotation is used for **signs**, while
the total count continues to use the unwrapped phase.

This is a **complete finite-height verification through 26**, not a
25000-zero certificate, a reproduction of the published VK region, or a
world-record zero-free region. The full list, complete count and matching
through the published height remain open.

### Scaling to the published height

The direct Dirichlet prefix remains a major computational cost. An
exploratory native evaluation at height 22000 took about 41 seconds at
Taylor depth 16 and returned a rectangle containing zero. Depth 32 took
about 87 seconds and gave a narrow nonzero enclosure. These timing probes
are **not kernel-checked certificates**. An inverse-square-root amplitude
prototype reduced the first timing to about 35 seconds but retained the
wide enclosure, so amplitude evaluation alone does not solve the problem.
The four checked Hardy samples took about eight minutes in the local Lean
build. Do not extrapolate the small validation windows into a completed
25000-zero verification or launch the entire naive calculation by default.

The next scaling candidate is the classical Riemann–Siegel evaluator,
which [Lehmer's account](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5833-11511_2006_Article_BF02401102.pdf)
also introduces to overcome the growing Euler–Maclaurin prefix. Its main
sum has cutoff `floor(sqrt(T/(2*pi)))`; an **explicit proved remainder**
is still required. The asymptotic `O(T^(-1/4))` in
[DLMF 25.10](https://dlmf.nist.gov/25.10) is not a numerical allowance.
[Arias de Reyna's error-analysis paper](https://arxiv.org/abs/2201.00342)
is a further implementation source, not an imported Lean proof. Any faster
evaluator should feed the existing sign-window and complete-count chain.

[Hiary's elementary alternative](https://arxiv.org/abs/1403.0317), Theorem
1.1 and Lemma 3.3, is another concrete candidate: it accelerates the same
Dirichlet prefix by Taylor expansion around blocks and evaluates the
resulting geometric sums and derivatives. The paper supplies an explicit
block error and explicitly permits retaining the Euler--Maclaurin
corrections. This may reuse more of the current Lean chain than the
Riemann--Siegel contour derivation; that is an implementation judgment,
not a proved speedup. Test the numerical cost and conditioning before
choosing. The block evaluator is now formalized with the finite-height
budget below; this is an independently proved specialization of the
elementary block idea, not a reproduction of all Hiary constants.

### Proved block accelerator and remaining cost

[ZetaBlockTaylor](../RiemannGaussian/ZetaBlockTaylor.lean) uses the fixed
scale `x/300`, sharing one coefficient table across all blocks. For
`f_s(x)=exp(s*(x/300-log(1+x/300)))`, its coefficients satisfy

```math
c_0=1,\qquad c_1=0,\qquad
(j+2)c_{j+2}=\frac{s}{90000}c_j-\frac{j+1}{300}c_{j+1}.
```

The finite residual of this differential equation, together with a
kernel-checked positive rational majorant, proves
`norm_model_sub_eighteen_le`: error at most `4e-14` for `0<=x<=1`,
`Re(s)>=0`, `norm(s)<=22500`. This is a proved error for the actual
complex exponential and logarithm. No infinite-series remainder is assumed.

[ZetaBlockApproximation.zeta_error_lt](../RiemannGaussian/ZetaBlockApproximation.lean)
retains each actual term and its phase, pays every valid consecutive block,
and keeps the original Euler--Maclaurin correction. The total error is
strictly below `1e-9` for `1/2<=Re(s)<=3/2`, `abs(Im(s))<=22000`, `s!=1`,
at cutoff 22020. [ZetaBlockMoments](../RiemannGaussian/ZetaBlockMoments.lean)
proves the exact finite geometric-moment recurrence; the division-free
identity remains valid at resonance. The implementation uses actual arrays
to store moments: a function-valued recurrence caused exponential
recomputation after compiler eta expansion and was replaced.

[ZetaBlockCertificate](../RiemannGaussian/ZetaBlockCertificate.lean)
provides a sound interval evaluator and zero-exclusion checker. All width,
coverage-dependent cutoff and original analytic checks are executable.
[ZetaBlockHardyCertificate](../RiemannGaussian/ZetaBlockHardyCertificate.lean)
pays the same total error inside the bounded phase rotation and proves
signs of actual Hardy Z from successful checks. The existing complete-count
and sign-window matching theorems can consume those signs directly.
[ZetaBlockValidation](../RiemannGaussian/ZetaBlockValidation.lean) checks
18-term and 20-term blocks starting at 6000, at height 22000, with
`decide +kernel`, then bounds the original sums after paying the Taylor
error. These validate the computation paths; they are not new zero counts.

The optional manual native timing probe is:

```bash
lake env lean --run scripts/ProbeZetaBlocks.lean
```

The sound degree-eighteen implementation took about 23 seconds at height
22000, with head 299 and 1167 blocks. Its finite-approximation rectangle
was near `2.32824-1.53213i` and narrower than `3e-8` in each coordinate,
before the separately proved `1e-9` analytic allowance. These **native
execution results are exploratory, not kernel certificates**. The earlier
unproved degree-fourteen prototype took about 19 seconds. Do not mix those
timings or treat the numerical output as a checked zero list.

### Reusing blocks across nearby heights

[Bober–Hiary, section 7](https://arxiv.org/pdf/1607.00709), factors out a
block's main oscillation before reusing its slowly varying inner sum.
Our finite-height implementation uses a degree-twelve correction to that
idea; it does not assume the paper's numerical remainder or reproduce its
high-height implementation.

[ZetaBlockShift](../RiemannGaussian/ZetaBlockShift.lean) treats the exact
factor `g_d(x)=exp(-d*log(1+x/300))`. Its finite coefficients satisfy

```math
a_0(d)=1,\qquad
a_{j+1}(d)=-\frac{d+j}{300(j+1)}a_j(d).
```

The polynomial's differential residual has only one uncancelled term.
An integrating-factor estimate and checked rational majorant prove
error at most `1.25e-17` for `Re(d)=0`, `norm(d)<=64`, `0<=x<=1`.
Combining it with the degree-eighteen center polynomial costs at most
`4.005e-14` per original term.

[ZetaBlockBatch.zeta_error_lt](../RiemannGaussian/ZetaBlockBatch.lean)
pays that error over the complete original prefix and retains the entire
Euler–Maclaurin correction. The full allowance remains strictly below
`1e-9`. Its hypotheses keep both the center size `norm(s)<=22500` and
the actual shifted evaluation rectangle explicit. The corresponding
checker also supports shorter prefixes under the original analytic
domain check.

The exact reusable amplitudes are

```math
V_j(s;v,K)=v^{-s}\sum_{i=0}^{18}c_i(s)G_{i+j}(s;v,K),\qquad
G_\ell=\sum_{k=0}^{K-1}(300k/v)^\ell e^{-sk/v}.
```

Thus 31 geometric moments supply 13 amplitudes, shared by every shift:
the block value is `v^(-d)*sum_{j=0}^{12} a_j(d)*V_j`.
[ZetaBlockBatchPacket](../RiemannGaussian/ZetaBlockBatchPacket.lean)
certifies this cache, and
[ZetaBlockBatchPrefix](../RiemannGaussian/ZetaBlockBatchPrefix.lean)
reuses the exact early terms. Every eighth sample resets the outer phase
using repeated squaring. The exact power law and every rounding operation
are proved; the reset avoids the interval wrapping observed in a naive
chain of rectangular multiplications.

[ZetaBlockBatchCertificate](../RiemannGaussian/ZetaBlockBatchCertificate.lean)
checks each sample's geometry, full shift radius and separation margin.
[ZetaBlockBatchHardy.hardy_sign_of_check](../RiemannGaussian/ZetaBlockBatchHardy.lean)
uses the same bounded Gamma rotation and pays the full error before
concluding a sign of actual Hardy Z. Preparation soundness is proved once
and can be reused; no unverified numerical table is an analytic premise.

The manual benchmark is `lake env lean --run scripts/ProbeZetaBatch.lean`;
an optional argument limits the number of its 257 samples. It stays outside
ordinary CI. The initial phase-reset prototype took about 426 seconds for
257 half-step values from 21836 through 21964, including 107 seconds of
preparation. All exploratory comparisons with 40-digit mpmath values
agreed with the computed rectangles; their largest coordinate width was
less than `1.32e-7`, before the analytic allowance. These are **native
performance and diagnostic results, not kernel certificates**. The
repository implementation has its own manual probe; do not identify a
prototype timing with a kernel-verification cost.

The proved repository implementation's probe took about **641 seconds**
for the same 257 samples: 58 seconds to prepare the cache and 584 seconds
to evaluate the samples. It also kept all coordinate widths below
`1.32e-7`. This is about nine times faster per value than repeating the
previous 23-second evaluator. A preparation-only run took 61 seconds.
All these timings use executable evaluation, not kernel replay. The
current pure evaluator recomputes short phase chains at each sample;
the prototype carried the phase state forward explicitly.

[ZetaBlockCacheCheck](../RiemannGaussian/ZetaBlockCacheCheck.lean) provides
an independent checker for supplied early-term cache entries. Each
candidate rectangle must contain the result of the sound power evaluator.
Its soundness theorem recovers the same exact-prefix premise used by the
batch theorem; numerical data alone supplies no mathematical assumption.
`prefixCheck_cons` assembles independently checked entries into the very
same full-length checker. This matters for kernel cost: in a 40-entry
probe, one combined reduction took 385 seconds, while separate entry
checks and their proof assembly took 43 seconds. Both checks passed in
the kernel. These are small-cache measurements, not a cost projection
for the complete low-zero list.

[ZetaBlockBatchValidation](../RiemannGaussian/ZetaBlockBatchValidation.lean)
discharges actual kernel checks for a direct 20-term block at height
21836 and a compressed 32-term block at heights 21836, 21840 and 21964.
Their conclusions concern the original finite Dirichlet sums and include
the polynomial error. `cached_zeta_nonzero` also checks the entire
40-term cache and Euler–Maclaurin correction, proving
`zeta(1/2+18i) != 0` after a phase reset. Its small-height configuration
is precision `-32`, Taylor depth 12; the high block tests use `-48`, 24.
No supplied cache entry is assumed. Separating the entry checks reduced
this module's measured build from 512 seconds to 84 seconds. The point
at height 18 is a validation case inside the already complete window,
not a new zero-free height. The direct warning-as-error run also passed
in 85 seconds, with peak resident memory about 7 GiB. Its asynchronous
profile includes time waiting behind other kernel checks: the apparent
80-second final-sample span is not an isolated evaluation cost. Separate
linear and balanced-sum probes both took about 7.8 seconds. The balanced
variant was therefore not adopted; it did not demonstrate a scaling gain.

## Complete verification through height 54

[ZetaElevenZeroCompleteness.count_fiftyFour](../RiemannGaussian/ZetaElevenZeroCompleteness.lean)
proves the complete symmetric multiplicity count `C(54)=22`.
`critical_line_through_fiftyFour` proves that every nontrivial zero with
`abs(Im(rho))<=54` has real part one half.
`nonzero_through_fiftyFour` states actual off-line zeta nonvanishing for
`Re(s)>0`, with the pole at one excluded. These are unconditional theorems;
the terminal axiom audit uses only the three standard logical axioms.

The twelve actual Hardy values at
`14,15,22,26,31,34,38,42,44,49,51,54` have alternating signs, beginning
negative. The first four were already checked. The eight additional signs
are in [ZetaHardySamplesFiftyFour](../RiemannGaussian/ZetaHardySamplesFiftyFour.lean).
[ZetaHardyBatchData](../RiemannGaussian/ZetaHardyBatchData.lean) checks all
eighty cached terms and phase increments at precision `-40`, Taylor depth
20. Its lattice starts at height 14, with center 34 and unit spacing.
Each sample retains its own domain checks and the complete analytic error.
The cache and eight sign checks compiled in 124 and 134 seconds respectively.

Completeness uses separate contour evidence.
[GammaThetaFiftyFour.theta_bounds](../RiemannGaussian/GammaThetaFiftyFour.lean)
proves `30<theta(54)<31`, with the unwrapped phase and its analytic error.
[ZetaHeightFiftyFour.horizontal_positive](../RiemannGaussian/ZetaHeightFiftyFour.lean)
covers the entire horizontal segment using the four closed cells
`[1/2,5/8]`, `[5/8,3/4]`, `[3/4,1]`, `[1,3/2]`; the endpoint's imaginary
part is checked independently. The resulting total count exhausts the
eleven positive sign windows and their conjugates, retaining every analytic
multiplicity. No supplied zero table or simplicity premise is assumed.

The contour calculation uses literal prefix checkpoints. Each checkpoint
is proved equal to the original Euler--Maclaurin computation, and the final
check retains the original analytic allowance. One-term checkpoints took
74 seconds for the first cell, versus 152 seconds for ten-term checkpoints.
All five checks passed together in 344 seconds; the earlier monolithic
evaluation was interrupted after 21 minutes without a completed verdict.
The combined checkpoint module peaked at about 17 GiB, so the five cells
are separated into [independent modules](../RiemannGaussian/ZetaHeightFiftyFour/).
Each separate cell check completed in 77–79 seconds, with peak resident
memory below 6.7 GiB. The mathematical conclusions and numerical data are
unchanged by this split.
The manual generator is
`lake env lean --run scripts/GenerateZetaHeightFiftyFour.lean`; it reproduces
all 400 numerical checkpoints. Its output proposes data, while
`decide +kernel` proves every equality and final check.

This extends the **complete finite verification from height 26 to 54**.
It does not reproduce the required low-zero verification through the
published height near 22000. The full list and count, actual prime-count
bounds, short-prime supply and published VK region remain open. The
high-degree Ford moment formula is proved conditional on short-prime
supply; its lower-degree numerical tables remain open. The public default
region and RH arithmetic frontier are unchanged.

Return to the [literature reproduction ledger](vinogradov-literature-reproduction.md).
