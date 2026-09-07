# Arithmetic decay and the exterior-parity steer

The full arithmetic decay theorem remains unproved. The active goal
remains reconstruction of the original leading current and its uniform
weighted arithmetic bound. Both the growing head through `floor(log M)`
and the complete tail beyond `M²` now decay. The intervening arithmetic
band still needs a uniform estimate.

## The exact arithmetic target

For real weights `w`, define

\[
 p_{M,w}=\sum_{n\le M}\frac{\mu(n)w(n)}n,\qquad
 H_\eta(L)=\sum_{m\le L}\frac{(-1)^{m+1}}m,
\]

\[
 C_{M,w}(l)=\sum_{de=l,\ d\le M}\mu(d)w(d)(-1)^{e+1},\qquad
 r_{M,w}(L)=1_{L=1}-\sum_{l\le L}\frac{C_{M,w}(l)}l+p_{M,w}H_\eta(L).
\]

The cutoff on `d` is retained even when `L>M`. The original continuum
residual on `(log L,log(L+1)]` is exactly `exp(t)*r_(M,w)(L)`.
[EtaMoebiusArithmeticCells](../RiemannGaussian/EtaMoebiusArithmeticCells.lean)
proves this identity at the actual endpoints. Since the weighted integral
of its square over that cell is exactly `r_(M,w)(L)^2`,
[EtaMoebiusArithmeticEnergy](../RiemannGaussian/EtaMoebiusArithmeticEnergy.lean)
proves `HasSum`, square summability, and

\[
 E^\infty_{M,w}=\sum_{L\ge1}r_{M,w}(L)^2.
\]

This includes every cell beyond `M`. For bounded weights,
[EtaMoebiusArithmeticTail](../RiemannGaussian/EtaMoebiusArithmeticTail.lean)
proves

\[
 \sum_{L>R}r_{M,w}(L)^2\le\frac{4M^2}{R+1}\quad(R\ge1),
 \qquad
 \sum_{L>(M+1)^4}r_{M,w}(L)^2\le\frac4{(M+1)^2}.
\]

Every fixed cell and every fixed finite prefix tend to zero for the
logarithmic weights, by
[EtaMoebiusArithmeticLocalDecay](../RiemannGaussian/EtaMoebiusArithmeticLocalDecay.lean).
The improved sampling argument below moves the proved vanishing tail to
the smaller cutoff `M²`. The finite prefix through that growing cutoff
has not been proved to tend to zero. Neither tail argument is uniform in
`M` at fixed `R`; they cannot justify exchanging the arithmetic limit and
infinite sum.

## Prime variance retains the interior cancellation

For `w_M(n)=1-log(n)/log(M)`, `M>1`, and `1≤L≤M`,
[EtaMoebiusPrimeArithmetic](../RiemannGaussian/EtaMoebiusPrimeArithmetic.lean)
proves

\[
 r_M(L)=p_M H_\eta(L)-P(L)/\log M,
 \qquad
 P(L)=\sum_{n\le L}\Lambda(n)/n-\sum_{n\le L/2}\Lambda(n)/n.
\]

Put `A=Σ_(L≤M) H_eta(L)^2`, `B=Σ_(L≤M) H_eta(L)P(L)`,
`C=Σ_(L≤M)P(L)^2`, `V=C-B²/A`, and `p*=B/(A log M)`.
[EtaMoebiusPrimeVariance](../RiemannGaussian/EtaMoebiusPrimeVariance.lean)
proves `A≥1`, `V≥0`, and the exact full identity

\[
 E^\infty_M=\frac{V_M}{\log^2 M}+A_M(p_M-p_M^*)^2+
             \sum_{L>M}r_M(L)^2.
\]

Thus changing only a scalar harmonic correction cannot eliminate the
prime variance. Neither `p_M→0` nor the new bound `|p_M|≤5/log M` controls
the full normalization term with its growing coefficient `A_M`.

A floating-point check at `M=10000` found prime-variance contribution
about `0.0270902`, normalization contribution about `0.00000407`, and
residual squares through `256M` about `0.0292848`. These are exploratory
values, not Lean bounds, infinite-tail measurements, or zero certificates.
They suggest that scalar normalization is not the dominant difficulty at
that cutoff; they do not establish an asymptotic rate.

## What was taken from the supplied steer

The local source is
`/home/dbsanfte/riemann/RiemannGaussian_exterior_leakage_endgame_steer.md`.
It proposes parity waves, discrete summation by parts, and signed dyadic
covariance. The following parts are now checked for the actual carrier.

Use the existing right-closed colour to set
`epsilon(x)=1-2*etaUnitIntervalColour(x)`. This is exactly periodic with
period two and agrees with the floor-based square wave off integer
boundaries. Using the right-closed version gives an identity everywhere,
rather than ignoring boundary values.

For `d>0`, `M≤d`, and the original coefficients, let

\[
 F_{d,M,w}(z)=\sum_{j<d}c_j\epsilon((j+1)z).
\]

[EtaMoebiusExteriorParity](../RiemannGaussian/EtaMoebiusExteriorParity.lean)
proves exact periodicity, zero constant-colour contribution, and
`U_(d,M,w)(log(dz))=-F(z)/2` for every `z>0`. It also proves

\[
 F(z)=\sum_{j<d-1}A_{M,w}(d/(j+2))
       [\epsilon((j+2)z)-\epsilon((j+1)z)].
\]

Both boundary terms vanish by the original primitive endpoint theorems.
No absolute value is taken in this identity.

[EtaMoebiusExteriorParityEnergy](../RiemannGaussian/EtaMoebiusExteriorParityEnergy.lean)
proves both substitutions, genuine integrability, and

\[
 E_{\rm exterior}=\frac1{4d}\int_{2/d}^\infty\frac{F(z)^2}{z^2}\,dz,
 \qquad
 E_{\rm exterior}\le E_{\rm near}+\frac{M^2}{2d},
\]

where `E_near` is the same integral on `(2/d,2]`.
[EtaMoebiusParityCovariance](../RiemannGaussian/EtaMoebiusParityCovariance.lean)
proves its exact signed matrix formula on every physical interval
`(a,b]`, `a>0`, using

\[
 K_{a,b}(m,n)=\int_a^b\frac{\Delta\epsilon_m(z)\Delta\epsilon_n(z)}{z^2}\,dz.
\]

Every entry is integrable, and all signed primitive cross terms are kept.
In particular the formula can be instantiated on each proposed dyadic
shell. A separate theorem summing the whole dyadic partition has not yet
been added; no decay estimate for those shell matrices has been proved.

[EtaMoebiusParityBudget](../RiemannGaussian/EtaMoebiusParityBudget.lean)
uses the unrefined grid `d=2^k`, `M=k+1` and proves

\[
 |2\Re\rho-1|W_\rho\le D_k\le E_{{\rm near},k}+B_k,
 \qquad
 B_k=\mathrm{ExteriorAllowance}_k+\tfrac12\mathrm{TrialAllowance}_k\to0.
\]

This preserves the original zero weight and canonical family. No
arithmetic-decay premise or RH assumption is introduced.

## Two points that prevent a premature endgame claim

First, the checked covariance is a short-window integral. The existing
[weighted divisor sampling theorem](../RiemannGaussian/EtaWeightedDivisorSampling.lean)
has cost `constant*(4T²+L)`; its mean-square corollary assumes `T²≤L`.
Its exact gcd form is for a complete common period, with a divisibility
condition for every divisor pair. The parity steer requires a new
comparison retaining the short-window and inverse-square-weight effects.
The present work does not discharge that comparison. The existing
[coherent-band obstruction](../RiemannGaussian/EtaCoherentBandWindowObstruction.lean)
also rules out dropping physical-window dependence in the older region
budget indiscriminately.

Second, the steer's optional estimate
`C_r≤C(k+1)^A*2^(-delta*r)` cannot hold uniformly over all its shells for
this fixed logarithmic family. The compiled input to this rate audit is
[pairedEtaMoebiusArithmeticExterior_twoCell_lower](../RiemannGaussian/EtaMoebiusExteriorTwoCell.lean):

\[
 r_M(2)^2+r_M(3)^2\ge
 \frac{(\log3-\log2)^2}{34\log^2 M}\quad(M\ge3),
\]

with strictly positive numerator constant proved separately. These are
actual exterior cells `2<x≤4`. The following is a mathematical inference
from this checked lower bound and the existing grid-error estimate, not a
new terminal Lean theorem: on the dyadic grid these cells occupy the last
near shell, `r=k-1`; the exponentially small grid-square error cannot erase
their inverse-logarithmic lower rate. A uniform exponential-in-`r` bound
with fixed polynomial cost in `k` would be too strong. This does not
exclude logarithmic decay of the full exterior energy.

The uniform estimate should retain both arithmetic cutoff `M` and
physical scale `X=d*2^(-r)`. The first fixed shells may decay only
logarithmically. The growing region, particularly `X` comparable with `M`,
still carries the prime-variance difficulty.

## Exact quotient amplitudes and decay beyond the quadratic cutoff

[EtaAlternatingHarmonicRemainder](../RiemannGaussian/EtaAlternatingHarmonicRemainder.lean)
proves, including `L=0`,

\[
 I_L=\int_0^1\frac{x^L}{1+x}\,dx,\qquad
 H_\eta(L)-\log2=\eta(L)I_L,
\]

\[
 \frac1{2(L+1)}\le I_L\le
 \frac1{2(L+1)}+\frac1{2(L+1)(L+2)}.
\]

For every positive `L,n`, the compiled
`etaAlternatingHarmonicAmplitude_quotient_error_le` gives

\[
 \left|\frac{I_{\lfloor L/n\rfloor}}n-\frac1{2L}\right|
 \le\frac{n}{2L^2}.
\]

[EtaMoebiusQuotientParity](../RiemannGaussian/EtaMoebiusQuotientParity.lean)
regroups the complete truncated divisor sum and cancels its constant
logarithmic terms exactly:

\[
 r_{M,w}(L)=1_{L=1}+p_{M,w}\eta(L)I_L
 -\sum_{n\le M}\frac{\mu(n)w(n)}n
       \eta(\lfloor L/n\rfloor)I_{\lfloor L/n\rfloor}.
\]

Put `S_(M,w)(L)=Σ_(n≤M) μ(n)w(n)η(floor(L/n))`, the existing weighted
quotient-parity family. For `M≥1,L≥2,|w(n)|≤1`,
[EtaMoebiusQuotientError](../RiemannGaussian/EtaMoebiusQuotientError.lean)
retains the exact error identity and then proves

\[
 \left|r_{M,w}(L)-\frac{p_{M,w}\eta(L)-S_{M,w}(L)}{2L}\right|
 \le\frac{M^2}{L^2},
\]

\[
 r_{M,w}(L)^2\le
 \frac{p_{M,w}^2+|S_{M,w}(L)|^2}{L^2}+\frac{2M^4}{L^4}.
\]

This is a checked comparison for the actual residual. Only the amplitude
error is estimated before the signed quotient family reaches the sampler.
For `R≥M²`, consecutive blocks of length `R` meet the sampler's actual
window condition. Genuine summability permits regrouping all residual
squares, and a reciprocal telescoping majorant includes the whole tail.
Writing `C=finiteCircleSamplingConstant`,
[pairedEtaMoebiusArithmeticSquareTail_le_sampling](../RiemannGaussian/EtaMoebiusArithmeticSamplingTail.lean)
proves

\[
 \sum_{L>R}r_{M,w}(L)^2\le
 \frac{2[p_{M,w}^2+5C(1+\log M)^2M]}R+\frac{4M^4}{R^3}.
\]

At `R=M²`, the exact logarithmic family therefore satisfies

\[
 \sum_{L>M^2}r_M(L)^2\le
 \frac{2p_M^2+4}{M^2}+\frac{10C(1+\log M)^2}{M}\longrightarrow0.
\]

The limit is compiled as
`pairedEtaMoebiusArithmeticSquareTail_quadratic_tendsto_zero`, using
the previously proved `p_M→0`. The terminal theorem
`pairedEtaMoebiusContinuumResidualEnergy_sub_quadraticPrefix_tendsto_zero`
proves that the complete original continuum energy differs from its
unchanged finite square sum through `M²` by a quantity tending to zero.
This reduces the uncontrolled physical range. It does not prove decay
of the growing prefix, its prime variance, or its normalization cost.

## Full comparison with the original balanced floor cells

Put `a_n=μ(n)w(n)` and retain the original `p=Σ_(n≤M) a_n/n`.
[EtaMoebiusBeurlingCells](../RiemannGaussian/EtaMoebiusBeurlingCells.lean)
defines `B(0)=0` and, for `L≥1`,

\[
 B(L)=1-\sum_{n\le M}a_n\lfloor L/n\rfloor+pL
     =1+\sum_{n\le M}a_n\frac{L\bmod n}{n}.
\]

The remainder identity is exact, and bounded original weights imply
`|B(L)|≤1+M` for every physical cell. Let `H(L)=Σ_(n≤L)1/n` and

\[
 R(L)=1_{L\ne0}-\sum_{n\le M}\frac{a_n}{n}H(\lfloor L/n\rfloor)+pH(L).
\]

The same module proves, at all integer endpoints,

\[
 r(L)=R(L)-R(\lfloor L/2\rfloor),\qquad
 R(L+1)-R(L)=\frac{B(L+1)-B(L)}{L+1}.
\]

[EtaDiscreteHardyTransform](../RiemannGaussian/EtaDiscreteHardyTransform.lean)
defines the genuine full tail and transformed coefficient

\[
 T(L)=\sum_{j>L}\frac{B(j)}{j(j+1)},\qquad
 q(L)=\frac{B(L)}{L+1}-T(L).
\]

For bounded cells it proves tail summability and
`|T(L)|≤C/(L+1)`. The exact finite identity is

\[
 \sum_{L=0}^{N}q(L)^2
 =\sum_{L=1}^{N}\frac{B(L)^2}{L(L+1)}+(N+1)T(N)^2.
\]

The boundary term tends to zero with an explicit bound `C²/(N+1)`.
All square sums are proved summable, so the full identity is

\[
 \sum_{L\ge0}q(L)^2=\sum_{L\ge1}\frac{B(L)^2}{L(L+1)}.
\]

The actual primitive and this transform satisfy `q(L)=q(0)+R(L)`.
Consequently the unchanged residual is exactly
`r(L)=q(L)-q(floor(L/2))`, including its empty-cell cancellation.
[EtaDyadicDifferenceEnergy](../RiemannGaussian/EtaDyadicDifferenceEnergy.lean)
proves the full signed cross identity

\[
 \sum_{L\ge0}[q(L)-q(\lfloor L/2\rfloor)]^2
 =3\sum_{L\ge0}q(L)^2
   -2\sum_{L\ge0}q(L)q(\lfloor L/2\rfloor).
\]

Every parent occurs twice, giving exactly doubled parent energy. The
cross series is genuinely summable. Universal inequalities give lower
and upper constants `1/6` and `6`, without assuming arithmetic cancellation.
[pairedEtaMoebiusContinuumResidualEnergy_beurling_bounds](../RiemannGaussian/EtaMoebiusBeurlingComparison.lean)
therefore proves

\[
 \frac16\sum_{L\ge1}\frac{B(L)^2}{L(L+1)}
 \le E^\infty_{M,w}\le
 6\sum_{L\ge1}\frac{B(L)^2}{L(L+1)}.
\]

For the exact logarithmic family, the compiled
`pairedEtaMoebiusContinuumResidualEnergy_tendsto_zero_iff_beurling`
proves equivalence of the two full decay assertions. Neither assertion
is proved. This is an audit of the representation's strength: changing
the eta colour description alone cannot bypass decay of the same
coefficient family's balanced floor-cell norm. The quantitative end
estimates below do not follow from this comparison alone.

## Uniform inverse-logarithmic estimate and growing head decay

[EtaMoebiusLogHarmonicBound](../RiemannGaussian/EtaMoebiusLogHarmonicBound.lean)
uses the exact Möbius convolution

\[
 \sum_{n\le M}\frac{\mu(n)}n H(\lfloor M/n\rfloor)=1 \quad(M\ge1).
\]

Writing `m(M)=Σ_(n≤M) μ(n)/n`, `γ` for the Euler constant, and
`e(M,n)=H(floor(M/n))−log(M/n)−γ`, its retained signed identity is

\[
 p_M\log M=1-\gamma m(M)-\sum_{n\le M}\frac{\mu(n)}n e(M,n).
\]

Lean proves `|m(M)|≤2`, `|e(M,n)|≤2n/M` for `1≤n≤M`, and absolute
value at most `2` for the complete signed remainder sum. Hence
`abs_pairedEtaMoebiusLogHarmonic_le_five_div_log` gives
`|p_M|≤5/log M` at every `M>1`. The sharper main-term limit is now
proved below. The full weighted distance from the prime optimum still
has no decay estimate.

The harmonic Möbius bound is classical; Tao's
[2010 paper, §1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D8B367C2D4EECF135A190CCC1B1D057F/S0004972709000884a.pdf/a-remark-on-partial-sums-involving-the-mobius-function.pdf)
proves the sharper constant `1` by elementary Möbius inversion. The present
Lean proof derives the sufficient constant `2` directly from the repo's
checked full floor identity. No external theorem is added as an axiom,
and no novelty claim is made for this classical normalization argument.

[EtaMoebiusArithmeticGrowingHead](../RiemannGaussian/EtaMoebiusArithmeticGrowingHead.lean)
keeps the exact prime shell `P(L)=Σ_(L/2<n≤L) Λ(n)/n`. The proved
Chebyshev bound `ψ(L)≤6L` gives `0≤P(L)≤12`; the actual alternating
harmonic prefixes have absolute value at most `2`. Substitution into the
original prime-shell identity proves, for `M>1` and `1≤L≤M`,

\[
 |r_M(L)|\le\frac{22}{\log M},\qquad
 \sum_{L\le R}r_M(L)^2\le\frac{484R}{(\log M)^2}\quad(R\le M).
\]

In particular `R=floor(log M)` grows to infinity and the complete head
energy is at most `484/log M→0`. This extends the former fixed-prefix
convergence to a specific growing physical interval. It remains far
short of controlling the prefix through `M²`.

Define `Q_M=Σ_(floor(log M)<L≤M²) r_M(L)^2`. The exact head/middle/tail
split and `pairedEtaMoebiusContinuumResidualEnergy_sub_middle_tendsto_zero`
prove `E^∞_M−Q_M→0`, using both genuine full end estimates. Finally,
[EtaMoebiusMiddleBudget](../RiemannGaussian/EtaMoebiusMiddleBudget.lean)
proves for each actual zero and original stage `k≥7`, with `M=k+1`,

\[
 d_\rho W_\rho\le D_k\le Q_{k+1}+B_k,\qquad
 B_k=\frac{484}{\log(k+1)}+T_{k+1}+A_k\longrightarrow0.
\]

Here `T_M` is the existing complete quadratic-tail allowance and `A_k`
is the unchanged grid/coefficient transport allowance. The compiled
terminal zero theorem is
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_middle`.
No decay bound for `Q_M` has been proved. The new estimate gives no
sharper numerical zero strip or full uniform weighted current bound.

## Complete Euler cancellation and the normalization main term

[MoebiusHarmonicMonotoneTail](../RiemannGaussian/MoebiusHarmonicMonotoneTail.lean)
proves the exact finite Abel identity on every interval `D<n≤M`:

\[
 \sum_{D<n\le M}\frac{\mu(n)}n b(n)
 =b(M)m(M)-b(D+1)m(D)
  -\sum_{D<n<M}[b(n+1)-b(n)]m(n).
\]

For a nonnegative decreasing `b` on that same interval, a proved bound
`|m(n)|≤ε` for all `D≤n≤M` gives absolute value at most `2ε b(D+1)`.
Both endpoints and every increment are retained before this estimate.

Let `C_M=Σ_(n≤M) μ(n)e(M,n)/n` be the complete original Euler correction.
[EtaMoebiusLogEulerCancellation](../RiemannGaussian/EtaMoebiusLogEulerCancellation.lean)
splits it at `D=floor(M/Q)` for an integer `Q≥2`. The low part costs at
most `2/Q`. On the complementary interval, both `H(floor(M/n))` and
`log(M/n)` are nonnegative decreasing weights, each controlled at its
original first endpoint. The resulting full bound is

\[
 |C_M|\le\frac2Q+4\varepsilon(1+\log Q)
 \quad\text{if } |m(n)|\le\varepsilon\text{ for }\lfloor M/Q\rfloor\le n\le M.
\]

The repo's proved harmonic Möbius cancellation makes this entire
complement small at every fixed `Q`; choosing `Q` large controls the
low part. `pairedEtaMoebiusLogEulerCorrection_tendsto_zero` proves
`C_M→0` without replacing the complete sum by finitely many fixed terms.

The unchanged signed identity `p_M log M=1−γ m(M)−C_M` now gives

\[
 p_M\log M\longrightarrow1,
 \qquad e_M:=p_M\log M-1\longrightarrow0.
\]

The compiled main-term theorem is
`pairedEtaMoebiusLogHarmonic_mul_log_tendsto_one` in
[EtaMoebiusNormalizationMainTerm](../RiemannGaussian/EtaMoebiusNormalizationMainTerm.lean).
The original coefficients have not been adjusted to impose this limit.

For the exact prime discrepancy `Δ(L)=H_eta(L)−P(L)`, the same module
proves at every `M>1` and `1≤L≤M`

\[
 \log M\,r_M(L)=\Delta(L)+e_M H_\eta(L),
 \qquad |\log M\,r_M(L)-\Delta(L)|\le2|e_M|.
\]

The convergence to the prime discrepancy is uniform over the entire
growing interior at the cell level. Its complete finite square identity,
for `R≤M`, retains the signed cross moment:

\[
 (\log M)^2\sum_{L\le R}r_M(L)^2
 =\sum_{L\le R}\Delta(L)^2
  +2e_M\sum_{L\le R}H_\eta(L)\Delta(L)
  +e_M^2\sum_{L\le R}H_\eta(L)^2.
\]

A proved sufficient upper bound is

\[
 \sum_{L\le R}r_M(L)^2\le
 \frac{2\sum_{L\le R}\Delta(L)^2+8R e_M^2}{(\log M)^2}.
\]

The factor `R` remains explicit. The new qualitative main-term limit
does not prove decay of this bound at `R=M`, nor has the needed growing
prime-discrepancy square estimate been proved. The exact cross term
remains available for a sharper argument. The complementary range
`M<L≤M²` still retains its truncated quotient correlations. Full
arithmetic decay, the original uniform weighted current bound, and a
new numerical zero strip remain unproved.

## Literature checks and the remaining arithmetic test

Maier and Rassias prove unconditional cancellation in a restricted
large-parameter range of Möbius/cotangent sums; that is not an estimate on
all of the present short shells. [Primary paper](https://arxiv.org/pdf/1806.05070).
Ehm's Gram decomposition explicitly leaves its main Möbius inversion error
to be estimated; it does not supply full residual decay for this project.
[Primary paper, section 8](https://arxiv.org/pdf/2405.06349).

The amplitude comparison and the quadratic-range tail estimate are now
proved above, with the sampler's window cost retained. The next estimate
must control the original band `floor(log M)<L≤M²`, including its
remaining prime-variance contribution on `L≤M`. Full-period covariance formulas and
the present large-window sampling bound do not discharge that estimate.

Wei and Wu's Proposition 1.9 proves that the classical logarithmic
Nyman–Beurling norm tending to zero implies both RH and simplicity of all
zeros. Their Theorem 1.10 also records a boundedness criterion sufficient
for RH. [Published paper](https://www.sciencedirect.com/science/article/pii/S0723086922000524),
[author-hosted preprint](https://bimsa.net/doc/publication/1424.pdf).
The new checked comparison is specifically with the explicit balanced
floor-cell series above. The further identification with the classical
fractional-part integral and its Mellin boundary norm, and a transported
simplicity theorem, have not been formalized. These external results
remain evidence for auditing the fixed logarithmic coefficient choice,
not assumptions inserted into the Lean chain.

Acceptance remains a proof that the actual full square sum, equivalently
the transported full residual, tends to zero. Fixed-cell convergence,
finite numerical decreases, kernel identities, and vanishing allowances
do not satisfy that acceptance condition. No full arithmetic decay,
canonical-deficit decay, new zero strip, or RH proof is claimed.
