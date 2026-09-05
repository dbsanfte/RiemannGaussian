# An overnight Lean theorem push from the actual eta support

Research plan prepared on 2026-09-05 against `f016ab7c4b9a8ef819faed7bea48865622840f20`.
The body below records the original proposed targets. The implementation
ledger distinguishes checked results from outstanding work.
The current request changes this session's objective from improving a zero-count
certificate to proving useful auxiliary mathematics for the RH program.

## Implementation ledger

The first implemented slice supplies the actual-support boundary identity
and phase-uniform tail bound (1), the explicit strip masses (2), and
`|D(r) - r log(1/r)| ≤ 5r` on `0 < r ≤ 1/8` in
`EtaLogSupportShift.lean` and `EtaLogSupportCritical.lean`.
`EtaSupportGapGaussianProfile.lean` and `EtaSupportGapGaussian.lean` prove
the continuous displacement identity (4), the exact coefficient
`Ψ(0) = 2/√π`, and (5a) with **`C = 32` on `0 < h ≤ 1`**, uniformly in
every real ordinate. The actual continuous kernel is integrable; no model
measure replaces the eta support.

Still outstanding: the independent cutoff and fixed-ordinate estimates,
the literal eta spectral identity (6), mixed finite Gram coercivity (5b),
kernel normalization (7), the moving-tilt/cubic scaling target (8), and the
review of a quantitative application to the completed signed leading flux.
No RH or improved-proportion milestone follows from the completed slice.

**Recommendation:** make Gaussian heat on the literal eta support quantitative,
retaining its phase channels and its omitted intervals. The core deliverable is
an arithmetic boundary estimate with a uniform phase-dependent remainder, a
critical heat asymptotic uniform in the ordinate, and an identity with the
existing eta Gaussian integrals. The main matrix target is an explicit lower
bound for a finite family of phase probes on this actual continuous support.
A joint scaling limit involving cubic phases and a moving horizontal tilt is
the longer stretch target.

This would close a concrete gap between the repo's continuous eta arithmetic
and its algebra of matrix heat leakage. It would not establish the signed
cancellation still required for RH. Budget one sequential eight-hour session;
the cubic/moving-tilt extension is a stretch target, not a promised deliverable.

## What the checked repository actually supplies

| Building block | Checked result and useful input | Remaining obstruction |
| --- | --- | --- |
| Literal eta support | [InfiniteLaplaceMeasure](../RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure.lean#L219): on `Re s > 0`, the integral over alternating logarithmic intervals equals `pairedEtaCore s / s`. Every actual nontrivial zeta zero annihilates this transform. | Positivity of the measure does not exclude complex zeros. Its arithmetic interval structure must enter an estimate. |
| Omitted eta intervals | [HorizontalDefectGapArithmetic](../RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapArithmetic.lean#L328): the gap transform is exactly `1 / s - pairedEtaLaplacePartition s`. Support and gaps partition positive time. | Mixed support/gap Gaussian correlations have not been quantitatively estimated in the source inspected. |
| Infinite Gaussian arithmetic | [InfiniteGaussianLaplaceGram](../RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGram.lean#L195) and [its localized version](../RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalized.lean): genuine integrability, Fubini, and exact Gaussian Gram identities, including the ordinate-dependent cosine. | The raw positive Gram and the completed reflected energy have different weights. Raw monotonicity does not transfer through completion. |
| Phase colour | [PhaseTwistZeroSide](../RiemannGaussian/External/Zeta23PhaseTwistZeroSide.lean#L159): cubic holonomy factors under an additive relation; parameter averaging gives sinc decay. [FourthMomentPhaseColour](../RiemannGaussian/External/Zeta23FourthMomentPhaseColour.lean#L161): exact fourth-root colour selection. | These are algebraic or averaged statements. A bound after colour averaging does not bound the original channel. Cubic modulation changes the eta transform. |
| Hybrid matrix heat | [ProjectionHeatLeakage](../RiemannGaussian/Hybrid/ProjectionHeatLeakage.lean#L125): compression defects equal retained/complement transition products. [EtaSpectralHeatCubicPaths](../RiemannGaussian/Hybrid/EtaSpectralHeatCubicPaths.lean): ordered one-gap and two-gap paths remain explicit. | Existing coordinate projections are finite matrix projections; they have not been identified with multiplication by the infinite eta support indicator. |
| Actual eta feature geometry | [EtaGeometricPackedFeatureRank](../RiemannGaussian/Hybrid/EtaGeometricPackedFeatureRank.lean#L210): eventual independence on a suitable prime geometric grid. [TwoScalePreconditioned](../RiemannGaussian/Hybrid/EtaGeometricReflectionSignedAggregateTwoScalePreconditioned.lean#L147): exact recovery from adjacent starts. | Nonsingularity and exact recovery supply no uniform conditioning or arithmetic bound. Whitening away the entire metric loses useful amplitudes. |
| Signed eta frontier | [EtaEnergyLeadingFlux](../RiemannGaussian/EtaEnergyLeadingFlux.lean#L598): the first absolute moment of the actual leading flux is summable exactly on the critical line. [KernelFactorization](../RiemannGaussian/EtaEnergyLeadingFluxKernelFactorization.lean#L461): for multiplicity at least two, the flux is an explicit finite eta double integral. | Its cosine and single horizontal crossover require an arithmetic signed estimate. Proving universal first-moment summability is already equivalent to RH. |
| Gaussian/Weil and Suzuki | [GaussianXiLogDerivativeGrowth](../RiemannGaussian/GaussianXiLogDerivativeGrowth.lean#L1235) identifies the arithmetic Gaussian formula with the canonical zero sum. [SuzukiWeilVerticalLimit](../RiemannGaussian/RiemannXiSuzukiWeilVerticalLimit.lean#L462) proves the arithmetic/spectral identity on `Im z > 1/2`. | These are strong terminal bridges, but their missing positivity/vanishing direction is substantial mathematics. Suzuki's checked local positivity does not imply global positivity. |
| Other analytic infrastructure | [Xi inverse-square summability](../RiemannGaussian/GaussianXiInverseSquareSummability.lean#L294), [finite Hardy orthogonality](../RiemannGaussian/FiniteHardyOrthogonality.lean#L260), and [residual determinant geometry](../RiemannGaussian/FiniteHardyMetricDeterminant.lean#L294). | Useful for a later actual-zero operator bridge. They do not identify an arbitrary positive kernel with the xi divisor. |

There are three distinct heat constructions here: logarithmic-time Gaussian
convolution, finite spectral matrix heat, and heat weights on the xi divisor.
Every passage between them needs its own theorem. In particular, the
[reflected-zero heat vanishing criterion](../RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L197)
is not a criterion asserting that the eta-support leakage below vanishes.

## The proposed arithmetic theorem

Use the existing measurable set

\[
A=\bigcup_{n\geq0}(\log(2n+1),\log(2n+2)],\qquad
G=(0,\infty)\setminus A,\qquad \chi=1_A.
\]

For `sigma > 0`, displacement `r > 0`, and a measurable real phase `phi`, define

\[
D_{\sigma,\phi}(r)=\int_0^\infty e^{-2\sigma t}
  (\chi(t+r)-\chi(t))^2
  e^{i(\phi(t+r)-\phi(t))}\,dt.
\]

Keep this complex quantity as the primary object. Its real part and the
uncoloured nonnegative quantity are downstream specializations.

**Core boundary estimate.** For an integer `M >= 2` and
`0 < r <= log((M+1)/M)`, prove

\[
\left|D_{\sigma,\phi}(r)-
 \sum_{n=2}^{M}\int_{\log n-r}^{\log n}
   e^{-2\sigma t}e^{i(\phi(t+r)-\phi(t))}\,dt\right|
 \leq \frac{M^{-2\sigma}}{2\sigma}.                    \tag{1}
\]

The bound is uniform in the phase. No separation hypothesis on zeta zeros,
averaging over colours, or unproved correlation estimate is involved.

The proof uses the actual arithmetic intervals: below `log M`, a displacement
of this size crosses at most one boundary, and the crossing strips are exactly
the disjoint intervals `(log n-r, log n]`, `2 <= n <= M`, up to endpoints.
The rest has modulus bounded by `integral_(log M)^infinity exp(-2 sigma t)`.
Formalize the exact decomposition before its norm bound, so its signed tail
remains available.

For zero phase, each strip integral is explicit:

\[
0\leq D_{\sigma,0}(r)
 -\frac{e^{2\sigma r}-1}{2\sigma}\sum_{n=2}^{M}n^{-2\sigma}
\leq\frac{M^{-2\sigma}}{2\sigma}.                       \tag{2}
\]

Taking `M = floor(1/(2r))`, for sufficiently small positive `r`, makes the
geometric hypothesis automatic. At `sigma = 1/2`, the existing Mathlib
harmonic-number bounds give the quantitative statement

\[
D_{1/2,0}(r)=r\log(1/r)+O(r).                           \tag{3}
\]

Prove an eventual explicit-constant inequality first, then package its limit.
Mathlib already has `log_add_one_le_harmonic`,
`harmonic_le_one_add_log`, and bounds at a natural floor in
`Mathlib/NumberTheory/Harmonic/Bounds.lean`.
Do not create another harmonic-number theory.

The same comparison predicts orders `r`, `r log(1/r)`, and `r^(2 sigma)`
for `sigma > 1/2`, `sigma = 1/2`, and `0 < sigma < 1/2`, respectively.
The critical case is the overnight priority; a full classification can wait.

## Gaussian and literal eta consequences

Fix the normalization, with heat time `h^2`:

\[
p_{h^2}(v)=\frac{e^{-v^2/(4h^2)}}{2\sqrt\pi\,h},\qquad h>0,
\]

\[
\Lambda_{\sigma,\phi}(h)=\int_{t,u>0}
 e^{-\sigma(t+u)}p_{h^2}(t-u)(\chi(t)-\chi(u))^2
 \cos(\phi(t)-\phi(u))\,dt\,du.
\]

Fubini and the displacement substitution should give

\[
\Lambda_{\sigma,\phi}(h)=2\int_0^\infty
 p_{h^2}(r)e^{-\sigma r}\operatorname{Re}D_{\sigma,\phi}(r)\,dr.
                                                               \tag{4}
\]

The main Gaussian target is the sharp leading term with a controlled error:

\[
\Lambda_{1/2,0}(h)
 =\frac{2}{\sqrt\pi}\,h\log(1/h)+O(h),\qquad h\downarrow0. \tag{5}
\]

Its proposed Lean terminal statement is an eventual bound
`abs (leakage - (2 / sqrt pi) * h * log (1 / h)) <= C * h`,
with a proved positive constant and positive small-time range. If the exact
coefficient needs more time, a compiled two-sided `h * log (1/h)` bound is a
useful reduced deliverable, clearly reported as weaker than (5).

**Retain the full ordinate dependence in the same proof.** Define

\[
\Psi(\kappa)=\frac1{\sqrt\pi}\int_0^\infty
 v e^{-v^2/4}\cos(\kappa v)\,dv.
\]

The stronger preferred terminal bound is

\[
\left|\Lambda_{1/2,\,\kappa t/h}(h)
      -h\log(1/h)\Psi(\kappa)\right|\leq C h
\quad\text{for every real }\kappa,                       \tag{5a}
\]

with one constant `C` and one small-time range independent of `kappa`.
This does not require a new exponential-sum estimate: the linear phase in
`D` is exactly `exp(i*kappa*r/h)`. After `r=h*v`, the remainder from (3)
has an integrable absolute majorant independent of `kappa`. Leave `Psi` as
an integral; introducing a special-function formula adds no useful strength.
The scalar result (5) follows from `Psi(0)=2/sqrt pi`.

Two accompanying estimates make this useful for the existing program:

1. Restricting both variables to `(0,L]`, with `L >= 0`, has error at most
   `exp(sigma^2 * h^2) * exp(-2*sigma*L) / sigma`, uniformly in the phase.
   This follows by completing the square after dominating by the full
   Gaussian integral in the other variable. At the critical tilt, choosing
   `L = log(1/h)` makes this `O(h)`. Keep `L` and `h` independent in the
   theorem; fixing the cutoff before taking the heat limit misses the log.
2. For a fixed ordinate phase `phi(t)=gamma*t`,
   `0 <= Lambda_(sigma,0) - Lambda_(sigma,phi)
      <= gamma^2 * h^2 / (2*sigma)`.
   Use `1-cos x <= x^2/2` and the Gaussian second moment. This is only a
   fixed-ordinate control; it is insufficient at `gamma` of order `1/h`.

There is an exact bridge to the literal, untwisted eta function. Put
`P(s) = pairedEtaLaplacePartition s` and use the checked gap identity
`Q(s) = 1/s - P(s)`. Polarize the existing Gaussian/Fubini proof to obtain

\[
\Lambda_{\sigma,\,\gamma t}(h)=\frac1\pi
\int_{\mathbb R}e^{-h^2(y-\gamma)^2}
 \operatorname{Re}\!\left(P(\sigma+iy)
                  \overline{Q(\sigma+iy)}\right)\,dy.     \tag{6}
\]

The coefficient follows from the repo's Fourier convention:
`integral exp(-h^2*y^2) * exp(i*y*v) dy = (sqrt pi / h) *
exp(-v^2/(4*h^2))`. Support/gap symmetry supplies the other factor of two.
Check that normalization explicitly in Lean. Equation (6) concerns the actual
eta transform throughout `sigma > 0`; it is not a replacement model measure.

## Phase colour and the finite/continuous matrix bridge

For a fixed finite family of phases, define the matrix

\[
K_{ij}(h)=\Lambda_{\sigma,\,\phi_j-\phi_i}(h).
\]

It is a genuine Gram matrix: use the positive measure with density
`exp(-sigma*(t+u)) * p_(h^2)(t-u) * (chi(t)-chi(u))^2`
and features `exp(i*(phi_j(t)-phi_j(u)))`. The entries are real by exchanging
`t,u`, but keep the complex Gram representation and all mixed entries.
Prove integrability and positivity from that representation. Fourth-root
colour identities can then select specified combinations exactly; averaging
alone will not establish a bound on the zero-colour entry.

**Quantitative matrix target.** Choose any distinct integer probe labels
`k_1,...,k_m` and set `phi_j(t)=2*pi*k_j*t/h`. These are freely chosen probes;
there is no assumption that actual zero ordinates form an integer grid. Let

\[
B_{ij}=\Psi(2\pi(k_j-k_i)),\qquad c_* = e^{-1}/\sqrt\pi.
\]

Prove `B >= c_* I` in the positive-semidefinite order. The proof is elementary
but retains the whole matrix: write the quadratic form as the average of the
positive and negative frequency exponential squares. Restrict each integral
to `1 <= v <= 2`, where `v*exp(-v^2/4) >= exp(-1)`, and use exact orthogonality
of the distinct integer Fourier modes on this interval.

Equation (5a), followed by finite Cauchy--Schwarz, then gives

\[
K(h)\ \succeq\ h\big(c_*\log(1/h)-mC\big)I.             \tag{5b}
\]

In particular, `log(1/h) >= 2*m*C/c_*` gives the lower bound
`(c_*/2)*h*log(1/h) * I`, within the proved small-time range.
This is an actual arithmetic coercivity theorem, with an explicit dimension
cost, rather than only a Gram identity or an eventual rank theorem. It is
the preferred matrix deliverable for the night. It does not bound the signed
completed eta zero-feature matrix without a further identification theorem.

There is also a precise operator interpretation to guide subsequent work.
On the full real line let `H_s` be convolution by `p_s`, let `P_A` multiply
by `chi`, and let `W_sigma` multiply by
`1_(t>0) * exp(-sigma*t/2)`. The squared integral norm of the kernel of
`W_sigma [P_A,H_(2*h^2)] W_sigma` is

\[
\frac{\Lambda_{\sigma,0}(h)}{4\sqrt\pi\,h}.              \tag{7}
\]

Conjugate that kernel by multiplication by `exp(i*phi_j)` to obtain mixed
kernel inner products `K_ij/(4*sqrt pi*h)`. The diagonal norms are invariant
under this conjugation; the useful phase data are the mixed products.
Equation (7) uses the **half tilt** in each `W_sigma`; using the full tilt
there would move the apparent transition to the wrong value of `sigma`.

For this session, formalize the kernel integrals and their finite Gram matrix.
A complete infinite-dimensional Hilbert--Schmidt operator library or an
exhaustive Galerkin convergence theorem is unnecessary to prove (1)--(6).
Do not identify heat of a compressed generator with compressed continuous
heat. The repo's separate support and finite-compression leakage terms explain
exactly why that identification would need additional estimates.

## The more ambitious auxiliary result

The candidate for a more distinctive result is a **joint critical scaling law
for mixed phase colours**, rather than the uncoloured boundary law alone.
Let

\[
\ell_h=\log(1/h),\quad
\sigma_h=\tfrac12+\lambda/\ell_h,\quad
\phi_h(t)=\kappa t/h+\alpha t^3/(h\ell_h^2).
\]

For fixed real `lambda, kappa, alpha`, small `h` makes `sigma_h > 0`.
The proposed limit is

\[
\frac{\Lambda_{\sigma_h,\phi_h}(h)}{h\ell_h}
\longrightarrow
\mathcal K_\lambda(\kappa,\alpha)
:=\frac1{\sqrt\pi}\int_0^\infty v e^{-v^2/4}
  \int_0^1 e^{-2\lambda z}
        \cos\!\left(v(\kappa+3\alpha z^2)\right)\,dz\,dv. \tag{8}
\]

This is a conjectured target with an explicit proof route, not an established
result of this audit. For `r=h*v`, apply (1), approximate the phase increment
on the boundary at `log n` by
`v * (kappa + 3*alpha*(log n/ell_h)^2)`, and turn the weighted harmonic sum
into an integral in `z=log n/ell_h`. Bound the unresolved tail before the
Gaussian integration. The `lambda=alpha=0` case is the uniform bound (5a)
already targeted in the core; only attempt the moving-tilt/cubic extension
after that bound and its finite matrix consequence are checked.

The constants pass the elementary consistency check

\[
\mathcal K_\lambda(0,0)
=\frac2{\sqrt\pi}\int_0^1e^{-2\lambda z}\,dz,
\qquad \mathcal K_0(0,0)=\frac2{\sqrt\pi}.
\]

A finite family of pairs `(kappa_j,alpha_j)` would yield entrywise convergence
of the normalized mixed Gram matrix to
`mathcal K_lambda(kappa_j-kappa_i,alpha_j-alpha_i)`. Positivity of this limit
has its own integral-of-squares proof. Any norm error bound must retain its
dependence on the number of colours; fixed-size convergence gives no uniform
control over growing zero windows.

Linear phases in (8) still have the literal eta interpretation (6), at
ordinate `kappa/h`. Cubic phases define modulated transforms. Their mixed
kernel identities are legitimate, but those transforms do not inherit eta's
zeros. Retain the untwisted channel explicitly in every proposed use for RH.

## How this could advance the RH program, and what remains open

The immediate gain is an actual arithmetic estimate on a continuous
support/complement transition, with cutoff and phase information preserved.
It supplies a quantitative scale on which a finite representation can
approximate the eta heat integrals. It also identifies a universal leading
boundary contribution that should be separated from any proposed signed
reflection effect.

The existing direct RH target is still

\[
\forall\rho,\quad
\sum_{N\geq0}(2N+1)\,|F_\rho(N)|<\infty,
\]

where `F_rho` is the literal `pairedEtaTopPrefixFiniteEnergyLeadingFlux`.
The repo already proves its equivalence to RH. For multiplicity at least two,
the checked kernel retains a negative centered odd monomial, a positive
cutoff scale, `cos(Im(rho)*(u-t))`, and the bracket

\[
w(1-\overline\rho)e^{-(1-\operatorname{Re}\rho)(t+u)}
 -w(\rho)e^{-\operatorname{Re}\rho(t+u)}.
\]

The next application to investigate is a finite-cutoff pairing theorem that
inserts the new continuous support/gap transition into this signed kernel,
retaining the completion weights and the adjacent moment orders. Such a
theorem must bound a real smoothing or truncation error and state its
dependence on `rho`, multiplicity, and cutoff. The simple-zero head term
needs its separate existing formula; the higher-multiplicity factorization
does not cover it.

Neither (5) nor (8) supplies the sign of the remaining completed reflection
term. A universal positive leakage law is compatible with RH and with the
failure of RH. Its threshold at `1/2` comes from a harmonic boundary sum,
not from a proof that zeros must lie there. If the proposed application only
reproduces a triangle bound or restates the summability criterion, record
that limitation and stop that application. Do not advertise it as an RH step.

## Work sequence and decision gates

Proposed modules use short names; reuse existing definitions instead of
duplicating the long eta families. The ledger above records implemented targets.

| Elapsed time | Work and proposed terminal result | Completion / decision gate |
| --- | --- | --- |
| 0--1 h | `EtaLogSupportShift.lean`: measurable displacement carrier, exact disjoint crossing strips below `log M`, retained complex tail. | Compile the actual-support set identity. If endpoint/parity machinery expands, specialize first to zero phase while preserving the intended decomposition. |
| 1--3 h | Same module: `pairedEtaPhaseMismatch_boundary_error_le`, equation (1); uncoloured harmonic specialization; `pairedEtaMismatch_critical_error_le`, equation (3). | Must prove a quantitative estimate, not stop at a representation. If this takes the entire first four hours, prioritize finishing it and a Gaussian corollary over the scaling extension. |
| 3--5 h | `EtaSupportGapGaussian.lean`: integrability, displacement identity, equation (6), the uniform scaled-ordinate estimate (5a), and uniform cutoff error. | Core success is (1), a proved critical heat bound, and the literal eta bridge. Target (5a) directly so phase dependence survives; label a weaker scalar or two-sided result accurately if that is all that closes. |
| 5--6.5 h | `Hybrid/EtaSupportGapPhaseGram.lean`: mixed finite Gram, Fourier-mode lower bound, and the dimension-dependent actual eta matrix estimate (5b). Kernel normalization (7) is secondary. | A phase Gram identity alone is not a substitute for (5b). Attempt full cubic/moving-tilt asymptotics only after the core matrix estimate is checked and verification time remains protected. |
| 6.5--7 h | Review the exact proposed use in the signed eta leading-flux kernel; prove a bounded finite-cutoff error if its hypotheses follow from available weighted estimates. | Preserve all weights and multiplicities. If no quantitative application closes, explicitly leave this connection open and retain the completed auxiliary theorem as the session result. |
| 7--8 h | Root imports, warning-clean focused builds, project lint, terminal axiom audit, full build, generated-status and whitespace checks. | No placeholders, no custom axioms, no unproved premise presented as progress. Reserve this time even if the stretch target remains open. |

Use the pinned toolchain through
`env ELAN_HOME=/home/dbsanfte/riemann/.lean/elan /home/dbsanfte/riemann/.lean/elan/bin/lake`.
Follow the repository's focused-build, `scripts/LintProject.lean`,
`#print axioms`, and generated-status workflow. Permitted transitive axioms
remain `propext`, `Classical.choice`, and `Quot.sound`. Update research status
only to describe the theorem actually checked. The dashboard must not gain
an RH or improved-proportion milestone from this auxiliary result.

## Routes considered and deprioritized

| Route | Assessment for this overnight session |
| --- | --- |
| Stronger raw eta tail asymptotics | Already extensively developed: [FiniteCenteredTailQuantitativeAsymptotic](../RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTailQuantitativeAsymptotic.lean#L119) gives all-order normalized tail control. Repeating scalar tail work would miss the mixed two-variable estimate. |
| Global Suzuki positivity or vanishing of reflected xi heat | Directly valuable but much larger than the checked local positivity/safe-domain identities. No new arithmetic argument emerged that would make the missing global direction a credible overnight deliverable. |
| Higher prime moments and phase-colour certificate optimization | The continuum `-1/48` calculation, tensor Hilbert bound, and summable frequency tails do not discharge the required prime-correlation asymptotics. This also continues the certificate program the user has moved away from. |
| Generic spectral or cubic commutator coercivity | Existing source and adjacent research notes warn of lost phase information, shrinking colour amplitudes, and misleading finite-model moment fits. Those numerical models are diagnostics, not zeta counterexamples. Require the actual eta interval geometry before pursuing a new coercivity claim. |
| Quantitative conditioning of the two-start eta matrix alone | Concrete backup work, but still requires an arithmetic bound after inversion and careful degeneration near colliding reflection modes. Less useful by itself than estimating an actual continuous eta kernel. |

## Novelty and evidence

The uncoloured mechanism is related to established heat-content/perimeter
asymptotics. [Angiuli, Massari and Miranda, *Geometric properties of the heat
content*](https://cvgmt.sns.it/media/doc/paper/1791/AngMasMir12.pdf) study heat
semigroups and boundary geometry. [Van den Berg and den Hollander,
*Asymptotics for the Heat Content of a Planar Region with a Fractal Polygonal
Boundary*](https://people.maths.bris.ac.uk/~mamvdb/pdfs/Publication55.pdf)
exhibit critical logarithmic behaviour in a different geometric setting.
Neither reference establishes the eta-specific statements proposed here.
The scalar spectral formulation also needs comparison with classical
eta/zeta mean-square estimates before any claim of mathematical originality.

The broader use of arithmetic dilation spaces and Gram matrices for RH also
has substantial prior art: [Alouges, Darses and Hillion, *Polynomial
approximations in a generalized Nyman--Beurling criterion*](https://arxiv.org/abs/2006.02953)
separates approximation from the difficult coefficient control and studies
structured Gram matrices. This is a useful warning against mistaking a new
representation for the missing estimate.

Source searches found no counterpart of (1), (5a), (5b), or (8) in the current
project. The concrete new-in-repo target is the uniform phase estimate and
its dimension-dependent matrix coercivity. The strongest candidate for
original auxiliary mathematics is the quantitative joint phase/moving-tilt
estimate behind (8), together with its actual eta and finite Gram connections.
Priority in the wider literature is
**not established** by this bounded search; use “new in this repository”
until a dedicated comparison justifies a stronger claim.

As a sanity check, floating-point integration in `x=exp(t)` was performed for
the uncoloured critical displacement. The support becomes alternating unit
intervals; merging the endpoints of `x` and `exp(r)*x` avoids a mesh that
misses small intervals. For `r=2^-4, 2^-10, 2^-14`, the truncated ratios
`D_(1/2,0)(r)/(r*log(1/r))` were approximately `1.07287`, `1.01637`, and
`1.01137`. The omitted integral beyond `x=32/r` is at most `r/32`; rounding
error was not certified. These checks support the normalization and the
boundary decomposition only. They prove none of the proposed Lean theorems
and do not validate the full phase scaling conjecture.
