# Completed eta current reconstruction and the weighted arithmetic estimate

The user authorized the full objective on 2026-09-06: **reconstruct the
original leading current and prove the uniform weighted arithmetic
estimate**. The objective remains active until both parts are proved and
verified. The completed [signed endpoint package](eta-signed-endpoint-theorem-plan.md)
provides the actual support, gap, phase, Gaussian, and mixed-matrix inputs.

## Actual target and current status

Write `J_rho(N)` for the existing, unchanged
`pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N`. Its literal kernel is the
completed head at analytic multiplicity one and the completed adjacent-moment
kernel otherwise. In the head branch the physical first time is the shifted
coordinate plus `pairedEtaLogTailCutoff(N+1)`.

The arithmetic target is a bound for

\[
 S_\rho(K)=\sum_{N<K}(2N+1)|J_\rho(N)|
\]

uniform in the upper cutoff `K`, for every actual nontrivial zeta zero.
Any allowed dependence on the zero, analytic multiplicity, and completion
factors must be explicit. This must establish the existing universal
first-absolute-moment summability statement, whose equivalence to RH is
already proved in `EtaEnergyLeadingFluxKernel.lean`. Neither that arithmetic
bound nor RH is currently proved. Reconstruction alone does not complete
the objective.

| Obligation | Evidence | Status |
| --- | --- | --- |
| Integrate the ordered return over the entire actual gap | `integrable_leadingCurrent_gapReturn_prod`, `pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod`, and `pairedEtaLeadingCurrentIntegratedTwoTransition_eq_neg_gapReturn` in [EtaIntegratedGapReturn.lean](../RiemannGaussian/EtaIntegratedGapReturn.lean). | Proved for nonnegative tilts with positive sum, positive widths, and measurable phases. |
| Normalize the actual return and reconstruct the original current | Positive gap mass and dominated broad-heat limit in [EtaBroadGapReturn.lean](../RiemannGaussian/EtaBroadGapReturn.lean); `pairedEtaLeadingCurrent_gapReturn_reconstruction` in [EtaLeadingCurrentReconstruction.lean](../RiemannGaussian/EtaLeadingCurrentReconstruction.lean). | Proved as iterated limits at every fixed zero and cutoff. |
| Quantify the dependence of reconstruction on the arithmetic cutoff | Exact multiplier and signed defect in [EtaGapReturnMultiplier.lean](../RiemannGaussian/EtaGapReturnMultiplier.lean); `pairedEtaLeadingCurrentNormalizedGapReturn_error_le` and its small-tilt bound in [EtaCurrentReconstructionError.lean](../RiemannGaussian/EtaCurrentReconstructionError.lean). | Proved with the actual absolute kernel mass and physical endpoint retained. |
| Control the completed absolute kernel masses across cutoffs | Requires an arithmetic upper bound for the actual `pairedEtaLeadingCurrentAbsoluteKernelMass`. | Open. |
| Prove a signed arithmetic estimate controlling `S_rho(K)` uniformly in `K` | Must preserve completion factors, multiplicity, the head branch, and the correlations needed before taking absolute values. | Open; this is the remaining conjecture-strength objective. |

## Checked reconstruction

Let `G_(sigma,h,tau,k,phi,psi)(t,u,w)` be the existing ordered complex
gap-return core. Its exact identity with two actual commutators has a
negative sign. Before specializing any phase, the new bound is

\[
 |G(t,u,w)|\le
 \frac{e^{-(\sigma+\tau)w/2}}{A(h)A(k)},\qquad
 A(h)=2\sqrt\pi\sqrt2h,
\]

for nonnegative physical endpoint times and tilts, and positive widths.
The literal current is integrable on its finite measure, and the exponential
is integrable on the entire gap when `sigma+tau>0`. Their product proves
genuine three-time integrability. Fubini connects the integrated existing
pairing to the literal current-gap product integral. The negative ordered
two-transition identity survives this integration.

For equal tilts `a>0`, equal widths `h`, and zero probe phases, define

\[
 M(a)=\int_{\mathrm{gap}}e^{-aw}\,dw>0,\qquad
 R_{\rho,N}(a,h)=\frac{8\pi h^2}{M(a)}
 \int_{\mathrm{gap}}\mathrm{GapReturnPairing}_{\rho,N}(a,h,a,h,0,0;w)\,dw.
\]

`pairedEtaLeadingCurrentNormalizedGapReturn` is exactly this normalization of
the existing pairing. Positivity of `M(a)` uses the actual first nonempty gap
interval, and `A(h)^2=8*pi*h^2` is separately proved. Removing the two Gaussian
amplitudes gives the exact profile

\[
 e^{-a(t+u)/2}e^{-aw}
 \exp\left[-\frac{(w-t)^2+(u-w)^2}{8h^2}\right].
\]

It is dominated by `exp(-a*w)` and tends to the same expression without the
Gaussian. Dominated convergence on the actual current-gap product proves

\[
 R_{\rho,N}(a,h)\longrightarrow
 T_{\rho,N}(a)=\int J_{\rho,N}(t,u)e^{-a(t+u)/2}\,d\mu_{\rho,N}(t,u)
 \quad(h\to\infty).
\]

A second dominated-convergence argument proves

\[
 T_{\rho,N}(a)\longrightarrow J_\rho(N)\quad(a\to0^+).
\]

The Lean endpoint is the existing `pairedEtaTopPrefixFiniteEnergyLeadingFlux`,
using the proved exhaustive multiplicity formulas. The completed current is
never replaced by its positive envelope. The raw ordered phase kernel remains
available upstream; only the reconstruction specialization sets the added
probe phases to zero. The ordinate phase inside the completed current remains.

## Checked quantitative error

The new scalar multiplier is the exact gap-time average

\[
 Q_{a,h}(t,u)=\frac1{M(a)}\int_{\mathrm{gap}}e^{-aw}
  \exp\left[-\frac{(w-t)^2+(u-w)^2}{8h^2}\right]\,dw.
\]

It is measurable, genuinely integrable, and between zero and one. Its exact
signed difference from one is retained as an integral before bounding it.
Let `M₂(a)=integral_gap w² exp(-aw) dw`. Lean proves

\[
 0\le M_2(a)\le 2/a^3,\qquad
 |Q_{a,h}(t,u)-1|\le\frac{M_2(a)/M(a)+t^2+u^2}{h^2}.
\]

For `0<a≤1`, monotonicity of the actual gap mass gives
`M₂(a)/M(a) ≤ 2/(M(1)a³)`, with `M(1)>0` proved earlier.
Fubini now identifies the normalized return exactly with the original
current integral against `exp(-a(t+u)/2)*Q`. Consequently its signed error
is the integral of the original current times that multiplier minus one.

The two physical times are proved to lie in `[0,L_N]`, where
`L_N=pairedEtaLogTailCutoff(N+2)=log(2N+5)`, also for the translated head.
Writing `B_rho(N)` for the actual selected kernel's integral of absolute
value, `pairedEtaLeadingCurrentNormalizedGapReturn_error_le` proves

\[
 \|R_{\rho,N}(a,h)-J_\rho(N)\|
 \le B_\rho(N)\left[aL_N+
   \frac{M_2(a)/M(a)+2L_N^2}{h^2}\right].
\]

The small-tilt corollary replaces the moment ratio by `2/(M(1)a³)`.
The factor `B_rho(N)` is finite by the existing genuine kernel integrability;
it has not been assumed bounded or summable across cutoffs. This estimate
controls reconstruction error and does not bound the original signed flux
itself. The separate weighted arithmetic target remains unchanged.

## Next mathematical obligations

1. Bound the actual completed absolute kernel mass across cutoffs, with
   dependence on zero, multiplicity, and completion factors explicit. Use
   that bound and the checked scale errors to select simultaneous tilt and
   heat parameters with a summable cutoff-weighted reconstruction error.
   Preserve the exact signed error integral upstream of this bound.
2. Establish arithmetic cancellation on the retained current or return
   family sufficient to control `S_rho(K)`. Bounds for a positive heat Gram
   or a norm of a single phase channel do not establish the required signed
   completed-current bound. The small-width signed endpoint theorem and the
   broad-width reconstruction concern different regimes; a use of one to
   bound the other requires a proved intervening identity and estimate.
3. Only after that bound is discharged, prove the existing first-moment
   summability statement and use its existing equivalence to derive
   `RiemannHypothesis`. Audit the terminal theorem, all transitive axioms,
   full library, generated status, and exact-commit CI before any completion
   claim.

A candidate for step 1 is a bound of the form
`B_rho(N) ≤ C_rho (1+L_N)^d_rho/(N+1)`, derived from the literal completed
features and the one cutoff increment. With such a proved bound, the explicit
schedule `a_N=(N+1)^(-2)`, `h_N=(N+1)^4` would put both displayed scale
errors at order `(1+L_N)^2/(N+1)^2` or better before the kernel-mass factor.
The weighted error would then have a summable logarithmic-over-square
majorant. The mass bound and this schedule's summability are next proof
targets, not current theorems. Even after them, bounding the reconstructed
signed return itself remains necessary for the full objective.

No reconstruction or summability premise has been introduced as an axiom.
The goal remains open because the uniform weighted arithmetic estimate is
not yet established. No `13/18` certificate or RH proof is claimed.
