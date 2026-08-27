import RiemannGaussian.RiemannXiHyperbolicPoissonDefect

/-!
# Finite-window decomposition of the genuine spectral-xi logarithmic derivative

This file separates `logDeriv riemannXiSpectral` into the literal
multiplicity-weighted Cauchy principal sum over one finite spectral window and
a remainder.  The remainder is proved removable at every selected zero and
therefore admits one analytic representative on the complete contour
rectangle.  No global partial-fraction identity and no vanishing of the
remainder are assumed.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The genuine multiplicity-weighted Cauchy principal part at one spectral
xi zero. -/
def zetaSpectralLogDerivativePrincipalPart
    (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) /
    (z - zetaSpectralCoordinate rho.1)

/-- A principal part is analytic away from its selected spectral zero. -/
theorem analyticAt_zetaSpectralLogDerivativePrincipalPart_of_ne
    (rho : NontrivialZetaZero) {z : ℂ}
    (hz : z ≠ zetaSpectralCoordinate rho.1) :
    AnalyticAt ℂ (zetaSpectralLogDerivativePrincipalPart rho) z := by
  unfold zetaSpectralLogDerivativePrincipalPart
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hz)

/-- The finite multiplicity-weighted Cauchy sum over a symmetric spectral
window. -/
def riemannXiSpectralWindowCauchySum (T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaSpectralLogDerivativePrincipalPart rho z

/-- The raw difference between the actual spectral-xi logarithmic derivative
and its finite window of genuine principal parts. -/
def riemannXiSpectralWindowLogDerivativeRawRemainder
    (T : ℝ) (z : ℂ) : ℂ :=
  logDeriv riemannXiSpectral z - riemannXiSpectralWindowCauchySum T z

/-- Exact pointwise decomposition.  This is bookkeeping, but importantly the
left side is the actual `xi'/xi` and every coefficient on the right has
already been identified with analytic zeta-zero multiplicity. -/
theorem logDeriv_riemannXiSpectral_eq_windowCauchySum_add_rawRemainder
    (T : ℝ) (z : ℂ) :
    logDeriv riemannXiSpectral z =
      riemannXiSpectralWindowCauchySum T z +
        riemannXiSpectralWindowLogDerivativeRawRemainder T z := by
  unfold riemannXiSpectralWindowLogDerivativeRawRemainder
  ring

/-- Inside the horizontal range of the window, the raw remainder is analytic
away from the finite selected zero set. -/
theorem analyticAt_riemannXiSpectralWindowLogDerivativeRawRemainder_of_not_mem
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hzRe : |z.re| ≤ T)
    (hz : z ∉ spectralXiZeroWindow T) :
    AnalyticAt ℂ
      (riemannXiSpectralWindowLogDerivativeRawRemainder T) z := by
  have hxi : riemannXiSpectral z ≠ 0 := by
    intro hzero
    exact hz ((mem_spectralXiZeroWindow_iff hT z).mpr ⟨hzero, hzRe⟩)
  unfold riemannXiSpectralWindowLogDerivativeRawRemainder
    riemannXiSpectralWindowCauchySum
  apply (analyticAt_logDeriv_riemannXiSpectral_of_ne hxi).sub
  have hterm (rho : NontrivialZetaZero)
      (hrho : rho ∈ spectralZetaZeroWindow T) :
      AnalyticAt ℂ (zetaSpectralLogDerivativePrincipalPart rho) z := by
    apply analyticAt_zetaSpectralLogDerivativePrincipalPart_of_ne
    intro hzr
    apply hz
    apply Finset.mem_image.mpr
    exact ⟨rho, hrho, hzr.symm⟩
  exact analyticAt_finset_sum_apply
    (spectralZetaZeroWindow T)
    zetaSpectralLogDerivativePrincipalPart hterm

/-- At each selected zero, the raw finite-window remainder agrees on a
punctured neighborhood with a function analytic through that zero. -/
theorem exists_riemannXiSpectralWindowLogDerivativeRawRemainder_eq_analyticAt
    {T : ℝ} (_hT : 0 ≤ T) (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate rho.1) ∧
      riemannXiSpectralWindowLogDerivativeRawRemainder T =ᶠ[
        𝓝[≠] zetaSpectralCoordinate rho.1] h := by
  obtain ⟨k, hk, horiginal⟩ :=
    exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic rho
  let W := spectralZetaZeroWindow T
  let h : ℂ → ℂ := fun z =>
    k z - ∑ sigma ∈ W.erase rho,
      zetaSpectralLogDerivativePrincipalPart sigma z
  have hother :
      AnalyticAt ℂ
        (fun z => ∑ sigma ∈ W.erase rho,
          zetaSpectralLogDerivativePrincipalPart sigma z)
        (zetaSpectralCoordinate rho.1) := by
    have hterm (sigma : NontrivialZetaZero)
        (hsigma : sigma ∈ W.erase rho) :
        AnalyticAt ℂ (zetaSpectralLogDerivativePrincipalPart sigma)
          (zetaSpectralCoordinate rho.1) := by
      apply analyticAt_zetaSpectralLogDerivativePrincipalPart_of_ne
      intro heq
      have hval : rho.1 = sigma.1 :=
        zetaSpectralCoordinate_injective heq
      have hrs : rho = sigma := Subtype.ext hval
      exact (Finset.mem_erase.mp hsigma).1 hrs.symm
    exact analyticAt_finset_sum_apply (W.erase rho)
      zetaSpectralLogDerivativePrincipalPart hterm
  have hh : AnalyticAt ℂ h (zetaSpectralCoordinate rho.1) := by
    unfold h
    exact hk.sub hother
  refine ⟨h, hh, ?_⟩
  filter_upwards [horiginal] with z hz
  unfold riemannXiSpectralWindowLogDerivativeRawRemainder
    riemannXiSpectralWindowCauchySum h
  rw [hz]
  have hsum := W.add_sum_erase
    (fun sigma => zetaSpectralLogDerivativePrincipalPart sigma z) hrho
  rw [← hsum]
  unfold zetaSpectralLogDerivativePrincipalPart
  ring

/-- The finite-window logarithmic-derivative remainder has one analytic
representative throughout the complete safe contour rectangle, while agreeing
with the raw difference away from the finite window divisor. -/
theorem exists_riemannXiSpectralWindowLogDerivativeRegularization
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ spectralContourRectangle T, AnalyticAt ℂ F z) ∧
      (∀ z ∉ spectralXiZeroWindow T,
        F z = riemannXiSpectralWindowLogDerivativeRawRemainder T z) := by
  apply exists_analyticAtOn_of_finite_removable
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, rfl⟩
    constructor
    · exact (mem_spectralZetaZeroWindow hT rho).mp hrho
    · exact (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le.trans
        (by norm_num)
  · intro z hzU hz
    exact
      analyticAt_riemannXiSpectralWindowLogDerivativeRawRemainder_of_not_mem
        hT hzU.1 hz
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, rfl⟩
    exact
      exists_riemannXiSpectralWindowLogDerivativeRawRemainder_eq_analyticAt
        hT rho hrho

end

end RiemannGaussian
