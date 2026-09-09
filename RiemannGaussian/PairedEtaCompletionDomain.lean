/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletedSymmetry

/-!
# Paired eta completion beyond the open critical strip

The completion identity and its logarithmic derivative hold in the whole
positive half-plane away from one and the elementary dyadic factor's
zeros. These are the actual analytic exclusions of this representation;
no xi or eta zero is removed. This wider domain reaches both the upper
spectral strip boundary and the safe half-plane used by Suzuki contours.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The positive-half-plane domain of the nonvanishing eta completion.
The explicit exceptional factors, rather than a strict upper strip bound,
determine the domain. -/
def pairedEtaCompletionDomain : Set ℂ :=
  {s | 0 < s.re ∧ s ≠ 1 ∧ pairedEtaFactor s ≠ 0}

/-- The exact completion domain is open, so its identities can be
differentiated locally. -/
theorem isOpen_pairedEtaCompletionDomain : IsOpen pairedEtaCompletionDomain := by
  have hc : Continuous pairedEtaFactor := continuous_iff_continuousAt.mpr
    fun s => (hasDerivAt_pairedEtaFactor s).continuousAt
  exact (Complex.isOpen_re_gt 0).inter
    ((isOpen_ne_fun continuous_id continuous_const).inter (isOpen_ne_fun hc continuous_const))

/-- The previous open critical strip lies in the full completion domain. -/
theorem mem_pairedEtaCompletionDomain_of_re_lt_one {s : ℂ}
    (hpos : 0 < s.re) (hlt : s.re < 1) : s ∈ pairedEtaCompletionDomain := by
  refine ⟨hpos, ?_, pairedEtaFactor_ne_zero_of_re_lt_one hlt⟩
  intro he
  subst s
  norm_num at hlt

/-- The polynomial and Archimedean completion numerator is nonzero on
the positive half-plane except at one. -/
theorem pairedEtaXiCompletionNumerator_ne_zero_of_re_pos {s : ℂ}
    (hpos : 0 < s.re) (h1 : s ≠ 1) : pairedEtaXiCompletionNumerator s ≠ 0 := by
  have h0 : s ≠ 0 := by
    intro he
    subst s
    norm_num at hpos
  exact mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1.symm))
    (Gammaℝ_ne_zero_of_re_pos hpos)

/-- The original completion factor is nonzero on its full domain. -/
theorem pairedEtaXiCompletionFactor_ne_zero_on_completionDomain {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) : pairedEtaXiCompletionFactor s ≠ 0 :=
  div_ne_zero (pairedEtaXiCompletionNumerator_ne_zero_of_re_pos hs.1 hs.2.1) hs.2.2

/-- The completion factor is analytic on the full positive-half-plane
domain, including eligible points on and beyond `Re(s)=1`. -/
theorem analyticAt_pairedEtaXiCompletionFactor_on_completionDomain {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) : AnalyticAt ℂ pairedEtaXiCompletionFactor s := by
  have hd : DifferentiableOn ℂ pairedEtaXiCompletionFactor pairedEtaCompletionDomain := by
    intro w hw
    exact ((differentiableAt_pairedEtaXiCompletionNumerator hw.1).div
      (hasDerivAt_pairedEtaFactor w).differentiableAt hw.2.2).differentiableWithinAt
  exact hd.analyticAt (isOpen_pairedEtaCompletionDomain.mem_nhds hs)

/-- The explicit polynomial and digamma correction is the numerator's
logarithmic derivative throughout the positive half-plane except at one. -/
theorem logDeriv_pairedEtaXiCompletionNumerator_of_re_pos {s : ℂ}
    (hpos : 0 < s.re) (h1 : s ≠ 1) :
    logDeriv pairedEtaXiCompletionNumerator s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 := by
  have h0 : s ≠ 0 := by
    intro he
    subst s
    norm_num at hpos
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have hlinear : logDeriv (fun z : ℂ => z * (1 - z)) s =
      1 / s + 1 / (s - 1) := by
    have hd : deriv (fun z : ℂ => 1 - z) s = -1 :=
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv.trans (by ring)
    rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => 1 - z)
      s h0 h1s (by fun_prop) (by fun_prop)]
    simp only [logDeriv_apply, deriv_id'', hd]
    field_simp [h0, h1]
    ring
  unfold pairedEtaXiCompletionNumerator
  rw [logDeriv_mul (f := fun z : ℂ => z * (1 - z)) (g := Complex.Gammaℝ)
    s (mul_ne_zero h0 h1s) (Gammaℝ_ne_zero_of_re_pos hpos)
    (by fun_prop) (differentiableAt_Gammaℝ_of_re_pos hpos),
    hlinear, logDeriv_Gammaℝ hpos]
  ring

/-- The same explicit regular correction is the completion logarithmic
derivative on the wider domain. No arithmetic coefficients are changed. -/
theorem logDeriv_pairedEtaXiCompletionFactor_on_completionDomain {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) :
    logDeriv pairedEtaXiCompletionFactor s = pairedEtaArithmeticXiRegularCorrection s := by
  unfold pairedEtaXiCompletionFactor
  rw [logDeriv_div s (pairedEtaXiCompletionNumerator_ne_zero_of_re_pos hs.1 hs.2.1)
    hs.2.2 (differentiableAt_pairedEtaXiCompletionNumerator hs.1)
    (hasDerivAt_pairedEtaFactor s).differentiableAt,
    logDeriv_pairedEtaXiCompletionNumerator_of_re_pos hs.1 hs.2.1, logDeriv_pairedEtaFactor]
  unfold pairedEtaArithmeticXiRegularCorrection
  ring

/-- Completed paired eta equals the actual entire xi on the full
completion domain, with no nonvanishing assumption on either numerator. -/
theorem pairedEtaCompletedXi_eq_riemannXi_on_completionDomain {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) : pairedEtaCompletedXi s = riemannXi s := by
  rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs.1 hs.2.1]
  unfold pairedEtaCompletedXi pairedEtaXiCompletionFactor pairedEtaXiCompletionNumerator
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs.1 hs.2.1]
  change (s * (1 - s) * Complex.Gammaℝ s / pairedEtaFactor s) *
      (pairedEtaFactor s * riemannZeta s) = _
  field_simp [hs.2.2]

/-- The wider completed eta identity holds in a neighborhood, supplying
the local equality needed for every derivative transport. -/
theorem pairedEtaCompletedXi_eventuallyEq_riemannXi_on_completionDomain {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) : pairedEtaCompletedXi =ᶠ[𝓝 s] riemannXi := by
  filter_upwards [isOpen_pairedEtaCompletionDomain.mem_nhds hs] with w hw
  exact pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hw

/-- The explicit correction is analytic throughout the full completion
domain, including its allowed points on the dyadic boundary line. -/
theorem analyticAt_pairedEtaArithmeticXiRegularCorrection_on_completionDomain {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) : AnalyticAt ℂ pairedEtaArithmeticXiRegularCorrection s := by
  have hH := analyticAt_pairedEtaXiCompletionFactor_on_completionDomain hs
  have hn := pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hs
  have heq : pairedEtaArithmeticXiRegularCorrection =ᶠ[𝓝 s]
      logDeriv pairedEtaXiCompletionFactor := by
    filter_upwards [isOpen_pairedEtaCompletionDomain.mem_nhds hs] with w hw
    exact (logDeriv_pairedEtaXiCompletionFactor_on_completionDomain hw).symm
  exact (hH.deriv.div hH hn).congr heq.symm

end
end RiemannGaussian
