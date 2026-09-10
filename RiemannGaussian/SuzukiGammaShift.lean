/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.TrigammaHalfPlane
import RiemannGaussian.SuzukiEtaSmoothSource
import RiemannGaussian.EtaZetaMultiplicitySchwarz

/-!
# A shifted Gamma representation of the actual Suzuki carrier

Three Gamma recurrences move two polynomial factors out of the pole-removed
zeta numerator. The remaining completion curvature is a shifted trigamma
term with positive real part. The exact homogeneous carrier and source are
retained through numerator and denominator zeros on the positive half-plane.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The actual pole-removed zeta numerator after two polynomial factors
are transferred to the Gamma completion. -/
def suzukiGammaShiftNumerator (s : ℂ) : ℂ :=
  riemannZeta₁ s / ((s + 2) * (s + 4))

/-- Three Gamma recurrences, with the repository's xi normalization. -/
def suzukiGammaShiftFactor (s : ℂ) : ℂ :=
  (-8 * (Real.pi : ℂ) ^ 3) * Complex.Gammaℝ (s + 6)

/-- The full logarithmic derivative of the shifted completion. -/
def suzukiGammaShiftCorrection (s : ℂ) : ℂ :=
  -Complex.log Real.pi / 2 + Complex.digamma ((s + 6) / 2) / 2

/-- The arithmetic denominator of the shifted carrier keeps xi plus
its first derivative after multiplication by the common completion. -/
def suzukiGammaShiftDenominator (s : ℂ) : ℂ :=
  deriv suzukiGammaShiftNumerator s +
    (1 + suzukiGammaShiftCorrection s) * suzukiGammaShiftNumerator s

private lemma shift_ne_zero {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a) :
    s + (a : ℂ) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)

/-- The shifted zeta numerator is holomorphic at every point with
positive real part, including the original zeta pole. -/
theorem analyticAt_suzukiGammaShiftNumerator {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ suzukiGammaShiftNumerator s := by
  exact (differentiable_riemannZeta₁.analyticAt s).div
    ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
    (mul_ne_zero (shift_ne_zero hs (a := 2) (by norm_num))
      (shift_ne_zero hs (a := 4) (by norm_num)))

/-- The common completion has no zeros on the positive half-plane. -/
theorem suzukiGammaShiftFactor_ne_zero {s : ℂ} (hs : 0 < s.re) :
    suzukiGammaShiftFactor s ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- The actual shifted completion is holomorphic on the positive half-plane. -/
theorem analyticAt_suzukiGammaShiftFactor {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ suzukiGammaShiftFactor s := by
  have h : DifferentiableOn ℂ suzukiGammaShiftFactor {w : ℂ | 0 < w.re} := by
    intro w hw
    change 0 < w.re at hw
    exact (((differentiableAt_Gammaℝ_of_re_pos (s := w + 6) (by simp; linarith)).comp
      w ((hasDerivAt_id w).add_const 6).differentiableAt).const_mul _).differentiableWithinAt
  exact h.analyticAt ((Complex.isOpen_re_gt 0).mem_nhds hs)

/-- Exact polynomial form of the shifted completion, preserving its
full complex value. -/
theorem suzukiGammaShiftFactor_eq_polynomial {s : ℂ} (hs : 0 < s.re) :
    suzukiGammaShiftFactor s = -s * (s + 2) * (s + 4) * Complex.Gammaℝ s := by
  have hs0 := ne_zero_of_re_pos hs
  have hs2 : s + 2 ≠ 0 := by simpa using shift_ne_zero hs (a := 2) (by norm_num)
  have hs4 : s + 4 ≠ 0 := by simpa using shift_ne_zero hs (a := 4) (by norm_num)
  unfold suzukiGammaShiftFactor
  rw [show s + 6 = (s + 4) + 2 by ring, Complex.Gammaℝ_add_two hs4,
    show s + 4 = (s + 2) + 2 by ring, Complex.Gammaℝ_add_two hs2,
    Complex.Gammaℝ_add_two hs0]
  field_simp
  ring

/-- The shifted factorization equals the actual entire xi function,
including at the removed pole and at every xi zero in this half-plane. -/
theorem suzukiGammaShiftFactor_mul_numerator {s : ℂ} (hs : 0 < s.re) :
    suzukiGammaShiftFactor s * suzukiGammaShiftNumerator s = riemannXi s := by
  rw [suzukiGammaShiftFactor_eq_polynomial hs, suzukiGammaShiftNumerator]
  have hs2 : s + 2 ≠ 0 := by simpa using shift_ne_zero hs (a := 2) (by norm_num)
  have hs4 : s + 4 ≠ 0 := by simpa using shift_ne_zero hs (a := 4) (by norm_num)
  by_cases h1 : s = 1
  · subst s
    norm_num [riemannXi_one, riemannZeta₁_one, Complex.Gammaℝ_one]
  · rw [riemannZeta₁_eq_sub_one_mul h1, riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs h1]
    field_simp [hs2, hs4]
    ring

/-- The logarithmic derivative of the exact shifted completion contains
only the shifted digamma and the constant pi term. -/
theorem logDeriv_suzukiGammaShiftFactor {s : ℂ} (hs : 0 < s.re) :
    logDeriv suzukiGammaShiftFactor s = suzukiGammaShiftCorrection s := by
  have hc : (-8 * (Real.pi : ℂ) ^ 3) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hg := differentiableAt_Gammaℝ_of_re_pos (s := s + 6) (by simp; linarith)
  unfold suzukiGammaShiftFactor
  rw [logDeriv_const_mul s _ hc]
  change logDeriv (Complex.Gammaℝ ∘ (fun w : ℂ => w + 6)) s = _
  rw [logDeriv_comp (g := fun w : ℂ => w + 6) (x := s) hg (by fun_prop),
    logDeriv_Gammaℝ (by simp; linarith)]
  simp [suzukiGammaShiftCorrection]

/-- The actual shifted completion curvature is one quarter of trigamma,
with the chain-rule factor retained exactly. -/
theorem hasDerivAt_suzukiGammaShiftCorrection {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt suzukiGammaShiftCorrection
      (deriv Complex.digamma ((s + 6) / 2) / 4) s := by
  have hz : 0 < ((s + 6) / 2).re := by simp; linarith
  have hd := ((hasDerivAt_digamma_euler hz).comp s
    (((hasDerivAt_id s).add_const 6).div_const 2)).div_const 2
  rw [← deriv_digamma_eq_tsum hz] at hd
  convert! hd.const_add (-Complex.log Real.pi / 2) using 1
  ring

/-- The shifted completion curvature has strictly positive real part
throughout the entire positive half-plane. -/
theorem suzukiGammaShiftCorrection_deriv_re_pos {s : ℂ} (hs : 0 < s.re) :
    0 < (deriv suzukiGammaShiftCorrection s).re := by
  rw [(hasDerivAt_suzukiGammaShiftCorrection hs).deriv]
  simp only [div_ofNat_re]
  exact div_pos (trigamma_re_pos (by simp; linarith)) (by norm_num)

/-- The complete complex shifted curvature is uniformly bounded on the
positive half-plane, including at arbitrarily large imaginary height. -/
theorem norm_deriv_suzukiGammaShiftCorrection_le {s : ℂ} (hs : 0 < s.re) :
    ‖deriv suzukiGammaShiftCorrection s‖ ≤ 1 / 8 := by
  let z : ℂ := (s + 6) / 2
  have hz3 : 3 < z.re := by dsimp [z]; simp; linarith
  have hz : 1 / 2 < z.re := by linarith
  have hm : (5 / 2 : ℝ) ≤ ‖z - 1 / 2‖ := by
    have h := Complex.re_le_norm (z - 1 / 2)
    simp only [sub_re, div_ofNat_re, one_re] at h
    linarith
  have hN : 9 ≤ normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 3)]
  have hden : 90 ≤ 4 * normSq z * (z.re - 1 / 2) := by
    nlinarith [mul_nonneg (show 0 ≤ normSq z - 9 by linarith)
      (show 0 ≤ z.re - 3 by linarith)]
  have herr : ‖deriv Complex.digamma z - (z - 1 / 2)⁻¹‖ ≤ 1 / 90 :=
    (norm_trigamma_sub_midpoint_le hz).trans
      (one_div_le_one_div_of_le (by norm_num) hden)
  have hinv : ‖(z - 1 / 2)⁻¹‖ ≤ 2 / 5 := by
    rw [norm_inv, ← one_div]
    exact (one_div_le_one_div_of_le (by norm_num) hm).trans_eq (by norm_num)
  have hnorm : ‖deriv Complex.digamma z‖ ≤ 1 / 2 := by
    have ht := norm_add_le (deriv Complex.digamma z - (z - 1 / 2)⁻¹) (z - 1 / 2)⁻¹
    rw [sub_add_cancel] at ht
    linarith
  rw [(hasDerivAt_suzukiGammaShiftCorrection hs).deriv, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right hnorm (by norm_num)).trans_eq (by norm_num)

/-- The shifted correction is holomorphic through the entire positive
half-plane; no eta dyadic-factor exclusion is needed. -/
theorem analyticAt_suzukiGammaShiftCorrection {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ suzukiGammaShiftCorrection s := by
  have h : DifferentiableOn ℂ suzukiGammaShiftCorrection {w : ℂ | 0 < w.re} :=
    fun _ hw => (hasDerivAt_suzukiGammaShiftCorrection hw).differentiableAt.differentiableWithinAt
  exact h.analyticAt ((Complex.isOpen_re_gt 0).mem_nhds hs)

/-- The full shifted denominator is holomorphic, including its own
zeros and any common zeros with the numerator. -/
theorem analyticAt_suzukiGammaShiftDenominator {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ suzukiGammaShiftDenominator s := by
  have hF := analyticAt_suzukiGammaShiftNumerator hs
  exact hF.deriv.add ((analyticAt_const.add (analyticAt_suzukiGammaShiftCorrection hs)).mul hF)

/-- The new arithmetic denominator represents the same actual xi plus
derivative at every point of the positive half-plane. -/
theorem suzukiGammaShiftFactor_mul_denominator {s : ℂ} (hs : 0 < s.re) :
    suzukiGammaShiftFactor s * suzukiGammaShiftDenominator s =
      riemannXi s + deriv riemannXi s := by
  have hH := (analyticAt_suzukiGammaShiftFactor hs).differentiableAt
  have hF := (analyticAt_suzukiGammaShiftNumerator hs).differentiableAt
  have hnear : (fun w => suzukiGammaShiftFactor w * suzukiGammaShiftNumerator w) =ᶠ[𝓝 s]
      riemannXi := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with w hw
    exact suzukiGammaShiftFactor_mul_numerator hw
  have hd : deriv riemannXi s = deriv suzukiGammaShiftFactor s * suzukiGammaShiftNumerator s +
      suzukiGammaShiftFactor s * deriv suzukiGammaShiftNumerator s :=
    hnear.deriv_eq.symm.trans (hH.hasDerivAt.mul hF.hasDerivAt).deriv
  have hq : suzukiGammaShiftFactor s * suzukiGammaShiftCorrection s =
      deriv suzukiGammaShiftFactor s := by
    rw [← logDeriv_suzukiGammaShiftFactor hs, logDeriv_apply]
    exact mul_div_cancel₀ _ (suzukiGammaShiftFactor_ne_zero hs)
  rw [hd, ← suzukiGammaShiftFactor_mul_numerator hs, ← hq]
  unfold suzukiGammaShiftDenominator
  ring

/-- The actual spectral denominator has this same shifted factorization,
with the reflected-coordinate derivative sign kept explicitly. -/
theorem suzukiXiEValue_eq_gammaShift {z : ℂ}
    (hz : 0 < (suzukiArithmeticZetaArgument z).re) :
    suzukiXiEValue z = suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z) *
      suzukiGammaShiftDenominator (suzukiArithmeticZetaArgument z) := by
  rw [suzukiGammaShiftFactor_mul_denominator hz,
    suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate,
    riemannXi_one_sub, deriv_riemannXi_one_sub, suzukiXiEValue_eq, deriv_riemannXiSpectral]
  change riemannXi (completedSpectralCoordinate z) + I *
    (I * deriv riemannXi (completedSpectralCoordinate z)) = _
  rw [← mul_assoc, I_mul_I]
  ring

end
end RiemannGaussian
