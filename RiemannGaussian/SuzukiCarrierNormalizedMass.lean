/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaProjectiveCurrent

/-!
# A globally smooth normalized mass for the actual xi carrier

The local xi charts remove common numerator/denominator zeros from the
real mass, just as they do for the complex smooth carrier. This supplies
the regularity needed for integration by parts through the complete
carrier divisor, without deleting repeated xi zeros or genuine poles.
-/

open Complex Filter Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The real mass of a pair, with the full common factor retained until cancellation. -/
private def pairMass (r : ℝ) (a b : ℂ) : ℝ := normSq a / (normSq b + r ^ 2 * normSq a)

private lemma pairMass_mul (r : ℝ) (a b : ℂ) {c : ℂ} (hc : c ≠ 0) :
    pairMass r (c * a) (c * b) = pairMass r a b := by
  have hn : normSq c ≠ 0 := (normSq_pos.mpr hc).ne'
  unfold pairMass
  simp only [map_mul]
  rw [show normSq c * normSq b + r ^ 2 * (normSq c * normSq a) =
      normSq c * (normSq b + r ^ 2 * normSq a) by ring]
  exact mul_div_mul_left _ _ hn

/-- The normalized xi mass uses the original entire numerator and denominator. -/
def suzukiXiNormalizedMass (r : ℝ) (z : ℂ) : ℝ :=
  pairMass r (riemannXiSpectral z) (suzukiXiEValue z)

/-- All xi zeros, including common zeros, have mass zero. -/
theorem suzukiXiNormalizedMass_eq_zero (r : ℝ) {z : ℂ} (hA : riemannXiSpectral z = 0) :
    suzukiXiNormalizedMass r z = 0 := by simp [suzukiXiNormalizedMass, pairMass, hA]

/-- The actual normalized mass is nonnegative everywhere. -/
theorem suzukiXiNormalizedMass_nonneg (r : ℝ) (z : ℂ) :
    0 ≤ suzukiXiNormalizedMass r z := by
  unfold suzukiXiNormalizedMass pairMass
  exact div_nonneg (normSq_nonneg _) (add_nonneg (normSq_nonneg _)
    (mul_nonneg (sq_nonneg _) (normSq_nonneg _)))

/-- A uniform mass bound that also covers every zero of either original factor. -/
theorem suzukiXiNormalizedMass_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    suzukiXiNormalizedMass r z ≤ 1/r^2 := by
  by_cases hA : riemannXiSpectral z = 0
  · rw [suzukiXiNormalizedMass_eq_zero r hA]
    positivity
  have hp := complexSmoothQuotient_denominator_pos hr
    (b := suzukiXiEValue z) (Or.inl hA)
  apply (div_le_div_iff₀ hp (sq_pos_of_pos hr)).mpr
  nlinarith [normSq_nonneg (suzukiXiEValue z)]

/-- On the original regular domain the mass has its literal radial chart. -/
theorem suzukiXiNormalizedMass_eq_regular_chart (r : ℝ) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiNormalizedMass r z = normSq (suzukiXiZeroCarrier z) /
      (1 + r ^ 2 * normSq (suzukiXiZeroCarrier z)) := by
  have h := pairMass_mul r (riemannXiSpectral z / suzukiXiEValue z) 1 hE
  rw [mul_div_cancel₀ _ hE, mul_one] at h
  rw [suzukiXiNormalizedMass, h, suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]
  simp only [pairMass, map_div₀, map_mul, normSq_I, one_mul, normSq_one]

/-- Every xi zero has an actual smooth mass chart, including its central
common-zero value and the original inverse multiplicity. -/
theorem exists_suzukiXiNormalizedMass_zero_chart (rho : NontrivialZetaZero) (r : ℝ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      suzukiXiNormalizedMass r =ᶠ[𝓝 (zetaSpectralCoordinate rho.1)]
        fun z => normSq ((z - zetaSpectralCoordinate rho.1) * q z) /
          (1 + r ^ 2 * normSq ((z - zetaSpectralCoordinate rho.1) * q z)) := by
  obtain ⟨q, p, hq, _hp, hq0, _hp0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  refine ⟨q, hq, hq0, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz
  by_cases hza : z = zetaSpectralCoordinate rho.1
  · subst z
    rw [suzukiXiNormalizedMass_eq_zero r
      ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩)]
    simp
  · have hlocal := hz hza
    rw [suzukiXiNormalizedMass_eq_regular_chart r hlocal.1, hlocal.2.2.1]

/-- The real mass is globally smooth through genuine carrier poles and
all repeated xi zeros; no unproved denominator separation is needed. -/
theorem contDiff_suzukiXiNormalizedMass {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (suzukiXiNormalizedMass r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hA : riemannXiSpectral z = 0
  · obtain ⟨rho, rfl⟩ := (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mp hA
    obtain ⟨q, hq, _hq0, he⟩ := exists_suzukiXiNormalizedMass_zero_chart rho r
    have hqR : ContDiffAt ℝ ∞ (fun z => (z - zetaSpectralCoordinate rho.1) * q z)
        (zetaSpectralCoordinate rho.1) :=
      (contDiffAt_id.sub contDiffAt_const).mul (hq.contDiffAt.restrict_scalars ℝ)
    have hn : ContDiffAt ℝ ∞ (fun z => normSq ((z - zetaSpectralCoordinate rho.1) * q z))
        (zetaSpectralCoordinate rho.1) := by
      simpa only [normSq_eq_norm_sq] using hqR.norm_sq (𝕜 := ℂ)
    exact (hn.div (contDiffAt_const.add (contDiffAt_const.mul hn)) (by simp)).congr_of_eventuallyEq he
  · have hf : ContDiffAt ℝ ∞ (fun z => normSq (riemannXiSpectral z)) z := by
      simpa only [normSq_eq_norm_sq] using
        ((analyticAt_riemannXiSpectral z).contDiffAt.restrict_scalars ℝ).norm_sq (𝕜 := ℂ)
    have hg : ContDiffAt ℝ ∞ (fun z => normSq (suzukiXiEValue z)) z := by
      simpa only [normSq_eq_norm_sq] using
        ((analyticAt_suzukiXiEValue z).contDiffAt.restrict_scalars ℝ).norm_sq (𝕜 := ℂ)
    exact hf.div (hg.add (contDiffAt_const.mul hf))
      (complexSmoothQuotient_denominator_pos hr (Or.inl hA)).ne'

/-- The mass agrees with the literal eta mass on its full completion
domain, including common zeros. The complex completion factor cancels exactly. -/
theorem suzukiXiNormalizedMass_eq_eta (r : ℝ) {z : ℂ}
    (hs : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    suzukiXiNormalizedMass r z = suzukiEtaNormalizedMass r (suzukiArithmeticZetaArgument z) := by
  have hA : riemannXiSpectral z = pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) := by
    rw [show pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
        pairedEtaCore (suzukiArithmeticZetaArgument z) = riemannXi (suzukiArithmeticZetaArgument z) from
      pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hs,
      suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
    rfl
  rw [suzukiXiNormalizedMass, hA, suzukiXiEValue_eq_etaCarrierDenominator_on_completionDomain hs,
    pairMass_mul r _ _ (pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hs)]
  rfl

/-- The current used in integration by parts has a uniform value bound,
with no exception at a pole or a common zero. -/
theorem norm_suzukiXiNormalizedMass_mul_carrier_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖(suzukiXiNormalizedMass r z : ℂ) * suzukiXiSmoothCarrier r z‖ ≤ 1 / (2 * r ^ 3) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (suzukiXiNormalizedMass_nonneg r z)]
  calc
    _ ≤ (1/r^2) * (1/(2*r)) :=
      mul_le_mul (suzukiXiNormalizedMass_le hr z) (norm_suzukiXiSmoothCarrier_le hr z)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end RiemannGaussian
