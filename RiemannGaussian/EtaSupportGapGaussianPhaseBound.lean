import RiemannGaussian.EtaSupportGapGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fixed-ordinate error for actual eta support/gap heat transfer

The exact displacement representation gives a second-moment bound for
removing a fixed linear phase. This supplements the stronger critical bound
uniform at ordinates of order `1/h`; it does not replace that bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Removing a fixed scaled phase can only increase the real heat
correlation, and its loss is controlled by the Gaussian second moment. -/
theorem pairedEtaScaledGaussianMismatch_zero_sub_bounds {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (kappa : ℝ) :
    0 ≤ pairedEtaScaledGaussianMismatch sigma h 0 - pairedEtaScaledGaussianMismatch sigma h kappa ∧
      pairedEtaScaledGaussianMismatch sigma h 0 - pairedEtaScaledGaussianMismatch sigma h kappa ≤
        kappa ^ 2 / (2 * sigma) := by
  let A : ℝ → ℝ := fun v ↦ Real.exp (-(1 / 4) * v ^ 2) * Real.exp (-sigma * (h * v)) *
    pairedEtaMismatch sigma (h * v)
  let R : ℝ → ℝ := fun v ↦ A v * (1 - Real.cos (kappa * v))
  have hA : IntegrableOn A (Ioi 0) := by
    simpa only [zero_mul, Real.cos_zero, mul_one] using
      integrableOn_pairedEtaScaledGaussianMismatch_kernel hsigma hh 0
  have hAc : IntegrableOn (fun v ↦ A v * Real.cos (kappa * v)) (Ioi 0) :=
    integrableOn_pairedEtaScaledGaussianMismatch_kernel hsigma hh kappa
  have hR : IntegrableOn R (Ioi 0) := by
    have hf : R = (fun v ↦ A v - A v * Real.cos (kappa * v)) := by funext v; dsimp [R]; ring
    rw [hf]
    exact hA.sub hAc
  have heq : pairedEtaScaledGaussianMismatch sigma h 0 - pairedEtaScaledGaussianMismatch sigma h kappa =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0, R v := by
    have hf : R = (fun v ↦ A v - A v * Real.cos (kappa * v)) := by funext v; dsimp [R]; ring
    rw [hf, integral_sub hA hAc]
    simp only [pairedEtaScaledGaussianMismatch, zero_mul, Real.cos_zero, mul_one]
    change (1 / Real.sqrt Real.pi) * (∫ v in Ioi 0, A v) -
      (1 / Real.sqrt Real.pi) * (∫ v in Ioi 0, A v * Real.cos (kappa * v)) = _
    ring
  have hRnonneg : ∀ v : ℝ, 0 ≤ R v := fun v ↦
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (pairedEtaMismatch_nonneg sigma (h * v))) (sub_nonneg.mpr (Real.cos_le_one _))
  have hmajor : ∀ᵐ v ∂volume.restrict (Ioi 0),
      R v ≤ (kappa ^ 2 / (4 * sigma)) * (v ^ 2 * Real.exp (-(1 / 4) * v ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hvpos : 0 < v := hv
    have he : Real.exp (-sigma * (h * v)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hh hvpos])
    have hD := pairedEtaMismatch_le_inv hsigma (h * v)
    have hDnonneg := pairedEtaMismatch_nonneg sigma (h * v)
    have hcos : 1 - Real.cos (kappa * v) ≤ (kappa * v) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := kappa * v)]
    have hcospos : 0 ≤ 1 - Real.cos (kappa * v) := sub_nonneg.mpr (Real.cos_le_one _)
    have hweight : Real.exp (-sigma * (h * v)) * pairedEtaMismatch sigma (h * v) ≤
        1 / (2 * sigma) := by
      exact (mul_le_of_le_one_left hDnonneg he).trans hD
    calc
      R v = Real.exp (-(1 / 4) * v ^ 2) *
          (Real.exp (-sigma * (h * v)) * pairedEtaMismatch sigma (h * v)) *
          (1 - Real.cos (kappa * v)) := by dsimp [R, A]; ring
      _ ≤ Real.exp (-(1 / 4) * v ^ 2) * (1 / (2 * sigma)) * ((kappa * v) ^ 2 / 2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hweight (Real.exp_pos _).le) hcos
          hcospos (by positivity)
      _ = _ := by ring
  have hb := integral_mono_ae hR
    (integrableOn_sq_mul_etaHeatGaussian.const_mul (kappa ^ 2 / (4 * sigma))) hmajor
  rw [integral_const_mul, integral_sq_mul_etaHeatGaussian] at hb
  rw [heq]
  constructor
  · exact mul_nonneg (by positivity) (integral_nonneg hRnonneg)
  · calc
      _ ≤ (1 / Real.sqrt Real.pi) * ((kappa ^ 2 / (4 * sigma)) * (2 * Real.sqrt Real.pi)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = kappa ^ 2 / (2 * sigma) := by
        have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
        field_simp
        ring

/-- Fixed-ordinate phase removal for the literal continuous eta heat
kernel, with the exact second-moment bound `gamma^2 * h^2 / (2 sigma)`. -/
theorem pairedEtaSupportGapGaussianLeakage_fixed_phase_bounds {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (gamma : ℝ) :
    0 ≤ pairedEtaSupportGapGaussianLeakage sigma h (fun _ ↦ 0) -
        pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ gamma * t) ∧
      pairedEtaSupportGapGaussianLeakage sigma h (fun _ ↦ 0) -
        pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ gamma * t) ≤
          gamma ^ 2 * h ^ 2 / (2 * sigma) := by
  have hzero : pairedEtaSupportGapGaussianLeakage sigma h (fun _ ↦ 0) =
      pairedEtaScaledGaussianMismatch sigma h 0 := by
    simpa only [zero_mul, mul_zero] using
      pairedEtaSupportGapGaussianLeakage_linear_eq_scaled hsigma hh 0
  rw [hzero, pairedEtaSupportGapGaussianLeakage_linear_eq_scaled hsigma hh]
  have hb := pairedEtaScaledGaussianMismatch_zero_sub_bounds hsigma hh (h * gamma)
  rw [show (h * gamma) ^ 2 / (2 * sigma) = gamma ^ 2 * h ^ 2 / (2 * sigma) by ring] at hb
  exact hb

end

end RiemannGaussian
