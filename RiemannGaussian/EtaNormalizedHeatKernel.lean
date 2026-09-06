import RiemannGaussian.EtaSupportGapGaussian

/-!
# Normalization and tilted Gaussian integration for eta heat

Completing the square evaluates the full-line tilted heat envelope. These
identities supply the exact constants for independent time cutoffs and the
weighted commutator-kernel interpretation of support/gap transfer.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The normalized heat kernel in the standard quadratic-exponent form. -/
theorem etaNormalizedHeatKernel_eq_quadratic {h : ℝ} (hh : 0 < h) (r : ℝ) :
    etaNormalizedHeatKernel h r =
      Real.exp (-(1 / (4 * h ^ 2)) * r ^ 2) / (2 * Real.sqrt Real.pi * h) := by
  unfold etaNormalizedHeatKernel
  congr 2
  field_simp

/-- Absolute integrability of the normalized Gaussian at every positive width. -/
theorem integrable_etaNormalizedHeatKernel {h : ℝ} (hh : 0 < h) :
    Integrable (etaNormalizedHeatKernel h) := by
  have hfun : etaNormalizedHeatKernel h =
      (fun r ↦ Real.exp (-(1 / (4 * h ^ 2)) * r ^ 2) / (2 * Real.sqrt Real.pi * h)) :=
    funext (etaNormalizedHeatKernel_eq_quadratic hh)
  rw [hfun]
  exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (4 * h ^ 2))).div_const _

/-- The Gaussian used in the eta heat law has total mass exactly one. -/
theorem integral_etaNormalizedHeatKernel {h : ℝ} (hh : 0 < h) :
    (∫ r : ℝ, etaNormalizedHeatKernel h r) = 1 := by
  simp_rw [etaNormalizedHeatKernel_eq_quadratic hh]
  rw [integral_div, integral_gaussian]
  rw [show Real.pi / (1 / (4 * h ^ 2)) = Real.pi * (2 * h) ^ 2 by field_simp; ring,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (by positivity)]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

/-- The positive tilted heat envelope before the arithmetic mismatch and
phase factors are inserted. -/
def etaTiltedHeatEnvelope (sigma h : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-sigma * (p.1 + p.2)) * etaNormalizedHeatKernel h (p.2 - p.1)

/-- Positivity of the tilted heat envelope at every ordered time pair. -/
theorem etaTiltedHeatEnvelope_pos {h : ℝ} (hh : 0 < h) (sigma : ℝ) (p : ℝ × ℝ) :
    0 < etaTiltedHeatEnvelope sigma h p :=
  mul_pos (Real.exp_pos _) (etaNormalizedHeatKernel_pos hh _)

/-- The full tilted envelope is symmetric in its two times. -/
theorem etaTiltedHeatEnvelope_swap (sigma h : ℝ) (p : ℝ × ℝ) :
    etaTiltedHeatEnvelope sigma h p.swap = etaTiltedHeatEnvelope sigma h p := by
  unfold etaTiltedHeatEnvelope
  change Real.exp (-sigma * (p.2 + p.1)) * etaNormalizedHeatKernel h (p.1 - p.2) = _
  rw [add_comm p.2 p.1, show p.1 - p.2 = -(p.2 - p.1) by ring, etaNormalizedHeatKernel_neg]

/-- Exact completion of the square retains the tilted normalization factor. -/
theorem etaTiltedHeatEnvelope_complete_square {h : ℝ} (hh : 0 < h) (sigma t u : ℝ) :
    etaTiltedHeatEnvelope sigma h (t, u) =
      Real.exp (sigma ^ 2 * h ^ 2 - 2 * sigma * t) *
        etaNormalizedHeatKernel h (u - (t - 2 * sigma * h ^ 2)) := by
  unfold etaTiltedHeatEnvelope etaNormalizedHeatKernel
  rw [← mul_div_assoc, ← mul_div_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- A fixed-time slice of the tilted Gaussian is integrable on the full
real line, even though the exponential tilt alone grows on one side. -/
theorem integrable_etaTiltedHeatEnvelope_slice {h : ℝ} (hh : 0 < h) (sigma t : ℝ) :
    Integrable (fun u : ℝ ↦ etaTiltedHeatEnvelope sigma h (t, u)) := by
  have hf : (fun u : ℝ ↦ etaTiltedHeatEnvelope sigma h (t, u)) =
      (fun u ↦ Real.exp (sigma ^ 2 * h ^ 2 - 2 * sigma * t) *
        etaNormalizedHeatKernel h (u - (t - 2 * sigma * h ^ 2))) :=
    funext (etaTiltedHeatEnvelope_complete_square hh sigma t)
  rw [hf]
  exact ((integrable_etaNormalizedHeatKernel hh).comp_sub_right _).const_mul _

/-- The exact full-line mass of a tilted heat slice. -/
theorem integral_etaTiltedHeatEnvelope_slice {h : ℝ} (hh : 0 < h) (sigma t : ℝ) :
    (∫ u : ℝ, etaTiltedHeatEnvelope sigma h (t, u)) =
      Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * t) := by
  simp_rw [etaTiltedHeatEnvelope_complete_square hh sigma t]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_etaNormalizedHeatKernel hh,
    mul_one, Real.exp_sub]
  rw [show Real.exp (-(2 * sigma) * t) = Real.exp (-(2 * sigma * t)) by congr 1; ring,
    Real.exp_neg]
  ring

/-- Restricting the other time to the positive half-line loses only positive
mass, so the full-line completion-of-square value is an upper bound. -/
theorem integral_Ioi_etaTiltedHeatEnvelope_slice_le {h : ℝ} (hh : 0 < h) (sigma t : ℝ) :
    (∫ u : ℝ in Ioi 0, etaTiltedHeatEnvelope sigma h (t, u)) ≤
      Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * t) := by
  rw [← integral_etaTiltedHeatEnvelope_slice hh sigma t]
  exact setIntegral_le_integral (integrable_etaTiltedHeatEnvelope_slice hh sigma t)
    (Eventually.of_forall fun u ↦ (etaTiltedHeatEnvelope_pos hh sigma (t, u)).le)

/-- Measurability of the two-time tilted envelope. -/
theorem measurable_etaTiltedHeatEnvelope (sigma h : ℝ) :
    Measurable (etaTiltedHeatEnvelope sigma h) := by
  exact (show Continuous (etaTiltedHeatEnvelope sigma h) by
    unfold etaTiltedHeatEnvelope etaNormalizedHeatKernel
    fun_prop).measurable

/-- Integrability of the two-time envelope on the positive quadrant. -/
theorem integrable_etaTiltedHeatEnvelope {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h) :
    Integrable (etaTiltedHeatEnvelope sigma h)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-sigma * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  apply ((he.mul_prod he).const_mul (1 / (2 * Real.sqrt Real.pi * h))).mono'
    (measurable_etaTiltedHeatEnvelope sigma h).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_pos (etaTiltedHeatEnvelope_pos hh sigma p)]
  calc
    etaTiltedHeatEnvelope sigma h p ≤
        Real.exp (-sigma * (p.1 + p.2)) * (1 / (2 * Real.sqrt Real.pi * h)) :=
      mul_le_mul_of_nonneg_left (etaNormalizedHeatKernel_le hh _) (Real.exp_pos _).le
    _ = _ := by
      rw [show -sigma * (p.1 + p.2) = -sigma * p.1 + -sigma * p.2 by ring, Real.exp_add]
      ring

/-- The actual phase kernel is bounded by the positive envelope before any
integration, uniformly over all real phase functions. -/
theorem norm_pairedEtaSupportGapHeatKernel_le_envelope {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (phi : ℝ → ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaSupportGapHeatKernel sigma h phi p‖ ≤ etaTiltedHeatEnvelope sigma h p := by
  rw [pairedEtaSupportGapHeatKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pairedEtaSupportGapHeatWeight_nonneg hh sigma p)]
  calc
    _ ≤ pairedEtaSupportGapHeatWeight sigma h p :=
      mul_le_of_le_one_right (pairedEtaSupportGapHeatWeight_nonneg hh sigma p) (Real.abs_cos_le_one _)
    _ ≤ etaTiltedHeatEnvelope sigma h p :=
      mul_le_of_le_one_right (etaTiltedHeatEnvelope_pos hh sigma p).le (pairedEtaLogShiftMismatch_le_one _ _)

end

end RiemannGaussian
