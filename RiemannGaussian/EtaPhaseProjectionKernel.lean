import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGram
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A phase-matched exponential projection for the actual eta measure

The real residual keeps the complete two-exponential projection. Its exact
half-line square integral measures the ratio between a zero's two boundary
distances. The complex companion retains the ordinate phase until the eta
zero condition is applied. This is the elementary Hilbert-space projection
mechanism underlying Hardy-space zero bounds, not a positivity assumption.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The exact coefficient removing the exponential at a putative right-half zero. -/
def etaPhaseProjectionCoefficient (beta : ℝ) : ℝ := (2 * beta - 1) / beta

/-- The full real residual of the phase-matched exponential projection. -/
def etaPhaseProjectionResidual (beta t : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * t) - etaPhaseProjectionCoefficient beta * Real.exp (-(beta - 1 / 2) * t)

/-- The projection square retains its cross term and all three original exponential rates. -/
theorem etaPhaseProjectionResidual_sq (beta t : ℝ) :
    etaPhaseProjectionResidual beta t ^ 2 =
      Real.exp (-t) - 2 * etaPhaseProjectionCoefficient beta * Real.exp (-beta * t) +
        etaPhaseProjectionCoefficient beta ^ 2 * Real.exp (-(2 * beta - 1) * t) := by
  have h1 : Real.exp (-(1 / 2) * t) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(beta - 1 / 2) * t) ^ 2 = Real.exp (-(2 * beta - 1) * t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-(1 / 2) * t) * Real.exp (-(beta - 1 / 2) * t) = Real.exp (-beta * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold etaPhaseProjectionResidual
  calc
    _ = Real.exp (-(1 / 2) * t) ^ 2 -
        2 * etaPhaseProjectionCoefficient beta *
          (Real.exp (-(1 / 2) * t) * Real.exp (-(beta - 1 / 2) * t)) +
        etaPhaseProjectionCoefficient beta ^ 2 * Real.exp (-(beta - 1 / 2) * t) ^ 2 := by ring
    _ = _ := by rw [h1, h2, h3]

/-- The residual square is integrable on the entire positive half-line when the right-half exponent is positive. -/
theorem integrableOn_etaPhaseProjectionResidual_sq {beta : ℝ} (hb : 1 / 2 < beta) :
    IntegrableOn (fun t : ℝ ↦ etaPhaseProjectionResidual beta t ^ 2) (Ioi 0) := by
  simp_rw [etaPhaseProjectionResidual_sq]
  have h1 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have h2 := integrableOn_exp_mul_Ioi (by linarith : -beta < 0) 0
  have h3 := integrableOn_exp_mul_Ioi (by linarith : -(2 * beta - 1) < 0) 0
  exact (h1.sub (h2.const_mul (2 * etaPhaseProjectionCoefficient beta))).add
    (h3.const_mul (etaPhaseProjectionCoefficient beta ^ 2))

/-- The complete projection error has its exact boundary-distance ratio, with no tail discarded. -/
theorem integral_etaPhaseProjectionResidual_sq {beta : ℝ} (hb : 1 / 2 < beta) :
    (∫ t : ℝ in Ioi 0, etaPhaseProjectionResidual beta t ^ 2) = ((1 - beta) / beta) ^ 2 := by
  have h1 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have h2 := integrableOn_exp_mul_Ioi (by linarith : -beta < 0) 0
  have h3 := integrableOn_exp_mul_Ioi (by linarith : -(2 * beta - 1) < 0) 0
  simp_rw [etaPhaseProjectionResidual_sq]
  have hsub : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) -
      2 * etaPhaseProjectionCoefficient beta * Real.exp (-beta * t)) (Ioi 0) :=
    h1.sub (h2.const_mul _)
  have hlast : IntegrableOn (fun t : ℝ ↦ etaPhaseProjectionCoefficient beta ^ 2 *
      Real.exp (-(2 * beta - 1) * t)) (Ioi 0) := h3.const_mul _
  rw [integral_add hsub hlast]
  have hmiddle : IntegrableOn (fun t : ℝ ↦
      2 * etaPhaseProjectionCoefficient beta * Real.exp (-beta * t)) (Ioi 0) := h2.const_mul _
  rw [integral_sub h1 hmiddle, integral_const_mul, integral_const_mul]
  have he : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  rw [he, integral_exp_mul_Ioi (by linarith : -beta < 0),
    integral_exp_mul_Ioi (by linarith : -(2 * beta - 1) < 0)]
  simp only [mul_zero, Real.exp_zero]
  unfold etaPhaseProjectionCoefficient
  field_simp [show beta ≠ 0 by linarith, show 2 * beta - 1 ≠ 0 by linarith]
  ring

/-- The actual eta support inherits integrability of the full projection error. -/
theorem integrable_etaPhaseProjectionResidual_sq {beta : ℝ} (hb : 1 / 2 < beta) :
    Integrable (fun t : ℝ ↦ etaPhaseProjectionResidual beta t ^ 2) pairedEtaLogMeasure :=
  Integrable.mono_measure (integrableOn_etaPhaseProjectionResidual_sq hb)
    pairedEtaLogMeasure_le_volume_restrict_Ioi_zero

/-- Restricting the nonnegative residual square to the literal eta support preserves the exact half-line budget. -/
theorem integral_etaPhaseProjectionResidual_sq_le {beta : ℝ} (hb : 1 / 2 < beta) :
    (∫ t : ℝ, etaPhaseProjectionResidual beta t ^ 2 ∂pairedEtaLogMeasure) ≤ ((1 - beta) / beta) ^ 2 := by
  have h := integral_mono_measure pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
    (Eventually.of_forall (fun t : ℝ ↦ sq_nonneg (etaPhaseProjectionResidual beta t)))
    (integrableOn_etaPhaseProjectionResidual_sq hb)
  exact h.trans_eq (integral_etaPhaseProjectionResidual_sq hb)

/-- The critical real exponential belongs to the actual eta support's square-integrable space. -/
theorem memLp_etaPhaseProjectionBase :
    MemLp (fun t : ℝ ↦ Real.exp (-(1 / 2) * t)) 2 pairedEtaLogMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have he : (fun t : ℝ ↦ Real.exp (-(1 / 2) * t) ^ 2) = fun t ↦ Real.exp (-t) := by
    funext t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  simpa using integrable_rexp_neg_mul_pairedEtaLogMeasure (by norm_num : (0 : ℝ) < 1)

/-- The exact residual also belongs to the same actual square-integrable space. -/
theorem memLp_etaPhaseProjectionResidual {beta : ℝ} (hb : 1 / 2 < beta) :
    MemLp (etaPhaseProjectionResidual beta) 2 pairedEtaLogMeasure :=
  (memLp_two_iff_integrable_sq (by unfold etaPhaseProjectionResidual; fun_prop)).mpr
    (integrable_etaPhaseProjectionResidual_sq hb)

end

end RiemannGaussian
