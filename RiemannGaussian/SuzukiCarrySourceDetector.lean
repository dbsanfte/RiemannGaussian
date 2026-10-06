/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryCorrelation

/-!
# A phase-retaining source detector for two-scale carry overlap

After the fixed height twist, a matched power component has a positive
overlap response at least one tenth of its source scale. This is an exact
test of a specified component, not an assertion that it is the sole term
of the actual prime sum. Arithmetic gcd bounds for the literal incidences
remain distinct from a global bound on this centered overlap.
-/

namespace RiemannGaussian.SuzukiCarrySourceDetector
noncomputable section
open Complex MeasureTheory Set
open SuzukiIntegerCarryMellinAudit

/-- The literal two-scale overlap retains both floor colours. -/
def overlapColour (t : ℝ) : ℝ := carryLogColour t * carryLogColour (t + Real.log 2)

/-- The real source coefficient after the matched fixed-height twist. -/
def sourceCoefficient (beta : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-beta*t) * overlapColour t

private theorem colour_bounds (t : ℝ) : 0 ≤ carryLogColour t ∧ carryLogColour t ≤ 1 := by
  unfold carryLogColour
  split_ifs <;> norm_num

private theorem measurable_colour : Measurable carryLogColour := by
  exact (measurable_of_countable
    (fun k : ℤ => if Even k then (0 : ℝ) else 1)).comp
      (Int.measurable_floor.comp (measurable_const.mul Real.measurable_exp))

/-- The two-scale support is measurable with its literal endpoint convention. -/
theorem measurable_overlapColour : Measurable overlapColour :=
  measurable_colour.mul (measurable_colour.comp (measurable_id.add measurable_const))

/-- Both colours stay inside the exact unit interval. -/
theorem overlapColour_bounds (t : ℝ) : 0 ≤ overlapColour t ∧ overlapColour t ≤ carryLogColour t := by
  exact ⟨mul_nonneg (colour_bounds t).1 (colour_bounds _).1,
    (mul_le_mul_of_nonneg_left (colour_bounds _).2 (colour_bounds t).1).trans_eq (mul_one _)⟩

/-- A fixed rational interior cell has both colours equal to one. -/
theorem overlapColour_eq_one_on_cell {t : ℝ} (ht : t ∈ Ico (-1/10 : ℝ) 0) :
    overlapColour t = 1 := by
  have hlo : (9/10 : ℝ) ≤ Real.exp t := by linarith [Real.add_one_le_exp t, ht.1]
  have hhi : Real.exp t < 1 := Real.exp_lt_one_iff.mpr ht.2
  have h1 : (⌊2*Real.exp t⌋ : ℤ) = 1 := Int.floor_eq_iff.mpr (by
    norm_num
    constructor <;> linarith [ht.2])
  have h3 : (⌊2*Real.exp (t+Real.log 2)⌋ : ℤ) = 3 := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Int.floor_eq_iff.mpr
    norm_num
    constructor <;> linarith
  have ho1 : ¬Even (1 : ℤ) := by decide
  have ho3 : ¬Even (3 : ℤ) := by decide
  simp only [overlapColour, carryLogColour, h1, h3, if_neg ho1, if_neg ho3, one_mul]

/-- Source-coefficient integrability is proved, so its positivity is not
a formal or totalized-integral assertion. -/
theorem integrable_sourceKernel {beta : ℝ} (hb : 0 < beta) :
    Integrable (fun t : ℝ => Real.exp (-beta*t) * overlapColour t) := by
  have h := (integrable_exp_mul_carryLogColour (s := (beta : ℂ)) (by simpa using hb)).norm
  refine h.mono' ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    measurable_overlapColour).aestronglyMeasurable ?_
  filter_upwards with t
  have hc := colour_bounds t
  have ho := overlapColour_bounds t
  simp only [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc.1, abs_of_nonneg ho.1,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left ho.2 (Real.exp_pos _).le

/-- The matched source has a fixed explicit response, independently of
height and without a hypothetical-zero or prime-density approximation. -/
theorem sourceCoefficient_ge_one_tenth {beta : ℝ} (hb : 0 < beta) :
    (1/10 : ℝ) ≤ sourceCoefficient beta := by
  let cell := Ico (-1/10 : ℝ) 0
  have hi : Integrable (cell.indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (by simp))
  have he : (∫ t : ℝ, cell.indicator (fun _ : ℝ => (1 : ℝ)) t) = (1/10 : ℝ) := by
    rw [integral_indicator_const _ measurableSet_Ico]
    norm_num
  rw [← he]
  apply integral_mono hi (integrable_sourceKernel hb)
  intro t
  change cell.indicator (fun _ : ℝ => (1 : ℝ)) t ≤ Real.exp (-beta*t) * overlapColour t
  by_cases ht : t ∈ cell
  · rw [Set.indicator_of_mem ht, overlapColour_eq_one_on_cell ht, mul_one]
    exact Real.one_le_exp_iff.mpr (by have := ht.2; nlinarith)
  · rw [Set.indicator_of_notMem ht]
    exact mul_nonneg (Real.exp_pos _).le (overlapColour_bounds t).1

/-- Full matched phase cancellation before any integration or norm. -/
theorem matched_mode_overlap_response (beta y T : ℝ) :
    (∫ t : ℝ, Complex.exp (((beta : ℂ)+I*y)*t) * Complex.exp (-(I*y)*t) *
      (overlapColour (T-t) : ℂ)) =
        (Real.exp (beta*T) * sourceCoefficient beta : ℝ) := by
  have hp (t : ℝ) : Complex.exp (((beta : ℂ)+I*y)*t) * Complex.exp (-(I*y)*t) =
      Complex.exp ((beta : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hp]
  have h := integral_sub_left_eq_self
    (fun t : ℝ => Complex.exp ((beta : ℂ)*((T-t : ℝ) : ℂ)) * (overlapColour t : ℂ)) volume T
  have hi (t : ℝ) : T-(T-t) = t := by ring
  simp_rw [hi] at h
  rw [h]
  have he (t : ℝ) : Complex.exp ((beta : ℂ)*((T-t : ℝ) : ℂ)) =
      ((Real.exp (beta*T) * Real.exp (-beta*t) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    rw [← Real.exp_add]
    congr 2
    ring
  simp_rw [he, ← Complex.ofReal_mul]
  simp_rw [mul_assoc]
  rw [integral_complex_ofReal, integral_const_mul]
  rfl

/-- Matched-mode responses are genuinely integrable on the whole line.
The height phase cancels pointwise, before the positive source estimate. -/
theorem integrable_matched_mode_overlap {beta y : ℝ} (hb : 0 < beta) (T : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (((beta : ℂ)+I*y)*t) *
      Complex.exp (-(I*y)*t) * (overlapColour (T-t) : ℂ)) := by
  have h : Integrable (fun t : ℝ => ((Real.exp (beta*T) *
      (Real.exp (-beta*t)*overlapColour t) : ℝ) : ℂ)) :=
    ((integrable_sourceKernel hb).const_mul (Real.exp (beta*T))).ofReal
  refine (h.comp_sub_left T).congr (Filter.Eventually.of_forall (fun t => ?_))
  have hp : Complex.exp (((beta : ℂ)+I*y)*t) * Complex.exp (-(I*y)*t) =
      Complex.exp ((beta : ℂ)*t) := by rw [← Complex.exp_add]; congr 1; ring
  have he : Real.exp (beta*T) * Real.exp (-beta*(T-t)) = Real.exp (beta*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [hp, ← mul_assoc, he, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_mul]

/-- This detector does not annihilate a matched positive-real-part power
component. The lower bound is at its exact source scale. -/
theorem matched_mode_overlap_source_lower {beta y : ℝ} (hb : 0 < beta) (T : ℝ) :
    (1/10 : ℝ)*Real.exp (beta*T) ≤
      (∫ t : ℝ, Complex.exp (((beta : ℂ)+I*y)*t) * Complex.exp (-(I*y)*t) *
        (overlapColour (T-t) : ℂ)).re := by
  rw [matched_mode_overlap_response, Complex.ofReal_re]
  simpa only [mul_comm (1/10 : ℝ)] using
    mul_le_mul_of_nonneg_left (sourceCoefficient_ge_one_tenth hb) (Real.exp_pos _).le

end
end RiemannGaussian.SuzukiCarrySourceDetector
