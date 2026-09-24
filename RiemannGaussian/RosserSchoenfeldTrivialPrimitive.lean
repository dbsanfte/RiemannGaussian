/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldZeroPrimitive
import RiemannGaussian.RiemannXiSuzukiWeilArchimedean
import Mathlib.NumberTheory.ZetaValues

/-!
# The complete trivial-zero correction in logarithmic time

The convergent series `(1-exp(-2*n*t))/(4*n^2)`, for `n >= 1`,
is retained exactly. Its bound and Laplace transform account for the
entire gamma correction in the smoothed prime explicit formula.
-/

namespace RiemannGaussian.RosserSchoenfeldTrivialPrimitive
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open RosserSchoenfeldLaplace

/-- The uniform positive trivial-zero weight. -/
def weight (n : ℕ) : ℝ := 1/(4*((n : ℝ)+1)^2)

/-- The full logarithmic primitive of a negative even zero. -/
def term (n : ℕ) (t : ℝ) : ℂ :=
  (((1-Real.exp (-2*((n : ℝ)+1)*t))/(4*((n : ℝ)+1)^2) : ℝ) : ℂ)

/-- All negative even zeros, with no cutoff. -/
def value (t : ℝ) : ℂ := ∑' n : ℕ, term n t

/-- The exact sum of the uniform trivial-zero weights. -/
theorem hasSum_weight : HasSum weight (Real.pi^2/24) := by
  have hh := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    div_zero, sub_zero] at hh
  have h := hh.mul_left (1/4 : ℝ)
  convert! h using 1
  · funext n
    simp only [weight, Nat.cast_add, Nat.cast_one]
    field_simp
  · ring

/-- Each exact correction is nonnegative and bounded by its uniform weight. -/
theorem norm_term_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖term n t‖ ≤ weight n := by
  have hn : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have he : Real.exp (-2*((n : ℝ)+1)*t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hpos : 0 ≤ (1-Real.exp (-2*((n : ℝ)+1)*t))/(4*((n : ℝ)+1)^2) := by positivity
  rw [term, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [Real.exp_pos (-2*((n : ℝ)+1)*t)]

/-- The full correction is absolutely summable at every nonnegative time. -/
theorem summable_norm_term {t : ℝ} (ht : 0 ≤ t) : Summable (fun n : ℕ => ‖term n t‖) :=
  hasSum_weight.summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le n ht)

/-- Uniform bound for the complete trivial-zero contribution. -/
theorem norm_value_le {t : ℝ} (ht : 0 ≤ t) : ‖value t‖ ≤ Real.pi^2/24 := by
  have hh := (summable_norm_term ht).tsum_le_tsum (fun n => norm_term_le n ht) hasSum_weight.summable
  rw [hasSum_weight.tsum_eq] at hh
  exact (norm_tsum_le_tsum_norm (summable_norm_term ht)).trans hh

/-- Uniform convergence preserves continuity, including at time zero. -/
theorem continuousOn_value : ContinuousOn value (Ici 0) :=
  continuousOn_tsum (fun _ => (by unfold term; fun_prop : Continuous (term _)).continuousOn)
    hasSum_weight.summable (fun n _ ht => norm_term_le n ht)

/-- The correction has no unaccounted constant at the origin. -/
@[simp] theorem value_zero : value 0 = 0 := by simp [value, term]

private theorem term_eq_neg_atom (n : ℕ) (t : ℝ) :
    term n t = -RosserSchoenfeldZeroPrimitive.atom (-2*((n : ℂ)+1)) t := by
  unfold term RosserSchoenfeldZeroPrimitive.atom
  push_cast
  ring

/-- Each exact trivial-zero contribution has an absolutely convergent transform. -/
theorem integrable_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*term n t) (Ioi 0) := by
  have hz : (-2*((n : ℂ)+1)).re < s.re := by simp; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := (RosserSchoenfeldZeroPrimitive.integrable_atom hs hz).neg
  apply hh.congr
  filter_upwards with t
  simp only [term_eq_neg_atom, mul_neg, Pi.neg_apply]

private lemma norm_damped_term (s : ℂ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-s*t)*term n t‖ ≤ Real.exp (-s.re*t)*weight n := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (norm_term_le n ht) (Real.exp_nonneg _)

/-- The absolute integrals are summable over the complete trivial divisor. -/
theorem summable_integral_norm {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖Complex.exp (-s*t)*term n t‖) := by
  have hd := integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) (0 : ℝ)
  apply (hasSum_weight.summable.mul_left (∫ t : ℝ in Ioi 0, Real.exp (-s.re*t))).of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun _ => norm_nonneg _)
  · intro n
    have hh := integral_mono_ae (integrable_term hs n).norm (hd.mul_const (weight n)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_damped_term s n ht.le)
    simpa only [integral_mul_const] using hh

/-- The complete correction has a genuinely integrable Laplace kernel. -/
theorem integrable_value {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*value t) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) (0 : ℝ)).mul_const (Real.pi^2/24)).mono'
  · exact ((show Continuous (fun t : ℝ => Complex.exp (-s*t)) by fun_prop).continuousOn.mul
      (continuousOn_value.mono Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (norm_value_le ht.le) (Real.exp_nonneg _)

private theorem integral_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-s*t)*term n t) =
      suzukiWeilDigammaDifferenceSummand (1+s/2) 1 n / (2*s^2) := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hn : (n : ℂ)+1 ≠ 0 := ne_zero_of_re_pos (by simp; positivity)
  have hz : (-2*((n : ℂ)+1)).re < s.re := by simp; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hz0 : -2*((n : ℂ)+1) ≠ 0 := mul_ne_zero (by norm_num) hn
  have hsum : (n : ℂ)+(1+s/2) ≠ 0 := ne_zero_of_re_pos (by simp; positivity)
  have hsum2 : 2+s+(n : ℂ)*2 ≠ 0 := ne_zero_of_re_pos (by simp; positivity)
  simp only [term_eq_neg_atom, mul_neg, integral_neg]
  change -transform s (RosserSchoenfeldZeroPrimitive.atom (-2*((n : ℂ)+1))) = _
  rw [RosserSchoenfeldZeroPrimitive.transform_atom hs hz hz0]
  unfold suzukiWeilDigammaDifferenceSummand
  rw [show s-(-2*((n : ℂ)+1)) = 2*((n : ℂ)+(1+s/2)) by ring]
  field_simp
  ring_nf
  linear_combination mul_inv_cancel₀ hsum2

/-- Exact Laplace transform of the full trivial-zero correction. -/
theorem transform_value {s : ℂ} (hs : 0 < s.re) :
    transform s value =
      (Complex.digamma (1+s/2)+(Real.eulerMascheroniConstant : ℂ))/(2*s^2) := by
  have hh := integral_tsum_of_summable_integral_norm (integrable_term hs)
    (summable_integral_norm hs)
  have he : (fun t : ℝ => ∑' n : ℕ, Complex.exp (-s*t)*term n t) =
      (fun t : ℝ => Complex.exp (-s*t)*value t) := by
    funext t
    rw [tsum_mul_left]
    rfl
  rw [he] at hh
  rw [transform, ← hh]
  simp only [integral_term hs, tsum_div_const]
  have hd := hasSum_suzukiWeilDigammaDifferenceSummand
    (a := 1+s/2) (b := 1) (by simp; positivity) (by norm_num)
  rw [hd.tsum_eq, Complex.digamma_one, sub_neg_eq_add]

end
end RiemannGaussian.RosserSchoenfeldTrivialPrimitive
