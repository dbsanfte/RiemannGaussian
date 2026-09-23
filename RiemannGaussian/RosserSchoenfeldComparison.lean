/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The literal Rosser--Schoenfeld comparison integral

This is the anchored comparison in equation (7.1) of Rosser and
Schoenfeld (1962). Abel summation transports bounds for the actual
Chebyshev theta function into it, retaining the real endpoint and the
finite anchor. No estimate for theta is assumed as a global theorem.
-/

namespace RiemannGaussian.RosserSchoenfeldComparison
noncomputable section
open MeasureTheory Real

/-- The integrand of equation (7.1). -/
def kernel (a x : ℝ) : ℝ := (1 + a / log x) / log x ^ 2

/-- The literal equation (7.1), including both arithmetic anchor terms. -/
def comparison (a x : ℝ) : ℝ :=
  (Nat.primeCounting 1451 : ℝ) - Chebyshev.theta 1451 / log 1451 +
    x / log x * (1 + a / log x) + ∫ t in (1451 : ℝ)..x, kernel a t

/-- The upper function in (3.2), with its published coefficient. -/
def upper (x : ℝ) : ℝ := x / log x * (1 + 3 / (2 * log x))

/-- The lower function in (3.3), with its published denominator shift. -/
def lower (x : ℝ) : ℝ := x / (log x - 1 / 2)

/-- Continuity on the entire domain used by the anchored integral. -/
theorem kernel_continuousOn (a : ℝ) : ContinuousOn (kernel a) (Set.Ioi 1) := by
  intro x hx
  have hx0 : x ≠ 0 := by have := hx; simp only [Set.mem_Ioi] at this; linarith
  have hl : log x ≠ 0 := (log_pos hx).ne'
  unfold kernel
  fun_prop (disch := positivity)

/-- Every finite anchored comparison integral is genuinely integrable. -/
theorem kernel_intervalIntegrable (a : ℝ) {b x : ℝ} (hb : 1 < b) (hx : 1 < x) :
    IntervalIntegrable (kernel a) volume b x := by
  apply ContinuousOn.intervalIntegrable
  apply (kernel_continuousOn a).mono
  intro t ht
  rcases Set.mem_uIcc.mp ht with ht | ht
  · exact hb.trans_le ht.1
  · exact hx.trans_le ht.1

/-- Differentiation of a finite anchored integral includes its endpoint atom. -/
theorem integral_hasDerivAt (a : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => ∫ t in (1451 : ℝ)..x, kernel a t) (kernel a x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (kernel_intervalIntegrable a (by norm_num) hx)
    ((kernel_continuousOn a).stronglyMeasurableAtFilter isOpen_Ioi x hx)
    ((kernel_continuousOn a x hx).continuousAt (Ioi_mem_nhds hx))

/-- The elementary logarithmic monomials used by the explicit comparison. -/
theorem logTerm_hasDerivAt (n : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => x / log x ^ (n + 1))
      ((log x - (n + 1)) / log x ^ (n + 2)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : log x ≠ 0 := (log_pos hx).ne'
  convert! (hasDerivAt_id x).div ((hasDerivAt_log hx0).pow (n + 1))
    (pow_ne_zero _ hl) using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply, id_eq,
    pow_succ]
  field_simp

/-- The derivative used in all five comparisons of Section 7. -/
theorem comparison_hasDerivAt (a : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (comparison a)
      (1 / log x + a / log x ^ 2 - a / log x ^ 3) x := by
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have hd := (((logTerm_hasDerivAt 0 hx).add
    ((logTerm_hasDerivAt 1 hx).const_mul a)).const_add
      ((Nat.primeCounting 1451 : ℝ) - Chebyshev.theta 1451 / log 1451)).add
        (integral_hasDerivAt a hx)
  convert! hd using 1
  · ext t
    simp only [comparison, pow_one, Nat.reduceAdd, Pi.add_apply]
    ring
  · simp only [kernel, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd]
    field_simp
    ring

/-- Abel summation with the source's finite anchor and literal real endpoint. -/
theorem primeCounting_anchored {x : ℝ} (hx : 1451 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      (Nat.primeCounting 1451 : ℝ) - Chebyshev.theta 1451 / log 1451 +
        Chebyshev.theta x / log x +
          ∫ t in (1451 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2) := by
  have h1 := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (show (2 : ℝ) ≤ x by linarith)
  have h0 := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (show (2 : ℝ) ≤ 1451 by norm_num)
  norm_num only [Nat.floor_ofNat] at h0
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t / (t * log t ^ 2))
      volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (2 : ℝ) ≤ x)]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hi0 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * log t ^ 2))
      volume 2 1451 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (2 : ℝ) ≤ 1451)]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq 1451
  have hisplit := intervalIntegral.integral_add_adjacent_intervals hi0 (hi0.symm.trans hi)
  linarith

/-- Upper theta bounds on the actual finite interval give the upper comparison. -/
theorem primeCounting_le_comparison {a x : ℝ} (hx : 1451 ≤ x)
    (htheta : ∀ t ∈ Set.Icc 1451 x, Chebyshev.theta t ≤ t * (1 + a / log t)) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ comparison a x := by
  have hx1 : 1 < x := by linarith
  rw [primeCounting_anchored hx]
  unfold comparison
  apply add_le_add
  · gcongr
    convert! div_le_div_of_nonneg_right (htheta x ⟨hx, le_rfl⟩) (log_pos hx1).le using 1
    ring
  · apply intervalIntegral.integral_mono_on hx
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
        (Set.Icc_subset_Icc_left (by norm_num))
    · exact kernel_intervalIntegrable a (by norm_num) hx1
    · intro t ht
      have ht0 : t ≠ 0 := by have := ht.1; linarith
      have hh := div_le_div_of_nonneg_right (htheta t ht)
        (show 0 ≤ t * log t ^ 2 by have := ht.1; positivity)
      simpa only [kernel, mul_div_mul_left _ _ ht0] using hh

/-- Lower theta bounds on the same interval give the lower comparison. -/
theorem comparison_le_primeCounting {a x : ℝ} (hx : 1451 ≤ x)
    (htheta : ∀ t ∈ Set.Icc 1451 x, t * (1 + a / log t) ≤ Chebyshev.theta t) :
    comparison a x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  rw [primeCounting_anchored hx]
  have hx1 : 1 < x := by linarith
  unfold comparison
  apply add_le_add
  · gcongr
    convert! div_le_div_of_nonneg_right (htheta x ⟨hx, le_rfl⟩) (log_pos hx1).le using 1
    ring
  · apply intervalIntegral.integral_mono_on hx
    · exact kernel_intervalIntegrable a (by norm_num) hx1
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
        (Set.Icc_subset_Icc_left (by norm_num))
    · intro t ht
      have ht0 : t ≠ 0 := by have := ht.1; linarith
      have hh := div_le_div_of_nonneg_right (htheta t ht)
        (show 0 ≤ t * log t ^ 2 by have := ht.1; positivity)
      simpa only [kernel, mul_div_mul_left _ _ ht0] using hh

end
end RiemannGaussian.RosserSchoenfeldComparison
