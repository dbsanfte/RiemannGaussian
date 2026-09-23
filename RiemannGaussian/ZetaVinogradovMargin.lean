/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovSignedBudget

/-!
# A fully paid explicit zero exclusion from the Vinogradov branch

One displayed logarithmic reserve pays both local profiles, the real-axis
cost and the reciprocal-zeta center. The proposed margin is its reciprocal
times the proved line displacement. Every term in the signed prime budget
and its radial correction is numerically bounded before invoking the
actual-zero contradiction. No analytic or arithmetic bound is a premise.
This parameter-indexed region is not asserted to improve the proved union
or any published benchmark; optimizing its degree by height is separate.
-/

namespace RiemannGaussian.ZetaVinogradovMargin
noncomputable section
open VinogradovNearOneBudget VinogradovScaleSelection ZetaVinogradovLocalDisc
open ZetaVinogradovCanonical ZetaVinogradovSignedBudget

/-- The complete explicit reserve for both heights and the actual center. -/
def reserve (n : ℕ) (t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 + profile n t + profile n (2 * t) + Real.log (1 / delta n) + 20

/-- The proposed strict right-edge margin, with no implicit cutoff choice. -/
def width (n : ℕ) (t : ℝ) : ℝ := delta n / (4096 * reserve n t)

/-- The full reserve pays each named nonnegative component. -/
theorem reserve_bounds {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    20 ≤ reserve n t ∧ profile n t ≤ reserve n t ∧ profile n (2 * t) ≤ reserve n t ∧
      Real.log (1 / delta n) + 20 ≤ reserve n t ∧
        1344 * localZetaLogHeight 0 ≤ reserve n t := by
  have hD : 0 ≤ 1344 * localZetaLogHeight 0 := by linarith [two_lt_localZetaLogHeight 0]
  have h1 := profile_nonneg hn t
  have h2 := profile_nonneg hn (2 * t)
  have hi : 0 ≤ Real.log (1 / delta n) := Real.log_nonneg
    ((one_le_div (delta_pos n)).mpr (by linarith [delta_le n]))
  unfold reserve
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Every proposed margin is strictly positive. -/
theorem width_pos {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : 0 < width n t := by
  have hQ : 0 < reserve n t := by linarith [(reserve_bounds hn t).1]
  unfold width
  exact div_pos (delta_pos n) (by positivity)

/-- The proposed margin is inside the full signed-source radius. -/
theorem width_lt_radius {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : width n t < delta n / 28 := by
  have hQ := (reserve_bounds hn t).1
  unfold width
  exact div_lt_div_of_pos_left (delta_pos n) (by norm_num) (by linarith)

/-- The complete Euler-center logarithm at six proposed margins costs
at most twice the explicit reserve. -/
theorem center_log_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Real.log (1 + 1 / (6 * width n t)) ≤ 2 * reserve n t := by
  obtain ⟨hQ, _, _, hlogQ, _⟩ := reserve_bounds hn t
  have hQpos : 0 < reserve n t := by linarith
  have hd := width_pos hn t
  have hδ := delta_pos n
  have harg : 1 + 1 / (6 * width n t) ≤ 8192 * reserve n t / delta n := by
    apply (le_div_iff₀ hδ).mpr
    rw [add_mul, one_mul]
    have he : (1 / (6 * width n t)) * delta n = 4096 * reserve n t / 6 := by
      unfold width
      field_simp
    rw [he]
    linarith [delta_le n]
  have h := Real.log_le_log (by positivity : 0 < 1 + 1 / (6 * width n t)) harg
  rw [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 8192) hQpos).ne' hδ.ne',
    Real.log_mul (by norm_num : (8192 : ℝ) ≠ 0) hQpos.ne'] at h
  have hconst : Real.log (8192 : ℝ) ≤ 13 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl := Real.log_le_self hQpos.le
  have hinv : Real.log (1 / delta n) = -Real.log (delta n) := by simp
  rw [hinv] at hlogQ
  linarith

/-- Both height allowances and the complete real-axis cost are paid by
121 reserve units per original line displacement. -/
theorem budget_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    budget n (6 * width n t) t ≤ 121 * reserve n t / delta n := by
  obtain ⟨_, h1, h2, _, hD⟩ := reserve_bounds hn t
  have hlog := center_log_le hn t
  have hA1 : allowance n (6 * width n t) t ≤ 3 * reserve n t := by
    unfold allowance
    linarith
  have hA2 : allowance n (6 * width n t) (2 * t) ≤ 3 * reserve n t := by
    unfold allowance
    linarith
  have hD0 : 0 ≤ 1344 * localZetaLogHeight 0 := by linarith [two_lt_localZetaLogHeight 0]
  have hDdelta : 1344 * localZetaLogHeight 0 * delta n ≤ reserve n t := by
    have h := mul_le_mul_of_nonneg_left (show delta n ≤ 1 by linarith [delta_le n]) hD0
    linarith
  apply (le_div_iff₀ (delta_pos n)).mpr
  unfold budget
  rw [add_mul, div_mul_cancel₀ _ (delta_pos n).ne']
  nlinarith

/-- The proposed margin pays the entire signed budget and the retained
quadratic radial correction with a strict numerical surplus. -/
theorem budget_paid {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    14 * width n t * budget n (6 * width n t) t +
      6272 * (width n t) ^ 2 / (delta n) ^ 2 < 1 := by
  have hd := width_pos hn t
  have hδ := delta_pos n
  have hQ : 1 ≤ reserve n t := by linarith [(reserve_bounds hn t).1]
  have hQpos : 0 < reserve n t := by linarith
  have hb := mul_le_mul_of_nonneg_left (budget_le hn t) hd.le
  have he : width n t * (121 * reserve n t / delta n) = 121 / 4096 := by
    unfold width
    field_simp
  rw [he] at hb
  have hr : width n t / delta n ≤ 1 / 4096 := by
    have he' : width n t / delta n = 1 / (4096 * reserve n t) := by
      unfold width
      field_simp
    rw [he']
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4096) (by linarith)
  have hs : (width n t) ^ 2 / (delta n) ^ 2 ≤ (1 / 4096 : ℝ) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) hr 2
  calc
    _ = 14 * (width n t * budget n (6 * width n t) t) +
        6272 * ((width n t) ^ 2 / (delta n) ^ 2) := by ring
    _ ≤ 14 * (121 / 4096) + 6272 * (1 / 4096 : ℝ) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
        (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ < 1 := by norm_num

/-- Every actual nontrivial zero lies strictly beyond the explicit
Vinogradov right edge once the displayed height threshold is met. -/
theorem exact_margin (n : ℕ) (hn : 12 ≤ n) (ρ : NontrivialZetaZero)
    (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|) : width n ρ.1.im < 1 - ρ.1.re :=
  margin_of_budget n hn ρ ht (width_pos (by omega : 1 ≤ n) ρ.1.im)
    (width_lt_radius (by omega : 1 ≤ n) ρ.1.im) (budget_paid (by omega : 1 ≤ n) ρ.1.im)

/-- Literal zeta is nonzero on the full closed right edge of the new
parameter-indexed region. All analytic and arithmetic inputs are proved. -/
theorem nonvanishing (n : ℕ) (hn : 12 ≤ n) (s : ℂ)
    (ht : (heightThreshold n : ℝ) + 1 ≤ |s.im|) (hσ : 1 - width n s.im ≤ s.re) :
    riemannZeta s ≠ 0 := by
  have htpos : 0 < |s.im| := by linarith [Nat.cast_nonneg (α := ℝ) (heightThreshold n)]
  intro hz
  have htriv : ¬ ∃ m : ℕ, s = -2 * (m + 1) := by
    rintro ⟨m, rfl⟩
    norm_num at htpos
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at htpos
  let ρ : NontrivialZetaZero := ⟨s, hz, htriv, hs1⟩
  have h := exact_margin n hn ρ ht
  change width n s.im < 1 - s.re at h
  linarith

end
end RiemannGaussian.ZetaVinogradovMargin
