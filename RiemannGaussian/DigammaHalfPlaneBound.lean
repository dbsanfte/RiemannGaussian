/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiWeilArchimedean

/-!
# A uniform polynomial digamma bound away from the imaginary axis

The full Gauss difference series gives a linear bound on every closed
right half-plane. This coarse estimate is enough to count the zeros of
the actual arithmetic carrier denominator in moving disks, without
introducing the exponential size of the Gamma completion.
-/

open Complex
namespace RiemannGaussian
noncomputable section

private lemma square_series_summable :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h

private lemma difference_term_bound {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {z : ℂ} (hz : c ≤ z.re) (n : ℕ) :
    ‖suzukiWeilDigammaDifferenceSummand z 1 n‖ ≤
      (‖z - 1‖ / c ^ 2) * (1 / (((n : ℝ) + 1) ^ 2)) := by
  have hden : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + z‖ := by
    calc
      _ = c * n + c := by ring
      _ ≤ (n : ℝ) + z.re := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      _ = ((n : ℂ) + z).re := by simp
      _ ≤ _ := Complex.re_le_norm _
  have hden1 : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + 1‖ := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
    exact mul_le_of_le_one_left (by positivity) hc1
  have hp : 0 < c * ((n : ℝ) + 1) := by positivity
  have hnz : (n : ℂ) + z ≠ 0 := norm_pos_iff.mp (hp.trans_le hden)
  have hn1 : (n : ℂ) + 1 ≠ 0 := norm_pos_iff.mp (hp.trans_le hden1)
  have he : suzukiWeilDigammaDifferenceSummand z 1 n =
      (z - 1) / (((n : ℂ) + 1) * ((n : ℂ) + z)) := by
    unfold suzukiWeilDigammaDifferenceSummand
    field_simp
    ring
  rw [he, norm_div, norm_mul]
  calc
    _ ≤ ‖z - 1‖ / (c * ((n : ℝ) + 1)) ^ 2 := by
      apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hp)
      simpa only [pow_two] using mul_le_mul hden1 hden hp.le (norm_nonneg _)
    _ = _ := by rw [mul_pow, div_mul_eq_div_mul_one_div]

/-- For every positive real-part margin, digamma has a uniform linear
bound on the entire corresponding closed half-plane. -/
theorem exists_norm_digamma_le_linear_of_re_ge {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, delta ≤ z.re → ‖Complex.digamma z‖ ≤ C * (1 + ‖z‖) := by
  let c : ℝ := min 1 delta
  have hc : 0 < c := lt_min one_pos hdelta
  have hc1 : c ≤ 1 := min_le_left _ _
  let M : ℝ := ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2)
  have hM : 0 ≤ M := tsum_nonneg fun n => by positivity
  let K : ℝ := M / c ^ 2
  have hK : 0 ≤ K := div_nonneg hM (sq_nonneg _)
  let C : ℝ := 1 + ‖Complex.digamma 1‖ + K
  refine ⟨C, by dsimp [C]; linarith [norm_nonneg (Complex.digamma 1)], ?_⟩
  intro z hz
  have hzc : c ≤ z.re := (min_le_right _ _).trans hz
  have hsum := hasSum_suzukiWeilDigammaDifferenceSummand (hdelta.trans_le hz)
    (by norm_num : (0 : ℝ) < (1 : ℂ).re)
  have hsumnorm := summable_norm_suzukiWeilDigammaDifferenceSummand (hdelta.trans_le hz)
    (by norm_num : (0 : ℝ) < (1 : ℂ).re)
  have hdiff : ‖Complex.digamma z - Complex.digamma 1‖ ≤ K * ‖z - 1‖ := by
    rw [← hsum.tsum_eq]
    calc
      _ ≤ ∑' n : ℕ, ‖suzukiWeilDigammaDifferenceSummand z 1 n‖ := norm_tsum_le_tsum_norm hsumnorm
      _ ≤ ∑' n : ℕ, (‖z - 1‖ / c ^ 2) * (1 / (((n : ℝ) + 1) ^ 2)) :=
        hsumnorm.tsum_le_tsum (difference_term_bound hc hc1 hzc) (square_series_summable.mul_left _)
      _ = _ := by rw [tsum_mul_left]; dsimp [K, M]; ring
  have hz1 : ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa only [norm_one] using norm_sub_le z (1 : ℂ)
  calc
    _ ≤ ‖Complex.digamma z - Complex.digamma 1‖ + ‖Complex.digamma 1‖ :=
      by simpa only [add_comm] using norm_le_insert' (Complex.digamma z) (Complex.digamma 1)
    _ ≤ K * (‖z‖ + 1) + ‖Complex.digamma 1‖ :=
      add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hz1 hK)) le_rfl
    _ ≤ _ := by dsimp [C]; nlinarith [norm_nonneg z, norm_nonneg (Complex.digamma 1)]

end
end RiemannGaussian
