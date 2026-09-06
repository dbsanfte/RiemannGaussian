import RiemannGaussian.EtaOverlapTail
import RiemannGaussian.EtaLogSupportCritical

/-!
# Wallis evaluation of the literal logarithmic eta tail

Two exact changes of variables carry the rescaled arithmetic tail back to
the existing critical eta mismatch. Its logarithmic cutoff cancels the
finite harmonic cutoff before passing to an asymptotic limit.
-/

open Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exponential and linear substitution preserve the literal critical eta
tail exactly, including the arithmetic lower endpoint. -/
theorem pairedEtaMismatchTail_half_eq_rescaledOverlap {r : ℝ} (hr : 0 < r)
    {M : ℕ} (hM : 1 ≤ M) :
    pairedEtaMismatchTail (1 / 2) r M =
      (Real.exp r - 1) * ∫ y in Ioi ((Real.exp r - 1) * M),
        etaRescaledOverlap (Real.exp r - 1) y / y ^ 2 := by
  let epsilon := Real.exp r - 1
  let g : ℝ → ℝ := fun y ↦ etaRescaledOverlap epsilon y / y ^ 2
  have he : 0 < epsilon := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  change pairedEtaMismatchTail (1 / 2) r M = epsilon * ∫ y in Ioi (epsilon * M), g y
  calc
    _ = ∫ t in Ioi (Real.log (M : ℝ)), Real.exp t * (epsilon ^ 2 * g (epsilon * Real.exp t)) := by
      unfold pairedEtaMismatchTail
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [pairedEtaLogShiftMismatch_eq_rescaledOverlap hr (hlog.trans_lt ht)]
      norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul]
      rw [Real.exp_neg]
      dsimp only [g, epsilon]
      field_simp [show Real.exp r - 1 ≠ 0 from he.ne', Real.exp_ne_zero]
    _ = ∫ x in Ioi (M : ℝ), epsilon ^ 2 * g (epsilon * x) := by
      simpa only [smul_eq_mul, Real.exp_log hMpos] using
        integral_comp_exp_Ioi (fun x ↦ epsilon ^ 2 * g (epsilon * x)) (Real.log (M : ℝ))
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi g (M : ℝ) he, smul_eq_mul]
      field_simp

/-- The critical logarithmic tail has an evaluated Wallis finite part,
with the exact logarithmic cutoff retained. -/
theorem pairedEtaMismatchTail_half_wallis_error_le {r : ℝ} (hr : 0 < r)
    (hepsilon1 : Real.exp r - 1 ≤ 1) {M : ℕ} (hM : 1 ≤ M)
    (hcutoff : (Real.exp r - 1) * M ≤ 1) :
    |pairedEtaMismatchTail (1 / 2) r M / (Real.exp r - 1) -
      (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * M))| ≤
      4 * (Real.exp r - 1) / ((Real.exp r - 1) * M) +
        (Real.exp r - 1) / ((Real.exp r - 1) * M) ^ 2 := by
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [pairedEtaMismatchTail_half_eq_rescaledOverlap hr hM, mul_div_cancel_left₀ _ he.ne']
  exact integral_Ioi_etaRescaledOverlap_div_sq_error_le he hepsilon1 (mul_pos he hMpos) hcutoff

/-- Combining the actual tail with the exact crossing sum cancels the
arithmetic cutoff inside the logarithms. -/
theorem pairedEtaMismatch_half_finite_part_cutoff_error_le {r : ℝ} (hr : 0 < r)
    (hepsilon1 : Real.exp r - 1 ≤ 1) {M : ℕ} (hM : 2 ≤ M)
    (hspacing : r ≤ Real.log (((M : ℝ) + 1) / M))
    (hcutoff : (Real.exp r - 1) * M ≤ 1) :
    |pairedEtaMismatch (1 / 2) r / (Real.exp r - 1) + Real.log (Real.exp r - 1) -
      ((harmonic M : ℝ) - Real.log M - Real.log (Real.pi / 2))| ≤
      4 * (Real.exp r - 1) / ((Real.exp r - 1) * M) +
        (Real.exp r - 1) / ((Real.exp r - 1) * M) ^ 2 := by
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ht := pairedEtaMismatchTail_half_wallis_error_le hr hepsilon1 (by omega : 1 ≤ M) hcutoff
  rw [Real.log_mul he.ne' hMpos.ne'] at ht
  rw [pairedEtaMismatch_half_eq_harmonic_add_tail hM hr hspacing,
    sum_Icc_two_inv_eq_harmonic_sub_one (by omega), add_div, mul_div_cancel_left₀ _ he.ne']
  convert ht using 1
  congr 1
  ring

/-- At the existing real-displacement cutoff the rescaled lower endpoint
stays in `[1/4,1]`, and the rescaled displacement is at most one. -/
theorem pairedEtaShiftBoundaryCutoff_rescaled_bounds {r : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    Real.exp r - 1 ≤ 1 ∧
      (1 / 4 : ℝ) ≤ (Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r ∧
      (Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r ≤ 1 := by
  obtain ⟨hM, hlower, hupper⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hM0 : (0 : ℝ) ≤ pairedEtaShiftBoundaryCutoff r := Nat.cast_nonneg _
  have hexp := Real.abs_exp_sub_one_sub_id_le
    (show |r| ≤ 1 by rw [abs_of_pos hr]; linarith)
  have heupper : Real.exp r - 1 ≤ 2 * r := by
    have h := (le_abs_self (Real.exp r - 1 - r)).trans hexp
    nlinarith
  have helower : r ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  have hl := (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hlower
  have hu := (le_div_iff₀ (by positivity : 0 < 2 * r)).mp hupper
  have hmulL := mul_le_mul_of_nonneg_right helower hM0
  have hmulU := mul_le_mul_of_nonneg_right heupper hM0
  exact ⟨by linarith, by nlinarith, by nlinarith⟩

/-- A uniform evaluated critical finite part with an explicit arithmetic
harmonic remainder, valid for every sufficiently small real displacement. -/
theorem pairedEtaMismatch_half_finite_part_harmonic_error_le {r : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    |pairedEtaMismatch (1 / 2) r / (Real.exp r - 1) + Real.log (Real.exp r - 1) -
      ((harmonic (pairedEtaShiftBoundaryCutoff r) : ℝ) -
        Real.log (pairedEtaShiftBoundaryCutoff r) - Real.log (Real.pi / 2))| ≤
      32 * (Real.exp r - 1) := by
  obtain ⟨he1, haL, haU⟩ := pairedEtaShiftBoundaryCutoff_rescaled_bounds hr hrsmall
  obtain ⟨hM, _, _⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  apply (pairedEtaMismatch_half_finite_part_cutoff_error_le hr he1 (by omega)
    (pairedEtaShiftBoundaryCutoff_spacing hr hrsmall) haU).trans
  have hden : 0 < (Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r := by linarith
  have hfirst : 4 * (Real.exp r - 1) / ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) ≤
      16 * (Real.exp r - 1) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hsecond : (Real.exp r - 1) / ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) ^ 2 ≤
      16 * (Real.exp r - 1) := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hs : (1 / 16 : ℝ) ≤ ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) ^ 2 := by
      nlinarith
    nlinarith
  linarith

end

end RiemannGaussian
