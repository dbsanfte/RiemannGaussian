/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiWeilArchimedean
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex

/-!
# Signed control of the complex trigamma function

The derivative of the actual digamma function is its absolutely convergent
Euler series. A midpoint telescoping identity retains the leading complex
term before bounding the remainder. This gives a positive real part on a
closed right half-plane, suitable for shifted Gamma completion factors.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

private lemma square_series_summable :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h

private lemma inverse_square_bound {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {z : ℂ} (hz : c ≤ z.re) (n : ℕ) :
    ‖1 / ((n : ℂ) + z) ^ 2‖ ≤ (1 / c ^ 2) * (1 / (((n : ℝ) + 1) ^ 2)) := by
  have hden : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + z‖ := by
    calc
      _ = c * n + c := by ring
      _ ≤ (n : ℝ) + z.re := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      _ = ((n : ℂ) + z).re := by simp
      _ ≤ _ := Complex.re_le_norm _
  rw [norm_div, norm_one, norm_pow]
  calc
    _ ≤ 1 / (c * ((n : ℝ) + 1)) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) hden 2
    _ = _ := by rw [mul_pow, one_div_mul_one_div]

/-- The actual complex trigamma Euler series is absolutely summable on
the open positive half-plane. -/
theorem summable_norm_trigamma_euler {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => ‖1 / ((n : ℂ) + z) ^ 2‖) := by
  let c : ℝ := min 1 z.re
  exact (square_series_summable.mul_left (1 / c ^ 2)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (inverse_square_bound (lt_min one_pos hz)
      (min_le_left _ _) (min_le_right _ _))

/-- Differentiating the convergent digamma difference series gives the
full complex derivative, with a uniform summable derivative majorant. -/
theorem hasDerivAt_digamma_euler {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.digamma (∑' n : ℕ, 1 / ((n : ℂ) + z) ^ 2) z := by
  let c : ℝ := min 1 (z.re / 2)
  have hc : 0 < c := lt_min one_pos (half_pos hz)
  have hcz : c < z.re := (min_le_right _ _).trans_lt (half_lt_self hz)
  have hseries : HasDerivAt
      (fun w => ∑' n : ℕ, suzukiWeilDigammaDifferenceSummand w 1 n)
      (∑' n : ℕ, 1 / ((n : ℂ) + z) ^ 2) z := by
    refine hasDerivAt_tsum_of_isPreconnected
      (t := {w : ℂ | c < w.re}) (y₀ := z)
      (g := fun n w => suzukiWeilDigammaDifferenceSummand w 1 n)
      (g' := fun n w => 1 / ((n : ℂ) + w) ^ 2)
      (square_series_summable.mul_left (1 / c ^ 2))
      (Complex.isOpen_re_gt c) (convex_halfSpace_re_gt c).isPreconnected
      ?_ ?_ hcz
      (summable_norm_suzukiWeilDigammaDifferenceSummand hz (by norm_num)).of_norm hcz
    · intro n w hw
      change c < w.re at hw
      have hn : (n : ℂ) + w ≠ 0 := by
        apply ne_zero_of_re_pos
        simp only [add_re, natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      simpa [suzukiWeilDigammaDifferenceSummand, neg_div, Pi.inv_apply] using
        (hasDerivAt_const w (((n : ℂ) + 1)⁻¹)).fun_sub
          (((hasDerivAt_id w).const_add (n : ℂ)).inv hn)
    · intro n w hw
      exact inverse_square_bound hc (min_le_left _ _) hw.le n
  have hnear : (fun w => (∑' n : ℕ, suzukiWeilDigammaDifferenceSummand w 1 n) +
      Complex.digamma 1) =ᶠ[𝓝 z] Complex.digamma := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hz] with w hw
    rw [(hasSum_suzukiWeilDigammaDifferenceSummand hw (by norm_num)).tsum_eq]
    exact sub_add_cancel _ _
  exact (hseries.add_const _).congr_of_eventuallyEq hnear.symm

/-- The trigamma derivative equals its full Euler sum on the positive
half-plane. -/
theorem deriv_digamma_eq_tsum {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.digamma z = ∑' n : ℕ, 1 / ((n : ℂ) + z) ^ 2 :=
  (hasDerivAt_digamma_euler hz).deriv

private lemma midpoint_hasSum {z : ℂ} (hz : 1 / 2 < z.re) :
    HasSum (fun n : ℕ => ((n : ℂ) + z - 1 / 2)⁻¹ -
      ((n : ℂ) + z + 1 / 2)⁻¹) (z - 1 / 2)⁻¹ := by
  have hminus : 0 < (z - 1 / 2).re := by simp; linarith
  have hplus : 0 < (z + 1 / 2).re := by simp; linarith
  have h := hasSum_suzukiWeilDigammaDifferenceSummand hplus hminus
  change HasSum (fun n : ℕ => ((n : ℂ) + (z - 1 / 2))⁻¹ -
    ((n : ℂ) + (z + 1 / 2))⁻¹) _ at h
  have he : Complex.digamma (z + 1 / 2) - Complex.digamma (z - 1 / 2) =
      (z - 1 / 2)⁻¹ := by
    rw [show z + 1 / 2 = (z - 1 / 2) + 1 by ring,
      Complex.digamma_apply_add_one]
    · ring
    · intro m
      apply ne_of_apply_ne Complex.re
      simp only [neg_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) m]
  simpa only [he, ← add_sub_assoc, ← add_assoc] using! h

/-- The exact complex correction to the midpoint telescoper. Keeping this
series separately preserves its phase before the downstream norm bound. -/
def trigammaMidpointRemainder (z : ℂ) (n : ℕ) : ℂ :=
  1 / (4 * ((n : ℂ) + z) ^ 2 * ((n : ℂ) + z - 1 / 2) *
    ((n : ℂ) + z + 1 / 2))

private lemma midpoint_term {z : ℂ} (hz : 1 / 2 < z.re) (n : ℕ) :
    ((n : ℂ) + z - 1 / 2)⁻¹ - ((n : ℂ) + z + 1 / 2)⁻¹ -
      1 / ((n : ℂ) + z) ^ 2 = trigammaMidpointRemainder z n := by
  have h0 : (n : ℂ) + z ≠ 0 := by
    apply ne_zero_of_re_pos
    simp only [add_re, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : (n : ℂ) + z - 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    simp
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (n : ℂ) + z + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    simp
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold trigammaMidpointRemainder
  generalize hw : (n : ℂ) + z = w at h0 hm hp ⊢
  generalize ha : w - 1 / 2 = a at hm ⊢
  generalize hb : w + 1 / 2 = b at hp ⊢
  field_simp [h0, hm, hp]
  rw [← ha, ← hb]
  ring

/-- Exact absolutely convergent midpoint decomposition of trigamma. The
leading reciprocal and the complete complex remainder are both retained. -/
theorem hasSum_trigammaMidpointRemainder {z : ℂ} (hz : 1 / 2 < z.re) :
    HasSum (trigammaMidpointRemainder z)
      ((z - 1 / 2)⁻¹ - deriv Complex.digamma z) := by
  have hz0 : 0 < z.re := by linarith
  rw [deriv_digamma_eq_tsum hz0]
  convert! (midpoint_hasSum hz).sub (summable_norm_trigamma_euler hz0).of_norm.hasSum using 1
  exact (funext (midpoint_term hz)).symm

private lemma midpoint_remainder_bound {z : ℂ} (hz : 1 / 2 < z.re) (n : ℕ) :
    ‖trigammaMidpointRemainder z n‖ ≤ 1 / (4 * normSq z) *
      (1 / ((n : ℝ) + z.re - 1 / 2) - 1 / ((n : ℝ) + z.re + 1 / 2)) := by
  have hxm : 0 < (n : ℝ) + z.re - 1 / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hxp : 0 < (n : ℝ) + z.re + 1 / 2 := by linarith
  have hzN : 0 < normSq z := normSq_pos.mpr (ne_zero_of_re_pos (by linarith))
  have hwN : normSq z ≤ ‖(n : ℂ) + z‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [normSq_apply, add_re, add_im, natCast_re, natCast_im, zero_add]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : (n : ℝ) + z.re - 1 / 2 ≤ ‖(n : ℂ) + z - 1 / 2‖ := by
    simpa using Complex.re_le_norm ((n : ℂ) + z - 1 / 2)
  have hp : (n : ℝ) + z.re + 1 / 2 ≤ ‖(n : ℂ) + z + 1 / 2‖ := by
    simpa using Complex.re_le_norm ((n : ℂ) + z + 1 / 2)
  unfold trigammaMidpointRemainder
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_mul, norm_pow]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ 1 / (4 * normSq z * ((n : ℝ) + z.re - 1 / 2) *
        ((n : ℝ) + z.re + 1 / 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    _ = _ := by
      generalize ha : (n : ℝ) + z.re - 1 / 2 = a at hxm ⊢
      generalize hb : (n : ℝ) + z.re + 1 / 2 = b at hxp ⊢
      field_simp [hxm.ne', hxp.ne']
      rw [← ha, ← hb]
      ring

/-- A quantitative complex error bound for the midpoint telescoper,
uniform in the imaginary part. -/
theorem norm_trigamma_sub_midpoint_le {z : ℂ} (hz : 1 / 2 < z.re) :
    ‖deriv Complex.digamma z - (z - 1 / 2)⁻¹‖ ≤
      1 / (4 * normSq z * (z.re - 1 / 2)) := by
  have hreal : HasSum (fun n : ℕ =>
      1 / ((n : ℝ) + z.re - 1 / 2) - 1 / ((n : ℝ) + z.re + 1 / 2))
      (1 / (z.re - 1 / 2)) := by
    have h := Complex.hasSum_re (midpoint_hasSum (z := (z.re : ℂ)) hz)
    simpa only [← ofReal_natCast, ← ofReal_add, ← ofReal_one, ← ofReal_ofNat,
      ← ofReal_div, ← ofReal_sub, ← ofReal_inv, ofReal_re, one_div] using h
  have hbound := hreal.summable.mul_left (1 / (4 * normSq z))
  have hnorm : Summable (fun n => ‖trigammaMidpointRemainder z n‖) :=
    hbound.of_nonneg_of_le (fun _ => norm_nonneg _) (midpoint_remainder_bound hz)
  rw [norm_sub_rev, ← (hasSum_trigammaMidpointRemainder hz).tsum_eq]
  calc
    _ ≤ ∑' n, ‖trigammaMidpointRemainder z n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, 1 / (4 * normSq z) *
        (1 / ((n : ℝ) + z.re - 1 / 2) - 1 / ((n : ℝ) + z.re + 1 / 2)) :=
      hnorm.tsum_le_tsum (midpoint_remainder_bound hz) hbound
    _ = _ := by rw [tsum_mul_left, hreal.tsum_eq, one_div_mul_one_div]

/-- The midpoint expansion yields an explicit lower bound for the real
part of trigamma without dropping the phase of its leading term. -/
theorem trigamma_re_lower {z : ℂ} (hz : 1 / 2 < z.re) :
    (z.re - 1 / 2 - 1 / (4 * (z.re - 1 / 2))) / normSq z ≤
      (deriv Complex.digamma z).re := by
  have hx : 0 < z.re - 1 / 2 := by linarith
  have hzN : 0 < normSq z := normSq_pos.mpr (ne_zero_of_re_pos (by linarith))
  have hmN : 0 < normSq (z - 1 / 2) :=
    normSq_pos.mpr (ne_zero_of_re_pos (by simpa using hx))
  have hN : normSq (z - 1 / 2) ≤ normSq z := by
    simp [normSq_apply]
    nlinarith
  have hlead : (z.re - 1 / 2) / normSq z ≤ ((z - 1 / 2)⁻¹).re := by
    rw [Complex.inv_re]
    simp only [sub_re, div_ofNat_re, one_re]
    exact div_le_div_of_nonneg_left hx.le hmN hN
  have herror := (Complex.re_le_norm ((z - 1 / 2)⁻¹ - deriv Complex.digamma z)).trans
    ((norm_sub_rev _ _).le.trans (norm_trigamma_sub_midpoint_le hz))
  rw [sub_re] at herror
  have hsplit : (z.re - 1 / 2 - 1 / (4 * (z.re - 1 / 2))) / normSq z =
      (z.re - 1 / 2) / normSq z - 1 / (4 * normSq z * (z.re - 1 / 2)) := by
    field_simp
  rw [hsplit]
  linarith

/-- The real part of complex trigamma is nonnegative on `Re(z) ≥ 1`. -/
theorem trigamma_re_nonneg {z : ℂ} (hz : 1 ≤ z.re) :
    0 ≤ (deriv Complex.digamma z).re := by
  have hx : 0 < z.re - 1 / 2 := by linarith
  refine le_trans (div_nonneg ?_ (normSq_nonneg _)) (trigamma_re_lower (by linarith))
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (show 0 < 4 * (z.re - 1 / 2) by positivity)).mpr
  nlinarith [sq_nonneg (z.re - 1)]

/-- The real part of complex trigamma is strictly positive on `Re(z) > 1`. -/
theorem trigamma_re_pos {z : ℂ} (hz : 1 < z.re) :
    0 < (deriv Complex.digamma z).re := by
  have hx : 0 < z.re - 1 / 2 := by linarith
  refine lt_of_lt_of_le (div_pos ?_ (normSq_pos.mpr (ne_zero_of_re_pos (by linarith))))
    (trigamma_re_lower (by linarith))
  apply sub_pos.mpr
  apply (div_lt_iff₀ (show 0 < 4 * (z.re - 1 / 2) by positivity)).mpr
  nlinarith [sq_nonneg (z.re - 1)]

end
end RiemannGaussian
