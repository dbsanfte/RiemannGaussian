/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletBlockPowerProfile

/-!+# Paying the long blocks on the Vinogradov near-one lines

The existing sixth- and fourth-derivative estimates cover every scale
from t^(2/11) through 4t with absolute constants. Both terms of each
original profile are paid, including the complementary derivative term.
These bounds require only a line displacement between zero and 1/4096.
-/

namespace RiemannGaussian.VinogradovLongBlocks
noncomputable section
open DirichletBlockPowerProfile DerivativePowerExponents

/-- Increasing the real part decreases both terms of the proved profile
on every block whose physical scale is at least one. -/
theorem profile_antitone_sigma (q : ℕ) {sigma tau t X : ℝ}
    (ht : 0 ≤ t) (hX : 1 ≤ X) (hσ : sigma ≤ tau) :
    profile q tau t X ≤ profile q sigma t X := by
  unfold profile
  apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ (by positivity)
  all_goals exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- The sixth-derivative profile costs at most 320 between the two
explicit height powers, including its complementary term. -/
theorem sixth_profile_le {delta t X : ℝ} (hd : 0 ≤ delta) (hd' : delta ≤ 1 / 4096)
    (ht : 1 ≤ t) (hlo : t ^ (2 / 11 : ℝ) ≤ X) (hhi : X ≤ t ^ (1 / 3 : ℝ)) :
    profile 4 (1 - delta) t X ≤ 320 := by
  have htpos : 0 < t := by linarith
  have hXpos : 0 < X := (Real.rpow_pos_of_pos htpos _).trans_le hlo
  have hl := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos htpos (2 / 11))
    hlo (show delta - 6 / 62 ≤ 0 by linarith)
  have hl' := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg htpos.le (1 / 62))
  rw [← Real.rpow_mul htpos.le, ← Real.rpow_add htpos] at hl'
  have hlead : t ^ (1 / 62 : ℝ) * X ^ (delta - 6 / 62) ≤ 1 :=
    hl'.trans (Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith))
  have hc := Real.rpow_le_rpow hXpos.le hhi
    (show 0 ≤ delta - 1 / 16 + 6 / 62 by linarith)
  have hc' := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg htpos.le (-(1 / 62)))
  rw [← Real.rpow_mul htpos.le, ← Real.rpow_add htpos] at hc'
  have hcomp : t ^ (-(1 / 62 : ℝ)) * X ^ (delta - 1 / 16 + 6 / 62) ≤ 1 :=
    hc'.trans (Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith))
  have he : profile 4 (1 - delta) t X =
      256 * (t ^ (1 / 62 : ℝ) * X ^ (delta - 6 / 62)) +
        64 * (t ^ (-(1 / 62 : ℝ)) * X ^ (delta - 1 / 16 + 6 / 62)) := by
    norm_num [profile, alpha, beta, amp]
    ring_nf
  rw [he]
  linarith

/-- The fourth-derivative profile costs at most 512 from t^(1/3)
through the complete canonical cutoff 4t. -/
theorem fourth_profile_le {delta t X : ℝ} (hd : 0 ≤ delta) (hd' : delta ≤ 1 / 4096)
    (ht : 1 ≤ t) (hlo : t ^ (1 / 3 : ℝ) ≤ X) (hhi : X ≤ 4 * t) :
    profile 2 (1 - delta) t X ≤ 512 := by
  have htpos : 0 < t := by linarith
  have hXpos : 0 < X := (Real.rpow_pos_of_pos htpos _).trans_le hlo
  have hl := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos htpos (1 / 3))
    hlo (show delta - 4 / 14 ≤ 0 by linarith)
  have hl' := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg htpos.le (1 / 14))
  rw [← Real.rpow_mul htpos.le, ← Real.rpow_add htpos] at hl'
  have hlead : t ^ (1 / 14 : ℝ) * X ^ (delta - 4 / 14) ≤ 1 :=
    hl'.trans (Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith))
  let b := delta - 1 / 4 + 4 / 14
  have hb0 : 0 ≤ b := by dsimp only [b]; linarith
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith
  have hfour : (4 : ℝ) ^ b ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hb1).trans_eq
    exact Real.rpow_one _
  have hc : X ^ b ≤ 4 * t ^ b := by
    calc
      _ ≤ (4 * t) ^ b := Real.rpow_le_rpow hXpos.le hhi hb0
      _ = (4 : ℝ) ^ b * t ^ b := Real.mul_rpow (by norm_num) htpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg htpos.le b)
  have hc' := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg htpos.le (-(1 / 14)))
  have he : t ^ (-(1 / 14 : ℝ)) * (4 * t ^ b) = 4 * t ^ (-(1 / 14 : ℝ) + b) := by
    rw [show t ^ (-(1 / 14 : ℝ)) * (4 * t ^ b) =
      4 * (t ^ (-(1 / 14 : ℝ)) * t ^ b) by ring, ← Real.rpow_add htpos]
  rw [he] at hc'
  have hp : t ^ (-(1 / 14 : ℝ) + b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by dsimp only [b]; linarith)
  have hcomp : t ^ (-(1 / 14 : ℝ)) * X ^ (delta - 1 / 4 + 4 / 14) ≤ 4 := by
    change t ^ (-(1 / 14 : ℝ)) * X ^ b ≤ 4
    linarith
  have hprofile : profile 2 (1 - delta) t X =
      256 * (t ^ (1 / 14 : ℝ) * X ^ (delta - 4 / 14)) +
        64 * (t ^ (-(1 / 14 : ℝ)) * X ^ (delta - 1 / 4 + 4 / 14)) := by
    norm_num [profile, alpha, beta, amp]
    ring_nf
  rw [hprofile]
  linarith

end
end RiemannGaussian.VinogradovLongBlocks
