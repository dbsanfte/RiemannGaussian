/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletTransitionWindows

/-!
# All block scales needed by the canonical zeta cutoff

The second-derivative profile controls the remaining interval from the
height to four times the height. Together with the exact order-transition
windows this removes every scale restriction on the canonical eta prefix.
-/

namespace RiemannGaussian.DirichletFullRange
noncomputable section
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison
open DirichletBlockPowerProfile DirichletTransitionWindows

/-- On any balanced line in the right half-strip, the second-derivative
profile controls the entire last interval from the height to four times it. -/
theorem profile_le_above_height (k : ℕ) (hk : 1 ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hlower : t ≤ X) (hupper : X ≤ 4 * t) :
    profile 0 (line k) t X ≤ 512 * t ^ alpha k := by
  have htpos : 0 < t := by linarith
  have hd : delta k ≤ 1 / 2 := by
    rw [delta_eq_one_sub_line]
    linarith [half_le_line k hk]
  have hdpos := delta_pos k
  have ha : delta k - 1 ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le ht
    (show delta k - 1 / 2 ≤ alpha k by linarith [alpha_pos k])
  have hlead := Real.rpow_le_rpow_of_nonpos htpos hlower ha
  have hlead' := mul_le_mul_of_nonneg_left hlead
    (Real.rpow_nonneg htpos.le (1 / 2))
  rw [← Real.rpow_add htpos,
    show 1 / 2 + (delta k - 1) = delta k - 1 / 2 by ring] at hlead'
  have hfour : (4 : ℝ) ^ delta k ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by linarith : delta k ≤ 1)).trans_eq
    exact Real.rpow_one _
  have hcomp : X ^ delta k ≤ 4 * t ^ delta k := by
    calc
      _ ≤ (4 * t) ^ delta k := Real.rpow_le_rpow
        (by linarith : 0 ≤ X) hupper hdpos.le
      _ = (4 : ℝ) ^ delta k * t ^ delta k := Real.mul_rpow (by norm_num) htpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg htpos.le _)
  have hcomp' := mul_le_mul_of_nonneg_left hcomp
    (Real.rpow_nonneg htpos.le (-(1 / 2)))
  have he : t ^ (-(1 / 2 : ℝ)) * (4 * t ^ delta k) =
      4 * t ^ (delta k - 1 / 2) := by
    rw [show t ^ (-(1 / 2 : ℝ)) * (4 * t ^ delta k) =
      4 * (t ^ (-(1 / 2 : ℝ)) * t ^ delta k) by ring,
      ← Real.rpow_add htpos]
    congr 2
    ring
  rw [he] at hcomp'
  have hd0 : delta 0 = 1 := by norm_num [delta, alpha]
  rw [profile_on_later_line, hd0, amp_zero, alpha_zero,
    show delta k - 1 + 1 = delta k by ring]
  nlinarith

/-- A derivative order no larger than the target order controls every
positive block scale needed by the canonical zeta cutoff. -/
theorem exists_order_bound (k : ℕ) (hk : 1 ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hX : 0 < X) (hupper : X ≤ 4 * t) :
    ∃ r ≤ k, profile r (line k) t X ≤ 512 * t ^ alpha k := by
  by_cases hx : X ≤ t
  · obtain ⟨r, hr, h⟩ := DirichletTransitionWindows.exists_order_bound k ht hX hx
    refine ⟨r, hr, h.trans ?_⟩
    have hp := Real.rpow_nonneg (by linarith : 0 ≤ t) (alpha k)
    nlinarith
  · exact ⟨0, Nat.zero_le k, profile_le_above_height k hk ht
      (lt_of_not_ge hx).le hupper⟩

end
end RiemannGaussian.DirichletFullRange
