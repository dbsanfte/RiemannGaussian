/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DerivativeOrderComparison
import RiemannGaussian.DirichletCriticalRange

/-!
# Complete transition windows for Dirichlet block powers

The exact exponent curve chooses a derivative order on every block scale
up to the height. Both terms of the profile are controlled throughout each
transition window; no complementary power or interval is omitted.
-/

namespace RiemannGaussian.DirichletTransitionWindows
noncomputable section
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison
open DirichletBlockPowerProfile

/-- The two block exponents on a later balanced line retain their exact
displacements from the earlier-order line. -/
theorem profile_on_later_line (r k : ℕ) (t X : ℝ) :
    profile r (line k) t X =
      256 * t ^ alpha r * X ^ (delta k - delta r) +
      64 * t ^ (-alpha r) * X ^ (delta k - amp r + delta r) := by
  unfold profile line delta beta
  congr 2 <;> congr 1 <;> ring

/-- The complementary height exponent has an exact balanced expression
at the upper endpoint of its transition window. -/
theorem complementary_balance (r k : ℕ) :
    -alpha r + transition r * (delta k - amp r + delta r) =
      alpha r + transition r * (delta k - delta r) := by
  have h := transition_balance r
  have hs : DirichletPowerParameters.slope r = 2 * delta r - amp r := by
    unfold DirichletPowerParameters.slope delta
    ring
  rw [hs] at h
  nlinarith

/-- Both terms of an earlier-order profile have the target height power
throughout its complete transition window. -/
theorem profile_le_on_window (r k : ℕ) (hrk : r ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hX : 0 < X)
    (hlower : t ^ transition (r + 1) ≤ X) (hupper : X ≤ t ^ transition r) :
    profile r (line k) t X ≤ 320 * t ^ alpha k := by
  have htpos : 0 < t := by linarith
  have ha : delta k - delta r ≤ 0 := sub_nonpos.mpr (delta_antitone hrk)
  have hb : 0 ≤ delta k - amp r + delta r := by
    linarith [amp_le_delta r, delta_pos k]
  have hlead := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos htpos (transition (r + 1))) hlower ha
  rw [← Real.rpow_mul htpos.le] at hlead
  have hlead' := mul_le_mul_of_nonneg_left hlead (Real.rpow_nonneg htpos.le (alpha r))
  rw [← Real.rpow_add htpos] at hlead'
  have hlead'' := Real.rpow_le_rpow_of_exponent_le ht (order_comparison r k hrk)
  have hcomp := Real.rpow_le_rpow hX.le hupper hb
  rw [← Real.rpow_mul htpos.le] at hcomp
  have hcomp' := mul_le_mul_of_nonneg_left hcomp (Real.rpow_nonneg htpos.le (-alpha r))
  rw [← Real.rpow_add htpos, complementary_balance] at hcomp'
  have he : alpha r + transition r * (delta k - delta r) ≤ alpha k := by
    have hm := mul_le_mul_of_nonpos_right (transition_succ_le r) ha
    linarith [order_comparison r k hrk]
  have hcomp'' := Real.rpow_le_rpow_of_exponent_le ht he
  rw [profile_on_later_line]
  nlinarith

/-- The initial range and the successive transition windows cover every
positive scale up to the height. -/
theorem window_cover (k : ℕ) {t X : ℝ} (hupper : X ≤ t) :
    X ≤ t ^ transition k ∨
      ∃ r < k, t ^ transition (r + 1) ≤ X ∧ X ≤ t ^ transition r := by
  induction k with
  | zero => left; simpa [transition_zero] using hupper
  | succ k ih =>
    by_cases h : X ≤ t ^ transition (k + 1)
    · exact Or.inl h
    · right
      rcases ih with hi | ⟨r, hr, hlo, hhi⟩
      · exact ⟨k, Nat.lt_succ_self k, (lt_of_not_ge h).le, hi⟩
      · exact ⟨r, Nat.lt_succ_of_lt hr, hlo, hhi⟩

/-- An analytically selected derivative order controls every positive
block scale through the full height on any balanced line. -/
theorem exists_order_bound (k : ℕ) {t X : ℝ} (ht : 1 ≤ t) (hX : 0 < X)
    (hupper : X ≤ t) :
    ∃ r ≤ k, profile r (line k) t X ≤ 320 * t ^ alpha k := by
  rcases window_cover k hupper with h | ⟨r, hr, hlo, hhi⟩
  · exact ⟨k, le_rfl, DirichletCriticalRange.profile_le_on_range k
      (by linarith) hX h⟩
  · exact ⟨r, hr.le, profile_le_on_window r k hr.le ht hX hlo hhi⟩

end
end RiemannGaussian.DirichletTransitionWindows
