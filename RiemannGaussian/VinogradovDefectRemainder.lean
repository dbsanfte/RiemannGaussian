/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovUniformExponent

/-!
# Preserve the full exponent defect in the actual deep remainder

The exact quotient scaling retains the source exponent's distance above
critical as an additional prime power. Constant absorption preserves that
whole power and remains linear in the original homogeneous constant.
The general bound still names the two actual quotient moment budgets; the
critical-moment chain supplies such budgets. No global zero-free claim follows.
-/

namespace RiemannGaussian.VinogradovDefectRemainder
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap

/-- The exact exponent loss retains the complete defect above the critical
mean-value exponent, multiplied by the full quotient-scale separation. -/
theorem remainder_exponent_with_defect {k u a b H : ℝ} (hk : 2 ≤ k) (hu : k ≤ u)
    (hH : 0 ≤ H) (hgap : b - a ≤ 2 * H) (lam : ℝ) :
    (k - 1) * H + ((2 * k * (u + 1) - lam) * u / (u + 1)) * (b - a + H) -
      2 * (k * u) * H ≤
      -H - (lam - (2 * k * (u + 1) - k * (k + 1) / 2)) * u / (u + 1) * (b - a + H) := by
  have h := remainder_exponent_loss hk hu hH hgap
  have hu0 : u + 1 ≠ 0 := by linarith only [hk, hu]
  have hid : (k - 1) * H + ((2 * k * (u + 1) - lam) * u / (u + 1)) * (b - a + H) -
      2 * (k * u) * H =
      ((k - 1) * H + (k * (k + 1) / 2 * u / (u + 1)) * (b - a + H) - 2 * (k * u) * H) -
      (lam - (2 * k * (u + 1) - k * (k + 1) / 2)) * u / (u + 1) * (b - a + H) := by
    field_simp
    ring
  rw [hid]
  linarith only [h]

/-- The complete positive quotient product retains the extra prime power
from the exact exponent defect. This is valid for every real source exponent. -/
theorem scaled_remainder_with_defect {x P k u a b H lam : ℝ} (hx : 0 < x) (hP : 1 ≤ P)
    (hk : 2 ≤ k) (hu : k ≤ u) (hH : 0 ≤ H) (hgap : b - a ≤ 2 * H) :
    P ^ ((k - 1) * H) * (x / P ^ a) ^ (lam / (u + 1)) *
      (x / P ^ (b + H)) ^ (lam * u / (u + 1)) ≤
      ((x / P ^ a) ^ (lam - 2 * k * u) * (x / P ^ b) ^ (2 * k * u)) *
        P ^ (-H - (lam - (2 * k * (u + 1) - k * (k + 1) / 2)) * u / (u + 1) * (b - a + H)) := by
  rw [scaled_remainder_identity hx (zero_lt_one.trans_le hP) (by linarith : u + 1 ≠ 0)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hP (remainder_exponent_with_defect hk hu hH hgap lam)

/-- Constant absorption preserves the entire defect contribution to the
actual remainder exponent and remains linear in the homogeneous constant. -/
theorem defect_constant_absorption {C D P extra : ℝ} (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hP : 0 < P) (hbudget : D ^ 2 ≤ P) {H : ℕ} (hH : 1 ≤ H) :
    C * D ^ H * P ^ (-(H : ℝ) - extra) ≤ C * P ^ (-((H : ℝ) / 2) - extra) := by
  have hb := constant_power_absorption (C := 1) le_rfl hD hP
    (by simpa only [one_mul] using hbudget) hH
  simp only [one_mul] at hb
  have hp : P ^ (-(H : ℝ) - extra) = (P ^ H)⁻¹ * P ^ (-extra) := by
    rw [sub_eq_add_neg, Real.rpow_add hP, Real.rpow_neg hP.le, Real.rpow_natCast]
  rw [hp, sub_eq_add_neg, Real.rpow_add hP]
  calc
    _ = C * (D ^ H / P ^ H) * P ^ (-extra) := by ring
    _ ≤ C * P ^ (-((H : ℝ) / 2)) * P ^ (-extra) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (zero_le_one.trans hC)) (by positivity)
    _ = _ := by ring

/-- The original mixed remainder retains both its homogeneous constant and
the full extra prime saving supplied by the source exponent defect. -/
theorem deep_remainder_preserving_defect {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H)
    (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hbudget : iterationConstant k u ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ lam)
    (colour : Fin k → Bool) :
    let delta := lam - (2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2)
    singularCost p k u ^ H * levelMixedMaximum p k a (b + H) xi X u colour ≤
      C * ((((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
        ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) *
          (p : ℝ) ^ (-((H : ℝ) / 2) - delta * (u : ℝ) / ((u : ℝ) + 1) *
            ((b : ℝ) - (a : ℝ) + H))) := by
  have hCpos : 0 < C := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have hgapR : (b : ℝ) - a ≤ 2 * H := by
    have h : b ≤ a + 2 * H := by omega
    have h' : (b : ℝ) ≤ a + 2 * H := by exact_mod_cast h
    linarith
  have hI : levelMixedMaximum p k a (b + H) xi X u colour ≤ C *
      (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
       ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ))) := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro c hc
    exact mixed_le_of_scaled_bounds (by omega) hC hA hB colour
  have hS : singularCost p k u ^ H ≤ iterationConstant k u ^ H * (p : ℝ) ^ ((k - 1) * H) := by
    calc
      _ ≤ (iterationConstant k u * (p : ℝ) ^ (k - 1)) ^ H :=
        pow_le_pow_left₀ (by unfold singularCost; positivity) (singularCost_le_power p k u) H
      _ = _ := by rw [mul_pow, ← pow_mul]

  let extra := (lam - (2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2)) *
    (u : ℝ) / ((u : ℝ) + 1) * ((b : ℝ) - (a : ℝ) + H)
  let S := ((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
    ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))
  have hs := scaled_remainder_with_defect (show (0 : ℝ) < X by exact_mod_cast hX) hp1 hkR huR
    (Nat.cast_nonneg H) hgapR (lam := lam)
  have hs' : (p : ℝ) ^ ((k - 1) * H) *
      ((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
      ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ)) ≤
      S * (p : ℝ) ^ (-(H : ℝ) - extra) := by
    dsimp only [S, extra]
    convert hs using 1 <;>
      simp only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
        Nat.cast_add, Nat.cast_ofNat, mul_assoc]
  have hb := defect_constant_absorption hC
    (show 0 ≤ iterationConstant k u by unfold iterationConstant; positivity) hp0 hbudget hH (extra := extra)
  change _ ≤ C * (S * (p : ℝ) ^ (-((H : ℝ) / 2) - extra))
  calc
    _ ≤ singularCost p k u ^ H * (C *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
         ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hI (by unfold singularCost; positivity)
    _ ≤ (iterationConstant k u ^ H * (p : ℝ) ^ ((k - 1) * H)) * (C *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
         ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = (C * iterationConstant k u ^ H) * ((p : ℝ) ^ ((k - 1) * H) *
        ((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
        ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ))) := by ring
    _ ≤ (C * iterationConstant k u ^ H) * (S * (p : ℝ) ^ (-(H : ℝ) - extra)) :=
      mul_le_mul_of_nonneg_left hs' (by unfold iterationConstant; positivity)
    _ = S * (C * iterationConstant k u ^ H * (p : ℝ) ^ (-(H : ℝ) - extra)) := by ring
    _ ≤ S * (C * (p : ℝ) ^ (-((H : ℝ) / 2) - extra)) :=
      mul_le_mul_of_nonneg_left hb (by dsimp only [S]; positivity)
    _ = _ := by ring

end
end RiemannGaussian.VinogradovDefectRemainder
