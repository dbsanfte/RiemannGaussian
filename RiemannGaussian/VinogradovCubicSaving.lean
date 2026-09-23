/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovShortDyadic
import RiemannGaussian.VinogradovScaleSelection

/-!
# Retaining the physical-scale cubic saving

The original time rectangle couples the chosen degree to log(X)/log(t).
Keeping that relation gives the cubic exponent v*delta-v^3/10368 rather
than a uniform middle-block ceiling. Its maximum is at most
40*delta*sqrt(delta). All inequalities concern the existing actual block.
The cubic optimization is the classical VK block-to-growth mechanism;
no external exponential-sum estimate is assumed.
-/

namespace RiemannGaussian.VinogradovCubicSaving
noncomputable section
open VinogradovShortResonance

/-- A uniform numerical upper bound for the retained cubic profile. -/
theorem cubic_le {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) :
    d * v - v ^ 3 / 10368 ≤ 40 * d * Real.sqrt d := by
  let a := Real.sqrt (3456 * d)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 3456 * d := Real.sq_sqrt (by positivity)
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt hd
  have ha60 : a ≤ 60 * Real.sqrt d := by nlinarith
  have hfactor := mul_nonneg (sq_nonneg (v - a)) (show 0 ≤ v + 2 * a by positivity)
  have hid : (v - a) ^ 2 * (v + 2 * a) = v ^ 3 - 3 * a ^ 2 * v + 2 * a ^ 2 * a := by ring
  rw [hid, ha2] at hfactor
  have hmul := mul_le_mul_of_nonneg_left ha60 hd
  nlinarith

/-- Integer fourth-root rounding and the original time rectangle give
an explicit coupling of the physical logarithm with the actual degree. -/
theorem degree_log_bound {k M X : ℕ} (hk : 48 ≤ k) (hM : 16 ≤ M)
    (hX : X ≤ 2 * M ^ 4) {t : ℝ}
    (hlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hXpos : 0 < X) :
    (k : ℝ) * Real.log X ≤ (9 / 4 : ℝ) * Real.log t := by
  have hMr : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have htwo : 4 * Real.log 2 ≤ Real.log M := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hMr
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [he] at h
  have hXr : (X : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by exact_mod_cast hX
  have hlX := Real.log_le_log (by exact_mod_cast hXpos : (0 : ℝ) < X) hXr
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hMpos.ne'), Real.log_pow] at hlX
  norm_num only [Nat.cast_ofNat] at hlX
  have htime := Real.log_le_log (pow_pos hMpos _) hlo
  rw [Real.log_pow] at htime
  have hcast : ((2 * k - 2 : ℕ) : ℝ) = 2 * (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * k)]
    push_cast
    ring
  rw [hcast] at htime
  have hkr : (48 : ℝ) ≤ k := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_left (show Real.log X ≤ 17 / 4 * Real.log M by linarith)
    (show (0 : ℝ) ≤ k by positivity)
  have hreserve := mul_nonneg (show 0 ≤ (k : ℝ) - 18 by linarith) hlM
  nlinarith

/-- The full physical saving dominates the square of the logarithmic
scale ratio. This retains the dependence discarded by a uniform bound. -/
theorem saving_ge_ratio {k : ℕ} (hk : 48 ≤ k) {v : ℝ} (hv : 0 ≤ v)
    (hkv : (k : ℝ) * v ≤ 9 / 4) :
    v ^ 2 / 10368 ≤ saving k / 4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsq : ((k : ℝ) * v) ^ 2 ≤ (9 / 4 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hkpos.le hv) hkv 2
  simp only [saving, if_pos hk]
  rw [div_div]
  apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
  nlinarith

/-- The literal high-degree saving retains the unmaximized cubic profile
at its actual logarithmic scale. This stronger inequality stays available
for summation over scales before a uniform growth envelope is taken. -/
theorem power_le_cubic_profile {k M X : ℕ} (hk : 48 ≤ k) (hM : 16 ≤ M)
    (hX : X ≤ 2 * M ^ 4) (hXone : 1 ≤ X) {t σ d : ℝ}
    (ht : 1 < t) (hlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hσ : 1 - σ ≤ d) :
    (X : ℝ) ^ (1 - σ - saving k / 4) ≤ Real.exp
      ((d * (Real.log X / Real.log t) - (Real.log X / Real.log t) ^ 3 / 10368) * Real.log t) := by
  have hL : 0 < Real.log t := Real.log_pos ht
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hXone
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hXone)
  let v := Real.log X / Real.log t
  have hv : 0 ≤ v := div_nonneg hlogX hL.le
  have hkv : (k : ℝ) * v ≤ 9 / 4 := by
    rw [show (k : ℝ) * v = ((k : ℝ) * Real.log X) / Real.log t by dsimp [v]; ring]
    exact (div_le_iff₀ hL).mpr (degree_log_bound hk hM hX hlo (by omega))
  have hsav := saving_ge_ratio hk hv hkv
  have hmul := mul_le_mul_of_nonneg_right hsav hv
  have hdamp := mul_le_mul_of_nonneg_right hσ hv
  have he : (1 - σ - saving k / 4) * v ≤ d * v - v ^ 3 / 10368 := by nlinarith
  have hlog : (1 - σ - saving k / 4) * Real.log X ≤
      (d * v - v ^ 3 / 10368) * Real.log t := by
    have h := mul_le_mul_of_nonneg_right he hL.le
    have hvL : v * Real.log t = Real.log X := by dsimp [v]; field_simp
    simpa only [mul_assoc, hvL] using h
  rw [Real.rpow_def_of_pos hXpos]
  apply Real.exp_le_exp.mpr
  linarith

/-- Maximizing the retained profile gives the numerical exponent forty
without changing the actual degree, root or time rectangle. -/
theorem power_le {k M X : ℕ} (hk : 48 ≤ k) (hM : 16 ≤ M)
    (hX : X ≤ 2 * M ^ 4) (hXone : 1 ≤ X) {t σ d : ℝ}
    (ht : 1 < t) (hlo : (M : ℝ) ^ (2 * k - 2) ≤ t)
    (hd : 0 ≤ d) (hσ : 1 - σ ≤ d) :
    (X : ℝ) ^ (1 - σ - saving k / 4) ≤ t ^ (40 * d * Real.sqrt d) := by
  have hL := Real.log_pos ht
  have hv : 0 ≤ Real.log X / Real.log t :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hXone)) hL.le
  have h := power_le_cubic_profile hk hM hX hXone ht hlo hσ
  have hc := mul_le_mul_of_nonneg_right (cubic_le hd hv) hL.le
  apply h.trans
  rw [Real.rpow_def_of_pos (by linarith : 0 < t)]
  apply Real.exp_le_exp.mpr
  nlinarith

end
end RiemannGaussian.VinogradovCubicSaving
