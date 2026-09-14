/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditioningHolder

/-!
# Exact remainder scaling and explicit constant absorption

The full positive quotient powers retain an exact exponential identity.
For k>=2 and u>=k, depth at least half the scale gap gives a power saving
at every exponent at least 2k(u+1)-k(k+1)/2. A separate quantitative lemma
absorbs both fixed and iterated constants into a half-depth power of the
base. These are arithmetic and real-power ingredients; no moment estimate
or zeta-growth conclusion is assumed or established by this module.
-/

namespace RiemannGaussian.VinogradovRemainderScaling
noncomputable section

/-- At half-gap depth, the full scale exponent is at most minus the depth for every k>=2 and u>=k. -/
theorem remainder_exponent_loss {k u a b H : ℝ} (hk : 2 ≤ k) (hu : k ≤ u)
    (hH : 0 ≤ H) (hgap : b - a ≤ 2 * H) :
    (k - 1) * H + (k * (k + 1) / 2 * u / (u + 1)) * (b - a + H) -
      2 * (k * u) * H ≤ -H := by
  have hupos : 0 < u + 1 := by linarith
  have hpoly : 0 ≤ 4 * u ^ 2 - (3 * k + 1) * u - 2 := by
    have h1 := mul_nonneg (show 0 ≤ u - k by linarith) (show 0 ≤ u by linarith)
    have h2 := mul_nonneg (show 0 ≤ u - 2 by linarith) (show 0 ≤ u + 1 by linarith)
    nlinarith
  let T := k * (k + 1) / 2 * u / (u + 1)
  have hk0 : 0 ≤ k := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hT : 0 ≤ T := by unfold T; positivity
  have he : (2 * k * u - k - 3 * T) * (2 * (u + 1)) =
      k * (4 * u ^ 2 - (3 * k + 1) * u - 2) := by
    unfold T
    field_simp
    ring
  have hnonneg := mul_nonneg (show 0 ≤ k by linarith) hpoly
  have hcoef : k + 3 * T ≤ 2 * k * u := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hcoef hH
  have hgap' := mul_le_mul_of_nonneg_left (show b - a + H ≤ 3 * H by linarith) hT
  change (k - 1) * H + T * (b - a + H) - 2 * (k * u) * H ≤ -H
  nlinarith

/-- Retain each positive quotient power exactly through its logarithmic exponential form. -/
theorem quotient_power_exp {x P : ℝ} (hx : 0 < x) (hP : 0 < P) (a t : ℝ) :
    (x / P ^ a) ^ t = Real.exp (t * Real.log x - a * t * Real.log P) := by
  rw [Real.rpow_def_of_pos (div_pos hx (Real.rpow_pos_of_pos hP a)),
    Real.log_div hx.ne' (Real.rpow_pos_of_pos hP a).ne', Real.log_rpow hP a]
  congr 1
  ring

/-- Preserve the exact complete source-scale factor and the full remaining base exponent. -/
theorem scaled_remainder_identity {x P : ℝ} (hx : 0 < x) (hP : 0 < P)
    {k u : ℝ} (hu : u + 1 ≠ 0) (a b H lam : ℝ) :
    P ^ ((k - 1) * H) * (x / P ^ a) ^ (lam / (u + 1)) *
      (x / P ^ (b + H)) ^ (lam * u / (u + 1)) =
      ((x / P ^ a) ^ (lam - 2 * k * u) * (x / P ^ b) ^ (2 * k * u)) *
      P ^ ((k - 1) * H + ((2 * k * (u + 1) - lam) * u / (u + 1)) *
        (b - a + H) - 2 * (k * u) * H) := by
  simp_rw [quotient_power_exp hx hP]
  simp only [Real.rpow_def_of_pos hP, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The complete scale factor saves a full depth power at every real exponent above the critical threshold. -/
theorem scaled_remainder_le {x P k u a b H lam : ℝ} (hx : 0 < x) (hP : 1 ≤ P)
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 0 ≤ H) (hgap : b - a ≤ 2 * H)
    (hlam : 2 * k * (u + 1) - k * (k + 1) / 2 ≤ lam) :
    P ^ ((k - 1) * H) * (x / P ^ a) ^ (lam / (u + 1)) *
      (x / P ^ (b + H)) ^ (lam * u / (u + 1)) ≤
      ((x / P ^ a) ^ (lam - 2 * k * u) * (x / P ^ b) ^ (2 * k * u)) * P ^ (-H) := by
  have hPpos : 0 < P := by linarith
  have hu1 : 0 < u + 1 := by linarith
  rw [scaled_remainder_identity hx hPpos hu1.ne']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hP
  have hdelta : (2 * k * (u + 1) - lam) * u / (u + 1) ≤
      k * (k + 1) / 2 * u / (u + 1) := by
    apply div_le_div_of_nonneg_right _ hu1.le
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have he := mul_le_mul_of_nonneg_right hdelta (show 0 ≤ b - a + H by linarith)
  have hb := remainder_exponent_loss hk hu hH hgap
  linarith

/-- Combine a common positive constant across both fractional powers exactly, before any estimate. -/
theorem common_power_mean {C A B : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (lam theta : ℝ) :
    (C * A ^ lam) ^ theta * (C * B ^ lam) ^ (1 - theta) =
      C * (A ^ (lam * theta) * B ^ (lam * (1 - theta))) := by
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hA lam),
    Real.mul_rpow hC.le (Real.rpow_nonneg hB lam), ← Real.rpow_mul hA, ← Real.rpow_mul hB]
  calc
    _ = (C ^ theta * C ^ (1 - theta)) * (A ^ (lam * theta) * B ^ (lam * (1 - theta))) := by ring
    _ = _ := by rw [← Real.rpow_add hC]; simp

/-- An explicit square threshold absorbs fixed and iterated constants into a half-depth base saving. -/
theorem constant_power_absorption {C D P : ℝ} (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hP : 0 < P) (hbudget : (C * D) ^ 2 ≤ P) {H : ℕ} (hH : 1 ≤ H) :
    C * D ^ H / P ^ H ≤ P ^ (-((H : ℝ) / 2)) := by
  have hCD : 0 ≤ C * D := mul_nonneg (by linarith) hD
  have hroot : C * D ≤ P ^ (1 / 2 : ℝ) := by
    have he := Real.rpow_le_rpow (sq_nonneg (C * D)) hbudget (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hid : ((C * D) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = C * D := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast hCD (by omega : (2 : ℕ) ≠ 0)
    rwa [hid] at he
  have hCp : C ≤ C ^ H := by
    simpa only [pow_one] using pow_le_pow_right₀ hC hH
  calc
    C * D ^ H / P ^ H ≤ (C * D) ^ H / P ^ H := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hP.le H)
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hCp (pow_nonneg hD H)
    _ ≤ (P ^ (1 / 2 : ℝ)) ^ H / P ^ H := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hP.le H)
      exact pow_le_pow_left₀ hCD hroot H
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le, ← Real.rpow_natCast, ← Real.rpow_sub hP]
      congr 1
      ring

end
end RiemannGaussian.VinogradovRemainderScaling
