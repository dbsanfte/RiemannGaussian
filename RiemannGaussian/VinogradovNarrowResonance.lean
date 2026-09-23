/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowGaussian
import RiemannGaussian.VinogradovNarrowCost
import RiemannGaussian.VinogradovRelativeResonance

/-!
# Actual polynomial cancellation with a uniform coefficient

The fixed-width prime packet supplies both homogeneous moments at their
actual tuple order. Their full coefficients and all Gaussian costs fit
within a constant multiplier after the exact high-moment root. No moment
or resonance premise is supplied to the final polynomial-sum theorem.
-/

namespace RiemannGaussian.VinogradovNarrowResonance
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovShiftedMoment VinogradovKorobovMoment
open VinogradovKorobovBilinearPhase VinogradovCriticalKorobov
open VinogradovGaussianBounds VinogradovResonanceScaling
open VinogradovRectangleResonance VinogradovRectanglePowerSaving
open VinogradovKorobovPowerSaving
open VinogradovRelativeProfile

/-- The literal product moment preserves both exponent allowances and its
given homogeneous coefficient; every Gaussian cost is numerically bounded. -/
theorem product_moment_bound_with_defect (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M)
    (C eps : ℝ) (hC : 0 ≤ C)
    (hJ : meanValue ((7 * k + 1) * k) k M ≤ C * (M : ℝ) ^
      (2 * (((7 * k + 1) * k : ℕ) : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps))
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    let r := (7 * k + 1) * k
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * r) ≤
      (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) *
        (M : ℝ) ^ (4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps) := by
  let r := (7 * k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := hr
  have hr2 : 2 ≤ 2 * r := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  let lam := 2 * (((7 * k + 1) * k : ℕ) : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
  let a (j : Fin k) := reciprocalScale r M (j.val + 1)
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hsecond := (finite_moment_le_interval r k M B hB).trans hJ
  have hK : 0 ≤ moment r (fun b : B => monomialFrequency k b.val) :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hJ0 : 0 ≤ meanValue r k M :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hE := resonanceEnvelope_nonneg r ha (phaseCoefficients k t z)
    (fun b : B => monomialFrequency k b.val)
  have hcard : (B.card : ℝ) ≤ M := by
    apply Nat.cast_le.mpr
    have hc := Finset.card_le_card (show B ⊆ Finset.Icc 1 M from
      fun b hb => Finset.mem_Icc.mpr (hB b hb))
    simpa using hc
  have hbase := interval_quarter_envelope_bound k (by omega : 0 < M) t z B hr1 hr1 a ha
  dsimp only at hbase
  rw [reciprocal_support_cost k r hr (by omega : 0 < M)] at hbase
  have hres := VinogradovNarrowGaussian.actual_gaussian_resonance_le k hk M hM hrM t z
    htlo hthi hzlo hzhi B (fun b hb => (hB b hb).2)
  let A := (r - 1) * (2 * r)
  let F := r * (2 * r - 2)
  let Q := k * (k + 1) - rectangleSaving k
  have hAr : (A : ℝ) = 2 * (r : ℝ) ^ 2 - 2 * r := by
    dsimp only [A]
    rw [Nat.cast_mul, Nat.cast_sub hr1]
    push_cast
    ring
  have hFr : (F : ℝ) = 2 * (r : ℝ) ^ 2 - 2 * r := by
    dsimp only [F]
    rw [Nat.cast_mul, Nat.cast_sub hr2]
    push_cast
    ring
  have hQr : (Q : ℝ) = (k : ℝ) * ((k : ℝ) + 1) - (rectangleSaving k : ℝ) := by
    dsimp only [Q]
    rw [Nat.cast_sub (rectangleSaving_le_dimension k)]
    push_cast
    ring
  have hexp : (A : ℝ) + F + lam + lam + Q =
      4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps := by
    rw [hAr, hFr, hQr]
    dsimp only [lam]
    dsimp only [r]
    ring
  apply hbase.trans
  calc
    _ ≤ (M : ℝ) ^ A * (M : ℝ) ^ F * (C * (M : ℝ) ^ lam) *
        Real.exp ((k : ℝ) * Real.pi / 4) * (C * (M : ℝ) ^ lam) *
        resonanceEnvelope r a (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val) := by
      gcongr
    _ = C ^ 2 * ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam) *
        (Real.exp ((k : ℝ) * Real.pi / 4) *
          resonanceEnvelope r a (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val)) := by ring
    _ ≤ C ^ 2 * ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam) *
        ((2 : ℝ) ^ (9 * k ^ 2) * (M : ℝ) ^ Q) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ = (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) *
        ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam * (M : ℝ) ^ Q) := by ring
    _ = (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) * (M : ℝ) ^ ((A : ℝ) + F + lam + lam + Q) := by
      rw [← Real.rpow_natCast (M : ℝ) A, ← Real.rpow_natCast (M : ℝ) F,
        ← Real.rpow_natCast (M : ℝ) Q, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos,
        ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
    _ = _ := by rw [hexp]


/-- At the actual larger tuple order, the paid relative defects still
leave an explicit inverse-square saving after the product moment root. -/
theorem inverse_square_le_ratio (k : ℕ) (hk : 12 ≤ k) :
    1 / (8192 * (k : ℝ) ^ 2) ≤
      ((rectangleSaving k : ℝ) - 2 * ((k : ℝ) ^ 2 / 256)) /
        (2 * (((7 * k + 1) * k : ℕ) : ℝ) * (((7 * k + 1) * k : ℕ) : ℝ)) := by
  let r := (7 * k + 1) * k
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  have hr : (0 : ℝ) < r := by dsimp only [r]; positivity
  have hgain : (k : ℝ) ^ 2 ≤ 32 * ((rectangleSaving k - 1 : ℕ) : ℝ) := by
    exact_mod_cast square_le_thirtytwo_net_rectangleSaving k hk
  have hS : 1 ≤ rectangleSaving k := (one_lt_rectangleSaving k hk).le
  rw [Nat.cast_sub hS, Nat.cast_one] at hgain
  have hnum : (k : ℝ) ^ 2 / 64 ≤ (rectangleSaving k : ℝ) - 2 * ((k : ℝ) ^ 2 / 256) := by
    nlinarith only [hgain, sq_nonneg (k : ℝ)]
  have hrk : (r : ℝ) ≤ 8 * (k : ℝ) ^ 2 := by
    dsimp only [r]
    push_cast
    nlinarith only [hk1, sq_nonneg ((k : ℝ) - 1)]
  have hden : 2 * (r : ℝ) * r ≤ 128 * (k : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ hr.le hrk 2
    nlinarith only [h]
  apply (le_div_iff₀ (show 0 < 2 * (r : ℝ) * r by positivity)).mpr
  calc
    _ ≤ (1 / (8192 * (k : ℝ) ^ 2)) * (128 * (k : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = (k : ℝ) ^ 2 / 64 := by field_simp; ring
    _ ≤ _ := hnum

/-- The literal polynomial product has uniform coefficient two and a
fixed inverse-square saving, after both actual moments and every Gaussian
cost are paid. There is no independent moment premise. -/
theorem polynomial_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      2 * (M : ℝ) ^ (2 - 1 / (8192 * (k : ℝ) ^ 2)) := by
  let r := (7 * k + 1) * k
  let n := 2 * r * r
  let C : ℝ := (((2 ^ 62 * k ^ 6) ^ (k ^ 3) : ℕ) : ℝ)
  let eps := (k : ℝ) ^ 2 / 256
  have hr : 0 < r := by dsimp only [r]; positivity
  have hn : (0 : ℝ) < n := by dsimp only [n]; positivity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hJ := VinogradovNarrowCost.explicit_relative_moment_bound (by omega : 2 ≤ k) M hM
  have hb := product_moment_bound_with_defect k hk M hM hrM C eps (by positivity) hJ
    t z htlo hthi hzlo hzhi B hB
  have hC : C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2) ≤ (2 : ℝ) ^ n := by
    dsimp only [C, n, r]
    exact_mod_cast VinogradovNarrowCost.two_moments_gaussian_le (by omega : 2 ≤ k)
  have hbound := hb.trans (mul_le_mul_of_nonneg_right hC
    (Real.rpow_nonneg (Nat.cast_nonneg M) _))
  have hroot := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hbound (one_div_pos.mpr hn).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)] at hroot
  change _ ^ ((n : ℝ) * (1 / (n : ℝ))) ≤ _ at hroot
  rw [mul_one_div_cancel hn.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hMpos.le _),
    ← Real.rpow_mul hMpos.le] at hroot
  have htwo : ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_one_div_cancel hn.ne', Real.rpow_one]
  have he : (4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps) * (1 / (n : ℝ)) =
      2 - ((rectangleSaving k : ℝ) - 2 * eps) / (2 * (r : ℝ) * r) := by
    dsimp only [n]
    push_cast
    field_simp
    ring
  change _ ≤ ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) *
    (M : ℝ) ^ ((4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps) * (1 / (n : ℝ))) at hroot
  rw [htwo, he] at hroot
  apply hroot.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM)
  have hdelta := inverse_square_le_ratio k hk
  change 1 / (8192 * (k : ℝ) ^ 2) ≤
    ((rectangleSaving k : ℝ) - 2 * eps) / (2 * (r : ℝ) * r) at hdelta
  linarith only [hdelta]

end
end RiemannGaussian.VinogradovNarrowResonance
