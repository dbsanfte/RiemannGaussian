/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovQuantitativeDescent
import RiemannGaussian.VinogradovGaussianCost

/-!
# The Gaussian gain pays relative moment-exponent allowances

The original polynomial product sum needs only moment exponent critical
plus `k^2/128` to retain a saving `1/(256*k^2)`. Both moment costs, all
Gaussian tails and the actual homogeneous coefficient remain explicit.
The quantitative finite descent supplies the moment input in the terminal
theorem, whose coefficient is a specified function of the degree. Its size
still has to be assessed before inferring uniform zeta growth.
-/

namespace RiemannGaussian.VinogradovRelativeResonance
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovShiftedMoment VinogradovKorobovMoment
open VinogradovKorobovBilinearPhase VinogradovCriticalKorobov
open VinogradovGaussianBounds VinogradovResonanceScaling
open VinogradovRectangleResonance VinogradovRectanglePowerSaving
open VinogradovKorobovPowerSaving
open VinogradovRelativeProfile
open VinogradovQuantitativeDescent

/-- The literal product moment preserves both exponent allowances and its
given homogeneous coefficient; every Gaussian cost is numerically bounded. -/
theorem product_moment_bound_with_defect (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (k + 1) * k ≤ M)
    (C eps : ℝ) (hC : 0 ≤ C)
    (hJ : meanValue ((k + 1) * k) k M ≤ C * (M : ℝ) ^
      (2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps))
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    let r := (k + 1) * k
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * r) ≤
      (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) *
        (M : ℝ) ^ (4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := hr
  have hr2 : 2 ≤ 2 * r := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  let lam := 2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
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
  have hres := VinogradovGaussianCost.actual_gaussian_resonance_le k hk M hM hrM t z
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
  have hrr : (r : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by dsimp only [r]; push_cast; ring
  have hexp : (A : ℝ) + F + lam + lam + Q =
      4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps := by
    rw [hAr, hFr, hQr]
    dsimp only [lam]
    nlinarith only [hrr]
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

/-- Paying two allowances `k^2/128` still leaves an inverse-square
saving at the original product's high-moment root. -/
theorem inverse_square_le_relative_ratio (k : ℕ) (hk : 12 ≤ k) :
    1 / (256 * (k : ℝ) ^ 2) ≤
      ((rectangleSaving k : ℝ) - 2 * relativeDefect k 128) /
        (2 * (((k + 1) * k : ℕ) : ℝ) * (((k + 1) * k : ℕ) : ℝ)) := by
  have hgain : (k : ℝ) ^ 2 ≤ 32 * ((rectangleSaving k - 1 : ℕ) : ℝ) := by
    exact_mod_cast square_le_thirtytwo_net_rectangleSaving k hk
  have hS : 1 ≤ rectangleSaving k := (one_lt_rectangleSaving k hk).le
  have hmargin : ((rectangleSaving k - 1 : ℕ) : ℝ) / 2 ≤
      (rectangleSaving k : ℝ) - 2 * relativeDefect k 128 := by
    rw [Nat.cast_sub hS, Nat.cast_one] at hgain ⊢
    unfold relativeDefect
    norm_num only [Nat.cast_ofNat]
    linarith only [hgain]
  calc
    _ = (1 / (128 * (k : ℝ) ^ 2)) / 2 := by ring
    _ ≤ (((rectangleSaving k - 1 : ℕ) : ℝ) /
        (2 * (((k + 1) * k : ℕ) : ℝ) * (((k + 1) * k : ℕ) : ℝ))) / 2 :=
      div_le_div_of_nonneg_right (inverse_square_le_rectangle_ratio k hk) (by norm_num)
    _ = (((rectangleSaving k - 1 : ℕ) : ℝ) / 2) /
        (2 * (((k + 1) * k : ℕ) : ℝ) * (((k + 1) * k : ℕ) : ℝ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hmargin (by positivity)

/-- The actual polynomial product retains inverse-square cancellation with
the larger moment allowance and a completely displayed constant. -/
theorem polynomial_bound_with_relative_defect (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (k + 1) * k ≤ M) (C : ℝ) (hC : 0 ≤ C)
    (hJ : meanValue ((k + 1) * k) k M ≤ C * (M : ℝ) ^
      (2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + relativeDefect k 128))
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    let r := (k + 1) * k
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) ^ (1 / ((2 * r * r : ℕ) : ℝ)) *
        (M : ℝ) ^ (2 - 1 / (256 * (k : ℝ) ^ 2)) := by
  let r := (k + 1) * k
  let n := 2 * r * r
  have hr : 0 < r := by dsimp only [r]; positivity
  have hn : (0 : ℝ) < n := by dsimp only [n]; positivity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := product_moment_bound_with_defect k hk M hM hrM C (relativeDefect k 128) hC hJ
    t z htlo hthi hzlo hzhi B hB
  have hroot := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hb (one_div_pos.mpr hn).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)] at hroot
  change _ ^ ((n : ℝ) * (1 / (n : ℝ))) ≤ _ at hroot
  rw [mul_one_div_cancel hn.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hMpos.le _), ← Real.rpow_mul hMpos.le] at hroot
  have he : (4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * relativeDefect k 128) * (1 / (n : ℝ)) =
      2 - ((rectangleSaving k : ℝ) - 2 * relativeDefect k 128) / (2 * (r : ℝ) * r) := by
    dsimp only [n]
    push_cast
    field_simp
    ring
  change _ ≤ (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) ^ (1 / (n : ℝ)) *
    (M : ℝ) ^ ((4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * relativeDefect k 128) * (1 / (n : ℝ))) at hroot
  rw [he] at hroot
  apply hroot.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM)
  have hdelta := inverse_square_le_relative_ratio k hk
  change 1 / (256 * (k : ℝ) ^ 2) ≤
    ((rectangleSaving k : ℝ) - 2 * relativeDefect k 128) / (2 * (r : ℝ) * r) at hdelta
  linarith only [hdelta]

/-- The complete coefficient after both actual moments and the Gaussian
factor have passed through the product's original high-moment root. -/
def productMultiplier (k : ℕ) : ℝ :=
  (momentMultiplier k 128 ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) ^
    (1 / ((2 * ((k + 1) * k) * ((k + 1) * k) : ℕ) : ℝ))

/-- The explicit product coefficient is strictly positive. -/
theorem productMultiplier_pos (k : ℕ) : 0 < productMultiplier k := by
  have h := momentMultiplier_pos k 128
  unfold productMultiplier
  positivity

/-- The original polynomial product has an unconditional explicit bound
at every supported endpoint and degree. No analytic moment premise remains. -/
theorem polynomial_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      productMultiplier k * (M : ℝ) ^ (2 - 1 / (256 * (k : ℝ) ^ 2)) := by
  have hqk : 128 ≤ k ^ 2 :=
    (by norm_num : 128 ≤ (12 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hk 2)
  exact polynomial_bound_with_relative_defect k hk M hM hrM (momentMultiplier k 128)
    (momentMultiplier_pos k 128).le
    (relative_moment_bound k 128 (by omega) (by norm_num) hqk M hM)
    t z htlo hthi hzlo hzhi B hB

end
end RiemannGaussian.VinogradovRelativeResonance
