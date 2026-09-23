/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovVariableGaussian
import RiemannGaussian.VinogradovShortMoment
import RiemannGaussian.VinogradovRelativeResonance

/-!
# Stronger actual polynomial cancellation from shorter moment orders

The same literal product, frequency window and Gaussian kernel now use
three or four blocks of the proved moment descent. All coefficients are
paid before the high-moment root. The saving is 1/(1600*k^2) for k>=12
and 1/(512*k^2) for k>=48, with no independent moment premise.
-/

namespace RiemannGaussian.VinogradovShortResonance
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovShiftedMoment VinogradovKorobovMoment
open VinogradovKorobovBilinearPhase VinogradovCriticalKorobov
open VinogradovGaussianBounds VinogradovResonanceScaling
open VinogradovRectangleResonance VinogradovRectanglePowerSaving
open VinogradovKorobovPowerSaving

/-- The literal product moment preserves both exponent allowances and its
given homogeneous coefficient; every Gaussian cost is numerically bounded. -/
theorem product_moment_bound_with_defect (k : ℕ) (hk : 12 ≤ k) (r : ℕ)
    (hkr : k ≤ r) (hrk : r ≤ 8 * k ^ 2)
    (M : ℕ) (hM : 1 ≤ M) (hrM : r ≤ M)
    (C eps : ℝ) (hC : 0 ≤ C)
    (hJ : meanValue r k M ≤ C * (M : ℝ) ^
      (2 * (r : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps))
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * r) ≤
      (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) *
        (M : ℝ) ^ (4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps) := by
  have hr : 0 < r := by omega
  have hr1 : 1 ≤ r := hr
  have hr2 : 2 ≤ 2 * r := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  let lam := 2 * (r : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
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
  have hres := VinogradovVariableGaussian.actual_gaussian_resonance_le k hk r hkr hrk M hM hrM t z
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


/-- Every retained frequency is counted; the complete window has a
stronger quadratic lower bound once degree is at least forty-eight. -/
theorem square_le_eleven_rectangleSaving (k : ℕ) (hk : 48 ≤ k) :
    k ^ 2 ≤ 11 * rectangleSaving k := by
  rw [rectangleSaving_eq]
  have ha : 5 * k ≤ 16 * (k - 2 * k / 3 - 1) := by omega
  have hb : 7 * k ≤ 24 * (k - 2 * k / 3 - 2) := by omega
  have h := Nat.mul_le_mul ha hb
  nlinarith only [h]

/-- Four degree blocks leave the explicit saving 1/(1600*k^2) at
every degree in the original continuous rectangle. -/
theorem four_ratio (k : ℕ) (hk : 12 ≤ k) :
    1 / (1600 * (k : ℝ) ^ 2) ≤
      ((rectangleSaving k : ℝ) - 2 * ((k : ℝ) ^ 2 / 100)) /
        (2 * (((4 * k + 1) * k : ℕ) : ℝ) * (((4 * k + 1) * k : ℕ) : ℝ)) := by
  have hkr : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hgain : (k : ℝ) ^ 2 ≤ 24 * (rectangleSaving k : ℝ) := by
    exact_mod_cast square_le_twentyfour_rectangleSaving k hk
  have hnum : (17 / 800 : ℝ) * (k : ℝ) ^ 2 ≤
      (rectangleSaving k : ℝ) - 2 * ((k : ℝ) ^ 2 / 100) := by nlinarith
  have hs : (4 * (k : ℝ) + 1) ^ 2 ≤ 17 * (k : ℝ) ^ 2 := by nlinarith
  have hden : 2 * (((4 * k + 1) * k : ℕ) : ℝ) * (((4 * k + 1) * k : ℕ) : ℝ) ≤
      34 * (k : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hs (sq_nonneg (k : ℝ))
    push_cast
    nlinarith only [h]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ (1 / (1600 * (k : ℝ) ^ 2)) * (34 * (k : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = (17 / 800 : ℝ) * (k : ℝ) ^ 2 := by field_simp; ring
    _ ≤ _ := hnum

/-- Three degree blocks and the complete retained window leave saving
1/(512*k^2) once k>=48, sixteen times the previous uniform saving. -/
theorem three_ratio (k : ℕ) (hk : 48 ≤ k) :
    1 / (512 * (k : ℝ) ^ 2) ≤
      ((rectangleSaving k : ℝ) - 2 * ((k : ℝ) ^ 2 / 40)) /
        (2 * (((3 * k + 1) * k : ℕ) : ℝ) * (((3 * k + 1) * k : ℕ) : ℝ)) := by
  have hkr : (48 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hgain : (k : ℝ) ^ 2 ≤ 11 * (rectangleSaving k : ℝ) := by
    exact_mod_cast square_le_eleven_rectangleSaving k hk
  have hnum : (5 / 128 : ℝ) * (k : ℝ) ^ 2 ≤
      (rectangleSaving k : ℝ) - 2 * ((k : ℝ) ^ 2 / 40) := by nlinarith
  have hs : (3 * (k : ℝ) + 1) ^ 2 ≤ 10 * (k : ℝ) ^ 2 := by nlinarith
  have hden : 2 * (((3 * k + 1) * k : ℕ) : ℝ) * (((3 * k + 1) * k : ℕ) : ℝ) ≤
      20 * (k : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hs (sq_nonneg (k : ℝ))
    push_cast
    nlinarith only [h]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ (1 / (512 * (k : ℝ) ^ 2)) * (20 * (k : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = (5 / 128 : ℝ) * (k : ℝ) ^ 2 := by field_simp; ring
    _ ≤ _ := hnum

/-- The exact high-moment root pays both specified moment coefficients
and all Gaussian costs before any saving is relaxed. -/
theorem polynomial_bound_of_defect (k : ℕ) (hk : 12 ≤ k) (r : ℕ)
    (hrlo : (3 * k + 1) * k ≤ r) (hrhi : r ≤ 8 * k ^ 2)
    (M : ℕ) (hM : 1 ≤ M) (hrM : r ≤ M) (eps d : ℝ)
    (hJ : meanValue r k M ≤ (VinogradovShortMoment.coefficient k : ℝ) * (M : ℝ) ^
      (2 * (r : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps))
    (hd : d ≤ ((rectangleSaving k : ℝ) - 2 * eps) / (2 * (r : ℝ) * r))
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      2 * (M : ℝ) ^ (2 - d) := by
  let n := 2 * r * r
  let C : ℝ := VinogradovShortMoment.coefficient k
  have hr : 0 < r := by nlinarith
  have hkr : k ≤ r := by nlinarith
  have hn : (0 : ℝ) < n := by dsimp only [n]; positivity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := product_moment_bound_with_defect k hk r hkr hrhi M hM hrM C eps
    (Nat.cast_nonneg _) hJ t z htlo hthi hzlo hzhi B hB
  have hC : C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2) ≤ (2 : ℝ) ^ n := by
    dsimp only [C, n]
    exact_mod_cast VinogradovShortMoment.two_moments_gaussian_le hk hrlo
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
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith only [hd])

/-- The improved saving keeps the stronger large-degree branch. -/
def saving (k : ℕ) : ℝ :=
  if 48 ≤ k then 1 / (512 * (k : ℝ) ^ 2) else 1 / (1600 * (k : ℝ) ^ 2)

/-- The actual saving is positive and no larger than one throughout
its original domain, so the Taylor and shift boundary payments remain valid. -/
theorem saving_bounds {k : ℕ} (hk : 1 ≤ k) : 0 < saving k ∧ saving k ≤ 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hs := one_le_pow₀ (n := 2) hkR
  unfold saving
  split_ifs
  · constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      nlinarith
  · constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      nlinarith

/-- The actual original polynomial product has its improved saving
with no moment premise. Both branches keep a common polynomial threshold. -/
theorem polynomial_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (4 * k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      2 * (M : ℝ) ^ (2 - saving k) := by
  by_cases hk48 : 48 ≤ k
  · rw [saving, if_pos hk48]
    exact polynomial_bound_of_defect k hk ((3 * k + 1) * k) le_rfl (by nlinarith)
      M hM (by nlinarith) _ _ (VinogradovShortMoment.moment_three_bound (by omega) M hM)
      (three_ratio k hk48) t z htlo hthi hzlo hzhi B hB
  · rw [saving, if_neg hk48]
    exact polynomial_bound_of_defect k hk ((4 * k + 1) * k) (by nlinarith) (by nlinarith)
      M hM hrM _ _ (VinogradovShortMoment.moment_four_bound (by omega) M hM)
      (four_ratio k hk) t z htlo hthi hzlo hzhi B hB

end
end RiemannGaussian.VinogradovShortResonance
