/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRectangleResonance

/-!
# Actual imaginary-power cancellation on a continuous parameter rectangle

For each k >= 12 the literal product sum has saving 1/(128*k^2), uniformly
on the displayed height and starting-point rectangle and over every
subset of positive shifts. Moment constants and starting thresholds are
unevaluated; a uniform Vinogradov--Korobov zeta estimate remains open.
-/

namespace RiemannGaussian.VinogradovRectanglePowerSaving
noncomputable section
open scoped BigOperators
open VinogradovRectangleResonance
open VinogradovGaussianBounds VinogradovResonanceScaling
open VinogradovKorobovPowerSaving

/-- The complete degree saving cannot exceed the full two-family frequency dimension. -/
theorem rectangleSaving_le_dimension (k : ℕ) : rectangleSaving k ≤ k * (k + 1) := by
  rw [rectangleSaving_eq]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Every degree at least twelve has a positive gain left after the two half-epsilon moments. -/
theorem one_lt_rectangleSaving (k : ℕ) (hk : 12 ≤ k) : 1 < rectangleSaving k := by
  rw [rectangleSaving_eq]
  have hm : 3 ≤ k - 2 * k / 3 - 1 := by omega
  have h := Nat.mul_le_mul hm (show 2 ≤ k - 2 * k / 3 - 2 by omega)
  omega

/-- The full degree window gives an inverse-square saving after taking the actual high-moment root. -/
theorem inverse_square_le_rectangle_ratio (k : ℕ) (hk : 12 ≤ k) :
    1 / (128 * (k : ℝ) ^ 2) ≤
      ((rectangleSaving k - 1 : ℕ) : ℝ) / (2 * (((k + 1) * k : ℕ) : ℝ) * (((k + 1) * k : ℕ) : ℝ)) := by
  have hkreal : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have hgain : (k : ℝ) ^ 2 ≤ 32 * ((rectangleSaving k - 1 : ℕ) : ℝ) := by
    exact_mod_cast square_le_thirtytwo_net_rectangleSaving k hk
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by
    nlinarith only [hkreal, sq_nonneg ((k : ℝ) - 3)]
  have hcoef : 2 * ((k : ℝ) + 1) ^ 2 ≤ 128 * ((rectangleSaving k - 1 : ℕ) : ℝ) := by
    linarith only [hgain, hsq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (k : ℝ))
  push_cast
  nlinarith only [hm]

/-- The original coupled polynomial sum has a genuine eventual power saving after both critical moments, the full resonance product and Gaussian smoothing costs. -/
theorem exists_rectangle_product_moment_saving (k : ℕ) (hk : 12 ≤ k) :
    let r := (k + 1) * k
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 4 * (M : ℝ) ^ 4 → ∀ B : Finset ℕ,
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ M) →
      ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * r) ≤
      C * (M : ℝ) ^ (4 * (r : ℝ) ^ 2 - ((rectangleSaving k - 1 : ℕ) : ℝ)) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := hr
  have hr2 : 2 ≤ 2 * r := by omega
  have hks := rectangleSaving_le_dimension k
  have hS1 : 1 ≤ rectangleSaving k := (one_lt_rectangleSaving k (by omega)).le
  have hgain : ((rectangleSaving k - 1 : ℕ) : ℝ) = (rectangleSaving k : ℝ) - 1 := by
    rw [Nat.cast_sub hS1, Nat.cast_one]
  obtain ⟨C, hC, M₀, D, hD, Y₀, h⟩ :=
    VinogradovCriticalKorobov.exists_critical_product_bound k k k (by omega) le_rfl le_rfl
      (1 / 2) (by norm_num)
  obtain ⟨E, hE, hres⟩ := exists_rectangle_resonance_power_saving k r r hr
  let V := C * Real.exp ((k : ℝ) * Real.pi / 4) * D * E
  refine ⟨V, by dsimp only [V]; positivity, max (max M₀ Y₀) (max r 1), ?_⟩
  intro M hM t z htlo hthi hzlo hzhi B hB
  have hM0 : M₀ ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans hM)
  have hMY : Y₀ ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hM)
  have hrM : r ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hM1 : 1 ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hcard : (B.card : ℝ) ≤ M := by
    apply Nat.cast_le.mpr
    have hc := Finset.card_le_card (show B ⊆ Finset.Icc 1 M from
      fun b hb => Finset.mem_Icc.mpr (hB b hb))
    simpa using hc
  let a (j : Fin k) := reciprocalScale r M (j.val + 1)
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hR := hres M hM1 hrM t z htlo hthi hzlo hzhi B (fun b hb => (hB b hb).2)
  have hbase := h M M hM0 hMY t z B hB a ha
  have hcost := reciprocal_support_cost k r hr (by omega : 0 < M)
  rw [hcost] at hbase
  let lam := 2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + 1 / 2
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
    rw [Nat.cast_sub hks]
    push_cast
    ring
  have hrr : (r : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by dsimp only [r]; push_cast; ring
  have hexp : (A : ℝ) + F + lam + lam + Q = 4 * (r : ℝ) ^ 2 - ((rectangleSaving k - 1 : ℕ) : ℝ) := by
    rw [hAr, hFr, hQr, hgain]
    dsimp only [lam]
    nlinarith only [hrr]
  apply hbase.trans
  calc
    _ ≤ (M : ℝ) ^ A * (M : ℝ) ^ F * (C * (M : ℝ) ^ lam) *
        Real.exp ((k : ℝ) * Real.pi / 4) * (D * (M : ℝ) ^ lam) * (E * (M : ℝ) ^ Q) := by
      gcongr
      exact resonanceEnvelope_nonneg r ha
        (VinogradovKorobovMoment.phaseCoefficients k t z)
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val)
    _ = V * ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam * (M : ℝ) ^ Q) := by
      dsimp only [V]
      ring
    _ = V * (M : ℝ) ^ ((A : ℝ) + F + lam + lam + Q) := by
      rw [← Real.rpow_natCast (M : ℝ) A, ← Real.rpow_natCast (M : ℝ) F,
        ← Real.rpow_natCast (M : ℝ) Q, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos,
        ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
    _ = _ := by rw [hexp]

/-- Taking the genuine positive moment root gives a strict saving below the full product support size. -/
theorem exists_rectangle_polynomial_saving (k : ℕ) (hk : 12 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 4 * (M : ℝ) ^ 4 → ∀ B : Finset ℕ,
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ M) →
      ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      C * (M : ℝ) ^ (2 - 1 / (128 * (k : ℝ) ^ 2)) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  let n := 2 * r * r
  have hn : (0 : ℝ) < n := by dsimp only [n]; positivity
  obtain ⟨C, hC, M₀, h⟩ := exists_rectangle_product_moment_saving k hk
  refine ⟨C ^ (1 / (n : ℝ)), Real.rpow_pos_of_pos hC _, max M₀ 1, ?_⟩
  intro M hM t z htlo hthi hzlo hzhi B hB
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (le_max_right M₀ 1).trans hM
  have hb := h M ((le_max_left _ _).trans hM) t z htlo hthi hzlo hzhi B hB
  have hroot := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hb (one_div_pos.mpr hn).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)] at hroot
  change _ ^ ((n : ℝ) * (1 / (n : ℝ))) ≤ _ at hroot
  rw [mul_one_div_cancel hn.ne', Real.rpow_one,
    Real.mul_rpow hC.le (Real.rpow_nonneg hMpos.le _), ← Real.rpow_mul hMpos.le] at hroot
  have he : (4 * (r : ℝ) ^ 2 - ((rectangleSaving k - 1 : ℕ) : ℝ)) * (1 / (n : ℝ)) = 2 - ((rectangleSaving k - 1 : ℕ) : ℝ) / (2 * (r : ℝ) * r) := by
    dsimp only [n]
    push_cast
    field_simp
    ring
  change _ ≤ C ^ (1 / (n : ℝ)) * (M : ℝ) ^ ((4 * (r : ℝ) ^ 2 - ((rectangleSaving k - 1 : ℕ) : ℝ)) * (1 / (n : ℝ))) at hroot
  rw [he] at hroot
  apply hroot.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC.le _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (le_max_right M₀ 1).trans hM)
  have hdelta := inverse_square_le_rectangle_ratio k hk
  change 1 / (128 * (k : ℝ) ^ 2) ≤ ((rectangleSaving k - 1 : ℕ) : ℝ) / (2 * (r : ℝ) * r) at hdelta
  linarith only [hdelta]

/-- At the actual power-related endpoints the full logarithmic approximation costs only a bounded total error. -/
theorem rectangle_logarithmic_error_le (k : ℕ) {M : ℕ} (hM : 0 < M) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {t z : ℝ} (ht : 0 ≤ t)
    (hti : t ≤ (M : ℝ) ^ (2 * k)) (hz : (M : ℝ) ^ 4 ≤ z) :
    ‖(∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase
        t z ((b.val + 1 : ℕ) : ℝ) c) -
      ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤ 1 / ((k : ℝ) + 1) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hZ : 0 < z := (pow_pos hMpos 4).trans_le hz
  have hcard : (B.card : ℝ) ≤ M := by
    apply Nat.cast_le.mpr
    have hc := Finset.card_le_card (show B ⊆ Finset.Icc 1 M from
      fun b hb => Finset.mem_Icc.mpr (hB b hb))
    simpa using hc
  have h := VinogradovKorobovBilinearPhase.sum_error_le_card (Finset.univ : Finset (Fin M)) B
    (fun b => ((b.val + 1 : ℕ) : ℝ)) (fun c : ℕ => (c : ℝ)) k t
    (z := z) (M₁ := M) (M₂ := M) ((pow_pos hMpos 4).trans_le hz)
    (by intro b _; constructor; positivity; exact_mod_cast b.isLt)
    (fun b hb => ⟨Nat.cast_nonneg b, by exact_mod_cast (hB b hb).2⟩)
  simp only [Finset.card_univ, Fintype.card_fin, abs_of_nonneg ht] at h
  apply h.trans
  calc
    _ ≤ (M : ℝ) * M * ((M : ℝ) ^ (2 * k) *
        ((M : ℝ) * M / (M : ℝ) ^ 4) ^ (k + 1) / (k + 1)) := by gcongr
    _ = _ := by
      have he : (M : ℝ) * M / (M : ℝ) ^ 4 = 1 / (M : ℝ) ^ 2 := by field_simp
      rw [he, div_pow, one_pow, ← pow_mul]
      field_simp
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      ring

/-- The literal shifted imaginary-power product sum inherits a genuine saving, after paying the entire logarithmic remainder. -/
theorem exists_rectangle_shifted_imaginary_power_saving (k : ℕ) (hk : 12 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 4 * (M : ℝ) ^ 4 → ∀ B : Finset ℕ,
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ M) →
      ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBlock.dirichletTerm
        t z ((b.val + 1) * c)‖ ≤
      C * (M : ℝ) ^ (2 - 1 / (128 * (k : ℝ) ^ 2)) := by
  let alpha := 2 - 1 / (128 * (k : ℝ) ^ 2)
  have hden : 1 ≤ 128 * (k : ℝ) ^ 2 := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hs := one_le_pow₀ (n := 2) hk1
    nlinarith only [hs]
  have halpha : 0 ≤ alpha := by
    have hdiv : 1 / (128 * (k : ℝ) ^ 2) ≤ 1 := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
    dsimp only [alpha]
    linarith only [hdiv]
  obtain ⟨C, hC, M₀, h⟩ := exists_rectangle_polynomial_saving k hk
  refine ⟨C + 1, by positivity, max M₀ 1, ?_⟩
  intro M hM t z htlo hthi hzlo hzhi B hB
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  let T := t
  let Z := z
  have hZ : 0 < Z := (pow_pos hMpos 4).trans_le hzlo
  have he : (∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBlock.dirichletTerm T Z ((b.val + 1) * c)) =
      VinogradovKorobovBlock.basePhase T Z *
        ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase T Z ((b.val + 1 : ℕ) : ℝ) c := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    simpa only [zero_add, Nat.cast_zero, add_zero] using
      VinogradovKorobovBlock.dirichletTerm_shift hZ T 0 (b.val + 1) c
  rw [he, norm_mul, VinogradovKorobovBlock.norm_basePhase, one_mul]
  have hpoly := h M ((le_max_left _ _).trans hM) t z htlo hthi hzlo hzhi B hB
  have herr := rectangle_logarithmic_error_le k (by omega : 0 < M) B hB
    ((pow_pos hMpos _).trans_le htlo).le hthi hzlo
  let L := ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase T Z ((b.val + 1 : ℕ) : ℝ) c
  let P := ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k T Z ((b.val + 1 : ℕ) : ℝ) c
  have hnorm : ‖L‖ ≤ ‖P‖ + ‖L - P‖ := by
    calc
      _ = ‖P + (L - P)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hpow : 1 ≤ (M : ℝ) ^ alpha := Real.one_le_rpow (by exact_mod_cast hM1) halpha
  have herror : 1 / ((k : ℝ) + 1) ≤ (M : ℝ) ^ alpha := by
    apply le_trans _ hpow
    apply (div_le_one (by positivity)).mpr
    linarith only [Nat.cast_nonneg (α := ℝ) k]
  have htotal := hnorm.trans (add_le_add hpoly herr)
  calc
    _ ≤ C * (M : ℝ) ^ alpha + 1 / ((k : ℝ) + 1) := htotal
    _ ≤ (C + 1) * (M : ℝ) ^ alpha := by nlinarith only [herror]

end
end RiemannGaussian.VinogradovRectanglePowerSaving
