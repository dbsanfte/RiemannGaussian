/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResonancePower
import RiemannGaussian.VinogradovCriticalKorobov
import RiemannGaussian.VinogradovKorobovBlock

/-!
# A genuine saving for the original shifted imaginary-power product sum

For every k>=4, let r=k(k+1). At t=M^(2k),z=M^4, every sufficiently large
integer M and every B contained in [1,M] have actual product sum bounded
by C*M^(2-1/(2r^2)). Both critical moments, the full resonance factor,
Gaussian smoothing and the entire logarithmic remainder are paid.

This proves the displayed parameter regime. Constants and thresholds are
unevaluated; their uniform degree dependence, wider parameter ranges,
zeta growth and any new zero-free region remain open. No RH claim follows.
-/

namespace RiemannGaussian.VinogradovKorobovPowerSaving
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianKernel
open VinogradovResonanceScaling VinogradovResonancePower

/-- The reciprocal scales pay exactly one pi per degree in the original first-family Gaussian support cost. -/
theorem reciprocal_support_cost (k r : ℕ) (hr : 0 < r) {M : ℕ} (hM : 0 < M) :
    VinogradovGaussianKernel.supportCost (fun j : Fin k => reciprocalScale r M (j.val + 1))
      (VinogradovMomentReduction.frequencySupport (VinogradovShiftedMoment.tupleFrequency r
        (fun b : Fin M => VinogradovMeanValue.monomialFrequency k (b.val + 1)))) = (k : ℝ) * Real.pi := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [VinogradovKorobovMoment.interval_origin_cost_eq r k hM
    (fun j => (reciprocalScale_pos hr hMpos (j.val + 1)).le)]
  have he (j : Fin k) : Real.pi * reciprocalScale r M (j.val + 1) *
      ((r : ℝ) * (M : ℝ) ^ (j.val + 1)) ^ 2 = Real.pi := by
    unfold reciprocalScale
    field_simp
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The original coupled polynomial sum has a genuine eventual power saving after both critical moments, the full resonance product and Gaussian smoothing costs. -/
theorem exists_power_product_moment_saving (k : ℕ) (hk : 4 ≤ k) :
    let r := (k + 1) * k
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ B : Finset ℕ,
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ M) →
      ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4) ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * r) ≤
      C * (M : ℝ) ^ (4 * (r : ℝ) ^ 2 - 1) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := hr
  have hr2 : 2 ≤ 2 * r := by omega
  have hk2 : 2 ≤ k * (k + 1) := by nlinarith
  obtain ⟨C, hC, M₀, D, hD, Y₀, h⟩ :=
    VinogradovCriticalKorobov.exists_critical_product_bound k k k (by omega) le_rfl le_rfl
      (1 / 2) (by norm_num)
  obtain ⟨E, hE, hres⟩ := exists_actual_resonance_power_saving k r r hk hr
  let V := C * Real.exp ((k : ℝ) * Real.pi / 4) * D * E
  refine ⟨V, by dsimp only [V]; positivity, max (max M₀ Y₀) (max r 1), ?_⟩
  intro M hM B hB
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
  have hR := hres M hM1 hrM B (fun b hb => (hB b hb).2)
  have hbase := h M M hM0 hMY ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4) B hB a ha
  have hcost := reciprocal_support_cost k r hr (by omega : 0 < M)
  rw [hcost] at hbase
  let lam := 2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + 1 / 2
  let A := (r - 1) * (2 * r)
  let F := r * (2 * r - 2)
  let Q := k * (k + 1) - 2
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
  have hQr : (Q : ℝ) = (k : ℝ) * ((k : ℝ) + 1) - 2 := by
    dsimp only [Q]
    rw [Nat.cast_sub hk2]
    push_cast
    ring
  have hrr : (r : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by dsimp only [r]; push_cast; ring
  have hexp : (A : ℝ) + F + lam + lam + Q = 4 * (r : ℝ) ^ 2 - 1 := by
    rw [hAr, hFr, hQr]
    dsimp only [lam]
    nlinarith only [hrr]
  apply hbase.trans
  calc
    _ ≤ (M : ℝ) ^ A * (M : ℝ) ^ F * (C * (M : ℝ) ^ lam) *
        Real.exp ((k : ℝ) * Real.pi / 4) * (D * (M : ℝ) ^ lam) * (E * (M : ℝ) ^ Q) := by
      gcongr
      exact resonanceEnvelope_nonneg r ha
        (VinogradovKorobovMoment.phaseCoefficients k ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4))
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
theorem exists_power_polynomial_saving (k : ℕ) (hk : 4 ≤ k) :
    let r := (k + 1) * k
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ B : Finset ℕ,
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ M) →
      ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4) ((b.val + 1 : ℕ) : ℝ) c‖ ≤
      C * (M : ℝ) ^ (2 - 1 / (2 * (r : ℝ) * r)) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  let n := 2 * r * r
  have hn : (0 : ℝ) < n := by dsimp only [n]; positivity
  obtain ⟨C, hC, M₀, h⟩ := exists_power_product_moment_saving k hk
  refine ⟨C ^ (1 / (n : ℝ)), Real.rpow_pos_of_pos hC _, max M₀ 1, ?_⟩
  intro M hM B hB
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (le_max_right M₀ 1).trans hM
  have hb := h M ((le_max_left _ _).trans hM) B hB
  have hroot := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hb (one_div_pos.mpr hn).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)] at hroot
  change _ ^ ((n : ℝ) * (1 / (n : ℝ))) ≤ _ at hroot
  rw [mul_one_div_cancel hn.ne', Real.rpow_one,
    Real.mul_rpow hC.le (Real.rpow_nonneg hMpos.le _), ← Real.rpow_mul hMpos.le] at hroot
  have he : (4 * (r : ℝ) ^ 2 - 1) * (1 / (n : ℝ)) = 2 - 1 / (2 * (r : ℝ) * r) := by
    dsimp only [n]
    push_cast
    field_simp
    ring
  change _ ≤ C ^ (1 / (n : ℝ)) * (M : ℝ) ^ ((4 * (r : ℝ) ^ 2 - 1) * (1 / (n : ℝ))) at hroot
  rw [he] at hroot
  exact hroot

/-- At the actual power-related endpoints the full logarithmic approximation costs only a bounded total error. -/
theorem power_logarithmic_error_le (k : ℕ) {M : ℕ} (hM : 0 < M) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖(∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase
        ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4) ((b.val + 1 : ℕ) : ℝ) c) -
      ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4) ((b.val + 1 : ℕ) : ℝ) c‖ ≤ 1 / ((k : ℝ) + 1) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard : (B.card : ℝ) ≤ M := by
    apply Nat.cast_le.mpr
    have hc := Finset.card_le_card (show B ⊆ Finset.Icc 1 M from
      fun b hb => Finset.mem_Icc.mpr (hB b hb))
    simpa using hc
  have h := VinogradovKorobovBilinearPhase.sum_error_le_card (Finset.univ : Finset (Fin M)) B
    (fun b => ((b.val + 1 : ℕ) : ℝ)) (fun c : ℕ => (c : ℝ)) k ((M : ℝ) ^ (2 * k))
    (z := (M : ℝ) ^ 4) (M₁ := M) (M₂ := M) (by positivity)
    (by intro b _; constructor; positivity; exact_mod_cast b.isLt)
    (fun b hb => ⟨Nat.cast_nonneg b, by exact_mod_cast (hB b hb).2⟩)
  simp only [Finset.card_univ, Fintype.card_fin, abs_of_pos (pow_pos hMpos _)] at h
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
theorem exists_shifted_imaginary_power_saving (k : ℕ) (hk : 4 ≤ k) :
    let r := (k + 1) * k
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ B : Finset ℕ,
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ M) →
      ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBlock.dirichletTerm
        ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4) ((b.val + 1) * c)‖ ≤
      C * (M : ℝ) ^ (2 - 1 / (2 * (r : ℝ) * r)) := by
  let r := (k + 1) * k
  let alpha := 2 - 1 / (2 * (r : ℝ) * r)
  have hr1 : (1 : ℝ) ≤ r := by
    have hr : 0 < r := by dsimp only [r]; positivity
    exact_mod_cast hr
  have hden : 1 ≤ 2 * (r : ℝ) * r := by nlinarith only [hr1, sq_nonneg ((r : ℝ) - 1)]
  have halpha : 0 ≤ alpha := by
    have hdiv : 1 / (2 * (r : ℝ) * r) ≤ 1 := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
    dsimp only [alpha]
    linarith only [hdiv]
  obtain ⟨C, hC, M₀, h⟩ := exists_power_polynomial_saving k hk
  refine ⟨C + 1, by positivity, max M₀ 1, ?_⟩
  intro M hM B hB
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  let T := (M : ℝ) ^ (2 * k)
  let Z := (M : ℝ) ^ 4
  have hZ : 0 < Z := by dsimp only [Z]; positivity
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
  have hpoly := h M ((le_max_left _ _).trans hM) B hB
  have herr := power_logarithmic_error_le k (by omega : 0 < M) B hB
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
end RiemannGaussian.VinogradovKorobovPowerSaving
