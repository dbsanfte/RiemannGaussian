/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRectanglePowerSaving

/-!
# A genuine power saving for the original Dirichlet block

The original signed shift identity precedes the named endpoint norm bound.
A proved product-sum estimate then gives a bound for every partial block and
a power saving for whole blocks of length M^4. This is an unconditional
finite Dirichlet-sum theorem at fixed degree, with unevaluated constants and
thresholds. No new zero-free region follows without further analytic work.
-/

namespace RiemannGaussian.VinogradovDirichletSaving
noncomputable section
open scoped BigOperators
open VinogradovKorobovBlock

/-- A uniform bound for the actual inner product sums transfers to the original
Dirichlet block after paying the complete endpoint correction. -/
theorem block_bound_of_product_bound {M L : ℕ} (hM : 0 < M) {z : ℝ} (hz : 0 < z)
    (t K : ℝ)
    (hK : ∀ n ∈ Finset.range L,
      ‖∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
        dirichletTerm t (z + n) ((a.val + 1) * b)‖ ≤ K) :
    ‖block (dirichletTerm t z) L‖ ≤ (L : ℝ) * K / (M : ℝ) ^ 2 + 2 * (M : ℝ) ^ 2 := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let A := (Finset.univ : Finset (Fin M)) ×ˢ Finset.Icc 1 M
  have h := weighted_shift_identity A (fun p => (p.1.val + 1) * p.2)
    (fun _ => 1) (dirichletTerm t z) L
  have he : ((M : ℂ) * M) * block (dirichletTerm t z) L =
      (∑ n ∈ Finset.range L, ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
        dirichletTerm t (z + n) ((a.val + 1) * b)) +
      ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
        boundary (dirichletTerm t z) L ((a.val + 1) * b) := by
    have hshift (n p : ℕ) : dirichletTerm t z (n + p) = dirichletTerm t (z + n) p := by
      simp only [dirichletTerm, Nat.cast_add, add_assoc]
    simpa only [A, Finset.sum_product, Finset.sum_const, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, Nat.cast_mul, mul_one, one_mul, hshift] using h
  have hsum : ‖∑ n ∈ Finset.range L, ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
      dirichletTerm t (z + n) ((a.val + 1) * b)‖ ≤ (L : ℝ) * K := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _n ∈ Finset.range L, K := Finset.sum_le_sum hK
      _ = _ := by simp
  have hb : ‖∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
      boundary (dirichletTerm t z) L ((a.val + 1) * b)‖ ≤ 2 * (M : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
          ‖boundary (dirichletTerm t z) L ((a.val + 1) * b)‖ := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : Fin M, ∑ _b ∈ Finset.Icc 1 M, 2 * (M : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b hb
        apply (boundary_norm_le (dirichletTerm t z)
          (fun n => (norm_dirichletTerm hz t n).le) L ((a.val + 1) * b)).trans
        have ha : ((a.val + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast a.isLt
        have hb' : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hb).2
        have hp := mul_le_mul ha hb' (Nat.cast_nonneg b) hMr.le
        push_cast at hp ⊢
        nlinarith only [hp]
      _ = _ := by simp; ring
  have hnorm : (M : ℝ) ^ 2 * ‖block (dirichletTerm t z) L‖ ≤
      (L : ℝ) * K + 2 * (M : ℝ) ^ 4 := by
    calc
      _ = ‖((M : ℂ) * M) * block (dirichletTerm t z) L‖ := by
        rw [norm_mul, norm_mul, Complex.norm_natCast, ← pow_two]
      _ = _ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsum hb)
  calc
    _ ≤ ((L : ℝ) * K + 2 * (M : ℝ) ^ 4) / (M : ℝ) ^ 2 :=
      (le_div_iff₀ (pow_pos hMr 2)).mpr (by simpa only [mul_comm] using hnorm)
    _ = _ := by field_simp

/-- Every partial original Dirichlet block in the continuous rectangle receives
the proved product saving, with the full normalized endpoint cost displayed. -/
theorem exists_partial_dirichlet_saving (k : ℕ) (hk : 12 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 2 * (M : ℝ) ^ 4 → ∀ L : ℕ, L ≤ 2 * M ^ 4 →
      ‖block (dirichletTerm t z) L‖ ≤
        C * L * (M : ℝ) ^ (-(1 / (128 * (k : ℝ) ^ 2))) + 2 * (M : ℝ) ^ 2 := by
  obtain ⟨C, hC, M₀, h⟩ :=
    VinogradovRectanglePowerSaving.exists_rectangle_shifted_imaginary_power_saving k hk
  refine ⟨C, hC, max M₀ 1, ?_⟩
  intro M hM t z htlo hthi hzlo hzhi L hL
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  have hz : 0 < z := (pow_pos hMr 4).trans_le hzlo
  let delta := 1 / (128 * (k : ℝ) ^ 2)
  have hp := block_bound_of_product_bound (by omega : 0 < M) hz t
    (C * (M : ℝ) ^ (2 - delta)) (by
      intro n hn
      apply h M ((le_max_left _ _).trans hM) t (z + n) htlo hthi
        (hzlo.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)))
      · have hn' : (n : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hn)).trans hL
        linarith only [hzhi, hn']
      · intro b hb
        exact Finset.mem_Icc.mp hb)
  apply hp.trans_eq
  congr 1
  rw [show 2 - delta = 2 + (-delta) by ring, Real.rpow_add hMr,
    Real.rpow_two]
  field_simp
  rfl

/-- A whole block of length M^4 has a genuine power saving throughout the
continuous height and starting-point intervals, with no assumed sum estimate. -/
theorem exists_dirichlet_block_saving (k : ℕ) (hk : 12 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 2 * (M : ℝ) ^ 4 →
      ‖block (dirichletTerm t z) (M ^ 4)‖ ≤
        C * (M : ℝ) ^ (4 - 1 / (128 * (k : ℝ) ^ 2)) := by
  obtain ⟨C, hC, M₀, h⟩ := exists_partial_dirichlet_saving k hk
  refine ⟨C + 2, by positivity, max M₀ 1, ?_⟩
  intro M hM t z htlo hthi hzlo hzhi
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right M₀ 1).trans hM
  have hMr := zero_lt_one.trans_le hM1
  have hb := h M ((le_max_left _ _).trans hM) t z htlo hthi hzlo hzhi (M ^ 4) (by omega)
  let delta := 1 / (128 * (k : ℝ) ^ 2)
  have hden : 1 ≤ 128 * (k : ℝ) ^ 2 := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hs := one_le_pow₀ (n := 2) hk1
    nlinarith only [hs]
  have hd : delta ≤ 1 := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
  have hpow : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ (4 - delta) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith only [hd])
  have he : C * ((M ^ 4 : ℕ) : ℝ) * (M : ℝ) ^ (-delta) =
      C * (M : ℝ) ^ (4 - delta) := by
    push_cast
    rw [mul_assoc, ← Real.rpow_natCast (M : ℝ) 4, ← Real.rpow_add hMr]
    congr 2
  change _ ≤ C * ((M ^ 4 : ℕ) : ℝ) * (M : ℝ) ^ (-delta) + 2 * (M : ℝ) ^ 2 at hb
  rw [he] at hb
  calc
    _ ≤ C * (M : ℝ) ^ (4 - delta) + 2 * (M : ℝ) ^ 2 := hb
    _ ≤ (C + 2) * (M : ℝ) ^ (4 - delta) := by nlinarith only [hpow]


end
end RiemannGaussian.VinogradovDirichletSaving
