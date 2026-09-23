/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowDirichlet
import RiemannGaussian.DirichletDyadicBlocks

/-!
# Original dyadic Dirichlet blocks at the fourth-root scale

The complete fixed-coefficient Vinogradov estimate applies to an actual
block of arbitrary integer length X comparable to M^4. Every damping
weight is retained until the literal mass is bounded. Rounding the fourth
root costs a factor two and no unproved block-completion premise.
-/

namespace RiemannGaussian.VinogradovDyadic
noncomputable section
open scoped BigOperators
open DirichletDyadicBlocks

/-- The literal integer fourth root covers every original endpoint once it is at least six. -/
theorem fourth_root_window (X : ℕ) (hM : 6 ≤ Nat.nthRoot 4 X) :
    (Nat.nthRoot 4 X) ^ 4 ≤ X ∧ X ≤ 2 * (Nat.nthRoot 4 X) ^ 4 := by
  let M := Nat.nthRoot 4 X
  have hlow : M ^ 4 ≤ X := Nat.pow_nthRoot_le (Or.inl (by norm_num : (4 : ℕ) ≠ 0))
  have hhigh : X < (M + 1) ^ 4 := Nat.lt_pow_nthRoot_add_one (by norm_num : (4 : ℕ) ≠ 0) X
  have hamp : 6 * (M + 1) ≤ 7 * M := by change 6 ≤ M at hM; omega
  have hp := Nat.pow_le_pow_left hamp 4
  simp only [mul_pow] at hp
  norm_num only [Nat.reducePow] at hp
  refine ⟨hlow, hhigh.le.trans ?_⟩
  change (M + 1) ^ 4 ≤ 2 * M ^ 4
  omega

/-- The original root-scale saving loses only a factor two on the physical block scale. -/
theorem root_saving_le {M X delta : ℝ} (hM : 0 < M) (hX : 0 < X)
    (hupper : X ≤ 2 * M ^ 4) (hd : 0 ≤ delta) (hd4 : delta ≤ 4) :
    M ^ (-delta) ≤ 2 * X ^ (-delta / 4) := by
  have hbase : X / 2 ≤ M ^ 4 := by linarith
  have h := Real.rpow_le_rpow_of_nonpos (show 0 < X / 2 by positivity)
    hbase (show -delta / 4 ≤ 0 by linarith)
  have hleft : (M ^ 4) ^ (-delta / 4) = M ^ (-delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1
    push_cast
    ring
  have htwo : (2 : ℝ) ^ (delta / 4) ≤ 2 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show delta / 4 ≤ 1 by linarith)).trans_eq
    exact Real.rpow_one _
  rw [hleft, Real.div_rpow hX.le (by norm_num)] at h
  have hinv : (2 : ℝ) ^ (-delta / 4) = ((2 : ℝ) ^ (delta / 4))⁻¹ := by
    rw [show -delta / 4 = -(delta / 4) by ring, Real.rpow_neg (by norm_num)]
  rw [hinv, div_inv_eq_mul] at h
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hX.le (-delta / 4))])

/-- The complete original block on [X,2X) has an explicit physical-scale
saving, including all real damping and the full shift boundary. -/
theorem original_block_bound (k M X : ℕ) (hk : 12 ≤ k) (hrM : (7 * k + 1) * k ≤ M)
    (hlo : M ^ 4 ≤ X) (hhi : X ≤ 2 * M ^ 4) (s : ℂ) (hσ : 0 ≤ s.re)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ s.im) (hthi : s.im ≤ (M : ℝ) ^ (2 * k)) :
    ‖∑ n ∈ Finset.range X, zetaPrimeFeature s (X + n)‖ ≤
      6 * (X : ℝ) ^ (1 - s.re - 1 / (32768 * (k : ℝ) ^ 2)) +
        2 * (X : ℝ) ^ (1 / 2 - s.re) := by
  have hkM : k ≤ M := by nlinarith
  have hM : 1 ≤ M := by omega
  have hX : 1 ≤ X := (Nat.one_le_pow _ _ hM).trans hlo
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlow : (M : ℝ) ^ 4 ≤ X := by exact_mod_cast hlo
  have hhigh : (X : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by exact_mod_cast hhi
  have hb := VinogradovNarrowDirichlet.feature_block_bound k hk M hM hrM s hσ
    htlo hthi X hlow hhigh (X - 1) (by omega)
  rw [Nat.sub_add_cancel hX] at hb
  have hmass : (∑ n ∈ Finset.range X, zetaPrimeExpWeight s.re (X + n)) ≤
      (X : ℝ) * (X : ℝ) ^ (-s.re) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range X, (X : ℝ) ^ (-s.re) := by
        apply Finset.sum_le_sum
        intro n _
        rw [weight_eq_rpow s.re (by omega : 0 < X + n)]
        exact Real.rpow_le_rpow_of_nonpos hXr
          (by exact_mod_cast Nat.le_add_right X n) (neg_nonpos.mpr hσ)
      _ = _ := by simp
  let delta := 1 / (8192 * (k : ℝ) ^ 2)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hden : 1 ≤ 8192 * (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg ((k : ℝ) - 1), hkR]
  have hd : 0 ≤ delta := by dsimp only [delta]; positivity
  have hd4 : delta ≤ 4 := by
    have h := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
    dsimp only [delta]
    linarith
  have hsav := root_saving_le hMr hXr hhigh hd hd4
  have hroot : (M : ℝ) ^ 2 ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (sq_nonneg _) hXr.le).mpr
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by omega] using hlow
  rw [weight_eq_rpow s.re (by omega : 0 < X)] at hb
  have hbound := hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass (by positivity)) le_rfl)
  have hlead : 3 * (2 * (X : ℝ) ^ (-delta / 4)) * ((X : ℝ) * (X : ℝ) ^ (-s.re)) =
      6 * (X : ℝ) ^ (1 - s.re - delta / 4) := by
    rw [show 1 - s.re - delta / 4 = (-delta / 4) + 1 + (-s.re) by ring,
      Real.rpow_add hXr, Real.rpow_add hXr, Real.rpow_one]
    ring
  have htail : 2 * (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (-s.re) =
      2 * (X : ℝ) ^ (1 / 2 - s.re) := by
    rw [mul_assoc, ← Real.rpow_add hXr]
    rfl
  have hquarter : delta / 4 = 1 / (32768 * (k : ℝ) ^ 2) := by
    dsimp only [delta]
    ring
  calc
    _ ≤ 3 * (M : ℝ) ^ (-delta) * ((X : ℝ) * (X : ℝ) ^ (-s.re)) +
        2 * (M : ℝ) ^ 2 * (X : ℝ) ^ (-s.re) := hbound
    _ ≤ 3 * (2 * (X : ℝ) ^ (-delta / 4)) * ((X : ℝ) * (X : ℝ) ^ (-s.re)) +
        2 * (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (-s.re) := by gcongr
    _ = _ := by rw [hlead, htail, hquarter]

/-- Specializing the original endpoint to a dyadic integer keeps exactly
the block used by the existing zeta reconstruction. -/
theorem dyadic_block_bound (k M j : ℕ) (hk : 12 ≤ k) (hrM : (7 * k + 1) * k ≤ M)
    (hlo : M ^ 4 ≤ 2 ^ j) (hhi : 2 ^ j ≤ 2 * M ^ 4) (s : ℂ) (hσ : 0 ≤ s.re)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ s.im) (hthi : s.im ≤ (M : ℝ) ^ (2 * k)) :
    ‖block s j‖ ≤
      6 * ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re - 1 / (32768 * (k : ℝ) ^ 2)) +
        2 * ((2 ^ j : ℕ) : ℝ) ^ (1 / 2 - s.re) :=
  original_block_bound k M (2 ^ j) hk hrM hlo hhi s hσ htlo hthi

end
end RiemannGaussian.VinogradovDyadic
