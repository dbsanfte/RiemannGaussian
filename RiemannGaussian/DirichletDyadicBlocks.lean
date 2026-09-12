/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.UniformDirichletPowerBound
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation

/-!
# Exact Dirichlet blocks and the finite eta truncation

The original positive-index Dirichlet prefix is partitioned into complete
dyadic blocks. Its exact odd-even identity gives the actual finite eta
sum, including the final endpoint and its complex dyadic multiplier.
No norm or absolute value is used in these reconstruction identities.
-/

namespace RiemannGaussian.DirichletDyadicBlocks
noncomputable section
open scoped Classical

/-- The original Dirichlet prefix on the half-open positive interval. -/
def positivePrefix (s : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 M, zetaPrimeFeature s n

/-- One complete dyadic block, with its original complex terms. -/
def block (s : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (2 ^ j), zetaPrimeFeature s (2 ^ j + n)

/-- At a positive index the original feature is the genuine complex power. -/
theorem feature_eq_cpow (s : ℂ) {n : ℕ} (hn : 0 < n) :
    zetaPrimeFeature s n = (n : ℂ) ^ (-s) := by
  rw [zetaPrimeFeature, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne'),
    ← Complex.natCast_log]
  congr 1
  ring

/-- Positive index dilation retains the complete complex phase factor. -/
theorem feature_mul (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    zetaPrimeFeature s (m * n) = zetaPrimeFeature s m * zetaPrimeFeature s n := by
  unfold zetaPrimeFeature
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne'),
    Complex.ofReal_add, mul_add, neg_add, Complex.exp_add]

/-- The radial factor retains its exact real power at positive indices. -/
theorem weight_eq_rpow (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    zetaPrimeExpWeight σ n = (n : ℝ) ^ (-σ) := by
  rw [zetaPrimeExpWeight, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

/-- Adding the final positive index retains its exact complex value. -/
theorem prefix_succ (s : ℂ) {M : ℕ} (hM : 1 ≤ M) :
    positivePrefix s (M + 1) = positivePrefix s M + zetaPrimeFeature s M :=
  Finset.sum_Ico_succ_top hM _

/-- A complete dyadic block is exactly its original half-open interval. -/
theorem block_eq_Ico (s : ℂ) (j : ℕ) :
    block s j = ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), zetaPrimeFeature s n := by
  rw [Finset.sum_Ico_eq_sum_range]
  have he : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
  rw [he]
  rfl

/-- Every dyadic prefix is the complete sum of its original dyadic blocks. -/
theorem prefix_pow_two (s : ℂ) (J : ℕ) :
    positivePrefix s (2 ^ J) = ∑ j ∈ Finset.range J, block s j := by
  induction J with
  | zero => simp [positivePrefix]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, block_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (one_le_pow₀ (by norm_num))
      (by rw [pow_succ]; omega)).symm

/-- Every eta pair is the signed pair of the original Dirichlet features. -/
theorem eta_pair_eq_features (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      zetaPrimeFeature s (2 * n + 1) - zetaPrimeFeature s (2 * n + 2) := by
  rw [feature_eq_cpow s (by omega), feature_eq_cpow s (by omega)]
  simp only [pairedEtaCoreSummand, Complex.ofReal_natCast]

/-- The full finite eta sum is the exact difference of two Dirichlet
prefixes with their original complex dyadic multiplier. -/
theorem eta_eq_prefix (s : ℂ) (N : ℕ) :
    pairedEtaCorePartialSum N s = positivePrefix s (2 * N + 1) -
      2 * zetaPrimeFeature s 2 * positivePrefix s (N + 1) := by
  induction N with
  | zero => simp [pairedEtaCorePartialSum, positivePrefix]
  | succ N ih =>
    have hη : pairedEtaCorePartialSum (N + 1) s =
        pairedEtaCorePartialSum N s + pairedEtaCoreSummand s N :=
      Finset.sum_range_succ _ _
    rw [hη, eta_pair_eq_features, ih]
    rw [show 2 * (N + 1) + 1 = (2 * N + 1 + 1) + 1 by omega]
    conv_rhs =>
      rw [prefix_succ s (M := 2 * N + 1 + 1) (by omega),
        prefix_succ s (M := 2 * N + 1) (by omega),
        prefix_succ s (M := N + 1) (by omega)]
    have hmul := feature_mul s (m := 2) (n := N + 1) (by norm_num) (by omega)
    rw [show 2 * (N + 1) = 2 * N + 2 by omega] at hmul
    rw [show 2 * N + 1 + 1 = 2 * N + 2 by omega]
    rw [hmul]
    ring

/-- A dyadic eta truncation retains every complete block, its full
complex multiplier, and the final negative endpoint. -/
theorem eta_pow_two_eq_blocks (s : ℂ) (J : ℕ) :
    pairedEtaCorePartialSum (2 ^ J) s =
      (∑ j ∈ Finset.range (J + 1), block s j) -
        2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
          zetaPrimeFeature s (2 ^ (J + 1)) := by
  have hN : 1 ≤ (2 : ℕ) ^ J := one_le_pow₀ (by norm_num)
  have htwo : 2 * (2 : ℕ) ^ J = 2 ^ (J + 1) := by rw [pow_succ]; ring
  have hmul := feature_mul s (m := 2) (n := 2 ^ J) (by norm_num) (by positivity)
  rw [htwo] at hmul
  rw [eta_eq_prefix, htwo,
    prefix_succ s (M := 2 ^ (J + 1)) (one_le_pow₀ (by norm_num)),
    prefix_succ s hN,
    prefix_pow_two, prefix_pow_two, hmul]
  ring

end
end RiemannGaussian.DirichletDyadicBlocks
