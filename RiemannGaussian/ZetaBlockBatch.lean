/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockShift
import RiemannGaussian.ZetaBlockMoments

/-!
# Quantitative batch evaluation from reusable block moments

Each center needs only thirty-one geometric moments per block. Thirteen
amplitudes formed from them serve every imaginary shift of norm at most
64. Every original term, its phase, and the analytic correction are kept.
The full zeta approximation retains the absolute error budget `1e-9`.
-/

namespace RiemannGaussian.ZetaBlockBatch
noncomputable section
open Complex Real Set
open scoped BigOperators

/-- The main carrier separates the center and the outer shift phase. -/
def carrier (s d : ℂ) (v k : ℝ) : ℂ :=
  ZetaBlockApproximation.geometric s v k * (v : ℂ) ^ (-d)

/-- The complete shifted term factors without discarding its phase. -/
theorem power_eq_carrier_models (s d : ℂ) {v k : ℝ} (hv : 0 < v) (hk : 0 ≤ k) :
    ((v + k : ℝ) : ℂ) ^ (-(s + d)) = carrier s d v k *
      (ZetaBlockTaylor.model s (300 * k / v) * ZetaBlockShift.model d (300 * k / v)) := by
  have hvk : 0 < v + k := by linarith
  have ht : 0 < 1 + k / v := by positivity
  have he : v + k = v * (1 + k / v) := by field_simp
  have hl : Real.log (v + k) = Real.log v + Real.log (1 + k / v) := by
    rw [he, Real.log_mul hv.ne' ht.ne']
  rw [carrier, ZetaBlockApproximation.geometric, ZetaBlockTaylor.model,
    ZetaBlockShift.model, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hvk.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hv.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hv.ne'),
    ← Complex.ofReal_log hvk.le, ← Complex.ofReal_log hv.le]
  simp only [← Complex.exp_add]
  congr 1
  rw [ZetaBlockTaylor.correction, show 300 * k / v / 300 = k / v by ring, hl]
  push_cast
  ring

theorem norm_main_phase {d : ℂ} (hd : d.re = 0) {v : ℝ} (hv : 0 < v) :
    ‖(v : ℂ) ^ (-d)‖ = 1 := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hv.ne'), ← Complex.ofReal_log hv.le,
    Complex.norm_exp]
  simp [mul_re, hd]

theorem norm_carrier_le {s d : ℂ} (hs : 0 ≤ s.re) (hd : d.re = 0) {v k : ℝ}
    (hv : 1 ≤ v) (hk : 0 ≤ k) : ‖carrier s d v k‖ ≤ 1 := by
  rw [carrier, norm_mul, norm_main_phase hd (by linarith), mul_one]
  exact ZetaBlockApproximation.norm_geometric_le hs hv hk

/-- Uniform error of each literal shifted term. -/
theorem norm_term_error_le {s d : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64) {v k : ℝ}
    (hv : 1 ≤ v) (hk : 0 ≤ k) (hkv : 300 * k ≤ v) :
    ‖((v + k : ℝ) : ℂ) ^ (-(s + d)) - carrier s d v k *
      (ZetaBlockTaylor.polynomial s 18 (300 * k / v) *
        ZetaBlockShift.polynomial d 12 (300 * k / v))‖ ≤ 801 / 20000000000000000 := by
  have hv0 : 0 < v := by linarith
  have hx : 300 * k / v ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hv0).mpr hkv⟩
  rw [power_eq_carrier_models s d hv0 hk, ← mul_sub, norm_mul]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    (mul_le_mul (norm_carrier_le hs0 hd0 hv hk)
    (ZetaBlockShift.norm_product_error_le hs0 hs hd0 hd hx)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- A complete block using the center polynomial and the shift polynomial. -/
def block (s d : ℂ) (v K : ℕ) : ℂ :=
  ∑ k ∈ Finset.range K, carrier s d v k *
    (ZetaBlockTaylor.polynomial s 18 (300 * (k : ℝ) / v) *
      ZetaBlockShift.polynomial d 12 (300 * (k : ℝ) / v))

theorem norm_block_error_le {s d : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64) {v K : ℕ}
    (hv : 1 ≤ v) (hK : ∀ k < K, 300 * k ≤ v) :
    ‖(∑ k ∈ Finset.range K, (v + k : ℂ) ^ (-(s + d))) - block s d v K‖ ≤
      (K : ℝ) * (801 / 20000000000000000) := by
  rw [block, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range K, (801 / 20000000000000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_ofNat] using
        norm_term_error_le hs0 hs hd0 hd (v := (v : ℝ)) (k := (k : ℝ))
          (by exact_mod_cast hv) (Nat.cast_nonneg k)
          (by exact_mod_cast hK k (Finset.mem_range.mp hk))
    _ = _ := by simp

/-- Reusable block amplitudes depend on the center, but not the height shift. -/
def amplitude (s : ℂ) (v K j : ℕ) : ℂ :=
  (v : ℂ) ^ (-s) * ∑ i ∈ Finset.range 19, ZetaBlockTaylor.coefficient s i *
    ZetaBlockMoments.moment (Complex.exp (-s / v)) (300 / v) K (i + j)

/-- A polynomial-weighted moment equals its complete finite geometric expansion. -/
theorem weighted_sum_eq_moments (s q h : ℂ) (K j : ℕ) :
    (∑ k ∈ Finset.range K, q ^ k * ZetaBlockTaylor.polynomial s 18 ((k : ℂ) * h) *
      ((k : ℂ) * h) ^ j) =
        ∑ i ∈ Finset.range 19, ZetaBlockTaylor.coefficient s i *
          ZetaBlockMoments.moment q h K (i + j) := by
  unfold ZetaBlockTaylor.polynomial ZetaBlockMoments.moment
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- Thirty-one center moments determine all thirteen shift amplitudes. -/
theorem amplitude_eq_sum (s : ℂ) (v K j : ℕ) :
    amplitude s v K j = (v : ℂ) ^ (-s) * ∑ k ∈ Finset.range K,
      (Complex.exp (-s / v)) ^ k * ZetaBlockTaylor.polynomial s 18 ((k : ℂ) * (300 / v)) *
        ((k : ℂ) * (300 / v)) ^ j := by
  unfold amplitude ZetaBlockMoments.moment ZetaBlockTaylor.polynomial
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- Exact batch formula: only the shift coefficients and outer phase change. -/
theorem block_eq_amplitudes (s d : ℂ) (v K : ℕ) :
    block s d v K = (v : ℂ) ^ (-d) * ∑ j ∈ Finset.range 13,
      ZetaBlockShift.coefficient d j * amplitude s v K j := by
  simp only [amplitude_eq_sum, Finset.mul_sum, block, carrier,
    ZetaBlockApproximation.geometric, ZetaBlockShift.polynomial,
    Complex.ofReal_natCast]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have hq : Complex.exp (-s * (k : ℂ) / v) = (Complex.exp (-s / v)) ^ k := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hx : (300 : ℂ) * k / v = (k : ℂ) * (300 / v) := by
    ring
  rw [hq, hx]
  ring

/-- Literal consecutive blocks with the center held fixed. -/
def partition (s d : ℂ) : ℕ → List ℕ → ℂ
  | _, [] => 0
  | v, K :: Ks => block s d v K + partition s d (v + K) Ks

theorem norm_partition_error_le {s d : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64) {v : ℕ} (hv : 1 ≤ v) (Ks : List ℕ)
    (hKs : ZetaBlockApproximation.Valid v Ks) :
    ‖(∑ k ∈ Finset.range Ks.sum, (v + k : ℂ) ^ (-(s + d))) - partition s d v Ks‖ ≤
      (Ks.sum : ℝ) * (801 / 20000000000000000) := by
  induction Ks generalizing v with
  | nil => simp [partition]
  | cons K Ks ih =>
    rw [List.sum_cons, Finset.sum_range_add, partition]
    have hr := ih (show 1 ≤ v + K by omega) hKs.2
    have hb := norm_block_error_le hs0 hs hd0 hd hv hKs.1
    have he : (∑ k ∈ Finset.range K, (v + k : ℂ) ^ (-(s + d))) +
        (∑ k ∈ Finset.range Ks.sum, (v + (K + k : ℕ) : ℂ) ^ (-(s + d))) -
        (block s d v K + partition s d (v + K) Ks) =
        ((∑ k ∈ Finset.range K, (v + k : ℂ) ^ (-(s + d))) - block s d v K) +
        ((∑ k ∈ Finset.range Ks.sum, ((v + K : ℕ) + k : ℂ) ^ (-(s + d))) -
          partition s d (v + K) Ks) := by
      push_cast
      simp only [add_assoc]
      ring
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hb hr).trans_eq (by push_cast; ring))

/-- Early terms remain exact at the shifted height. -/
def prefixValue (s d : ℂ) (H : ℕ) (Ks : List ℕ) : ℂ :=
  ZetaEulerCell.partialSum H (s + d) + partition s d (H + 1) Ks

theorem norm_prefix_error_le {s d : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64) (H : ℕ) (Ks : List ℕ)
    (hKs : ZetaBlockApproximation.Valid (H + 1) Ks) :
    ‖ZetaEulerCell.partialSum (H + Ks.sum) (s + d) - prefixValue s d H Ks‖ ≤
      (Ks.sum : ℝ) * (801 / 20000000000000000) := by
  have hp := norm_partition_error_le hs0 hs hd0 hd (show 1 ≤ H + 1 by omega) Ks hKs
  unfold prefixValue ZetaEulerCell.partialSum
  rw [Finset.sum_range_add, add_sub_add_left_eq_sub]
  convert hp using 1
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  congr 1
  ring

/-- The original Euler--Maclaurin correction is evaluated at the shifted point. -/
def approximation (s d : ℂ) (H : ℕ) (Ks : List ℕ) : ℂ :=
  prefixValue s d H Ks +
    (ZetaEulerMaclaurin.approximation (H + Ks.sum) (s + d) 18 -
      ZetaEulerCell.partialSum (H + Ks.sum) (s + d))

/-- A radius-64 batch keeps the original full `1e-9` zeta error allowance. -/
theorem zeta_error_lt {s d : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (hnorm : ‖s‖ ≤ 22500) (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64)
    (ht : |(s + d).im| ≤ 22000) (hsne : s + d ≠ 1) (H : ℕ) (Ks : List ℕ)
    (hKs : ZetaBlockApproximation.Valid (H + 1) Ks) (hN : H + Ks.sum = 22020) :
    ‖riemannZeta (s + d) - approximation s d H Ks‖ < 1 / 1000000000 := by
  have hr : (s + d).re = s.re := by simp [hd0]
  have hnorm' : ‖s + d‖ ≤ 22001 := by
    have hre : (s + d).re ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by rw [hr]; nlinarith
    have hi : (s + d).im ^ 2 ≤ (22000 : ℝ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (s + d).im) (by norm_num : (0 : ℝ) ≤ 22000)).mpr ht
    have hn := Complex.sq_norm (s + d)
    rw [Complex.normSq_apply] at hn
    nlinarith [norm_nonneg (s + d)]
  have hp := norm_prefix_error_le (by linarith : 0 ≤ s.re) hnorm hd0 hd H Ks hKs
  have he := ZetaEulerMaclaurinBudget.uniform_error_of_norm (by simpa only [hr] using hs)
    hsne 22020 le_rfl (by norm_num; linarith)
  have hsize : (Ks.sum : ℝ) ≤ 22020 := by exact_mod_cast (by omega : Ks.sum ≤ 22020)
  have hid : riemannZeta (s + d) - approximation s d H Ks =
      (riemannZeta (s + d) - ZetaEulerMaclaurin.approximation 22020 (s + d) 18) +
      (ZetaEulerCell.partialSum (H + Ks.sum) (s + d) - prefixValue s d H Ks) := by
    unfold approximation
    rw [hN]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans_lt
  linarith

end
end RiemannGaussian.ZetaBlockBatch
