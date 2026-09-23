/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockTaylor
import RiemannGaussian.ZetaEulerMaclaurinEnclosure

/-!
# Quantitative replacement of literal Dirichlet blocks

Every index and its complex phase are retained. Blocks share the degree
eighteen polynomial, with a proved absolute error, and the original
Euler--Maclaurin correction is kept in full.
-/

namespace RiemannGaussian.ZetaBlockApproximation
noncomputable section
open Complex Real Set ZetaBlockTaylor
open scoped BigOperators

/-- The geometric carrier of a single Dirichlet term. -/
def geometric (s : ℂ) (v k : ℝ) : ℂ :=
  (v : ℂ) ^ (-s) * Complex.exp (-s * (k : ℂ) / v)

/-- Exact factorization of the original term into its geometric part and
the logarithmic correction, including the full complex phase. -/
theorem power_eq_geometric_model (s : ℂ) {v k : ℝ} (hv : 0 < v) (hk : 0 ≤ k) :
    ((v + k : ℝ) : ℂ) ^ (-s) = geometric s v k * model s (300 * k / v) := by
  have hvk : 0 < v + k := by linarith
  have ht : 0 < 1 + k / v := by positivity
  have he : v + k = v * (1 + k / v) := by field_simp
  have hl : Real.log (v + k) = Real.log v + Real.log (1 + k / v) := by
    rw [he, Real.log_mul hv.ne' ht.ne']
  rw [geometric, model, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hvk.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hv.ne'),
    ← Complex.ofReal_log hvk.le, ← Complex.ofReal_log hv.le,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [correction, show 300 * k / v / 300 = k / v by ring, hl]
  push_cast
  ring

/-- The geometric carrier never amplifies the block error in the right half-plane. -/
theorem norm_geometric_le {s : ℂ} (hs : 0 ≤ s.re) {v k : ℝ}
    (hv : 1 ≤ v) (hk : 0 ≤ k) : ‖geometric s v k‖ ≤ 1 := by
  have hv0 : 0 < v := by linarith
  rw [geometric, norm_mul]
  have hp : ‖(v : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hv0.ne'),
      ← Complex.ofReal_log hv0.le, Complex.norm_exp, Real.exp_le_one_iff]
    simp only [mul_re, ofReal_re, ofReal_im, neg_re, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg hv) (neg_nonpos.mpr hs)
  have he : ‖Complex.exp (-s * (k : ℂ) / v)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [div_ofReal_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hs) hk) hv0.le
  simpa only [one_mul] using mul_le_mul hp he (norm_nonneg _) zero_le_one

/-- Uniform error for each original term in a valid block. -/
theorem norm_term_error_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    {v k : ℝ} (hv : 1 ≤ v) (hk : 0 ≤ k) (hkv : 300 * k ≤ v) :
    ‖((v + k : ℝ) : ℂ) ^ (-s) -
      geometric s v k * polynomial s 18 ((300 * k / v : ℝ) : ℂ)‖ ≤ 1 / 25000000000000 := by
  have hv0 : 0 < v := by linarith
  have hx : 300 * k / v ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hv0).mpr hkv⟩
  rw [power_eq_geometric_model s hv0 hk, ← mul_sub, norm_mul]
  exact (mul_le_mul (norm_geometric_le hs0 hv hk) (norm_model_sub_eighteen_le hs0 hs hx)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- The accelerated finite block, with no mask or term omitted. -/
def block (s : ℂ) (v K : ℕ) : ℂ :=
  ∑ k ∈ Finset.range K, geometric s v k * polynomial s 18 (300 * (k : ℝ) / v)

/-- A block of `K` terms costs at most `4e-14 K` in absolute error. -/
theorem norm_block_error_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    {v K : ℕ} (hv : 1 ≤ v) (hK : ∀ k < K, 300 * k ≤ v) :
    ‖(∑ k ∈ Finset.range K, (v + k : ℂ) ^ (-s)) - block s v K‖ ≤
      (K : ℝ) / 25000000000000 := by
  rw [block, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range K, (1 / 25000000000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_ofNat] using
        norm_term_error_le hs0 hs (v := (v : ℝ)) (k := (k : ℝ))
          (by exact_mod_cast hv) (Nat.cast_nonneg k) (by exact_mod_cast hK k (Finset.mem_range.mp hk))
    _ = _ := by simp; ring

/-- A literal consecutive partition, specified by its finite list of widths. -/
def partition (s : ℂ) : ℕ → List ℕ → ℂ
  | _, [] => 0
  | v, K :: Ks => block s v K + partition s (v + K) Ks

/-- Every actual block lies within the common normalized Taylor interval. -/
def Valid : ℕ → List ℕ → Prop
  | _, [] => True
  | v, K :: Ks => (∀ k < K, 300 * k ≤ v) ∧ Valid (v + K) Ks

theorem norm_partition_error_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    {v : ℕ} (hv : 1 ≤ v) (Ks : List ℕ) (hKs : Valid v Ks) :
    ‖(∑ k ∈ Finset.range Ks.sum, (v + k : ℂ) ^ (-s)) - partition s v Ks‖ ≤
      (Ks.sum : ℝ) / 25000000000000 := by
  induction Ks generalizing v with
  | nil => simp [partition]
  | cons K Ks ih =>
    rw [List.sum_cons, Finset.sum_range_add, partition]
    have hr := ih (show 1 ≤ v + K by omega) hKs.2
    have hb := norm_block_error_le hs0 hs hv hKs.1
    have he : (∑ k ∈ Finset.range K, (v + k : ℂ) ^ (-s)) +
        (∑ k ∈ Finset.range Ks.sum, (v + (K + k : ℕ) : ℂ) ^ (-s)) -
        (block s v K + partition s (v + K) Ks) =
        ((∑ k ∈ Finset.range K, (v + k : ℂ) ^ (-s)) - block s v K) +
        ((∑ k ∈ Finset.range Ks.sum, ((v + K : ℕ) + k : ℂ) ^ (-s)) -
          partition s (v + K) Ks) := by
      push_cast
      simp only [add_assoc]
      ring
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hb hr).trans_eq (by push_cast; ring))

/-- The complete prefix approximation keeps every early term exactly. -/
def prefixValue (s : ℂ) (H : ℕ) (Ks : List ℕ) : ℂ :=
  ZetaEulerCell.partialSum H s + partition s (H + 1) Ks

theorem norm_prefix_error_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (H : ℕ) (Ks : List ℕ) (hKs : Valid (H + 1) Ks) :
    ‖ZetaEulerCell.partialSum (H + Ks.sum) s - prefixValue s H Ks‖ ≤
      (Ks.sum : ℝ) / 25000000000000 := by
  have hp := norm_partition_error_le hs0 hs (show 1 ≤ H + 1 by omega) Ks hKs
  unfold prefixValue ZetaEulerCell.partialSum
  rw [Finset.sum_range_add, add_sub_add_left_eq_sub]
  convert hp using 1
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  congr 1
  ring

/-- Replace only the prefix; keep the complete original analytic correction. -/
def approximation (s : ℂ) (H : ℕ) (Ks : List ℕ) : ℂ :=
  prefixValue s H Ks +
    (ZetaEulerMaclaurin.approximation (H + Ks.sum) s 18 -
      ZetaEulerCell.partialSum (H + Ks.sum) s)

/-- The block accelerator and the original analytic remainder together cost
less than `1e-9` through the entire intended evaluation rectangle. -/
theorem zeta_error_lt {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (ht : |s.im| ≤ 22000) (hsne : s ≠ 1) (H : ℕ) (Ks : List ℕ)
    (hKs : Valid (H + 1) Ks) (hN : H + Ks.sum = 22020) :
    ‖riemannZeta s - approximation s H Ks‖ < 1 / 1000000000 := by
  have hnorm : ‖s‖ ≤ 22001 := by
    have hr : s.re ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by nlinarith
    have hi : s.im ^ 2 ≤ (22000 : ℝ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg s.im) (by norm_num : (0 : ℝ) ≤ 22000)).mpr ht
    have hn := Complex.sq_norm s
    rw [Complex.normSq_apply] at hn
    nlinarith [norm_nonneg s]
  have hp := norm_prefix_error_le (by linarith : 0 ≤ s.re)
    (hnorm.trans (by norm_num)) H Ks hKs
  have he := ZetaEulerMaclaurinBudget.uniform_error_of_norm hs hsne 22020 le_rfl
    (by norm_num; linarith)
  have hsize : (Ks.sum : ℝ) ≤ 22020 := by exact_mod_cast (by omega : Ks.sum ≤ 22020)
  have hid : riemannZeta s - approximation s H Ks =
      (riemannZeta s - ZetaEulerMaclaurin.approximation 22020 s 18) +
      (ZetaEulerCell.partialSum (H + Ks.sum) s - prefixValue s H Ks) := by
    unfold approximation
    rw [hN]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans_lt
  linarith

end
end RiemannGaussian.ZetaBlockApproximation
