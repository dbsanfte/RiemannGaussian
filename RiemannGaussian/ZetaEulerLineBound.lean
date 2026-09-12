/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerUniformRemainder
import RiemannGaussian.ZetaNearOneLineBudget
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Direct near-one growth without the eta denominator

The original ordinary Euler prefix is exactly the existing dyadic
Dirichlet prefix. Its uniform remainder and true pole endpoint give the
balanced-line height exponent with a constant independent of the strip
width. All block-order choices are discharged by the existing recursion.
-/

namespace RiemannGaussian.ZetaEulerLineBound
noncomputable section
open Complex ZetaEulerCell ZetaDyadicTruncation ZetaNearOneLineBudget
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison
open scoped ComplexConjugate

/-- The ordinary Euler prefix is exactly the original positive-index
Dirichlet prefix, including its first term and precise upper endpoint. -/
theorem partialSum_eq_positivePrefix (N : ℕ) (s : ℂ) :
    partialSum N s = DirichletDyadicBlocks.positivePrefix s (N + 1) := by
  rw [DirichletDyadicBlocks.positivePrefix, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro n _
  rw [DirichletDyadicBlocks.feature_eq_cpow s (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- The complete canonical dyadic endpoint strictly exceeds the
complex argument norm, before the cutoff condition is weakened. -/
theorem norm_lt_endpoint (s : ℂ) : ‖s‖ < ((2 ^ (depth s + 1) : ℕ) : ℝ) := by
  have hc := Nat.le_ceil ‖s‖
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (⌈‖s‖⌉₊ + 1)
  have hr : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) < ((2 ^ (depth s + 1) : ℕ) : ℝ) := by
    exact_mod_cast hp
  push_cast at hr ⊢
  linarith

/-- The same original endpoint is bounded by five times the ordinate
throughout the positive unit strip above height two. -/
theorem endpoint_le_five_height {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) : ((2 ^ (depth s + 1) : ℕ) : ℝ) ≤ 5 * s.im := by
  have h := depth_length_lt s
  have hn := norm_le_height_add_one hσ hσ1 (by linarith)
  rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- Direct Euler reconstruction bounds actual zeta by one ordinary
dyadic prefix and a uniform constant, with no eta division. -/
theorem norm_le_prefix_add_six {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ ‖DirichletDyadicBlocks.positivePrefix s (2 ^ (depth s + 1))‖ + 6 := by
  let M : ℕ := 2 ^ (depth s + 1)
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMN : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsne : s ≠ 1 := by intro h; subst s; norm_num at ht
  have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast hMN
  have hheight : |s.im| ≤ ((M - 1 : ℕ) : ℝ) + 1 := by
    rw [hcast]
    exact (Complex.abs_im_le_norm s).trans (norm_lt_endpoint s).le
  have h := ZetaEulerUniformRemainder.norm_zeta_sub_partialSum_le hσ hσ1 hsne (M - 1) hheight
  rw [partialSum_eq_positivePrefix, hMN] at h
  rw [hcast] at h
  have hp : (M : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM) (by linarith)
  have htpos : 0 < s.im := by linarith
  have hden : s.im ≤ ‖s - 1‖ := by
    simpa only [sub_im, one_im, sub_zero] using Complex.im_le_norm (s - 1)
  have hnum : (M : ℝ) ^ (1 - s.re) ≤ M := by
    calc
      _ ≤ (M : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith)
      _ = _ := Real.rpow_one _
  have hend : (M : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 5 := by
    calc
      _ ≤ (M : ℝ) / s.im :=
        (div_le_div_of_nonneg_left (by positivity) htpos hden).trans
          (div_le_div_of_nonneg_right hnum htpos.le)
      _ ≤ 5 := (div_le_iff₀ htpos).mpr (endpoint_le_five_height hσ.le hσ1 ht)
  have htri := norm_add_le (riemannZeta s - DirichletDyadicBlocks.positivePrefix s M)
    (DirichletDyadicBlocks.positivePrefix s M)
  simp only [sub_add_cancel] at htri
  dsimp [M] at h htri
  linarith

/-- Every balanced near-one line has an actual growth bound with a
coefficient independent of the displacement from one. -/
theorem bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k) (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ 8192 * s.im ^ alpha k * Real.log s.im := by
  have hσ : 0 < s.re := by rw [hline]; linarith [half_le_line k hk]
  have hσ1 : s.re ≤ 1 := by rw [hline]; exact (line_lt_one k).le
  obtain ⟨orders, _, hb⟩ := exists_prefix_budget_bound k hk hline ht
  have hprefix := (ZetaDyadicPowerBound.prefix_bound hσ.le (by linarith) orders (depth s + 1)).trans hb
  have hc := canonical_count_le hσ.le hσ1 ht
  have hp : 1 ≤ s.im ^ alpha k := Real.one_le_rpow (by linarith) (alpha_pos k).le
  have hlog : (1 / 2 : ℝ) ≤ Real.log s.im := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
    linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 512 * s.im ^ alpha k)
  have hprod : (1 / 2 : ℝ) ≤ s.im ^ alpha k * Real.log s.im := by nlinarith
  have h := norm_le_prefix_add_six hσ hσ1 ht
  nlinarith

/-- Conjugation preserves the direct near-one growth bound at both
signs of the ordinate, without introducing an eta denominator. -/
theorem bound_abs (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ alpha k * Real.log |s.im| := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound k hk hline ht
  · have h := bound k hk (s := conj s) (by simpa using hline)
      (by simpa [abs_of_neg (lt_of_not_ge hs)] using ht)
    simpa [abs_of_neg (lt_of_not_ge hs)] using h

end
end RiemannGaussian.ZetaEulerLineBound
