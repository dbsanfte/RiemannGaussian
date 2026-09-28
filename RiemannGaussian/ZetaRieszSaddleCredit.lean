/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralReserve
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Keeping the square-root factor in the actual joint credit

The previous factorial bound lost a square-root factor at the literal
saddle. Stirling monotonicity restores it without changing any arithmetic
population, phase cell, allocation or signed rest. The resulting bound is
spent in both whole-sum comparisons.
-/

namespace RiemannGaussian.ZetaRieszSaddleCredit
noncomputable section
open Filter Topology

/-- A global factorial upper bound follows from monotonicity of the
Stirling sequence, without an unevaluated asymptotic threshold. -/
theorem factorial_upper {N : ℕ} (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ 3*Real.sqrt N*((N : ℝ)/Real.exp 1)^N := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hs := Stirling.stirlingSeq'_antitone (show 0 ≤ k by omega)
  change Stirling.stirlingSeq (k+1) ≤ Stirling.stirlingSeq 1 at hs
  rw [Stirling.stirlingSeq_one,Stirling.stirlingSeq] at hs
  have hden : 0 < Real.sqrt (2*(k+1 : ℕ)) * (((k+1 : ℕ) : ℝ)/Real.exp 1)^(k+1) := by
    positivity
  have h := (div_le_iff₀ hden).mp hs
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hroot : Real.sqrt (2*(k+1 : ℕ)) = Real.sqrt 2*Real.sqrt (k+1 : ℕ) := by
    push_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hroot] at h
  have htwo : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h' : (Real.exp 1/Real.sqrt 2)*
      (Real.sqrt 2*Real.sqrt (k+1 : ℕ)*(((k+1 : ℕ) : ℝ)/Real.exp 1)^(k+1)) =
      Real.exp 1*Real.sqrt (k+1 : ℕ)*(((k+1 : ℕ) : ℝ)/Real.exp 1)^(k+1) := by
    field_simp
  rw [h'] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _)) (by positivity))

/-- The same bounded displacement from the exact factorial saddle now
has a square-root, rather than linear, denominator. -/
theorem saddle_radial_lower {N : ℕ} (hN : 1 ≤ N) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+1) :
    Real.exp (-1)*(2 : ℝ)^N/(3*Real.sqrt N) ≤
      Real.exp (-v/2)*v^N/N.factorial := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := factorial_upper hN
  have hex : (Real.exp 1)^N = Real.exp (N : ℝ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hpow : (Real.exp (-(N : ℝ))*(2*(N : ℝ))^N)*
      (3*Real.sqrt N) = (2 : ℝ)^N*(3*Real.sqrt N*((N : ℝ)/Real.exp 1)^N) := by
    rw [div_pow,hex,Real.exp_neg,mul_pow]
    ring
  have hbase : (2 : ℝ)^N/(3*Real.sqrt N) ≤
      Real.exp (-(N : ℝ))*(2*N)^N/N.factorial := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [hpow]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have he : Real.exp (-1)*Real.exp (-(N : ℝ)) ≤ Real.exp (-v/2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hvu])
  have hp : (2*(N : ℝ))^N ≤ v^N := pow_le_pow_left₀ (by positivity) hv N
  calc
    _ = Real.exp (-1)*((2 : ℝ)^N/(3*Real.sqrt N)) := by ring
    _ ≤ Real.exp (-1)*(Real.exp (-(N : ℝ))*(2*N)^N/N.factorial) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
    _ = (Real.exp (-1)*Real.exp (-(N : ℝ)))*(2*N)^N/N.factorial := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul he hp (by positivity) (Real.exp_nonneg _)) (by positivity)

/-- Recovering the missing square-root factor strengthens the existing
source credit; no new carrier or changed arithmetic support is introduced. -/
theorem sourceCredit_le_scaled_margin {u y : ℝ} (hu : 0 ≤ u) (hy : y ≠ 0)
    {N m : ℕ} (hN : 1 ≤ N) (hm : 0 < m) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+1) :
    2*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N ≤
      u^(N+1)*((m : ℝ)/1000*(Real.exp (-v/2)*v^N/N.factorial)*
        (Real.pi/(4*m*|y|))) := by
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : Real.sqrt ((N : ℝ)+1)*Real.sqrt N ≤ (N : ℝ)+1 := by
    calc
      _ ≤ Real.sqrt ((N : ℝ)+1)*Real.sqrt ((N : ℝ)+1) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (by positivity)
  have hcompare : 2*Real.sqrt ((N : ℝ)+1)*
      (Real.exp (-1)*(2 : ℝ)^N/(6*((N : ℝ)+1))) ≤
      Real.exp (-1)*(2 : ℝ)^N/(3*Real.sqrt N) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 6*Real.exp (-1)*(2 : ℝ)^N by positivity)
    nlinarith only [h]
  have hs := mul_le_mul_of_nonneg_left
    (hcompare.trans (saddle_radial_lower hN hv hvu))
    (show 0 ≤ u^(N+1)*(m : ℝ)*(Real.pi/(4*m*|y|))/1000 by positivity)
  convert hs using 1 <;>
    (try simp only [ZetaRieszCentralReserve.sourceCredit]) <;>
    (try rw [pow_succ,mul_pow]) <;> (try field_simp) <;> first | rfl | ring

end
end RiemannGaussian.ZetaRieszSaddleCredit
