/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveBranchRate

/-! # Whole actual recursion-call envelope at the requested main exponent
Every literal grid point, acquired mode and64 child groups is included. The
finite inventory is bounded uniformly in fuel; this counts calls, not the
primitive work of those calls or their leaf table contractions.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveTreeRate
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallInventory
open SemiprimeD1RecursiveCountEnvelope SemiprimeD1RecursiveBranchRate SemiprimeD1Schedule

/-- Grid and group factors contribute only a fixed quadratic logarithmic exponent. -/
theorem grid_power_le (s : ℕ) :
    (gridFactor s)^(SemiprimeD1PackingReady.logarithm s+1) ≤
      Real.exp (((4*SemiprimeD1PackingReady.logarithm s+7)*
        (SemiprimeD1PackingReady.logarithm s+1):ℕ):ℝ) := by
  have htwo : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2) htwo
    ((4*SemiprimeD1PackingReady.logarithm s+7)*(SemiprimeD1PackingReady.logarithm s+1))
  dsimp only [gridFactor]
  rw [←pow_mul]
  convert h using 1
  rw [←Real.exp_nat_mul]
  simp only [mul_one]

/-- The exact floor in the original root taper costs only the fixed512 factor. -/
theorem mode_total_le (s : ℕ)
    (hl : epsilonDenominator ≤ SemiprimeD1PackingReady.logarithm s) :
    2*modeFactor s ≤ 98304*(s:ℝ)/Real.sqrt (SemiprimeD1PackingReady.logarithm s:ℕ) := by
  have hroot := SemiprimeD1PathRate.sqrt_root_bound (SemiprimeD1PackingReady.logarithm s) hl
  have hb : 0 < SemiprimeD1PackingReady.logarithm s/epsilonDenominator :=
    Nat.div_pos hl (by norm_num [epsilonDenominator])
  have hlpos : 0 < SemiprimeD1PackingReady.logarithm s := by
    have hh : 0 < epsilonDenominator := by norm_num [epsilonDenominator]
    omega
  have hs1 : 0 < Real.sqrt (SemiprimeD1PackingReady.logarithm s/epsilonDenominator:ℕ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hb)
  have hs2 : 0 < Real.sqrt (SemiprimeD1PackingReady.logarithm s:ℕ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hlpos)
  dsimp only [modeFactor]
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hs1 hs2).mpr
  calc
    _ = (192*(s:ℝ))*Real.sqrt (SemiprimeD1PackingReady.logarithm s:ℕ) := by ring
    _ ≤ (192*(s:ℝ))*(512*Real.sqrt (SemiprimeD1PackingReady.logarithm s/epsilonDenominator:ℕ)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by ring

/-- Explicit whole-tree envelope for the ACTUAL closed controller inventory,
uniformly over all supplied fuels and every original root in the input caps.
No branching count, child solution, inherited precision or packing oracle occurs. -/
theorem eventually_count_le : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ (root : Call) (fuel : ℕ), root.depth=0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      SemiprimeD1TensorNetworkRecursion.DegreeBound root.net (SemiprimeD1PackingReady.degreeCap s) →
      (count s fuel root:ℝ) ≤ (SemiprimeD1PackingReady.logarithm s+2:ℕ)*
        Real.exp (98304*(s:ℝ)/Real.sqrt (SemiprimeD1PackingReady.logarithm s:ℕ)+
          (((4*SemiprimeD1PackingReady.logarithm s+7)*
            (SemiprimeD1PackingReady.logarithm s+1):ℕ):ℝ)) := by
  have hlim : Filter.Tendsto SemiprimeD1PackingReady.logarithm Filter.atTop Filter.atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (Filter.tendsto_add_atTop_nat 2)
  filter_upwards [eventually_reach_branch,hlim.eventually (Filter.eventually_ge_atTop epsilonDenominator)] with s hbranch hl
  intro root fuel hdepth hM hp hpos hw hg hd
  let lam := SemiprimeD1PackingReady.logarithm s
  let k := min fuel (lam+1)
  have hk : k ≤ lam+1 := Nat.min_le_right _ _
  have hG : 1 ≤ gridFactor s := by dsimp only [gridFactor];exact one_le_pow₀ (by norm_num)
  have hA : 0 ≤ modeFactor s := by dsimp only [modeFactor];positivity
  have h := count_le s root (gridFactor s) (modeFactor s) hG hA
    (fun call hr => hbranch root call hdepth hM hp hpos hw hg hd hr) k root Reach.root
  rw [hdepth] at h
  have htail : modeFactor s*tail 0 k ≤ 2*modeFactor s := by
    have hh := mul_le_mul_of_nonneg_left (tail_le 0 k) hA
    norm_num only [pow_zero,mul_one] at hh
    exact hh.trans (le_of_eq (mul_comm _ _))
  have hcoef : (k:ℝ)+1 ≤ (lam+2:ℕ) := by exact_mod_cast (by omega : k+1 ≤ lam+2)
  have hgrid : (gridFactor s)^k ≤ Real.exp (((4*lam+7)*(lam+1):ℕ):ℝ) :=
    (pow_le_pow_right₀ hG hk).trans (grid_power_le s)
  have hmode := mode_total_le s hl
  rw [count_fuel_cap s fuel root]
  calc
    _ ≤ _ := h
    _ ≤ (lam+2:ℕ)*
        (Real.exp (((4*lam+7)*(lam+1):ℕ):ℝ)*
          Real.exp (98304*(s:ℝ)/Real.sqrt (lam:ℕ))) := by
      have h1 := mul_le_mul hcoef hgrid (by positivity) (by positivity)
      have h2 := mul_le_mul h1 (Real.exp_le_exp.mpr (htail.trans hmode))
        (Real.exp_pos _).le (by positivity)
      convert h2 using 1
      ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring

end RiemannGaussian.SemiprimeD1RecursiveTreeRate
