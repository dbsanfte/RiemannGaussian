/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterEnumeration
import RiemannGaussian.SemiprimeCounterRate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Subexponential cost of the literal support traversal

The count is the actual inclusive weighted binomial menu, not an estimated
constant in an exponent. A vanishing support fraction suffices for every
positive target exponent. This theorem does not supply an algorithm clock.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeSupportRate
open Filter
open scoped Topology
open SemiprimeCounterEnumeration SemiprimeCounterRate

/-- Continuous entropy majorant, including the zero-support case. -/
def entropy (a : ℝ) : ℝ := a*Real.log 8-a*Real.log a

theorem entropy_zero : entropy 0=0 := by simp [entropy]

/-- The apparent logarithmic singularity disappears after multiplication by a. -/
theorem continuous_entropy : Continuous entropy :=
  (continuous_id.mul continuous_const).sub Real.continuous_mul_log

/-- Finite bound on the ACTUAL support callback count. No numerical aggregate
constant from a separate schedule calculation is assumed. -/
theorem weightedCount_bound (n q : ℕ) (hn : 0<n) (hq : q≤n) :
    (weightedCount n q : ℝ)≤((n : ℝ)+1)*Real.exp ((n : ℝ)*entropy ((q : ℝ)/n)) := by
  by_cases hq0 : q=0
  · subst q
    simp only [weightedCount_zero,Nat.cast_one,Nat.cast_zero,zero_div,entropy_zero,mul_zero,Real.exp_zero,mul_one]
    have hnonneg : (0 : ℝ)≤n := Nat.cast_nonneg n
    linarith
  · have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr hn
    have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr (by omega)
    have hqn : (q : ℝ)≤n := Nat.cast_le.mpr hq
    have hb := weightedCount_le_entropy n q hqR hqn (le_refl (q : ℝ))
    have he : (8*(n : ℝ)/(q : ℝ))^(q : ℝ)=Real.exp ((n : ℝ)*entropy ((q : ℝ)/n)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      have heq : 8*(n : ℝ)/(q : ℝ)=8/((q : ℝ)/n) := by field_simp
      rw [heq,Real.log_div (by norm_num : (8 : ℝ)≠0) (ne_of_gt (div_pos hqR hnR))]
      unfold entropy
      field_simp
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))

/-- A vanishing support fraction gives subexponential traversal for every
positive target exponent, including arbitrary occurrences of q=0. -/
theorem weightedCount_subexponential (q : ℕ → ℕ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, (weightedCount n (q n) : ℝ)≤Real.exp (ε*(n : ℝ)) := by
  have he : Tendsto (fun n : ℕ => entropy ((q n : ℝ)/(n : ℝ))) atTop (𝓝 0) := by
    simpa only [entropy_zero,Function.comp_def] using continuous_entropy.continuousAt.tendsto.comp hq
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := hnat.eventually
    (eventually_constant_polynomial_exp_rho_le 2 1 0 (ε/2) (by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hq.eventually (gt_mem_nhds (show (0 : ℝ)<1 by norm_num)),
    he.eventually (gt_mem_nhds (show (0 : ℝ)<ε/2 by positivity)),hp]
    with n hn hqn hen hpoly
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hqle : q n≤n := by
    have hh := (div_lt_iff₀ hnR).mp hqn
    exact Nat.cast_le.mp (by linarith : (q n : ℝ)≤n)
  have hb := weightedCount_bound n (q n) (by omega) hqle
  have hpoly' : 2*(n : ℝ)≤Real.exp (ε/2*(n : ℝ)) := by
    simpa only [Real.rpow_one,zero_mul,Real.exp_zero,mul_one] using hpoly
  calc
    (weightedCount n (q n) : ℝ)≤((n : ℝ)+1)*Real.exp ((n : ℝ)*entropy ((q n : ℝ)/n)) := hb
    _ ≤ (2*(n : ℝ))*Real.exp (ε/2*(n : ℝ)) := by
      apply mul_le_mul
      · have hnr : (1 : ℝ)≤n := Nat.one_le_cast.mpr hn
        linarith
      · apply Real.exp_le_exp.mpr
        nlinarith
      · exact Real.exp_nonneg _
      · positivity
    _ ≤ Real.exp (ε/2*(n : ℝ))*Real.exp (ε/2*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hpoly' (Real.exp_nonneg _)
    _ = Real.exp (ε*(n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

end RiemannGaussian.SemiprimeSupportRate
