/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszZeroParityCascade
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The first nonzero omitted-prime insertion

At eleven insertions only the empty subset can reach the supported
kernel. The signed difference is therefore a positive simplex indicator.
The literal core provides enough slack to bound its full density integral.
This file does not bound the sum of insertion orders twelve and above.
-/

namespace RiemannGaussian.ZetaRieszParityFirstInsertion
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszZeroParityCascade ZetaRieszParityPacket

/-- A slightly sharper rational gap, using the same exact moving length. -/
theorem core_support_gap_sharp {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) :
    289/1000 < 1-SquarefreeVaughanLogSource.length u N/Real.log n := by
  have hnlo := (Finset.mem_filter.mp hn).2.1
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log n := by linarith
  have hL := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : 2*Real.log 2 ≤ (13863/10000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlength : SquarefreeVaughanLogSource.length u N ≤ (13863/10000 : ℝ)*N :=
    hL.trans (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg _))
  have hh : SquarefreeVaughanLogSource.length u N/Real.log n < (711/1000 : ℝ) := by
    apply (div_lt_iff₀ hlog).mpr
    linarith
  linarith

/-- At the first possible insertion count every nonempty subset term
still vanishes. The surviving coefficient is exactly positive one. -/
theorem eleven_insertions_exact {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hcard : S.card = 11) (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 7/250)
    {s d : ℝ} (hgap : (7/25 : ℝ) < s-d) :
    insertedSupport S x s d = if s-d ≤ ∑ i ∈ S, x i then 1 else 0 := by
  unfold insertedSupport
  rw [Finset.sum_eq_single ∅]
  · simp only [Finset.card_empty, pow_zero, Finset.sum_empty, sub_zero, one_mul]
    unfold supportKernel
    congr 1
    apply propext
    constructor <;> intro hh <;> linarith
  · intro A hA hne
    have hsub := Finset.mem_powerset.mp hA
    have hc : (S \ A).card ≤ 10 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard]
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    have hs := Finset.sum_le_sum (fun i (hi : i ∈ S \ A) => (hx i (Finset.mem_sdiff.mp hi).1).2)
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    have hcr : ((S \ A).card : ℝ) ≤ 10 := by exact_mod_cast hc
    have he := Finset.sum_sdiff (f := x) hsub
    rw [supportKernel_eq_zero (by linarith), mul_zero]
  · simp

/-- Reaching the first support forces each inserted share above 9/1000. -/
theorem first_support_each_share {x : Fin 11 → ℝ}
    (hx : ∀ i, x i ≤ 7/250) {g : ℝ} (hg : (289/1000 : ℝ) < g)
    (hs : g ≤ ∑ i, x i) (i : Fin 11) : (9/1000 : ℝ) < x i := by
  have he := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
  have hu := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.univ.erase i) => hx j)
  norm_num at hu
  linarith

/-- The first supported insertion, including the original reciprocal
prime-density factors and the eleven-factor symmetry normalization. -/
def firstIntegrand (g : ℝ) (x : Fin 11 → ℝ) : ℝ :=
  (∏ i, (x i)⁻¹)*(if g ≤ ∑ i, x i then 1 else 0)

/-- The full eleven-variable density integral with its factorial symmetry factor. -/
def firstInsertion (g : ℝ) : ℝ :=
  ((11 : ℕ).factorial : ℝ)⁻¹ * ∫ x : Fin 11 → ℝ, firstIntegrand g x
    ∂Measure.pi (fun _ => volume.restrict (Ioc (0 : ℝ) (7/250)))

/-- The positive integrand is exactly the signed eleventh insertion,
including every reciprocal density factor. -/
theorem firstIntegrand_eq_insertedSupport {s d : ℝ}
    (hg : (289/1000 : ℝ) < s-d) {x : Fin 11 → ℝ}
    (hx : ∀ i, x i ∈ Ioc (0 : ℝ) (7/250)) :
    firstIntegrand (s-d) x = (∏ i, (x i)⁻¹)*insertedSupport Finset.univ x s d := by
  rw [eleven_insertions_exact Finset.univ x (by simp)
    (fun i _ => ⟨(hx i).1.le, (hx i).2⟩) (by linarith)]
  rfl

/-- A separable integrable majorant retaining the forced lower cutoff. -/
def firstDensity (x : ℝ) : ℝ := (Ioc (9/1000 : ℝ) (7/250)).indicator (fun t => t⁻¹) x

theorem firstDensity_nonneg (x : ℝ) : 0 ≤ firstDensity x := by
  unfold firstDensity
  by_cases hx : x ∈ Ioc (9/1000 : ℝ) (7/250)
  · rw [indicator_of_mem hx]
    exact inv_nonneg.mpr (by linarith [hx.1])
  · simp [hx]

theorem integrable_firstDensity :
    Integrable firstDensity (volume.restrict (Ioc (0 : ℝ) (7/250))) := by
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc (9/1000 : ℝ) (7/250)) := by
    intro x hx
    exact (continuousAt_inv₀ (by linarith [hx.1] : x ≠ 0)).continuousWithinAt
  have hi : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc (9/1000 : ℝ) (7/250)) volume :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold firstDensity
  rw [integrable_indicator_iff measurableSet_Ioc]
  change Integrable _ ((volume.restrict (Ioc (0 : ℝ) (7/250))).restrict (Ioc (9/1000 : ℝ) (7/250)))
  rw [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_left (by norm_num : (0 : ℝ) ≤ 9/1000))]
  exact hi

theorem integral_firstDensity :
    (∫ x : ℝ, firstDensity x ∂volume.restrict (Ioc (0 : ℝ) (7/250))) = Real.log (28/9) := by
  unfold firstDensity
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_left (by norm_num : (0 : ℝ) ≤ 9/1000)),
    ← intervalIntegral.integral_of_le (by norm_num : (9/1000 : ℝ) ≤ 7/250),
    integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num

theorem firstIntegrand_bounds {g : ℝ} (hg : (289/1000 : ℝ) < g) {x : Fin 11 → ℝ}
    (hx : ∀ i, x i ∈ Ioc (0 : ℝ) (7/250)) :
    0 ≤ firstIntegrand g x ∧ firstIntegrand g x ≤ ∏ i, firstDensity (x i) := by
  unfold firstIntegrand
  by_cases hs : g ≤ ∑ i, x i
  · rw [if_pos hs, mul_one]
    constructor
    · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hx i).1.le)
    · apply le_of_eq
      apply Finset.prod_congr rfl
      intro i _
      change (x i)⁻¹ = (Ioc (9/1000 : ℝ) (7/250)).indicator (fun t : ℝ => t⁻¹) (x i)
      rw [indicator_of_mem (show x i ∈ Ioc (9/1000 : ℝ) (7/250) from
        ⟨first_support_each_share (fun i => (hx i).2) hg hs i, (hx i).2⟩)]
  · simp only [if_neg hs, mul_zero]
    exact ⟨le_rfl, Finset.prod_nonneg (fun i _ => firstDensity_nonneg _)⟩

/-- The first nonzero density integral has a completely explicit small
upper bound. No numerical quadrature or discarded subset sign is used. -/
theorem firstInsertion_bounds {g : ℝ} (hg : (289/1000 : ℝ) < g) :
    0 ≤ firstInsertion g ∧ firstInsertion g < 1/1000000 := by
  let μ : Measure (Fin 11 → ℝ) :=
    Measure.pi (fun _ => volume.restrict (Ioc (0 : ℝ) (7/250)))
  have hx : ∀ᵐ x : Fin 11 → ℝ ∂μ, ∀ i, x i ∈ Ioc (0 : ℝ) (7/250) := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (i := i)).eventually (ae_restrict_mem measurableSet_Ioc)
  have hm := Integrable.fintype_prod (fun _ : Fin 11 => integrable_firstDensity)
  have hi : Integrable (firstIntegrand g) μ := by
    have hf : Measurable (firstIntegrand g) := by
      unfold firstIntegrand
      apply Measurable.mul
      · fun_prop
      · exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
          measurable_const measurable_const
    apply hm.mono' hf.aestronglyMeasurable
    filter_upwards [hx] with x hx
    have hb := firstIntegrand_bounds hg hx
    simpa only [Real.norm_of_nonneg hb.1] using hb.2
  have hnonneg : 0 ≤ ∫ x, firstIntegrand g x ∂μ :=
    integral_nonneg_of_ae (hx.mono (fun _ hx => (firstIntegrand_bounds hg hx).1))
  have hbound : (∫ x, firstIntegrand g x ∂μ) ≤ Real.log (28/9)^11 := by
    have hh := integral_mono_ae hi hm (hx.mono (fun _ hx => (firstIntegrand_bounds hg hx).2))
    have he := integral_fintype_prod_eq_pow (ι := Fin 11)
      (μ := volume.restrict (Ioc (0 : ℝ) (7/250))) firstDensity
    simpa only [Fintype.card_fin, integral_firstDensity] using hh.trans_eq he
  have hlo : 0 ≤ Real.log (28/9 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (28/9 : ℝ) ≤ 6/5 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6/5) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hp : Real.log (28/9 : ℝ)^11 ≤ (6/5 : ℝ)^11 := pow_le_pow_left₀ hlo hlog _
  constructor
  · exact mul_nonneg (by positivity) hnonneg
  · apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hbound.trans hp)
      (show 0 ≤ ((11 : ℕ).factorial : ℝ)⁻¹ by positivity))
    norm_num [Nat.factorial]

end
end RiemannGaussian.ZetaRieszParityFirstInsertion
