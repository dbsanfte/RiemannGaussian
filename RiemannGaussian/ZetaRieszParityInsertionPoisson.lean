/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityFirstInsertion
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Positive resummation of omitted-share insertions

The finite lower cutoff is retained. Summing the signed insertions before
estimating them gives a compensated positive count sum. This file concerns
the supported inverse kernel; the empty-cofactor boundary and the literal
arithmetic phase transfer are separate obligations.
-/

namespace RiemannGaussian.ZetaRieszParityInsertionPoisson
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- The fixed upper share of an omitted small prime. -/
def cutoff : ℝ := 7/250

/-- Finite reciprocal-density intensity above the auxiliary lower cutoff. -/
def jumpMass (a : ℝ) : ℝ := ∫ x in Ioc a cutoff, x⁻¹

/-- The unnormalised positive jump count, with the original reciprocal
density. The zero count is the supported inverse at gap `g`. -/
def jumpCount (a : ℝ) : ℕ → ℝ → ℝ
  | 0, g => if g ≤ 0 then 1 else 0
  | k+1, g => ∫ x in Ioc a cutoff, x⁻¹*jumpCount a k (g-x)

theorem integrable_density {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x⁻¹) (Ioc a cutoff) := by
  apply ContinuousOn.integrableOn_Icc ?_ |>.mono_set Ioc_subset_Icc_self
  intro x hx
  exact (continuousAt_inv₀ (ne_of_gt (ha.trans_le hx.1))).continuousWithinAt

theorem jumpMass_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ jumpMass a := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact inv_nonneg.mpr (ha.trans hx.1).le

private theorem integrable_weighted {a C : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∀ g, ‖f g‖ ≤ C) (g : ℝ) :
    IntegrableOn (fun x : ℝ => x⁻¹*f (g-x)) (Ioc a cutoff) := by
  apply ((integrable_density ha).mul_const C).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (ha.trans hx.1).le)]
  exact mul_le_mul_of_nonneg_left (hb _) (inv_nonneg.mpr (ha.trans hx.1).le)

/-- The positive count has finite mass, and remains a tail distribution
as a function of the gap. -/
theorem jumpCount_properties {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∀ g, 0 ≤ jumpCount a k g ∧ jumpCount a k g ≤ jumpMass a^k) ∧
      Antitone (jumpCount a k) := by
  induction k with
  | zero =>
    constructor
    · intro g
      simp only [jumpCount, pow_zero]
      split_ifs <;> norm_num
    · intro g h hgh
      simp only [jumpCount]
      split_ifs <;> norm_num at *; linarith
  | succ k ih =>
    have hint (g : ℝ) := integrable_weighted ha ih.2.measurable
      (fun t => by simpa only [Real.norm_of_nonneg (ih.1 t).1] using (ih.1 t).2) g
    constructor
    · intro g
      constructor
      · apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact mul_nonneg (inv_nonneg.mpr (ha.trans hx.1).le) (ih.1 _).1
      · change (∫ x in Ioc a cutoff, x⁻¹*jumpCount a k (g-x)) ≤ _
        calc
          _ ≤ ∫ x in Ioc a cutoff, x⁻¹*jumpMass a^k := by
            apply integral_mono_ae (hint g) ((integrable_density ha).mul_const _)
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
            exact mul_le_mul_of_nonneg_left (ih.1 _).2 (inv_nonneg.mpr (ha.trans hx.1).le)
          _ = _ := by rw [integral_mul_const]; dsimp [jumpMass]; ring
    · intro g h hgh
      apply integral_mono_ae (hint h) (hint g)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_le_mul_of_nonneg_left (ih.2 (by linarith))
        (inv_nonneg.mpr (ha.trans hx.1).le)

theorem integrable_jumpCount {a : ℝ} (ha : 0 < a) (k : ℕ) (g : ℝ) :
    IntegrableOn (fun x : ℝ => x⁻¹*jumpCount a k (g-x)) (Ioc a cutoff) :=
  integrable_weighted ha (jumpCount_properties ha k).2.measurable
    (fun t => by simpa only [Real.norm_of_nonneg ((jumpCount_properties ha k).1 t).1]
      using ((jumpCount_properties ha k).1 t).2) g

/-- The exponential jump moment is finite at every fixed tilt. -/
def jumpMoment (a t : ℝ) : ℝ := ∫ x in Ioc a cutoff, x⁻¹*Real.exp (t*x)

theorem integrable_jumpMoment {a : ℝ} (ha : 0 < a) (t : ℝ) :
    IntegrableOn (fun x : ℝ => x⁻¹*Real.exp (t*x)) (Ioc a cutoff) := by
  apply ContinuousOn.integrableOn_Icc ?_ |>.mono_set Ioc_subset_Icc_self
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
  fun_prop

theorem jumpMoment_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ jumpMoment a t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact mul_nonneg (inv_nonneg.mpr (ha.trans hx.1).le) (Real.exp_pos _).le

/-- A tilted bound for each complete positive count, before summation. -/
theorem jumpCount_tilt {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (k : ℕ) (g : ℝ) :
    jumpCount a k g ≤ Real.exp (-t*g)*jumpMoment a t^k := by
  induction k generalizing g with
  | zero =>
    simp only [jumpCount, pow_zero, mul_one]
    split_ifs with hg
    · exact Real.one_le_exp_iff.mpr (by nlinarith)
    · exact (Real.exp_pos _).le
  | succ k ih =>
    have he (x : ℝ) : x⁻¹*(Real.exp (-t*(g-x))*jumpMoment a t^k) =
        (Real.exp (-t*g)*jumpMoment a t^k)*(x⁻¹*Real.exp (t*x)) := by
      rw [show -t*(g-x) = -t*g+t*x by ring, Real.exp_add]
      ring
    calc
      _ ≤ ∫ x in Ioc a cutoff, (Real.exp (-t*g)*jumpMoment a t^k)*
          (x⁻¹*Real.exp (t*x)) := by
        apply integral_mono_ae (integrable_jumpCount ha k g)
          ((integrable_jumpMoment ha t).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        rw [← he]
        exact mul_le_mul_of_nonneg_left (ih _) (inv_nonneg.mpr (ha.trans hx.1).le)
      _ = _ := by rw [integral_const_mul]; dsimp [jumpMoment]; ring

/-- All positive jump counts with their exact factorial weights. -/
def positiveCountSum (a g : ℝ) : ℝ :=
  ∑' k : ℕ, jumpCount a k g/(k.factorial : ℝ)

theorem summable_positiveCount {a : ℝ} (ha : 0 < a) (g : ℝ) :
    Summable (fun k : ℕ => jumpCount a k g/(k.factorial : ℝ)) := by
  have he := (NormedSpace.expSeries_div_hasSum_exp (jumpMass a)).summable
  apply Summable.of_nonneg_of_le (fun k => by
    exact div_nonneg ((jumpCount_properties ha k).1 g).1 (by positivity))
    (fun k => div_le_div_of_nonneg_right ((jumpCount_properties ha k).1 g).2 (by positivity)) he

theorem positiveCountSum_bounds {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (g : ℝ) :
    0 ≤ positiveCountSum a g ∧
      positiveCountSum a g ≤ Real.exp (-t*g)*Real.exp (jumpMoment a t) := by
  have he := (NormedSpace.expSeries_div_hasSum_exp (jumpMoment a t)).mul_left
    (Real.exp (-t*g))
  rw [← Real.exp_eq_exp_ℝ] at he
  constructor
  · exact tsum_nonneg (fun k => div_nonneg ((jumpCount_properties ha k).1 g).1 (by positivity))
  · change (∑' k : ℕ, jumpCount a k g/(k.factorial : ℝ)) ≤ _
    apply ((summable_positiveCount ha g).tsum_le_tsum (fun k => ?_) he.summable).trans_eq he.tsum_eq
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (jumpCount_tilt ha ht k g) (by positivity : (0 : ℝ) ≤ k.factorial)

/-- The signed count at one insertion order, with its factorial already
included. The antidiagonal keeps every cancellation against zero jumps. -/
def insertion (a : ℝ) (k : ℕ) (g : ℝ) : ℝ :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
    (-jumpMass a)^ij.1/(ij.1.factorial : ℝ) *
      (jumpCount a ij.2 g/(ij.2.factorial : ℝ))

/-- The complete signed series before its positive compensated resummation. -/
def supportInsertionSum (a g : ℝ) : ℝ := ∑' k : ℕ, insertion a k g

theorem summable_insertion {a : ℝ} (ha : 0 < a) (g : ℝ) :
    Summable (fun k => insertion a k g) := by
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm
    (NormedSpace.expSeries_div_hasSum_exp (-jumpMass a)).summable.norm
    (summable_positiveCount ha g).norm).of_norm

/-- Resummation, rather than a termwise absolute-value bound: the whole
signed series is a compensated positive jump sum. -/
theorem supportInsertionSum_eq {a : ℝ} (ha : 0 < a) (g : ℝ) :
    supportInsertionSum a g = Real.exp (-jumpMass a)*positiveCountSum a g := by
  have he := NormedSpace.expSeries_div_hasSum_exp (-jumpMass a)
  rw [← Real.exp_eq_exp_ℝ] at he
  have hh := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    he.summable.norm (summable_positiveCount ha g).norm
  rw [he.tsum_eq] at hh
  exact hh.symm

/-- A Chernoff bound for the exact compensated count sum. The intensity
may grow without bound as the auxiliary lower cutoff tends to zero. -/
theorem supportInsertionSum_bounds {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (g : ℝ) :
    0 ≤ supportInsertionSum a g ∧
      supportInsertionSum a g ≤ Real.exp (jumpMoment a t-jumpMass a-t*g) := by
  rw [supportInsertionSum_eq ha]
  have hb := positiveCountSum_bounds ha ht g
  constructor
  · exact mul_nonneg (Real.exp_pos _).le hb.1
  · apply (mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

theorem jumpMoment_sub_mass {a : ℝ} (ha : 0 < a) (har : a ≤ cutoff) :
    jumpMoment a (2/cutoff)-jumpMass a ≤ Real.exp 2-1 := by
  have he1 : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hcut : (0 : ℝ) < cutoff := by norm_num [cutoff]
  have hb : ∀ x ∈ Ioc a cutoff,
      x⁻¹*(Real.exp ((2/cutoff)*x)-1) ≤ (Real.exp 2-1)/cutoff := by
    intro x hx
    have hx0 : 0 < x := ha.trans hx.1
    have hratio : 0 ≤ x/cutoff ∧ x/cutoff ≤ 1 :=
      ⟨div_nonneg hx0.le hcut.le, (div_le_one hcut).mpr hx.2⟩
    have hc := convexOn_exp.2 (show (0 : ℝ) ∈ univ from mem_univ _)
      (show (2 : ℝ) ∈ univ from mem_univ _) (by linarith : 0 ≤ 1-x/cutoff)
      hratio.1 (by ring : 1-x/cutoff+x/cutoff = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have hh : Real.exp ((2/cutoff)*x)-1 ≤ (x/cutoff)*(Real.exp 2-1) := by
      rw [show (2/cutoff)*x = x/cutoff*2 by ring]
      linarith
    calc
      _ ≤ x⁻¹*((x/cutoff)*(Real.exp 2-1)) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hx0.le)
      _ = _ := by field_simp
  have hint : IntegrableOn (fun x : ℝ => x⁻¹*(Real.exp ((2/cutoff)*x)-1)) (Ioc a cutoff) := by
    apply ((integrable_jumpMoment ha (2/cutoff)).sub (integrable_density ha)).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  calc
    _ = ∫ x in Ioc a cutoff, x⁻¹*(Real.exp ((2/cutoff)*x)-1) := by
      rw [show (fun x : ℝ => x⁻¹*(Real.exp ((2/cutoff)*x)-1)) =
        (fun x => x⁻¹*Real.exp ((2/cutoff)*x)-x⁻¹) by ext; ring]
      rw [integral_sub (integrable_jumpMoment ha _) (integrable_density ha)]
      rfl
    _ ≤ ∫ _x in Ioc a cutoff, (Real.exp 2-1)/cutoff := by
      apply integral_mono_ae hint (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hb x hx
    _ = (cutoff-a)*((Real.exp 2-1)/cutoff) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le har]
    _ ≤ Real.exp 2-1 := by
      apply (mul_le_mul_of_nonneg_right (sub_le_self cutoff ha.le)
        (div_nonneg (by linarith) hcut.le)).trans_eq
      field_simp

/-- The full compensated support-insertion sum is uniformly below a
millionth on the literal sharpened gap, for every positive lower cutoff. -/
theorem supportInsertionSum_core_bound {a g : ℝ} (ha : 0 < a)
    (har : a ≤ cutoff) (hg : (289/1000 : ℝ) < g) :
    0 ≤ supportInsertionSum a g ∧ supportInsertionSum a g < 1/1000000 := by
  have hb := supportInsertionSum_bounds ha
    (show (0 : ℝ) ≤ 2/cutoff by norm_num [cutoff]) g
  have hm := jumpMoment_sub_mass ha har
  have hexp2 : Real.exp (2 : ℝ) < 15/2 := by
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp (2 : ℝ) = Real.exp 1^2 := by
      rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add, pow_two]
    rw [h2]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hexp14 : (1000000 : ℝ) < Real.exp 14 := by
    have he := Real.exp_one_gt_d9
    have h27 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) h27 14
    have h14 : Real.exp (14 : ℝ) = Real.exp 1^14 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h14]
    exact lt_of_lt_of_le (by norm_num) hp
  have hexponent : jumpMoment a (2/cutoff)-jumpMass a-(2/cutoff)*g < -14 := by
    norm_num [cutoff] at *
    linarith
  refine ⟨hb.1, hb.2.trans_lt ?_⟩
  calc
    _ < Real.exp (-14 : ℝ) := Real.exp_lt_exp.mpr hexponent
    _ < 1/1000000 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) hexp14

end
end RiemannGaussian.ZetaRieszParityInsertionPoisson
