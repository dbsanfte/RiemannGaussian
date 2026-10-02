/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import RiemannGaussian.ZetaRieszReflectedLinear

/-!
# Signed crossing layers and their exact variance price

All hinges in a divisor-cardinality layer have the same Möbius sign.
After centering the COMPLETE layer its first displacement cancels. The
remaining Jensen defect is nonnegative, supported only in the crossing
interval, and has integral exactly half the total squared displacement.

The final inequality retains the signed phase weight at the layer center;
only its variation is priced. No prime-density transport, native floor,
or source-scale cancellation of the central terms is asserted.
-/

set_option autoImplicit false
noncomputable section
open Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLayerVariance

/-- Complete-layer centering, including every subset and its multiplicity. -/
def defect {ι : Type*} (S : Finset ι) (x : ι → ℝ) (m D : ℝ) : ℝ :=
  (∑ i ∈ S,max 0 (D-x i))-(S.card : ℝ)*max 0 (D-m)

private theorem sum_displacement {ι : Type*} (S : Finset ι) (x : ι → ℝ) (m D : ℝ)
    (hm : (∑ i ∈ S,x i)=(S.card : ℝ)*m) :
    (∑ i ∈ S,(D-x i))=(S.card : ℝ)*(D-m) := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,hm]
  simp only [nsmul_eq_mul]
  ring

/-- Convexity is used only after the complete layer's linear part cancels. -/
theorem defect_nonneg {ι : Type*} (S : Finset ι) (x : ι → ℝ) (m D : ℝ)
    (hm : (∑ i ∈ S,x i)=(S.card : ℝ)*m) : 0 ≤ defect S x m D := by
  by_cases h : D ≤ m
  · rw [defect,max_eq_left (by linarith : D-m ≤ 0),mul_zero,sub_zero]
    exact Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  · have hs := Finset.sum_le_sum (s := S) (fun i _ => le_max_right 0 (D-x i))
    rw [sum_displacement S x m D hm] at hs
    rw [defect,max_eq_right (by linarith : 0 ≤ D-m)]
    linarith only [hs]

/-- No unresolved response lies below the least subset log. -/
theorem defect_eq_zero_of_le {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {m D l : ℝ} (hD : D ≤ l) (hm : l ≤ m) (hx : ∀ i ∈ S,l ≤ x i) :
    defect S x m D=0 := by
  rw [defect,max_eq_left (by linarith : D-m ≤ 0),mul_zero,sub_zero]
  exact Finset.sum_eq_zero (fun i hi => max_eq_left (by linarith [hx i hi]))

/-- Above the greatest subset log the COMPLETE affine layer cancels. -/
theorem defect_eq_zero_of_ge {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {m D h : ℝ} (hD : h ≤ D) (hmh : m ≤ h) (hx : ∀ i ∈ S,x i ≤ h)
    (hm : (∑ i ∈ S,x i)=(S.card : ℝ)*m) : defect S x m D=0 := by
  have he : (∑ i ∈ S,max 0 (D-x i))=∑ i ∈ S,(D-x i) :=
    Finset.sum_congr rfl (fun i hi => max_eq_right (by linarith [hx i hi]))
  rw [defect,he,sum_displacement S x m D hm,
    max_eq_right (by linarith : 0 ≤ D-m),sub_self]

theorem continuous_defect {ι : Type*} (S : Finset ι) (x : ι → ℝ) (m : ℝ) :
    Continuous (defect S x m) := by
  unfold defect
  fun_prop

private theorem integral_hinge {l x h : ℝ} (hlx : l ≤ x) (hxh : x ≤ h) :
    (∫ D in l..h,max 0 (D-x))=(h-x)^2/2 := by
  have hc : Continuous (fun D : ℝ => max 0 (D-x)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable l x) (hc.intervalIntegrable x h)]
  have hz : (∫ D in l..x,max 0 (D-x))=0 := by
    calc
      _ = ∫ _D in l..x,(0 : ℝ) := intervalIntegral.integral_congr (by
        intro D hD
        rw [Set.uIcc_of_le hlx] at hD
        exact max_eq_left (by linarith [hD.2]))
      _ = 0 := by simp
  have he : (∫ D in x..h,max 0 (D-x))=∫ D in x..h,D-x := by
    apply intervalIntegral.integral_congr
    intro D hD
    rw [Set.uIcc_of_le hxh] at hD
    exact max_eq_right (by linarith [hD.1])
  have hf : IntervalIntegrable (fun D : ℝ => D) MeasureTheory.volume x h :=
    continuous_id.intervalIntegrable x h
  have hg : IntervalIntegrable (fun _D : ℝ => x) MeasureTheory.volume x h :=
    continuous_const.intervalIntegrable x h
  rw [hz,zero_add,he,intervalIntegral.integral_sub hf hg,
    integral_id,intervalIntegral.integral_const]
  ring

/-- Exact integrated price: first-moment cancellation leaves only variance.
This includes every crossing subset; no thin layer is skipped. -/
theorem integral_defect {ι : Type*} (S : Finset ι) (x : ι → ℝ) {m l h : ℝ}
    (hlm : l ≤ m) (hmh : m ≤ h) (hx : ∀ i ∈ S,l ≤ x i ∧ x i ≤ h)
    (hm : (∑ i ∈ S,x i)=(S.card : ℝ)*m) :
    (∫ D in l..h,defect S x m D)=(∑ i ∈ S,(x i-m)^2)/2 := by
  have hd : (∑ i ∈ S,(x i-m))=0 := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,hm]
    simp only [nsmul_eq_mul,sub_self]
  simp only [defect]
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_finsetSum (fun _ _ => by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul,integral_hinge hlm hmh]
  have he : (∑ i ∈ S,(∫ D in l..h,max 0 (D-x i)))=
      ∑ i ∈ S,(h-x i)^2/2 := Finset.sum_congr rfl
        (fun i hi => integral_hinge (hx i hi).1 (hx i hi).2)
  rw [he]
  have ha : (∑ i ∈ S,(h-x i)^2/2)=
      (S.card : ℝ)*(h-m)^2/2+(∑ i ∈ S,(x i-m)^2)/2 := by
    calc
      _ = ∑ i ∈ S,((h-m)^2/2+(x i-m)^2/2-(h-m)*(x i-m)) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by
        rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
          ← Finset.sum_div,← Finset.mul_sum,hd]
        simp only [nsmul_eq_mul,mul_zero,sub_zero]
        ring
  rw [ha]
  ring

/-- Preserve the phase-weighted central moment. Only weight variation is
paid, with the exact variance area. This works at every count. -/
theorem weighted_defect_bounds {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {m l h ε : ℝ} (hlm : l ≤ m) (hmh : m ≤ h)
    (hx : ∀ i ∈ S,l ≤ x i ∧ x i ≤ h)
    (hm : (∑ i ∈ S,x i)=(S.card : ℝ)*m)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Icc l h))
    (he : ∀ D ∈ Set.Icc l h,|w D-w m| ≤ ε) :
    (w m-ε)*((∑ i ∈ S,(x i-m)^2)/2) ≤
      (∫ D in l..h,w D*defect S x m D) ∧
    (∫ D in l..h,w D*defect S x m D) ≤
      (w m+ε)*((∑ i ∈ S,(x i-m)^2)/2) := by
  have hlh : l ≤ h := hlm.trans hmh
  have hc : ContinuousOn (defect S x m) (Set.Icc l h) :=
    (continuous_defect S x m).continuousOn
  have hi : IntervalIntegrable (fun D => w D*defect S x m D) MeasureTheory.volume l h :=
    (hw.mul hc).intervalIntegrable_of_Icc hlh
  have hlow : IntervalIntegrable (fun D => (w m-ε)*defect S x m D)
      MeasureTheory.volume l h := ((continuous_defect S x m).const_mul _).intervalIntegrable _ _
  have hhigh : IntervalIntegrable (fun D => (w m+ε)*defect S x m D)
      MeasureTheory.volume l h := ((continuous_defect S x m).const_mul _).intervalIntegrable _ _
  have hd D : 0 ≤ defect S x m D := defect_nonneg S x m D hm
  have hlo := intervalIntegral.integral_mono_on hlh hlow hi (by
    intro D hD
    have hh := (abs_le.mp (he D hD)).1
    exact mul_le_mul_of_nonneg_right (by linarith only [hh]) (hd D))
  have hhi := intervalIntegral.integral_mono_on hlh hi hhigh (by
    intro D hD
    have hh := (abs_le.mp (he D hD)).2
    exact mul_le_mul_of_nonneg_right (by linarith only [hh]) (hd D))
  rw [intervalIntegral.integral_const_mul,integral_defect S x hlm hmh hx hm] at hlo hhi
  exact ⟨hlo,hhi⟩

/-- A signed phase may be centered only AFTER its entire crossing layer
is joined. The remaining price is variance times variation, not layer width. -/
theorem weighted_defect_sub_center_abs_le {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {m l h ε : ℝ} (hlm : l ≤ m) (hmh : m ≤ h)
    (hx : ∀ i ∈ S,l ≤ x i ∧ x i ≤ h)
    (hm : (∑ i ∈ S,x i)=(S.card : ℝ)*m)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Icc l h))
    (he : ∀ D ∈ Set.Icc l h,|w D-w m| ≤ ε) :
    |(∫ D in l..h,w D*defect S x m D)-w m*((∑ i ∈ S,(x i-m)^2)/2)| ≤
      ε*((∑ i ∈ S,(x i-m)^2)/2) := by
  have hh := weighted_defect_bounds S x hlm hmh hx hm w hw he
  apply abs_le.mpr
  constructor <;> nlinarith only [hh.1,hh.2]

/-- Every selected count/quota/period enters ONE signed central aggregate.
Only the independently bounded crossing-weight variations are charged.
No phase, mask or prime-density estimate is supplied by this theorem. -/
theorem joined_weighted_defect_floor {κ ι : Type*} (B : Finset κ)
    (S : κ → Finset ι) (x : κ → ι → ℝ) (m l h ε sign : κ → ℝ)
    (w : κ → ℝ → ℝ)
    (hlm : ∀ b ∈ B,l b ≤ m b) (hmh : ∀ b ∈ B,m b ≤ h b)
    (hx : ∀ b ∈ B,∀ i ∈ S b,l b ≤ x b i ∧ x b i ≤ h b)
    (hm : ∀ b ∈ B,(∑ i ∈ S b,x b i)=(S b).card*(m b))
    (hw : ∀ b ∈ B,ContinuousOn (w b) (Set.Icc (l b) (h b)))
    (he : ∀ b ∈ B,∀ D ∈ Set.Icc (l b) (h b),|w b D-w b (m b)| ≤ ε b) :
    (∑ b ∈ B,sign b*w b (m b)*((∑ i ∈ S b,(x b i-m b)^2)/2))-
      (∑ b ∈ B,|sign b| * ε b*((∑ i ∈ S b,(x b i-m b)^2)/2)) ≤
        ∑ b ∈ B,sign b*(∫ D in l b..h b,w b D*defect (S b) (x b) (m b) D) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro b hb
  have hh := weighted_defect_sub_center_abs_le (S b) (x b)
    (hlm b hb) (hmh b hb) (hx b hb) (hm b hb) (w b) (hw b hb) (he b hb)
  have hc := mul_le_mul_of_nonneg_left hh (abs_nonneg (sign b))
  rw [← abs_mul] at hc
  have hl := neg_abs_le (sign b*((∫ D in l b..h b,w b D*defect (S b) (x b) (m b) D)-
    w b (m b)*((∑ i ∈ S b,(x b i-m b)^2)/2)))
  nlinarith only [hc,hl]

/-- An actual arithmetic divisor-cardinality layer, with no model labels. -/
def divisorLayer (a q : ℕ) : Finset ℕ :=
  a.divisors.filter (fun d => d.primeFactors.card=q)

/-- Its exact mean logarithm; the empty layer has no contribution. -/
def divisorLayerMean (a q : ℕ) : ℝ :=
  (∑ d ∈ divisorLayer a q,log d)/(divisorLayer a q).card

theorem divisorLayerMean_sum (a q : ℕ) :
    (∑ d ∈ divisorLayer a q,log d)=
      ((divisorLayer a q).card : ℝ)*divisorLayerMean a q := by
  by_cases hz : (divisorLayer a q).card=0
  · have he := Finset.card_eq_zero.mp hz
    simp only [he,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,zero_mul]
  · have hc : ((divisorLayer a q).card : ℝ) ≠ 0 := by exact_mod_cast hz
    rw [divisorLayerMean]
    field_simp

/-- The true Möbius sign is constant on every retained squarefree layer. -/
theorem divisorLayer_moebius {a q d : ℕ} (ha : Squarefree a)
    (hd : d ∈ divisorLayer a q) :
    (ArithmeticFunction.moebius d : ℝ)=(-1 : ℝ)^q := by
  obtain ⟨hd,hq⟩ := Finset.mem_filter.mp hd
  have hsf := ha.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hm := ZetaRieszReflectedLinear.moebius_eq_primeCount hsf
  exact_mod_cast hm.trans (congrArg (fun k => (-1 : ℤ)^k) hq)

/-- The variance identity applies directly to actual divisor logs.
It prices a Lebesgue cutoff average, not a discrete prime measure. -/
theorem actual_divisor_layer_integral (a q : ℕ) {l h : ℝ}
    (hlm : l ≤ divisorLayerMean a q) (hmh : divisorLayerMean a q ≤ h)
    (hx : ∀ d ∈ divisorLayer a q,l ≤ log d ∧ log d ≤ h) :
    (∫ D in l..h,defect (divisorLayer a q) (fun d => log d) (divisorLayerMean a q) D)=
      (∑ d ∈ divisorLayer a q,(log d-divisorLayerMean a q)^2)/2 :=
  integral_defect (divisorLayer a q) (fun d => log d) hlm hmh hx
    (divisorLayerMean_sum a q)

end RiemannGaussian.ZetaRieszLayerVariance
