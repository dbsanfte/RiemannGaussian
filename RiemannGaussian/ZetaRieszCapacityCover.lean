/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedBoxCover
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Additive integral bounds for a complete angular cover

The cap checker supplies bounds on whole outer cells. This module adds
their budgets over the existing binary box tree. Half-open cells partition
exactly: no face is counted twice and no subdivision boundary is deleted.
Every cut is checked to stay inside its parent. The terminal inequality is
for the integral on the complete root, not a collection of sampled points.
-/

namespace RiemannGaussian.ZetaRieszCapacityCover
open MeasureTheory
open scoped BigOperators

/-- The two outer variables in the four/five angular comparison. -/
abbrev Box := CertifiedBoxCover.Box (Fin 2)

/-- Each leaf carries lower and upper density bounds. -/
abbrev Tree := CertifiedBoxCover.Tree (Fin 2) (ℚ × ℚ)

/-- Half-open integration cells give an exact disjoint subdivision. -/
def region (B : Box) : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (B i).1 (B i).2)

/-- The signed rational area of a box; valid boxes have nonnegative area. -/
def area (B : Box) : ℚ := ∏ i, ((B i).2-(B i).1)

/-- Check every cut as well as every numerical leaf. -/
def check (leaf : Box → ℚ × ℚ → Bool) : Tree → Box → Bool
  | .leaf w, B => leaf B w
  | .split i q l r, B =>
    decide ((B i).1 ≤ q ∧ q ≤ (B i).2) &&
      check leaf l (CertifiedBoxCover.leftBox B i q) &&
      check leaf r (CertifiedBoxCover.rightBox B i q)

/-- Add the actual area-weighted leaf budgets, with no externally supplied
total and no dropped zero-valued children. -/
def totals : Tree → Box → ℚ × ℚ
  | .leaf w, B => (area B*w.1,area B*w.2)
  | .split i q l r, B =>
    let L := totals l (CertifiedBoxCover.leftBox B i q)
    let R := totals r (CertifiedBoxCover.rightBox B i q)
    (L.1+R.1,L.2+R.2)

private theorem mem_region {B : Box} {x : Fin 2 → ℝ} :
    x ∈ region B ↔ ∀ i, (B i).1 < x i ∧ x i ≤ (B i).2 := by
  simp [region]

private theorem measurable_region (B : Box) : MeasurableSet (region B) :=
  (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem volume_region_ne_top (B : Box) : volume (region B) ≠ ⊤ := by
  rw [region,Real.volume_pi_Ioc]
  exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))

private theorem volume_region (B : Box) (hB : ∀ i, (B i).1 ≤ (B i).2) :
    volume.real (region B) = (area B : ℝ) := by
  change (volume (region B)).toReal = _
  rw [region,Real.volume_pi_Ioc_toReal (by
    intro i
    change ((B i).1 : ℝ) ≤ ((B i).2 : ℝ)
    exact_mod_cast hB i)]
  simp [area]

private theorem split_regions {B : Box} (i : Fin 2) {q : ℚ}
    (hq : (B i).1 ≤ q ∧ q ≤ (B i).2) :
    region B = region (CertifiedBoxCover.leftBox B i q) ∪
      region (CertifiedBoxCover.rightBox B i q) := by
  have hql : ((B i).1 : ℝ) ≤ q := by exact_mod_cast hq.1
  have hqu : (q : ℝ) ≤ (B i).2 := by exact_mod_cast hq.2
  ext x
  simp only [Set.mem_union,mem_region]
  constructor
  · intro hx
    by_cases hxi : x i ≤ (q : ℝ)
    · left
      intro j
      by_cases hj : j = i
      · subst j
        simpa [CertifiedBoxCover.leftBox] using And.intro (hx i).1 hxi
      · simpa [CertifiedBoxCover.leftBox,Function.update_of_ne hj] using hx j
    · right
      intro j
      by_cases hj : j = i
      · subst j
        simpa [CertifiedBoxCover.rightBox] using And.intro (lt_of_not_ge hxi) (hx i).2
      · simpa [CertifiedBoxCover.rightBox,Function.update_of_ne hj] using hx j
  · intro hx j
    rcases hx with hl | hr
    · by_cases hj : j = i
      · subst j
        have hi := hl i
        simp only [CertifiedBoxCover.leftBox,Function.update_self] at hi
        exact ⟨hi.1,hi.2.trans hqu⟩
      · simpa [CertifiedBoxCover.leftBox,Function.update_of_ne hj] using hl j
    · by_cases hj : j = i
      · subst j
        have hi := hr i
        simp only [CertifiedBoxCover.rightBox,Function.update_self] at hi
        exact ⟨hql.trans_lt hi.1,hi.2⟩
      · simpa [CertifiedBoxCover.rightBox,Function.update_of_ne hj] using hr j

private theorem split_disjoint (B : Box) (i : Fin 2) (q : ℚ) :
    Disjoint (region (CertifiedBoxCover.leftBox B i q))
      (region (CertifiedBoxCover.rightBox B i q)) := by
  apply Set.disjoint_left.mpr
  intro x hl hr
  have hleft := (mem_region.mp hl) i
  have hright := (mem_region.mp hr) i
  simp only [CertifiedBoxCover.leftBox,CertifiedBoxCover.rightBox,
    Function.update_self] at hleft hright
  exact (not_lt_of_ge hleft.2) hright.1

private theorem leaf_bounds {f : (Fin 2 → ℝ) → ℝ} {B : Box} {w : ℚ × ℚ}
    (hB : ∀ i, (B i).1 ≤ (B i).2) (hf : IntegrableOn f (region B))
    (hw : ∀ x ∈ region B, (w.1 : ℝ) ≤ f x ∧ f x ≤ (w.2 : ℝ)) :
    (area B*w.1 : ℚ) ≤ (∫ x in region B, f x) ∧
      (∫ x in region B, f x) ≤ (area B*w.2 : ℚ) := by
  have hl := setIntegral_mono_on (integrableOn_const (volume_region_ne_top B)) hf
    (measurable_region B) (fun x hx => (hw x hx).1)
  have hu := setIntegral_mono_on hf (integrableOn_const (volume_region_ne_top B))
    (measurable_region B) (fun x hx => (hw x hx).2)
  simpa only [setIntegral_const,volume_region B hB,smul_eq_mul,Rat.cast_mul] using And.intro hl hu

/-- Successful bounded leaves also discharge integrability on the whole
cover. Measurability suffices; no continuity across clipping faces is needed. -/
theorem integrableOn_of_check (f : (Fin 2 → ℝ) → ℝ) (hf : Measurable f)
    (leaf : Box → ℚ × ℚ → Bool)
    (hleaf : ∀ B w, leaf B w = true →
      ∀ x ∈ region B, (w.1 : ℝ) ≤ f x ∧ f x ≤ (w.2 : ℝ))
    (tree : Tree) {B : Box} (hc : check leaf tree B = true) :
    IntegrableOn f (region B) := by
  induction tree generalizing B with
  | leaf w =>
    apply Measure.integrableOn_of_bounded (M := max |(w.1 : ℝ)| |(w.2 : ℝ)|)
      (volume_region_ne_top B) hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurable_region B)] with x hx
    have hb := hleaf B w hc x hx
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hb.1)
    · exact hb.2.trans ((le_abs_self _).trans (le_max_right _ _))
  | split i q l r ihl ihr =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    rw [split_regions i hc.1.1]
    exact (ihl hc.1.2).union (ihr hc.2)

/-- A checked exhaustive tree proves a two-sided integral inequality on
the complete root. Leaf soundness is a pointwise numerical enclosure;
integrability is retained explicitly and no count/phase estimate is assumed. -/
theorem integral_bounds_of_check (f : (Fin 2 → ℝ) → ℝ)
    (leaf : Box → ℚ × ℚ → Bool)
    (hleaf : ∀ B w, leaf B w = true →
      ∀ x ∈ region B, (w.1 : ℝ) ≤ f x ∧ f x ≤ (w.2 : ℝ))
    (tree : Tree) {B : Box} (hB : ∀ i, (B i).1 ≤ (B i).2)
    (hf : IntegrableOn f (region B)) (hc : check leaf tree B = true) :
    ((totals tree B).1 : ℝ) ≤ (∫ x in region B, f x) ∧
      (∫ x in region B, f x) ≤ ((totals tree B).2 : ℝ) := by
  induction tree generalizing B with
  | leaf w => exact leaf_bounds hB hf (hleaf B w hc)
  | split i q l r ihl ihr =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    have he := split_regions i hc.1.1
    have hlsub : region (CertifiedBoxCover.leftBox B i q) ⊆ region B :=
      he ▸ Set.subset_union_left
    have hrsub : region (CertifiedBoxCover.rightBox B i q) ⊆ region B :=
      he ▸ Set.subset_union_right
    have hBl : ∀ j, (CertifiedBoxCover.leftBox B i q j).1 ≤
        (CertifiedBoxCover.leftBox B i q j).2 := by
      intro j
      by_cases hj : j = i
      · subst j; simpa [CertifiedBoxCover.leftBox] using hc.1.1.1
      · simpa [CertifiedBoxCover.leftBox,Function.update_of_ne hj] using hB j
    have hBr : ∀ j, (CertifiedBoxCover.rightBox B i q j).1 ≤
        (CertifiedBoxCover.rightBox B i q j).2 := by
      intro j
      by_cases hj : j = i
      · subst j; simpa [CertifiedBoxCover.rightBox] using hc.1.1.2
      · simpa [CertifiedBoxCover.rightBox,Function.update_of_ne hj] using hB j
    have hl := ihl hBl (hf.mono_set hlsub) hc.1.2
    have hr := ihr hBr (hf.mono_set hrsub) hc.2
    have hi : (∫ x in region B, f x) =
        (∫ x in region (CertifiedBoxCover.leftBox B i q), f x)+
          ∫ x in region (CertifiedBoxCover.rightBox B i q), f x := by
      rw [he]
      exact setIntegral_union (split_disjoint B i q) (measurable_region _)
        (hf.mono_set hlsub) (hf.mono_set hrsub)
    simp only [totals,Rat.cast_add,hi]
    exact ⟨add_le_add hl.1 hr.1,add_le_add hl.2 hr.2⟩

/-- Compare the whole debit and supply integrals after both exhaustive
covers pass. The only final comparison is exact rational arithmetic on the
computed totals; there is no assumed population or signed-source estimate. -/
theorem compensation_of_checked_covers
    (debit supply : (Fin 2 → ℝ) → ℝ)
    (debitLeaf supplyLeaf : Box → ℚ × ℚ → Bool)
    (hdleaf : ∀ B w, debitLeaf B w = true →
      ∀ x ∈ region B, (w.1 : ℝ) ≤ debit x ∧ debit x ≤ (w.2 : ℝ))
    (hsleaf : ∀ B w, supplyLeaf B w = true →
      ∀ x ∈ region B, (w.1 : ℝ) ≤ supply x ∧ supply x ≤ (w.2 : ℝ))
    (dt st : Tree) {D S : Box}
    (hD : ∀ i, (D i).1 ≤ (D i).2) (hS : ∀ i, (S i).1 ≤ (S i).2)
    (hd : IntegrableOn debit (region D)) (hs : IntegrableOn supply (region S))
    (hdc : check debitLeaf dt D = true) (hsc : check supplyLeaf st S = true)
    {rate : ℚ} (hrate : 0 ≤ rate)
    (hpay : decide (rate*(totals dt D).2 ≤ (totals st S).1) = true) :
    (rate : ℝ)*(∫ x in region D, debit x) ≤ ∫ x in region S, supply x := by
  have hd := (integral_bounds_of_check debit debitLeaf hdleaf dt hD hd hdc).2
  have hs := (integral_bounds_of_check supply supplyLeaf hsleaf st hS hs hsc).1
  have hpay' : (rate : ℝ)*((totals dt D).2 : ℝ) ≤ ((totals st S).1 : ℝ) := by
    simp only [decide_eq_true_eq] at hpay
    exact_mod_cast hpay
  exact (mul_le_mul_of_nonneg_left hd (by exact_mod_cast hrate)).trans (hpay'.trans hs)

end RiemannGaussian.ZetaRieszCapacityCover
