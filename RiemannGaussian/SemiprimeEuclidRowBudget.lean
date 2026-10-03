/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCompanionCoverage
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Bertrand

/-!
# Complete Euclidean row-construction charges

Retain the entire division frame before charging all intermediate vectors.
The original constructor and its signs remain unchanged. Construction
counts are separate from useful collision coverage and full bit costs.
-/

namespace RiemannGaussian.SemiprimeEuclidRowBudget

open SemiprimeQuotientRows SemiprimeEuclidRowFamily SemiprimeWeightedRows
open scoped BigOperators

/-- The complete public division state before any row-count projection. -/
structure EuclidFrame where
  /-- Previous, larger Euclidean remainder. -/
  larger : ℕ
  /-- Current informative Euclidean remainder. -/
  smaller : ℕ
  /-- Previous nonnegative denominator weight. -/
  priorWeight : ℕ
  /-- Current positive denominator weight. -/
  currentWeight : ℕ
  /-- Signed numerator orientation, retained before absolute charges. -/
  negative : Bool
deriving DecidableEq, Repr

/-- The division quotient charges both current and intermediate vectors. -/
def frameQuotient (f : EuclidFrame) : ℕ := f.larger/f.smaller

/-- All vectors emitted at this exact retained division state. -/
def expandFrame (f : EuclidFrame) : List (ℤ×ℕ) :=
  (signed f.negative f.smaller,f.currentWeight)::
    (List.range (frameQuotient f-1)).map fun k =>
      (signed (!f.negative) (f.larger-(k+1)*f.smaller),
        f.priorWeight+(k+1)*f.currentWeight)

/-- Retain every division before expanding its whole quotient. -/
def euclidFrames (r₀ r₁ x y : ℕ) (negative : Bool) : List EuclidFrame :=
  if r₁=0 then [] else
    ⟨r₀,r₁,x,y,negative⟩::
      euclidFrames r₁ (r₀%r₁) y (x+r₀/r₁*y) (!negative)
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The richer frame carrier expands to the actual original constructor. -/
theorem euclidFrames_expand (r₀ r₁ x y : ℕ) (negative : Bool) :
    (euclidFrames r₀ r₁ x y negative).flatMap expandFrame=
      euclidPairs r₀ r₁ x y negative := by
  rw [euclidFrames,euclidPairs]
  by_cases h : r₁=0
  · simp only [if_pos h,List.flatMap_nil]
  · simp only [if_neg h,List.flatMap_cons,expandFrame,frameQuotient,List.cons_append]
    rw [euclidFrames_expand]
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- A quotient q contributes exactly q original vectors, not merely one
convergent. This identity includes every recursive division. -/
theorem euclidPairs_length_eq_frameSum {r₀ r₁ x y : ℕ} (negative : Bool)
    (horder : r₁<r₀) :
    (euclidPairs r₀ r₁ x y negative).length=
      ((euclidFrames r₀ r₁ x y negative).map frameQuotient).sum := by
  rw [euclidPairs,euclidFrames]
  by_cases h : r₁=0
  · simp only [if_pos h,List.length_nil,List.map_nil,List.sum_nil]
  · have hp : 0<r₁ := by omega
    have hq := Nat.div_pos horder.le hp
    simp only [if_neg h,List.length_cons,List.length_append,List.length_map,
      List.length_range,List.map_cons,List.sum_cons,frameQuotient]
    rw [euclidPairs_length_eq_frameSum (!negative) (Nat.mod_lt _ hp)]
    omega
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- All retained frames satisfy the actual public determinant invariant. -/
theorem euclidFrames_fit {m r₀ r₁ x y : ℕ} {negative : Bool}
    (horder : r₁<r₀) (hy : 0<y) (hdet : r₀*y+r₁*x=m)
    {f : EuclidFrame} (hf : f∈euclidFrames r₀ r₁ x y negative) :
    0<f.smaller ∧ 0<f.currentWeight ∧ f.smaller<f.larger ∧
      f.larger*f.currentWeight+f.smaller*f.priorWeight=m := by
  rw [euclidFrames] at hf
  by_cases h : r₁=0
  · simp only [if_pos h,List.not_mem_nil] at hf
  · have hp : 0<r₁ := by omega
    rw [if_neg h,List.mem_cons] at hf
    rcases hf with rfl|hf
    · exact ⟨hp,hy,horder,hdet⟩
    · have hq := Nat.div_pos horder.le hp
      have hn : r₁*(x+r₀/r₁*y)+(r₀%r₁)*y=m := by
        rw [←euclid_determinant_step,hdet]
      exact euclidFrames_fit (Nat.mod_lt _ hp) (by positivity) hn hf
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- One charge slot is a positive triple with product at most m. -/
theorem frame_charge_product {m : ℕ} {f : EuclidFrame}
    (hfit : f.larger*f.currentWeight+f.smaller*f.priorWeight=m)
    {k : ℕ} (hk : k<frameQuotient f) :
    f.smaller*f.currentWeight*(k+1)≤m := by
  have hq := Nat.div_mul_le_self f.larger f.smaller
  have hk' : k+1≤frameQuotient f := by omega
  calc
    _ = ((k+1)*f.smaller)*f.currentWeight := by ring
    _ ≤ (frameQuotient f*f.smaller)*f.currentWeight :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk')
    _ ≤ f.larger*f.currentWeight := Nat.mul_le_mul_right _ hq
    _ ≤ m := by omega

/-- Every retained positive remainder is bounded by its starting remainder. -/
theorem euclidFrames_remainder_bound {r₀ r₁ x y : ℕ} {negative : Bool}
    {f : EuclidFrame} (hf : f∈euclidFrames r₀ r₁ x y negative) :
    0<f.smaller ∧ f.smaller≤r₁ := by
  rw [euclidFrames] at hf
  by_cases h : r₁=0
  · simp only [if_pos h,List.not_mem_nil] at hf
  · have hp : 0<r₁ := by omega
    rw [if_neg h,List.mem_cons] at hf
    rcases hf with rfl|hf
    · exact ⟨hp,le_refl _⟩
    · have ht := euclidFrames_remainder_bound hf
      exact ⟨ht.1,ht.2.trans (Nat.mod_lt _ hp).le⟩
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- Current remainders decrease strictly, so no division frame is reused. -/
theorem euclidFrames_strict (r₀ r₁ x y : ℕ) (negative : Bool) :
    (euclidFrames r₀ r₁ x y negative).Pairwise (fun f g => g.smaller<f.smaller) := by
  rw [euclidFrames]
  by_cases h : r₁=0
  · simp only [if_pos h]
    exact List.Pairwise.nil
  · have hp : 0<r₁ := by omega
    rw [if_neg h,List.pairwise_cons]
    refine ⟨?_,euclidFrames_strict _ _ _ _ _⟩
    intro f hf
    exact (euclidFrames_remainder_bound hf).2.trans_lt (Nat.mod_lt _ hp)
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- A signed product charge plus its complete original public residue. -/
abbrev ChargeTag := (Bool×(ℕ×ℕ×ℕ))×ℕ

/-- Every full quotient slot is charged once beside its original frame. -/
def frameCharges (j : ℕ) (f : EuclidFrame) : List ChargeTag :=
  (List.range (frameQuotient f)).map fun k =>
    ((f.negative,(f.smaller,f.currentWeight,k+1)),j)

theorem frameCharges_mem {j : ℕ} {f : EuclidFrame} {tag : ChargeTag}
    (ht : tag∈frameCharges j f) :
    tag.1.2.1=f.smaller ∧ tag.1.2.2.1=f.currentWeight ∧ tag.1.1=f.negative ∧
      tag.2=j ∧ 0<tag.1.2.2.2 ∧ tag.1.2.2.2≤frameQuotient f := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
  have hk' := List.mem_range.mp hk
  refine ⟨rfl,rfl,rfl,rfl,Nat.succ_pos k,?_⟩
  change k+1≤frameQuotient f
  omega

theorem frameCharges_nodup (j : ℕ) (f : EuclidFrame) : (frameCharges j f).Nodup := by
  apply List.nodup_range.map
  intro a b he
  have h := congrArg (fun tag : ChargeTag => tag.1.2.2.2) he
  change a+1=b+1 at h
  omega

theorem euclidFrameCharges_nodup (j r₀ r₁ x y : ℕ) (negative : Bool) :
    ((euclidFrames r₀ r₁ x y negative).flatMap (frameCharges j)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro f _
    exact frameCharges_nodup j f
  · apply (euclidFrames_strict r₀ r₁ x y negative).imp
    intro f g hfg tag hf hg
    have ha := (frameCharges_mem hf).1
    have hb := (frameCharges_mem hg).1
    rw [←ha,←hb] at hfg
    exact (Nat.lt_irrefl _) hfg

theorem frameCharges_length (j : ℕ) (f : EuclidFrame) :
    (frameCharges j f).length=frameQuotient f := by
  simp only [frameCharges,List.length_map,List.length_range]

theorem frameCharges_length_sum (j : ℕ) (fs : List EuclidFrame) :
    (fs.flatMap (frameCharges j)).length=(fs.map frameQuotient).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.flatMap_cons,List.length_append,frameCharges_length,
      List.map_cons,List.sum_cons,ih]

/-- The actual residue constructor retains its full division frames. -/
def residueFrames (N m j : ℕ) : List EuclidFrame :=
  euclidFrames m (quotientSlope N m j%m) 0 1 false

/-- Signed charge slots retain the complete public residue upstream. -/
def residueChargeTags (N m j : ℕ) : List ChargeTag :=
  (residueFrames N m j).flatMap (frameCharges j)

/-- The complete public unit-residue scan, before any count estimate. -/
def publicChargeTags (N m : ℕ) : List ChargeTag :=
  (List.range m).flatMap fun j => if j.Coprime m then residueChargeTags N m j else []

theorem residueChargeTags_length {N m j : ℕ} (hm : 0<m) :
    (residueChargeTags N m j).length=(publicPairs N m j).length := by
  unfold residueChargeTags residueFrames publicPairs
  rw [frameCharges_length_sum,←euclidPairs_length_eq_frameSum false (Nat.mod_lt _ hm)]

theorem residueChargeTags_residue {N m j : ℕ} {tag : ChargeTag}
    (ht : tag∈residueChargeTags N m j) : tag.2=j := by
  obtain ⟨f,_,ht⟩ := List.mem_flatMap.mp ht
  exact (frameCharges_mem ht).2.2.2.1

theorem publicChargeTags_nodup (N m : ℕ) : (publicChargeTags N m).Nodup := by
  unfold publicChargeTags
  apply List.nodup_flatMap.mpr
  constructor
  · intro j _
    by_cases hj : j.Coprime m
    · rw [if_pos hj]
      exact euclidFrameCharges_nodup j _ _ _ _ _
    · simp only [if_neg hj,List.nodup_nil]
  · apply List.nodup_range.imp
    intro a b hne tag ha hb
    dsimp only at ha hb
    split_ifs at ha hb with hca hcb
    · exact hne ((residueChargeTags_residue ha).symm.trans (residueChargeTags_residue hb))
    all_goals simp only [List.not_mem_nil] at *

private theorem length_flatMap_const {α β : Type*} (f : α → List β) (k : ℕ)
    (hf : ∀ x, (f x).length=k) (xs : List α) : (xs.flatMap f).length=k*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [hf,ih,Nat.mul_add,Nat.add_comm]

private theorem length_flatMap_mul {α β γ : Type*} (f : α → List β) (g : α → List γ)
    (k : ℕ) (hf : ∀ x, (f x).length=k*(g x).length) (xs : List α) :
    (xs.flatMap f).length=k*(xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,hf,ih,Nat.mul_add]

/-- Both original center packets are priced for every emitted vector. -/
theorem publicPackets_length_two_charges {N m : ℕ} (hm : 0<m) :
    (publicPackets N m).length=2*(publicChargeTags N m).length := by
  unfold publicPackets publicChargeTags
  apply length_flatMap_mul
  intro j
  by_cases hj : j.Coprime m
  · rw [if_pos hj,if_pos hj,residueChargeTags_length hm]
    exact length_flatMap_const _ 2 (by intro v; rfl) _
  · simp only [if_neg hj,List.length_nil,Nat.mul_zero]

/-- Every retained current frame is still an actual original public vector. -/
theorem residueFrames_current_mem {N m j : ℕ} {f : EuclidFrame}
    (hf : f∈residueFrames N m j) :
    (signed f.negative f.smaller,f.currentWeight)∈publicPairs N m j := by
  have h : (signed f.negative f.smaller,f.currentWeight)∈
      (residueFrames N m j).flatMap expandFrame :=
    List.mem_flatMap.mpr ⟨f,hf,List.mem_cons_self⟩
  rwa [residueFrames,euclidFrames_expand] at h

/-- The actual original quotient relation gives a quadratic equation for
the public residue. No unknown prime factor occurs in this equation. -/
theorem residueFrame_square_eq {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m)
    {f : EuclidFrame} (hf : f∈residueFrames N m j) :
    (signed f.negative f.smaller : ZMod m)*(j : ZMod m)^2=
      (N : ZMod m)*(f.currentWeight : ZMod m) := by
  have hc := (publicPairs_correct hm (residueFrames_current_mem hf)).2.2
  have he : (signed f.negative f.smaller : ZMod m)=
      (N : ZMod m)*(publicInverse m j : ZMod m)^2*(f.currentWeight : ZMod m) := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ m).mpr hc
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_natCast] using h
  have hi : (j : ZMod m)*(publicInverse m j : ZMod m)=1 := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ m).mpr (publicInverse_correct hj)
    simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_one] using h
  calc
    _ = ((N : ZMod m)*(publicInverse m j : ZMod m)^2*(f.currentWeight : ZMod m))*
        (j : ZMod m)^2 := by rw [he]
    _ = (N : ZMod m)*(f.currentWeight : ZMod m)*
        ((j : ZMod m)*(publicInverse m j : ZMod m))^2 := by ring
    _ = _ := by rw [hi,one_pow,mul_one]

/-- Candidate residues for one retained signed current-frame coordinate. -/
def squareFiber (N m : ℕ) (negative : Bool) (a t : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun j =>
    (signed negative a : ZMod m)*(j : ZMod m)^2=(N : ZMod m)*(t : ZMod m)

theorem squareFiber_mem_iff {N m a t j : ℕ} {negative : Bool} :
    j∈squareFiber N m negative a t ↔ j<m ∧
      (signed negative a : ZMod m)*(j : ZMod m)^2=(N : ZMod m)*(t : ZMod m) := by
  simp only [squareFiber,Finset.mem_filter,Finset.mem_range]

/-- A public prime modulus gives at most two residues per signed charge.
The unknown factors and even coprimality of N are absent from the bound. -/
theorem squareFiber_card_le {N m a t : ℕ} (hm : m.Prime) (ha : 0<a) (ham : a<m)
    (negative : Bool) : (squareFiber N m negative a t).card≤2 := by
  let : Fact m.Prime := ⟨hm⟩
  have hna : (a : ZMod m)≠0 := by
    intro hz
    have h := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt ham,ZMod.val_zero] at h
    omega
  have hsa : (signed negative a : ZMod m)≠0 := by
    cases negative <;> simpa [signed] using hna
  by_cases he : (squareFiber N m negative a t).Nonempty
  · obtain ⟨j₀,hj₀⟩ := he
    obtain ⟨hj₀m,hj₀e⟩ := squareFiber_mem_iff.mp hj₀
    have hsub : squareFiber N m negative a t⊆{j₀,(-(j₀ : ZMod m)).val} := by
      intro j hj
      obtain ⟨hjm,hje⟩ := squareFiber_mem_iff.mp hj
      have hs : (j : ZMod m)^2=(j₀ : ZMod m)^2 :=
        mul_left_cancel₀ hsa (hje.trans hj₀e.symm)
      have hz : ((j : ZMod m)-(j₀ : ZMod m))*((j : ZMod m)+(j₀ : ZMod m))=0 := by
        linear_combination hs
      rcases mul_eq_zero.mp hz with hz|hz
      · have h := congrArg ZMod.val (sub_eq_zero.mp hz)
        rw [ZMod.val_natCast_of_lt hjm,ZMod.val_natCast_of_lt hj₀m] at h
        exact Finset.mem_insert.mpr (Or.inl h)
      · have h : (j : ZMod m)=-(j₀ : ZMod m) := by
          calc (j : ZMod m)=((j : ZMod m)+(j₀ : ZMod m))-(j₀ : ZMod m) := by ring
               _=-(j₀ : ZMod m) := by rw [hz,zero_sub]
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hjm] at hv
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hv))
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    omega

/-- A mathematical charge envelope; the algorithm never builds this cube. -/
def positiveTriples (m : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  ((Finset.Icc 1 m)×ˢ((Finset.Icc 1 m)×ˢ(Finset.Icc 1 m))).filter
    fun v => v.1*v.2.1*v.2.2≤m

theorem positiveTriples_mem_iff {m : ℕ} {v : ℕ×ℕ×ℕ} :
    v∈positiveTriples m ↔ 0<v.1 ∧ v.1≤m ∧ 0<v.2.1 ∧ v.2.1≤m ∧
      0<v.2.2 ∧ v.2.2≤m ∧ v.1*v.2.1*v.2.2≤m := by
  simp only [positiveTriples,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
    Nat.succ_le_iff,and_assoc]

/-- A dyadic box prices its last coordinate by the minimum first product. -/
def dyadicBox (m i j : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  (Finset.Ico (2^i) (2^(i+1)))×ˢ
    ((Finset.Ico (2^j) (2^(j+1)))×ˢ(Finset.Icc 1 (m/(2^i*2^j))))

theorem dyadicBox_card_le (m i j : ℕ) : (dyadicBox m i j).card≤m := by
  rw [dyadicBox,Finset.card_product,Finset.card_product,Nat.card_Ico,Nat.card_Ico,Nat.card_Icc]
  have hi : 2^(i+1)-2^i=2^i := by rw [pow_succ,Nat.mul_two,Nat.add_sub_cancel]
  have hj : 2^(j+1)-2^j=2^j := by rw [pow_succ,Nat.mul_two,Nat.add_sub_cancel]
  rw [hi,hj,Nat.add_sub_cancel]
  calc
    _ = (m/(2^i*2^j))*(2^i*2^j) := by ring
    _ ≤ m := Nat.div_mul_le_self _ _

/-- Each logarithmic fiber is contained in one box of cardinal at most m. -/
theorem triple_fiber_subset_box (m i j : ℕ) :
    {v∈positiveTriples m | (Nat.log2 v.1,Nat.log2 v.2.1)=(i,j)}⊆dyadicBox m i j := by
  intro v hv
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  obtain ⟨ha,_,ht,_,hk,_,hprod⟩ := positiveTriples_mem_iff.mp hv
  have hi : Nat.log2 v.1=i := congrArg Prod.fst he
  have hj : Nat.log2 v.2.1=j := congrArg Prod.snd he
  have hia : 2^i≤v.1 := by
    rw [←hi,Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 ha.ne'
  have hit : v.1<2^(i+1) := by
    rw [←hi,Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hja : 2^j≤v.2.1 := by
    rw [←hj,Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 ht.ne'
  have hjt : v.2.1<2^(j+1) := by
    rw [←hj,Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hlast : v.2.2≤m/(2^i*2^j) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      _ = (2^i*2^j)*v.2.2 := by ring
      _ ≤ (v.1*v.2.1)*v.2.2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hia hja)
      _ ≤ m := hprod
  exact Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hia,hit⟩,
    Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hja,hjt⟩,
      Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hk,hlast⟩⟩⟩

/-- The complete positive triple envelope is m times a squared logarithm. -/
theorem positiveTriples_card_le (m : ℕ) :
    (positiveTriples m).card≤m*(Nat.log2 m+1)^2 := by
  let labels := (Finset.range (Nat.log2 m+1))×ˢ(Finset.range (Nat.log2 m+1))
  have hmap : Set.MapsTo (fun v : ℕ×ℕ×ℕ => (Nat.log2 v.1,Nat.log2 v.2.1))
      (positiveTriples m) labels := by
    intro v hv
    obtain ⟨_,ham,_,htm,_,_,_⟩ := positiveTriples_mem_iff.mp hv
    have hi : Nat.log2 v.1≤Nat.log2 m := by
      rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
      exact Nat.log_mono_right ham
    have hj : Nat.log2 v.2.1≤Nat.log2 m := by
      rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
      exact Nat.log_mono_right htm
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hj)⟩
  calc
    (positiveTriples m).card = ∑ label∈labels,
        {v∈positiveTriples m | (Nat.log2 v.1,Nat.log2 v.2.1)=label}.card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _label∈labels, m := by
      apply Finset.sum_le_sum
      intro label _
      exact (Finset.card_le_card (triple_fiber_subset_box m label.1 label.2)).trans
        (dyadicBox_card_le m label.1 label.2)
    _ = m*(Nat.log2 m+1)^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul,labels,Finset.card_product,Finset.card_range]
      norm_cast
      ring

/-- Actual current remainders are strictly below the public modulus. -/
def chargeTriples (m : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  (positiveTriples m).filter fun v => v.1<m

/-- Keep both frame orientations in the counting carrier. -/
def chargeBases (m : ℕ) : Finset (Bool×(ℕ×ℕ×ℕ)) := Finset.univ×ˢchargeTriples m

/-- A finite mathematical envelope for every actual complete public charge. -/
def allowedCharges (N m : ℕ) : Finset ChargeTag :=
  (chargeBases m).biUnion fun base =>
    (squareFiber N m base.1 base.2.1 base.2.2.1).image fun j => (base,j)

/-- Every charged slot is bounded using the actual public recursive
determinant and quotient-class invariants, not a row-selection oracle. -/
theorem publicChargeTag_allowed {N m : ℕ} (hm : 0<m) {tag : ChargeTag}
    (ht : tag∈publicChargeTags N m) : tag∈allowedCharges N m := by
  obtain ⟨j,hjm,ht⟩ := List.mem_flatMap.mp ht
  change tag∈(if j.Coprime m then residueChargeTags N m j else []) at ht
  by_cases hj : j.Coprime m
  · rw [if_pos hj] at ht
    obtain ⟨f,hf,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
    have hkq := List.mem_range.mp hk
    have hfit := euclidFrames_fit (m:=m) (Nat.mod_lt _ hm) (by decide)
      (by simp) hf
    have hbound := euclidFrames_remainder_bound hf
    have ham : f.smaller<m := hbound.2.trans_lt (Nat.mod_lt _ hm)
    have hprod := frame_charge_product hfit.2.2.2 hkq
    have htm : f.currentWeight≤m :=
      (Nat.le_mul_of_pos_left _ hfit.1).trans
        ((Nat.le_mul_of_pos_right _ (Nat.succ_pos k)).trans hprod)
    have hkm : k+1≤m :=
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos hfit.1 hfit.2.1)).trans hprod
    have htriple : (f.smaller,f.currentWeight,k+1)∈chargeTriples m :=
      Finset.mem_filter.mpr ⟨positiveTriples_mem_iff.mpr
        ⟨hfit.1,ham.le,hfit.2.1,htm,Nat.succ_pos k,hkm,hprod⟩,ham⟩
    have hbase : (f.negative,(f.smaller,f.currentWeight,k+1))∈chargeBases m :=
      Finset.mem_product.mpr ⟨Finset.mem_univ _,htriple⟩
    have hjfiber : j∈squareFiber N m f.negative f.smaller f.currentWeight :=
      squareFiber_mem_iff.mpr ⟨List.mem_range.mp hjm,residueFrame_square_eq hm hj hf⟩
    exact Finset.mem_biUnion.mpr ⟨_,hbase,Finset.mem_image.mpr ⟨j,hjfiber,rfl⟩⟩
  · simp only [if_neg hj,List.not_mem_nil] at ht

theorem chargeTriples_card_le (m : ℕ) :
    (chargeTriples m).card≤m*(Nat.log2 m+1)^2 :=
  (Finset.card_filter_le _ _).trans (positiveTriples_card_le m)

/-- All residues and both signed frame orientations cost at most four
times the triple envelope at a public prime modulus. -/
theorem allowedCharges_card_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (allowedCharges N m).card≤4*m*(Nat.log2 m+1)^2 := by
  have hb : (chargeBases m).card=2*(chargeTriples m).card := by
    simp only [chargeBases,Finset.card_product,Finset.card_univ,Fintype.card_bool]
  calc
    (allowedCharges N m).card ≤ ∑ base∈chargeBases m,
        ((squareFiber N m base.1 base.2.1 base.2.2.1).image fun j => (base,j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _base∈chargeBases m, 2 := by
      apply Finset.sum_le_sum
      intro base hbase
      have ht := (Finset.mem_product.mp hbase).2
      obtain ⟨ht,ham⟩ := Finset.mem_filter.mp ht
      have ha := (positiveTriples_mem_iff.mp ht).1
      exact Finset.card_image_le.trans (squareFiber_card_le hm ha ham base.1)
    _ = 2*(chargeBases m).card := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      norm_cast
      ring
    _ ≤ 4*m*(Nat.log2 m+1)^2 := by
      rw [hb]
      calc
        _ = 4*(chargeTriples m).card := by ring
        _ ≤ 4*(m*(Nat.log2 m+1)^2) := Nat.mul_le_mul_left 4 (chargeTriples_card_le m)
        _ = _ := by ring

/-- The complete literal original packet constructor has a uniform
linear-modulus, squared-logarithm count, including every intermediate
row and both centers, for every N at every public prime modulus. -/
theorem publicPackets_length_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (publicPackets N m).length≤8*m*(Nat.log2 m+1)^2 := by
  have hsub : (publicChargeTags N m).toFinset⊆allowedCharges N m := by
    intro tag ht
    exact publicChargeTag_allowed hm.pos (List.mem_toFinset.mp ht)
  calc
    (publicPackets N m).length=2*(publicChargeTags N m).toFinset.card := by
      rw [publicPackets_length_two_charges hm.pos,
        List.toFinset_card_of_nodup (publicChargeTags_nodup N m)]
    _ ≤ 2*(allowedCharges N m).card := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)
    _ ≤ 2*(4*m*(Nat.log2 m+1)^2) := Nat.mul_le_mul_left 2 (allowedCharges_card_le N hm)
    _ = _ := by ring

open SemiprimeCompanionRows SemiprimeCompanionCoverage SemiprimeCartesianCompletion

/-- Filtering the complete weighted construction preserves its count bound. -/
theorem publicCompanions_length_prime_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (publicCompanions N m).length≤16*m*(Nat.log2 m+1)^2 := by
  calc
    _ ≤ 2*(publicPackets N m).length := publicCompanions_length_le N m
    _ ≤ 2*(8*m*(Nat.log2 m+1)^2) := Nat.mul_le_mul_left 2 (publicPackets_length_le N hm)
    _ = _ := by ring

/-- Whole-modulus deduplication is downstream of the retained integer list. -/
theorem publicCompanionRoots_card_prime_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (publicCompanionRoots N m).card≤16*m*(Nat.log2 m+1)^2 := by
  calc
    _ ≤ 2*(publicPackets N m).length := publicCompanionRoots_card_le N m
    _ ≤ 2*(8*m*(Nat.log2 m+1)^2) := Nat.mul_le_mul_left 2 (publicPackets_length_le N hm)
    _ = _ := by ring

/-- Adding both signs and zero still keeps only linearly many roots. -/
theorem signedCompanionRoots_card_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (signedRoots (publicCompanionRoots N m)).card≤32*m*(Nat.log2 m+1)^2+1 := by
  calc
    _ ≤ 2*(publicCompanionRoots N m).card+1 := signedRoots_card_le _
    _ ≤ 2*(16*m*(Nat.log2 m+1)^2)+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (publicCompanionRoots_card_prime_le N hm)) 1
    _ = _ := by ring

/-- The original endpoint and derivative source has a uniform GCD-query
bound. A query count does not price construction or polynomial bit work. -/
theorem recoverCompanionRows_gcd_prime_bound (N : ℕ) {m : ℕ} (hm : m.Prime) :
    scanGcdCount N ((publicCompanionRoots N m).toList.map ZMod.val)+
      recoveryGcdCount N (fun i => residueLeaves (publicCompanionRoots N m) (i : ZMod N))
        (evaluatedColumns (publicCompanionRoots N m) (publicCompanionRoots N m).toList)≤
          48*m*(Nat.log2 m+1)^2 := by
  calc
    _ ≤ 6*(publicPackets N m).length := recoverCompanionRows_gcd_bound N m
    _ ≤ 6*(8*m*(Nat.log2 m+1)^2) := Nat.mul_le_mul_left 6 (publicPackets_length_le N hm)
    _ = _ := by ring

/-- The zero anchor combines the complete original hit union in one
derivative with at most the stated number of recovery GCD queries. -/
theorem recoverAnchoredCompanions_gcd_prime_bound (N : ℕ) {m : ℕ} (hm : m.Prime) :
    recoveryGcdCount N
      (fun i => residueLeaves (anchoredRoots (publicCompanionRoots N m)) (i : ZMod N))
      (evaluatedColumns (anchoredRoots (publicCompanionRoots N m))
        (anchoredRoots (publicCompanionRoots N m)).toList)≤
      32*m*(Nat.log2 m+1)^2+2 := by
  calc
    _ ≤ 4*(publicPackets N m).length+2 := recoverAnchoredCompanions_gcd_bound N m
    _ ≤ 4*(8*m*(Nat.log2 m+1)^2)+2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 4 (publicPackets_length_le N hm)) 2
    _ = _ := by ring

/-- The full signed sum/difference/endpoint source has a uniform recovery
GCD-query bound; universal useful hits and its full bit clock are separate. -/
theorem recoverSignedCompanions_gcd_prime_bound (N : ℕ) {m : ℕ} (hm : m.Prime) :
    recoveryGcdCount N
      (fun i => residueLeaves (signedRoots (publicCompanionRoots N m)) (i : ZMod N))
      (evaluatedColumns (signedRoots (publicCompanionRoots N m))
        (signedRoots (publicCompanionRoots N m)).toList)≤
      64*m*(Nat.log2 m+1)^2+2 := by
  calc
    _ ≤ 8*(publicPackets N m).length+2 := recoverSignedCompanions_gcd_bound N m
    _ ≤ 8*(8*m*(Nat.log2 m+1)^2)+2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 8 (publicPackets_length_le N hm)) 2
    _ = _ := by ring

/-- A prime in a public doubled window gives a bound in the public scale B. -/
theorem publicPackets_length_window_le (N : ℕ) {m B : ℕ}
    (hm : m.Prime) (hbound : m≤2*B) :
    (publicPackets N m).length≤16*B*(Nat.log2 (2*B)+1)^2 := by
  have hlog : Nat.log2 m≤Nat.log2 (2*B) := by
    simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) hbound)
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hlog 1) 2
  calc
    _ ≤ 8*m*(Nat.log2 m+1)^2 := publicPackets_length_le N hm
    _ ≤ 8*(2*B)*(Nat.log2 (2*B)+1)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 hbound) hpow
    _ = _ := by ring

/-- Existence for the public least-prime search uses no factor of N. -/
theorem existsPublicPrime (B : ℕ) (hB : 0<B) : ∃ m, m.Prime ∧ B≤m := by
  obtain ⟨m,hm,hBm,_⟩ := Nat.exists_prime_lt_and_le_two_mul B (Nat.ne_of_gt hB)
  exact ⟨m,hm,hBm.le⟩

/-- The least prime at least the public scale B. Its definition is a
search, not an input prime or a priced acquisition certificate. -/
def publicPrimeAtLeast (B : ℕ) (hB : 0<B) : ℕ := Nat.find (existsPublicPrime B hB)

theorem publicPrimeAtLeast_prime (B : ℕ) (hB : 0<B) :
    (publicPrimeAtLeast B hB).Prime := (Nat.find_spec (existsPublicPrime B hB)).1

theorem publicPrimeAtLeast_ge (B : ℕ) (hB : 0<B) :
    B≤publicPrimeAtLeast B hB := (Nat.find_spec (existsPublicPrime B hB)).2

theorem publicPrimeAtLeast_minimal (B : ℕ) (hB : 0<B) {m : ℕ}
    (hm : m.Prime) (hBm : B≤m) : publicPrimeAtLeast B hB≤m :=
  Nat.find_min' (existsPublicPrime B hB) ⟨hm,hBm⟩

/-- The literal least-prime selector lies in the doubled public window.
This is a search-range theorem, not a bit bound for primality testing. -/
theorem publicPrimeAtLeast_le (B : ℕ) (hB : 0<B) :
    publicPrimeAtLeast B hB≤2*B := by
  obtain ⟨m,hm,hBm,hmB⟩ := Nat.exists_prime_lt_and_le_two_mul B (Nat.ne_of_gt hB)
  exact (publicPrimeAtLeast_minimal B hB hm hBm.le).trans hmB

/-- The complete original row count at the public least-prime selector
has a linear-scale squared-logarithm envelope for every N. -/
theorem publicPackets_publicPrime_length_le (N B : ℕ) (hB : 0<B) :
    (publicPackets N (publicPrimeAtLeast B hB)).length≤
      16*B*(Nat.log2 (2*B)+1)^2 :=
  publicPackets_length_window_le N (publicPrimeAtLeast_prime B hB) (publicPrimeAtLeast_le B hB)

/-- Use the existing literal ceiling-sixth-root width, with a public
positive fallback at zero. Primality itself excludes candidates below two. -/
def publicRowModulus (N : ℕ) : ℕ :=
  publicPrimeAtLeast (max 1 (SemiprimeLehmanCoverage.sixthWidth N))
    (lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _))

theorem publicRowModulus_prime (N : ℕ) : (publicRowModulus N).Prime :=
  publicPrimeAtLeast_prime _ _

/-- Positive inputs use their actual ceiling-sixth-root width, and the
least-prime selector lies between that width and twice that width. -/
theorem publicRowModulus_bounds {N : ℕ} (hN : 0<N) :
    SemiprimeLehmanCoverage.sixthWidth N≤publicRowModulus N ∧
      publicRowModulus N≤2*SemiprimeLehmanCoverage.sixthWidth N := by
  have hwidth : 0<SemiprimeLehmanCoverage.sixthWidth N := by
    have hu := SemiprimeLehmanCoverage.sixthWidth_upper N
    by_contra hn
    have he : SemiprimeLehmanCoverage.sixthWidth N=0 := by omega
    rw [he] at hu
    norm_num at hu
    omega
  have hm : max 1 (SemiprimeLehmanCoverage.sixthWidth N)=
      SemiprimeLehmanCoverage.sixthWidth N := max_eq_right hwidth
  constructor
  · simpa only [publicRowModulus,hm] using
      (publicPrimeAtLeast_ge (max 1 (SemiprimeLehmanCoverage.sixthWidth N))
        (lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)))
  · simpa only [publicRowModulus,hm] using
      (publicPrimeAtLeast_le (max 1 (SemiprimeLehmanCoverage.sixthWidth N))
        (lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)))

/-- All original rows at the literal N-only public modulus have a uniform
ceiling-sixth-root count. This count is independent of useful hit coverage. -/
theorem publicPackets_publicRowModulus_length_le {N : ℕ} (hN : 0<N) :
    (publicPackets N (publicRowModulus N)).length≤
      16*SemiprimeLehmanCoverage.sixthWidth N*
        (Nat.log2 (2*SemiprimeLehmanCoverage.sixthWidth N)+1)^2 :=
  publicPackets_length_window_le N (publicRowModulus_prime N) (publicRowModulus_bounds hN).2

end RiemannGaussian.SemiprimeEuclidRowBudget
