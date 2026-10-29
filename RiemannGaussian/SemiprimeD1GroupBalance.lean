/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1SelectedLoadBounds

/-! # Actual selected coordinate-group real-port balance
Uniform finite label fibres are proved by explicit colour permutations. No
complete label catalogue is executed, and parallel ports retain multiplicity.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1GroupBalance
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeSourceHistogramGrouping SemiprimeD1CollisionOriginal
open SemiprimeD1SelectedCollision SemiprimeD1SelectedLoadBounds

/-- Head or factor coordinate colour of a complete original pair label. -/
def colour (r a : ℕ) (head : Bool) (q : Fin a) (label : Word r a×Word r a) : Fin r :=
  if head then label.1 q else label.2 q

/-- Pointwise colour swap is an actual bijection of complete pair labels. -/
def swapLabels (r a : ℕ) (head : Bool) (c d : Fin r) (label : Word r a×Word r a) :
    Word r a×Word r a :=
  if head then (fun j => Equiv.swap c d (label.1 j),label.2)
  else (label.1,fun j => Equiv.swap c d (label.2 j))

/-- The label transformation is its own inverse. -/
theorem swapLabels_involutive (r a : ℕ) (head : Bool) (c d : Fin r) (label : Word r a×Word r a) :
    swapLabels r a head c d (swapLabels r a head c d label)=label := by
  cases head <;> ext j <;> simp [swapLabels,Equiv.swap_apply_self]

/-- Every coordinate-colour fibre is explicitly equivalent to every other one. -/
def fibreEquiv (r a : ℕ) (head : Bool) (q : Fin a) (c d : Fin r) :
    {label : Word r a×Word r a // colour r a head q label=c} ≃
      {label : Word r a×Word r a // colour r a head q label=d} where
  toFun label := ⟨swapLabels r a head c d label.val,by
    have h:=label.property
    cases head <;> simp only [colour,swapLabels,Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;>
      rw [h,Equiv.swap_apply_left]⟩
  invFun label := ⟨swapLabels r a head c d label.val,by
    have h:=label.property
    cases head <;> simp only [colour,swapLabels,Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;>
      rw [h,Equiv.swap_apply_right]⟩
  left_inv label := Subtype.ext (swapLabels_involutive _ _ _ _ _ _)
  right_inv label := Subtype.ext (swapLabels_involutive _ _ _ _ _ _)

/-- Exactly1/r of ALL pair labels have a specified coordinate colour. -/
theorem fibre_card (r a : ℕ) (head : Bool) (q : Fin a) (c : Fin r) :
    r*Fintype.card {label : Word r a×Word r a // colour r a head q label=c}=r^(2*a) := by
  have hc (d : Fin r) :
      Fintype.card {label : Word r a×Word r a // colour r a head q label=d}=
        Fintype.card {label : Word r a×Word r a // colour r a head q label=c} :=
    Fintype.card_congr (fibreEquiv r a head q d c)
  have ht:=Fintype.card_congr (Equiv.sigmaFiberEquiv (colour r a head q))
  rw [Fintype.card_sigma,card_labels] at ht
  simpa only [hc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using ht

/-- Literal original occurrence count in one group, not a deduplicated vertex count. -/
def groupCount {I K C : Type*} [DecidableEq C] (xs : List I) (key : I→K) (group : K→C) (c : C) : ℕ :=
  xs.countP (fun i => decide (group (key i)=c))

/-- Group counts are the sum of actual complete-label loads in that fibre. -/
theorem sum_fibre_loads {I K C : Type*} [Fintype K] [DecidableEq K] [DecidableEq C]
    (xs : List I) (key : I→K) (group : K→C) (c : C) :
    (∑label : {k : K // group k=c},multiplicity key xs label.val)=groupCount xs key group c := by
  induction xs with
  | nil => simp [SemiprimeSourceHistogramGrouping.multiplicity,groupCount]
  | cons i xs ih =>
    simp only [SemiprimeSourceHistogramGrouping.multiplicity,List.countP_cons,Finset.sum_add_distrib] at *
    rw [ih]
    by_cases h : group (key i)=c
    · let label : {k : K // group k=c}:=⟨key i,h⟩
      have he : (fun k : {k : K // group k=c} => if key i=k.val then (1:ℕ) else 0)=
          (fun k => if label=k then 1 else 0) := by
        funext k
        simp only [Subtype.ext_iff,label]
      simp only [decide_eq_true_eq,he,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      simp [groupCount,h,Nat.add_comm]
    · have he : ∀k : {k : K // group k=c},key i≠k.val := by
        intro k he
        exact h (he ▸ k.property)
      simp [he,groupCount,h]

/-- Actual uniform fibre size and computed label loads imply group balance. -/
theorem group_count_le {I K C : Type*} [Fintype K] [DecidableEq K] [DecidableEq C]
    (xs : List I) (key : I→K) (group : K→C) (c : C) (r D B : ℕ)
    (hD : 0<D) (hcard : r*Fintype.card {k : K // group k=c}=D)
    (hload : ∀label,D*multiplicity key xs label≤B) :
    r*groupCount xs key group c≤B := by
  have hs:=Finset.sum_le_sum (fun (label : {k : K // group k=c}) (_ : label∈Finset.univ) =>
    hload label.val)
  rw [←Finset.mul_sum,sum_fibre_loads] at hs
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at hs
  have hpos : 0<Fintype.card {k : K // group k=c} := by
    by_contra h
    have hz : Fintype.card {k : K // group k=c}=0 := by omega
    rw [hz,Nat.mul_zero] at hcard
    omega
  have hh : Fintype.card {k : K // group k=c}*(r*groupCount xs key group c)≤
      Fintype.card {k : K // group k=c}*B := by
    rw [←hcard] at hs
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs
  exact Nat.le_of_mul_le_mul_left hh hpos

/-- Actual selected owner/factor real-port count for one coordinate group. -/
def selectedGroupCount (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (head : Bool) (q : Fin a) (c : Fin r) : ℕ :=
  groupCount (ports n F a arity) (selectedLabel n F r a arity owner) (colour r a head q) c

/-- Both actual original endpoint namespaces satisfy the stronger2M/r bound. -/
theorem selected_group_le (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length)
    (head : Bool) (q : Fin a) (c : Fin r) :
    r*selectedGroupCount n F r a arity owner head q c≤2*(ports n F a arity).length := by
  unfold selectedGroupCount
  apply group_count_le _ _ _ _ r (r^(2*a)) (2*(ports n F a arity).length)
  · exact pow_pos (NeZero.pos r) _
  · exact fibre_card r a head q c
  · intro label
    exact selected_load_nat_le n F r a arity owner Δ ho hf hsmall label

/-- The actual two-sided group port total is bounded by4M/r. -/
theorem selected_both_le (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length) (q : Fin a) (c : Fin r) :
    r*(selectedGroupCount n F r a arity owner true q c+
      selectedGroupCount n F r a arity owner false q c)≤4*(ports n F a arity).length := by
  have hh:=selected_group_le n F r a arity owner Δ ho hf hsmall true q c
  have ht:=selected_group_le n F r a arity owner Δ ho hf hsmall false q c
  rw [Nat.mul_add]
  omega

/-- With the literal64 groups the two-sided real-port total already shrinks by16.
An actual child graph still needs its separate edge-to-retained-port proof. -/
theorem selected64_shrink (n F a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(64^(2*a))^2*Δ≤(ports n F a arity).length) (q : Fin a) (c : Fin 64) :
    16*(selectedGroupCount n F 64 a arity owner true q c+
      selectedGroupCount n F 64 a arity owner false q c)≤(ports n F a arity).length := by
  have h:=selected_both_le n F 64 a arity owner Δ ho hf hsmall q c
  omega

/-- The same actual group counts satisfy D.1's conservative factor8 shrink. -/
theorem selected64_eighth (n F a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(64^(2*a))^2*Δ≤(ports n F a arity).length) (q : Fin a) (c : Fin 64) :
    8*(selectedGroupCount n F 64 a arity owner true q c+
      selectedGroupCount n F 64 a arity owner false q c)≤(ports n F a arity).length := by
  have h:=selected64_shrink n F a arity owner Δ ho hf hsmall q c
  omega

end RiemannGaussian.SemiprimeD1GroupBalance
