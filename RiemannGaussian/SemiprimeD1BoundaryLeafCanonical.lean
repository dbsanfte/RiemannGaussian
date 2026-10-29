/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeaf
import RiemannGaussian.SemiprimeD1BoundaryRecordsCanonical
import RiemannGaussian.SemiprimeD1BoundaryChoice

/-! # Canonical full-jet output of the actual boundary leaf -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafCanonical
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecordsCanonical
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTables (GoodWords)

/-- A paid join retains every actual input address record. -/
theorem attach_nonempty (ctx : Context) (source target : List Nat) (acc table : List Entry)
    (h : acc≠[]) : (attach ctx source target acc table).value≠[] := by
  intro he
  have hl:=attach_length ctx source target acc table
  rw [he,List.length_nil] at hl
  exact h (List.eq_nil_of_length_eq_zero hl.symm)

/-- Each sequential vertex multiplication preserves a full canonical tensor. -/
theorem multiplyVertices_good (ctx : Context) (ports : List Nat) (vs : List Vertex)
    (acc : List Entry) (h : GoodEntries ctx acc) :
    GoodEntries ctx (multiplyVertices ctx ports vs acc).value := by
  induction vs generalizing acc with
  | nil => exact h
  | cons v vs ih => exact ih _ (attach_good ctx ports v.ports acc _)

/-- Local vertex products keep the unique empty assignment of isolated classes. -/
theorem multiplyVertices_nonempty (ctx : Context) (ports : List Nat) (vs : List Vertex)
    (acc : List Entry) (h : acc≠[]) : (multiplyVertices ctx ports vs acc).value≠[] := by
  induction vs generalizing acc with
  | nil => exact h
  | cons v vs ih => exact ih _ (attach_nonempty ctx ports v.ports acc _ h)

/-- Every actual class boundary entry is canonical, including empty classes/p0. -/
theorem bucket_good (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph)
    (vs : List Vertex) (colours : List Nat) (c : Nat) :
    GoodEntries ctx (bucket ctx g vs colours c).value.entries :=
  contract_good ctx _ _ _ (multiplyVertices_good ctx _ _ _ (seed_good ctx _))

/-- A class always retains at least its actual scalar/boundary assignment. -/
theorem bucket_nonempty (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph)
    (vs : List Vertex) (colours : List Nat) (c : Nat) :
    (bucket ctx g vs colours c).value.entries≠[] :=
  contract_nonempty ctx _ _ _ (multiplyVertices_nonempty ctx _ _ _ (seed_nonempty ctx _))

/-- Both real table joins and equal-address sum preserve the complete jet. -/
theorem merge_good (ctx : Context) (left right : Tensor) :
    GoodEntries ctx (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries :=
  contract_good ctx _ _ _ (attach_good ctx _ _ _ _)

/-- Every consecutive merge has at least one actual output address. -/
theorem merge_nonempty (ctx : Context) (left right : Tensor) :
    (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries≠[] :=
  contract_nonempty ctx _ _ _ (attach_nonempty ctx _ _ _ _
    (attach_nonempty ctx _ _ _ _ (seed_nonempty ctx _)))

/-- The consecutive merge chain retains canonical shape at every step. -/
theorem mergeAll_good (ctx : Context) (first : Tensor) (rest : List Tensor)
    (h : GoodEntries ctx first.entries) : GoodEntries ctx (mergeAll ctx first rest).value.entries := by
  induction rest generalizing first with
  | nil => exact h
  | cons t ts ih => exact ih _ (merge_good ctx first t)

/-- Empty final boundary still has a scalar entry, never an empty result vector. -/
theorem mergeAll_nonempty (ctx : Context) (first : Tensor) (rest : List Tensor)
    (h : first.entries≠[]) : (mergeAll ctx first rest).value.entries≠[] := by
  induction rest generalizing first with
  | nil => exact h
  | cons t ts ih => exact ih _ (merge_nonempty ctx first t)

/-- The acquired colour count produces a real first bucket, without width advice. -/
theorem buckets_nonempty (ctx : Context) (net : Network) :
    ((List.range (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).k).map
      (bucket ctx (SemiprimeD1BoundaryPlan.graph net) (SemiprimeD1TensorNetwork.vertices net)
        (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).colours))≠[] := by
  have hk:=(SemiprimeD1BoundaryChoice.chooseK_bounds (SemiprimeD1BoundaryPlan.graph net)).1
  intro h
  have hz := List.map_eq_nil_iff.mp h
  have hk0 := List.range_eq_nil.mp hz
  change SemiprimeD1BoundaryPlan.chooseK (SemiprimeD1BoundaryPlan.graph net)=0 at hk0
  omega

/-- A nonempty list's defaulted head is an actual member, independent of default. -/
theorem headD_member {α : Type} (xs : List α) (fallback : α) (h : xs≠[]) : xs.headD fallback∈xs := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs => exact List.mem_cons_self

/-- The concrete complete source acquires canonical entries and a nonempty tensor. -/
theorem acquire_tensor (ctx : Context) (net : Network) :
    GoodEntries ctx (acquire ctx net).tensor.entries ∧ (acquire ctx net).tensor.entries≠[] := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  let bs:=(List.range plan.k).map (bucket ctx g vs plan.colours)
  have hbs : bs≠[] := buckets_nonempty ctx net
  have hhead:=headD_member bs ⟨⟨[],[]⟩,1⟩ hbs
  obtain ⟨c,_,hc⟩:=List.mem_map.mp hhead
  have hg : GoodEntries ctx (bs.headD ⟨⟨[],[]⟩,1⟩).value.entries := by
    rw [←hc]
    exact bucket_good ctx g vs plan.colours c
  have hn : (bs.headD ⟨⟨[],[]⟩,1⟩).value.entries≠[] := by
    rw [←hc]
    exact bucket_nonempty ctx g vs plan.colours c
  exact ⟨mergeAll_good ctx _ _ hg,mergeAll_nonempty ctx _ _ hn⟩

/-- Final word extraction is a paid exact copy of the actual final record. -/
theorem acquire_words (ctx : Context) (net : Network) :
    (acquire ctx net).result.words=((acquire ctx net).tensor.entries.headD ⟨[],[]⟩).words :=
  SemiprimeD1JetAxes.copyVector_value _

/-- The closed source derives full shape/compactness/current-width itself.
This includes the rank-one zero-precision ring and arbitrarily many unit axes. -/
theorem run_good (ctx : Context) (net : Network) : GoodWords ctx (run ctx net).words := by
  have ht:=acquire_tensor ctx net
  have hm:=headD_member (acquire ctx net).tensor.entries ⟨[],[]⟩ ht.2
  change GoodWords ctx (acquire ctx net).result.words
  rw [acquire_words]
  exact ht.1 _ hm

/-- Paid malformed-input fallback also preserves canonical current-context words. -/
theorem checked_good (ctx : Context) (net : Network) : GoodWords ctx (checked ctx net).words := by
  simp only [checked]
  split
  · exact run_good ctx net
  · rw [SemiprimeD1TensorTapeLeaf.leaf_words]
    exact SemiprimeD1LeafCounterBounds.run_good _ _ _

end RiemannGaussian.SemiprimeD1BoundaryLeafCanonical
