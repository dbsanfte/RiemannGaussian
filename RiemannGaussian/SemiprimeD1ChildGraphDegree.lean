/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraphBounds

/-! # Original old-vertex degree control for the actual child graph
Only selected old endpoints are emitted. Packet grouping preserves exact endpoint
predicate multiplicities. Inactive/isolated vertices remain on the common side;
the future tensor-entry builder must assign inactive old tensors the scalar one.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildGraphDegree
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics SemiprimeD1ChildGraphPartition
open SemiprimeD1PacketInventory SemiprimeD1CollisionOriginal

/-- A physical colour test can only delete one or both original endpoints. -/
theorem one_sublist {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (inputArity e)) (out : Placement) :
    (one inputOwner dict a q target i out).value.Sublist
      [(endpoints inputOwner i out).1,(endpoints inputOwner i out).2] := by
  unfold one
  dsimp only
  have hl : (if (testColour target q (SemiprimeD1PacketRows.read dict a out.source).left).value
      then [(endpoints inputOwner i out).1] else []).Sublist [(endpoints inputOwner i out).1] := by
    split_ifs
    · exact List.Sublist.refl _
    · exact List.nil_sublist _
  have hr : (if (testColour target q (SemiprimeD1PacketRows.read dict a out.source).right).value
      then [(endpoints inputOwner i out).2] else []).Sublist [(endpoints inputOwner i out).2] := by
    split_ifs
    · exact List.Sublist.refl _
    · exact List.nil_sublist _
  exact hl.append hr

/-- The full physically selected scan is a sublist of the actual two endpoint stream. -/
theorem scan_sublist {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) :
    (scan inputOwner dict a q target pairs).value.Sublist
      (pairs.flatMap (fun p => [(endpoints inputOwner p.1 p.2).1,(endpoints inputOwner p.1 p.2).2])) := by
  induction pairs with
  | nil => exact List.Sublist.refl _
  | cons p pairs ih => exact (one_sublist inputOwner dict a q target p.1 p.2).append ih

/-- Every endpoint predicate on the unmasked pair stream splits into two counts. -/
theorem full_countP {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) (pred : Endpoint (n+F)→Bool) :
    (pairs.flatMap (fun p => [(endpoints inputOwner p.1 p.2).1,(endpoints inputOwner p.1 p.2).2])).countP pred=
      pairs.countP (fun p => pred (endpoints inputOwner p.1 p.2).1)+
      pairs.countP (fun p => pred (endpoints inputOwner p.1 p.2).2) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    simp only [List.flatMap_cons,List.countP_append,List.countP_cons,List.countP_nil,ih]
    omega

/-- Original degree in the common old-owner namespace, retaining parallel ports. -/
def parentDegree (n F a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (v : Fin (n+F)) : ℕ :=
  (ports n F a inputArity).countP (fun i => decide ((inputOwner i).val=v.val))+
  (ports n F a inputArity).countP (fun i => decide (n+i.1.val=v.val))

/-- Actual cached child incidences never increase any old vertex degree. -/
theorem degree_le (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F)) :
    ((acquire n F r a inputArity inputOwner q g).factors.flatten.countP
      (fun e => decide (e.vertex=v)))≤parentDegree n F a inputArity inputOwner v := by
  rw [graph_countP]
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hlen : (ports n F a inputArity).length=source.placements.length := by
    have hh := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hh
    exact hh.symm
  have he := (scan_sublist inputOwner source.padding.source.selection.cache.rows.source.dictionary
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
    ((ports n F a inputArity).zip source.placements)).countP_le (p:=fun e => decide (e.vertex=v))
  rw [full_countP] at he
  simp only [endpoints,Fin.ext_iff] at he
  rw [zip_countP _ _ hlen (fun i => decide ((inputOwner i).val=v.val)),
    zip_countP _ _ hlen (fun i => decide (n+i.1.val=v.val))] at he
  change (scan _ _ _ _ _ _).value.countP _≤_
  rw [original_ports]
  simpa only [Fin.ext_iff,parentDegree,source] using he

/-- Bounds on all occurring original fibres also bound every absent label by zero. -/
theorem fibre_bound {I K : Type*} [DecidableEq K] (xs : List I) (key : I→K) (Δ : ℕ)
    (h : ∀ i∈xs,SemiprimeSourceHistogramGrouping.multiplicity key xs (key i)≤Δ) (k : K) :
    SemiprimeSourceHistogramGrouping.multiplicity key xs k≤Δ := by
  by_cases he : ∃ i∈xs,key i=k
  · obtain ⟨i,hi,hk⟩ := he
    simpa only [hk] using h i hi
  · have hz : SemiprimeSourceHistogramGrouping.multiplicity key xs k=0 := by
      apply List.countP_eq_zero.mpr
      intro i hi heq
      exact he ⟨i,hi,of_decide_eq_true heq⟩
    rw [hz]
    exact Nat.zero_le _

/-- The common old-vertex namespace has the actual original maximum degree. -/
theorem parentDegree_le (n F a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (inputOwner i).val)
        (ports n F a inputArity) (inputOwner i).val≤Δ)
    (hf : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a inputArity) (n+i.1.val)≤Δ) (v : Fin (n+F)) :
    parentDegree n F a inputArity inputOwner v≤Δ := by
  have hr := fibre_bound _ (fun i => (inputOwner i).val) Δ ho v.val
  have hc := fibre_bound _ (fun i : (e : Fin F)×Fin (inputArity e) => n+i.1.val) Δ hf v.val
  unfold parentDegree
  by_cases hv : v.val<n
  · have hz : (ports n F a inputArity).countP (fun i => decide (n+i.1.val=v.val))=0 := by
      apply List.countP_eq_zero.mpr
      intro i _ he
      have hh := of_decide_eq_true he
      omega
    rw [hz,Nat.add_zero]
    exact hr
  · have hz : (ports n F a inputArity).countP (fun i => decide ((inputOwner i).val=v.val))=0 := by
      apply List.countP_eq_zero.mpr
      intro i _ he
      have hh := of_decide_eq_true he
      have hi := (inputOwner i).isLt
      omega
    rw [hz,Nat.zero_add]
    exact hc

/-- Every actual child old-owner vertex has degree at most the original Δ. -/
theorem child_degree_le (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (inputOwner i).val)
        (ports n F a inputArity) (inputOwner i).val≤Δ)
    (hf : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a inputArity) (n+i.1.val)≤Δ) (q : Fin a) (g : Fin r) (v : Fin (n+F)) :
    ((acquire n F r a inputArity inputOwner q g).factors.flatten.countP
      (fun e => decide (e.vertex=v)))≤Δ :=
  (degree_le n F r a inputArity inputOwner q g v).trans
    (parentDegree_le n F a inputArity inputOwner Δ ho hf v)

end RiemannGaussian.SemiprimeD1ChildGraphDegree
