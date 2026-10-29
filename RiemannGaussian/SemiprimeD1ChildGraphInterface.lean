/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraphEmbedding

/-! # Exact original finite incidence interface of constructed child graphs
These bridges use the literal factor-major metadata enumeration and the concrete
cached arity/owner functions, not an assumed graph-semantic equivalence.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildGraphInterface
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphDegree SemiprimeD1ChildGraphBounds
open SemiprimeD1CollisionOriginal SemiprimeSourceHistogramGrouping

/-- Exact literal factor-major port list of any concrete cached child graph. -/
theorem port_owner_values {V : ℕ} (graph : Graph V) (Q : ℕ) :
    ((ports V graph.factors.length Q (arity graph)).map (owner graph))=
      graph.factors.flatten.map Endpoint.vertex := by
  have inner (f : Fin graph.factors.length) :
      (List.finRange (arity graph f)).map (fun j => owner graph ⟨f,j⟩)=
        (graph.factors[f.val]).map Endpoint.vertex := by
    have h := congrArg (List.map Endpoint.vertex)
      (List.ofFn_getElem (xs:=graph.factors[f.val]))
    simpa only [List.finRange,List.map_ofFn,Function.comp_def,owner,arity] using h
  have hmap : (List.finRange graph.factors.length).map (fun f => graph.factors[f.val])=graph.factors := by
    simpa only [List.finRange,List.map_ofFn,Function.comp_def] using
      (List.ofFn_getElem (xs:=graph.factors))
  have houter := congrArg (fun bs : List (List (Endpoint V)) => bs.flatMap (fun b => b.map Endpoint.vertex)) hmap
  rw [List.flatMap_map] at houter
  have hflat (bs : List (List (Endpoint V))) :
      bs.flatMap (fun b => b.map Endpoint.vertex)=bs.flatten.map Endpoint.vertex := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons,List.flatten_cons,List.map_append,ih]
  simp only [ports,SemiprimeSourceHistogramMetadata.acquire,
    SemiprimePaidFiniteEnumerationLists.flat_value,SemiprimeSourceHistogramMetadata.finFast_value,
    SemiprimeSourceHistogramMetadata.ports_value,List.map_flatMap,List.map_map,Function.comp_def]
  trans (List.finRange graph.factors.length).flatMap
    (fun f => (graph.factors[f.val]).map Endpoint.vertex)
  · congr 1
    funext f
    exact inner f
  · exact houter.trans (hflat graph.factors)

/-- The actual child incidence-map owner fibre equals its cached endpoint degree. -/
theorem owner_fibre {V : ℕ} (graph : Graph V) (Q : ℕ) (v : Fin V) :
    SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner graph i).val)
      (ports V graph.factors.length Q (arity graph)) v.val=
      graph.factors.flatten.countP (fun e => decide (e.vertex=v)) := by
  have h := congrArg (List.countP (fun x : Fin V => decide (x.val=v.val))) (port_owner_values graph Q)
  simpa only [SemiprimeSourceHistogramGrouping.multiplicity,List.countP_map,Function.comp_def,Fin.ext_iff] using h

/-- The original-input degree contract holds for literal child metadata, not just
for the auxiliary endpoint list. This is usable by the next original selector. -/
theorem recursive_owner_bound (n F r a Q : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (inputOwner i).val) (ports n F a inputArity) (inputOwner i).val≤Δ)
    (hf : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val) (ports n F a inputArity) (n+i.1.val)≤Δ)
    (q : Fin a) (g : Fin r)
    (i : (f : Fin (acquire n F r a inputArity inputOwner q g).factors.length)×
      Fin (arity (acquire n F r a inputArity inputOwner q g) f)) :
    let graph := acquire n F r a inputArity inputOwner q g
    SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner graph i).val)
      (ports (n+F) graph.factors.length Q (arity graph)) (owner graph i).val≤Δ := by
  dsimp only
  rw [owner_fibre]
  exact child_degree_le n F r a inputArity inputOwner Δ ho hf q g _

/-- Literal factor-major incidence enumeration has exactly its declared factor arity. -/
theorem factor_fibre (n F Q : ℕ) (inputArity : Fin F→ℕ) (f : Fin F) :
    SemiprimeSourceHistogramGrouping.multiplicity (fun i : (e : Fin F)×Fin (inputArity e) => n+i.1.val)
      (ports n F Q inputArity) (n+f.val)=inputArity f := by
  have inner (e : Fin F) :
      ((List.finRange (inputArity e)).map (fun j : Fin (inputArity e) => (⟨e,j⟩ : (e : Fin F)×Fin (inputArity e)))).countP
        (fun i => decide (n+i.1.val=n+f.val))=(if e=f then inputArity f else 0) := by
    rw [List.countP_map]
    by_cases he : e=f
    · subst e
      simp [Function.comp_def]
    · have hv : e.val≠f.val := by intro h; exact he (Fin.ext h)
      simp [Function.comp_def,he,hv]
  simp only [SemiprimeSourceHistogramGrouping.multiplicity,ports,SemiprimeSourceHistogramMetadata.acquire,
    SemiprimePaidFiniteEnumerationLists.flat_value,SemiprimeSourceHistogramMetadata.finFast_value,
    SemiprimeSourceHistogramMetadata.ports_value,List.countP_flatMap]
  change ((List.finRange F).map (fun e =>
      ((List.finRange (inputArity e)).map (fun j : Fin (inputArity e) => (⟨e,j⟩ : (e : Fin F)×Fin (inputArity e)))).countP
        (fun i => decide (n+i.1.val=n+f.val)))).sum=_
  simp only [inner]
  simp only [List.finRange,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  simp

/-- Literal next-selector factor fibre is bounded by the actual packet arity. -/
theorem recursive_factor_bound (n F r a Q : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (i : (f : Fin (acquire n F r a inputArity inputOwner q g).factors.length)×
      Fin (arity (acquire n F r a inputArity inputOwner q g) f)) :
    let graph := acquire n F r a inputArity inputOwner q g
    SemiprimeSourceHistogramGrouping.multiplicity (fun i : (f : Fin graph.factors.length)×Fin (arity graph f) => n+F+i.1.val)
      (ports (n+F) graph.factors.length Q (arity graph)) (n+F+i.1.val)≤2*2^a := by
  dsimp only
  rw [factor_fibre]
  exact packet_arity n F r a inputArity inputOwner q g i.1

/-- Original graph degree contracts transfer to the actual recursive child with
the derived maximum max(Δ,2*2^a), not an advised degree certificate. -/
theorem recursive_degree_contract (n F r a Q : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (inputOwner i).val)
        (ports n F a inputArity) (inputOwner i).val≤Δ)
    (hf : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a inputArity) (n+i.1.val)≤Δ) (q : Fin a) (g : Fin r) :
    let graph := acquire n F r a inputArity inputOwner q g
    (∀ i∈ports (n+F) graph.factors.length Q (arity graph),
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner graph i).val)
        (ports (n+F) graph.factors.length Q (arity graph)) (owner graph i).val≤ max Δ (2*2^a)) ∧
    (∀ i∈ports (n+F) graph.factors.length Q (arity graph),
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+F+i.1.val)
        (ports (n+F) graph.factors.length Q (arity graph)) (n+F+i.1.val)≤ max Δ (2*2^a)) := by
  dsimp only
  constructor
  · intro i _
    exact (recursive_owner_bound n F r a Q inputArity inputOwner Δ ho hf q g i).trans (Nat.le_max_left _ _)
  · intro i _
    exact (recursive_factor_bound n F r a Q inputArity inputOwner q g i).trans (Nat.le_max_right _ _)

end RiemannGaussian.SemiprimeD1ChildGraphInterface
