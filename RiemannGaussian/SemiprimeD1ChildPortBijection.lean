/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortPullbackCorrectness

/-! # Bijective computed original-port pullback
The cached physically resolved table contains each selected original endpoint
once and contains no missing entry. The codomain is constructed from original
ports and the acquired mask, not supplied as a desired permutation.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildPortBijection
open SemiprimeD1ChildPortPullback SemiprimeD1ChildPortPullbackCorrectness
open SemiprimeD1ChildGraph SemiprimeD1ChildActivePorts SemiprimeD1PacketInventory
open SemiprimeD1CollisionOriginal

/-- Unmasked typed parent-port/side stream is the original Cartesian pair list. -/
theorem typed_full {I : Type*} (pairs : List (I×Placement)) :
    (pairs.flatMap (fun p => [(p.1,true),(p.1,false)]))=
      (pairs.map Prod.fst).product [true,false] := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    simp only [List.flatMap_cons,List.map_cons,ih]
    have hp : (p.1::pairs.map Prod.fst).product [true,false]=
        [(p.1,true),(p.1,false)]++(pairs.map Prod.fst).product [true,false] :=
      List.product_cons _ _ _
    exact hp.symm

/-- Actual mask restriction only deletes from the original typed endpoint stream. -/
theorem target_sublist {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (mask : SemiprimeSourceCompactBits.Report)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) :
    (targetLinks inputOwner mask pairs).Sublist
      (pairs.flatMap (fun p => [(p.1,true),(p.1,false)])) := by
  induction pairs with
  | nil => exact List.Sublist.refl _
  | cons p pairs ih =>
    have hl : (if maskAt mask (endpoints inputOwner p.1 p.2).1 then [(p.1,true)] else []).Sublist [(p.1,true)] := by
      split_ifs
      · exact List.Sublist.refl _
      · exact List.nil_sublist _
    have hr : (if maskAt mask (endpoints inputOwner p.1 p.2).2 then [(p.1,false)] else []).Sublist [(p.1,false)] := by
      split_ifs
      · exact List.Sublist.refl _
      · exact List.nil_sublist _
    exact (hl.append hr).append ih

/-- The exact original metadata incidence list has no repeated typed occurrence. -/
theorem original_ports_nodup (n F a : ℕ) (inputArity : Fin F→ℕ) :
    (ports n F a inputArity).Nodup := by
  change (SemiprimeSourceHistogramMetadata.acquire n F a inputArity).incidences.Nodup
  rw [(SemiprimeSourceHistogramMetadata.original_fields n F a inputArity).1]
  change (SemiprimePaidFiniteEnumerations.incidences F inputArity).value.Nodup
  rw [SemiprimePaidFiniteEnumerations.incidences_value]
  exact (SemiprimeFiniteEnumerations.indexedIncidences F inputArity).nodup

/-- No selected original typed endpoint repeats in the actual target list. -/
theorem target_nodup (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (targetLinks inputOwner (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
      (originalPairs n F r a inputArity inputOwner)).Nodup := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hlen : (ports n F a inputArity).length=source.placements.length := by
    have hh := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hh
    exact hh.symm
  have hm : (originalPairs n F r a inputArity inputOwner).map Prod.fst=ports n F a inputArity :=
    List.map_fst_zip hlen.le
  have hn : ((originalPairs n F r a inputArity inputOwner).map Prod.fst).Nodup := by
    rw [hm]
    exact original_ports_nodup n F a inputArity
  have hp : (((originalPairs n F r a inputArity inputOwner).map Prod.fst).product [true,false]).Nodup :=
    hn.product (by decide : ([true,false]:List Bool).Nodup)
  rw [←typed_full] at hp
  exact (target_sublist inputOwner _ _).nodup hp

/-- The actual acquired link cache is injective, including distinct original sides. -/
theorem links_nodup (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).links.Nodup := by
  have hp := links_perm n F r a inputArity inputOwner q g
  exact hp.nodup_iff.mpr ((target_nodup n F r a inputArity inputOwner q g).map (Option.some_injective _))

/-- Every actually acquired child-port link resolves successfully. -/
theorem no_missing (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    none∉(SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).links := by
  intro hm
  have hp := (links_perm n F r a inputArity inputOwner q g).mem_iff.mp hm
  simp at hp

/-- Exact multiplicity of every original typed endpoint in the computed cache.
This is a constructive finite bijection certificate, not a supplied inverse. -/
theorem link_count (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (link : ((e : Fin F)×Fin (inputArity e))×Bool) :
    ((SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).links.count (some link))=
      if link∈targetLinks inputOwner (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
        (originalPairs n F r a inputArity inputOwner) then 1 else 0 := by
  have hp := (links_perm n F r a inputArity inputOwner q g).count_eq (some link)
  rw [hp,List.count_map_of_injective _ Option.some (Option.some_injective _) link]
  exact (target_nodup n F r a inputArity inputOwner q g).count

/-- Materialize the resolved typed port table by a paid finite cache scan.
None is skipped on malformed inputs; the original endpoint proves none absent. -/
def resolveCache {A : Type*} : List (Option A)→SemiprimeMaterializedWords.Run (List A)
  | [] => ⟨[],2⟩
  | none::xs =>
    let tail := resolveCache xs
    ⟨tail.value,tail.work+4⟩
  | some x::xs =>
    let tail := resolveCache xs
    ⟨x::tail.value,tail.work+6⟩

/-- The executed cache traversal returns exactly its successfully resolved links. -/
theorem resolveCache_value {A : Type*} (xs : List (Option A)) :
    (resolveCache xs).value=xs.filterMap id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [resolveCache,List.filterMap_cons,ih,id_eq]

/-- All visited option cells and typed metadata copies remain in the report. -/
theorem resolveCache_work {A : Type*} (xs : List (Option A)) :
    (resolveCache xs).work≤6*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [resolveCache,List.length_cons] <;> omega

/-- Concrete cached permutation values, with no chosen inverse or advice. -/
def permutation {n F a : ℕ} {inputArity : Fin F→ℕ}
    (data : SemiprimeD1ChildPortPullback.Acquired n F a inputArity) :
    SemiprimeMaterializedWords.Run (List (((e : Fin F)×Fin (inputArity e))×Bool)) :=
  let out := resolveCache data.links
  ⟨out.value,data.work+out.work+3⟩

/-- The actually materialized table is a permutation of all selected original endpoints. -/
theorem permutation_perm (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (permutation (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g)).value.Perm
      (targetLinks inputOwner (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
        (originalPairs n F r a inputArity inputOwner)) := by
  have hp := (links_perm n F r a inputArity inputOwner q g).filterMap id
  change (resolveCache _).value.Perm _
  rw [resolveCache_value]
  have he (xs : List (((e : Fin F)×Fin (inputArity e))×Bool)) : (xs.map some).filterMap id=xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change x::((xs.map some).filterMap id)=x::xs
      rw [ih]
  rw [he] at hp
  exact hp

/-- The cached typed pullback is injective as well as surjective onto its target. -/
theorem permutation_nodup (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (permutation (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g)).value.Nodup :=
  (permutation_perm n F r a inputArity inputOwner q g).nodup_iff.mpr
    (target_nodup n F r a inputArity inputOwner q g)

/-- Original old vertex of one typed original endpoint, without colour data. -/
def linkVertex {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (link : ((e : Fin F)×Fin (inputArity e))×Bool) : Fin (n+F) :=
  if link.2 then ⟨(inputOwner link.1).val,by omega⟩ else ⟨n+link.1.1.val,by omega⟩

/-- Actual acquired activation lookup for a typed original endpoint. -/
def activeLink {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (mask : SemiprimeSourceCompactBits.Report)
    (link : ((e : Fin F)×Fin (inputArity e))×Bool) : Bool :=
  (mask.bits[(linkVertex inputOwner link).val]?).getD false

/-- The typed target list is an actual mask-filtered complete endpoint stream. -/
theorem target_filter {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (mask : SemiprimeSourceCompactBits.Report)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) :
    targetLinks inputOwner mask pairs=
      ((pairs.map Prod.fst).product [true,false]).filter (activeLink inputOwner mask) := by
  rw [←typed_full]
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    change ((if maskAt mask (endpoints inputOwner p.1 p.2).1 then [(p.1,true)] else [])++
      (if maskAt mask (endpoints inputOwner p.1 p.2).2 then [(p.1,false)] else []))++
      targetLinks inputOwner mask pairs=_
    rw [ih,List.flatMap_cons,List.filter_append]
    congr 1
    simp only [List.filter_cons,List.filter_nil,activeLink,linkVertex,maskAt,endpoints,ite_true,
      Bool.false_eq_true,ite_false]
    split_ifs
    all_goals simp_all only [Bool.false_eq_true,ite_true,ite_false,List.cons_append,List.nil_append]
    all_goals rfl

/-- Every original typed port occurs in the actual original factor-major list. -/
theorem original_ports_complete (n F a : ℕ) (inputArity : Fin F→ℕ)
    (i : (e : Fin F)×Fin (inputArity e)) : i∈ports n F a inputArity := by
  change i∈(SemiprimeSourceHistogramMetadata.acquire n F a inputArity).incidences
  rw [(SemiprimeSourceHistogramMetadata.original_fields n F a inputArity).1]
  change i∈(SemiprimePaidFiniteEnumerations.incidences F inputArity).value
  rw [SemiprimePaidFiniteEnumerations.incidences_value]
  exact (SemiprimeFiniteEnumerations.indexedIncidences F inputArity).complete i

/-- Target membership is exactly the physical activation bit of the old vertex. -/
theorem target_mem (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (link : ((e : Fin F)×Fin (inputArity e))×Bool) :
    link∈targetLinks inputOwner (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
      (originalPairs n F r a inputArity inputOwner) ↔
      activeLink inputOwner (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g) link=true := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hl : (ports n F a inputArity).length=source.placements.length := by
    have hh := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hh
    exact hh.symm
  have hm : (originalPairs n F r a inputArity inputOwner).map Prod.fst=ports n F a inputArity :=
    List.map_fst_zip hl.le
  rw [target_filter,hm,List.mem_filter]
  have hi := original_ports_complete n F a inputArity link.1
  have hb : link.2∈([true,false]:List Bool) := by cases link.2 <;> simp
  have hprod : link∈(ports n F a inputArity).product [true,false] := by
    change (link.1,link.2)∈(ports n F a inputArity).product [true,false]
    exact List.mem_product.mpr ⟨hi,hb⟩
  simp only [hprod,true_and]

/-- Every original incident port of a selected old vertex is present exactly once
in the actually computed permutation; inactive old vertices contribute none. -/
theorem permutation_count (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (link : ((e : Fin F)×Fin (inputArity e))×Bool) :
    ((permutation (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g)).value.count link)=
      if activeLink inputOwner (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g) link
        then 1 else 0 := by
  have hp := (permutation_perm n F r a inputArity inputOwner q g).count_eq link
  rw [hp,(target_nodup n F r a inputArity inputOwner q g).count]
  simp only [target_mem]

/-- Literal cached endpoint of one typed child factor-major incidence. -/
def portEntry {V : ℕ} (graph : Graph V)
    (i : (f : Fin graph.factors.length)×Fin (SemiprimeD1ChildGraph.arity graph f)) : Endpoint V :=
  graph.factors[i.1.val][i.2.val]

/-- Actual typed child metadata enumerates the complete cached endpoint records,
not only their vertex projections. -/
theorem port_entries {V : ℕ} (graph : Graph V) (Q : ℕ) :
    (ports V graph.factors.length Q (SemiprimeD1ChildGraph.arity graph)).map (portEntry graph)=
      graph.factors.flatten := by
  have inner (f : Fin graph.factors.length) :
      (List.finRange (SemiprimeD1ChildGraph.arity graph f)).map (fun j => portEntry graph ⟨f,j⟩)=
        graph.factors[f.val] := by
    simpa only [List.finRange,List.map_ofFn,Function.comp_def,portEntry,SemiprimeD1ChildGraph.arity] using
      (List.ofFn_getElem (xs:=graph.factors[f.val]))
  have hmap : (List.finRange graph.factors.length).map (fun f => graph.factors[f.val])=graph.factors := by
    simpa only [List.finRange,List.map_ofFn,Function.comp_def] using
      (List.ofFn_getElem (xs:=graph.factors))
  have houter := congrArg (fun bs : List (List (Endpoint V)) => bs.flatMap id) hmap
  rw [List.flatMap_map] at houter
  have hflat (bs : List (List (Endpoint V))) : bs.flatMap id=bs.flatten := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons,List.flatten_cons,ih,id_eq]
  simp only [ports,SemiprimeSourceHistogramMetadata.acquire,
    SemiprimePaidFiniteEnumerationLists.flat_value,SemiprimeSourceHistogramMetadata.finFast_value,
    SemiprimeSourceHistogramMetadata.ports_value,List.map_flatMap,List.map_map,Function.comp_def]
  trans (List.finRange graph.factors.length).flatMap (fun f => graph.factors[f.val])
  · congr 1
    funext f
    exact inner f
  · exact houter.trans (hflat graph.factors)

/-- The computed cache is aligned with the literal typed child port enumeration. -/
theorem pullback_port_order (n F r a Q : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    let data := SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g
    data.links=(ports (n+F) data.graph.factors.length Q (SemiprimeD1ChildGraph.arity data.graph)).map
      (fun i => resolve data.ids (portEntry data.graph i)) := by
  dsimp only
  let data := SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g
  have he := congrArg (List.map (resolve data.ids)) (port_entries data.graph Q)
  simp only [List.map_map,Function.comp_def] at he
  change data.links=_
  rw [he]
  exact SemiprimeD1ChildPortPullback.pull_value _ _

end RiemannGaussian.SemiprimeD1ChildPortBijection
