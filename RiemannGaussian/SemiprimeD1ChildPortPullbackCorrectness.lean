/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortPullback
import RiemannGaussian.SemiprimeD1ChildActivePorts

/-! # Correctness of the actually acquired original-port pullback
Original physical occurrence IDs give a unique typed original port. Exact graph
restriction/partition then proves the computed links are a permutation of the
actual selected original endpoints, with no supplied inverse or callback.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1ChildPortPullbackCorrectness
open SemiprimeD1ChildPortPullback SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics
open SemiprimeD1ChildActivePorts SemiprimeD1PacketInventory SemiprimeD1CollisionOriginal
open SemiprimeBitArithmetic

/-- Physical first-match lookup is exact on every actually acquired unique ID. -/
theorem findPort_member {I : Type*} (ids : List (List Bool×I))
    (hn : (ids.map Prod.fst).Nodup) (id : List Bool) (i : I) (hm : (id,i)∈ids) :
    (findPort id ids).value=some i := by
  induction ids with
  | nil => simp at hm
  | cons p ids ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he|he
    · cases he
      have hh : (equalBytes id id).value=true := (equalBytes_correct _ _).mpr rfl
      simp only [findPort,hh,ite_true]
    · have hne : p.1≠id := by
        intro hh
        have hmem : id∈ids.map Prod.fst := List.mem_map.mpr ⟨(id,i),he,rfl⟩
        rw [←hh] at hmem
        exact hnd.1 hmem
      have hb : (equalBytes p.1 id).value=false :=
        Bool.eq_false_iff.mpr (fun h => hne ((equalBytes_correct _ _).mp h))
      simp only [findPort,hb,Bool.false_eq_true,ite_false]
      exact ih hnd.2 he

/-- Concrete typed original-port/placement pairs in original order. -/
def originalPairs (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) :=
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  (ports n F a inputArity).zip source.placements

/-- The actual ID bank is acquired from precisely the original typed occurrences. -/
theorem ids_value (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).ids=
      (originalPairs n F r a inputArity inputOwner).map (fun p => (p.2.edge,p.1)) := by
  change (bank _).value=_
  rw [bank_value,SemiprimeD1ChildGraphSemantics.original_ports]
  rfl

/-- Actual positive original edge IDs have no raw byte alias or duplicate. -/
theorem ids_nodup (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    ((SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).ids.map Prod.fst).Nodup := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hlen : (ports n F a inputArity).length=source.placements.length := by
    have hh := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hh
    exact hh.symm
  have he := congrArg (List.map (fun p : Placement => bitValue p.edge)) (List.map_snd_zip hlen.symm.le)
  have he' : ((originalPairs n F r a inputArity inputOwner).map (fun p => bitValue p.2.edge))=
      source.placements.map (fun p => bitValue p.edge) := by
    simpa only [originalPairs,List.map_map,Function.comp_def] using he
  have hv : ((originalPairs n F r a inputArity inputOwner).map (fun p => bitValue p.2.edge)).Nodup := by
    rw [he']
    change ((SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements.map _).Nodup
    rw [SemiprimeD1PacketReplayOriginal.occurrence_ids]
    exact List.nodup_range'
  apply List.Nodup.of_map bitValue
  simpa only [ids_value,List.map_map,Function.comp_def] using hv

/-- Proof-side resolved original endpoint, using the actual physical lookup. -/
def resolve {I : Type*} {V : ℕ} (ids : List (List Bool×I)) (e : Endpoint V) : Option (I×Bool) :=
  (findPort e.edge ids).value.map (fun i => (i,e.side))

/-- Original typed endpoint order, filtered only by the actually acquired mask. -/
def targetLinks {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (mask : SemiprimeSourceCompactBits.Report)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) :=
  pairs.flatMap (fun p =>
    (if maskAt mask (endpoints inputOwner p.1 p.2).1 then [(p.1,true)] else [])++
    (if maskAt mask (endpoints inputOwner p.1 p.2).2 then [(p.1,false)] else []))

/-- The actually executed ID search restores every original typed endpoint. -/
theorem resolve_full {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (mask : SemiprimeSourceCompactBits.Report)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement))
    (ids : List (List Bool×((e : Fin F)×Fin (inputArity e))))
    (hfind : ∀ p∈pairs,(findPort p.2.edge ids).value=some p.1) :
    (((pairs.flatMap (fun p => [(endpoints inputOwner p.1 p.2).1,
      (endpoints inputOwner p.1 p.2).2])).filter (maskAt mask)).map (resolve ids))=
        (targetLinks inputOwner mask pairs).map some := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    have hh := hfind p List.mem_cons_self
    have ht := ih (fun x hx => hfind x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons,List.filter_append,List.map_append,ht,targetLinks]
    congr 1
    simp only [List.filter_cons,List.filter_nil]
    split_ifs <;> simp_all only [resolve,endpoints,Option.map_some,List.map_cons,List.map_nil,
      List.nil_append,List.cons_append,List.append_nil]

/-- Computed pullback is a genuine permutation of selected original typed ports.
In particular no original endpoint is lost, duplicated, or mapped to none. -/
theorem links_perm (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).links.Perm
      ((targetLinks inputOwner
        (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
        (originalPairs n F r a inputArity inputOwner)).map some) := by
  let ids := (SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).ids
  have hfind : ∀ p∈originalPairs n F r a inputArity inputOwner,
      (findPort p.2.edge ids).value=some p.1 := by
    intro p hp
    apply findPort_member ids (ids_nodup n F r a inputArity inputOwner q g) p.2.edge p.1
    change (p.2.edge,p.1)∈(SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).ids
    rw [ids_value]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have he := resolve_full inputOwner
    (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
    (originalPairs n F r a inputArity inputOwner) ids hfind
  have hp := graph_perm n F r a inputArity inputOwner q g
  rw [endpoints_mask] at hp
  have hm := hp.map (resolve ids)
  change ((SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).graph.factors.flatten.map (resolve ids)).Perm _ at hm
  change (pull ids _).value.Perm _
  rw [pull_value]
  change (((SemiprimeD1ChildPortPullback.acquire n F r a inputArity inputOwner q g).graph.factors.flatten.map (resolve ids))).Perm _
  exact hm.trans (List.Perm.of_eq he)

end RiemannGaussian.SemiprimeD1ChildPortPullbackCorrectness
