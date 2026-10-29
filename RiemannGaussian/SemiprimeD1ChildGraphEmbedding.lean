/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraphDegree

/-! # Faithful original occurrence/side embedding in the actual child graph
Positive original occurrence IDs distinguish parallel ports. The two endpoint
sides distinguish both contributions when their coordinate group agrees.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1ChildGraphEmbedding
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics SemiprimeD1ChildGraphPartition
open SemiprimeD1ChildGraphDegree SemiprimeD1PacketInventory SemiprimeBitArithmetic
open SemiprimeD1CollisionOriginal

/-- Erased endpoint identity: original occurrence number and its original side. -/
def tag {V : ℕ} (e : Endpoint V) : ℕ×Bool := (bitValue e.edge,e.side)

/-- Unmasked original endpoint tags form a literal two-sided Cartesian product. -/
theorem full_tags {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) :
    ((pairs.flatMap (fun p => [(endpoints inputOwner p.1 p.2).1,
      (endpoints inputOwner p.1 p.2).2])).map tag)=
      (pairs.map (fun p => bitValue p.2.edge)).product [true,false] := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons,List.map_nil]
    rw [ih]
    have hp : (bitValue p.2.edge::pairs.map (fun p => bitValue p.2.edge)).product [true,false]=
        [(bitValue p.2.edge,true),(bitValue p.2.edge,false)]++
          (pairs.map (fun p => bitValue p.2.edge)).product [true,false] :=
      List.product_cons _ _ _
    rw [hp]
    rfl

/-- Every emitted endpoint has a distinct original occurrence/side identity. -/
theorem endpoints_nodup (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    ((acquire n F r a inputArity inputOwner q g).endpoints.map tag).Nodup := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hlen : (ports n F a inputArity).length=source.placements.length := by
    have hh := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hh
    exact hh.symm
  let pairs := (ports n F a inputArity).zip source.placements
  have hid : (pairs.map (fun p => bitValue p.2.edge)).Nodup := by
    have he := congrArg (List.map (fun p : Placement => bitValue p.edge)) (List.map_snd_zip hlen.symm.le)
    have he' : (pairs.map (fun p => bitValue p.2.edge))=source.placements.map (fun p => bitValue p.edge) := by
      simpa only [pairs,List.map_map,Function.comp_def] using he
    rw [he']
    change ((SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements.map _).Nodup
    rw [SemiprimeD1PacketReplayOriginal.occurrence_ids]
    exact List.nodup_range'
  have hfull : ((pairs.map (fun p => bitValue p.2.edge)).product [true,false]).Nodup :=
    hid.product (by decide : ([true,false]:List Bool).Nodup)
  rw [←full_tags inputOwner pairs] at hfull
  have he := (scan_sublist inputOwner source.padding.source.selection.cache.rows.source.dictionary
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits pairs).map tag
  have hsmall := he.nodup hfull
  change ((scan _ _ _ _ _ _).value.map tag).Nodup
  rw [original_ports]
  exact hsmall

/-- Packet grouping preserves every original endpoint identity exactly once. -/
theorem graph_tags_nodup (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    ((acquire n F r a inputArity inputOwner q g).factors.flatten.map tag).Nodup := by
  have hs := endpoints_nodup n F r a inputArity inputOwner q g
  apply List.nodup_iff_count_le_one.mpr
  intro key
  have he := graph_countP n F r a inputArity inputOwner q g (fun e => tag e==key)
  have hc : ((acquire n F r a inputArity inputOwner q g).factors.flatten.map tag).count key=
      ((acquire n F r a inputArity inputOwner q g).endpoints.map tag).count key := by
    simpa only [List.count_eq_countP,List.countP_map,Function.comp_def] using he
  rw [hc]
  exact List.nodup_iff_count_le_one.mp hs key

end RiemannGaussian.SemiprimeD1ChildGraphEmbedding
