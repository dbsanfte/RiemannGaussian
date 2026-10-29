/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraph

/-! # Original endpoint refinement of the physically acquired child graph
Semantic finite-word expressions occur only in proofs of physical colour tests.
The child tensor-entry builder and inactive-vertex constant-one semantics remain
separate from this literal graph incidence construction.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildGraphSemantics
open SemiprimeD1ChildGraph SemiprimeD1PacketInventory SemiprimeBitArithmetic
open SemiprimeD1CollisionOriginal

/-- The executed byte test supplies the concrete decidable predicate. -/
theorem equalBytes_value (xs ys : List Bool) : (equalBytes xs ys).value=decide (xs=ys) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using equalBytes_correct xs ys

/-- Packet buckets retain exactly the original endpoint list multiplicities. -/
theorem bucket_value {vertices : ℕ} (key : List Bool) (es : List (Endpoint vertices)) :
    (bucket key es).value=es.filter (fun e => decide (e.packet=key)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [bucket,ih,equalBytes_value,List.filter_cons]

/-- All observed packet buckets are cached in the same original discovery order. -/
theorem buckets_value {vertices : ℕ} (es : List (Endpoint vertices)) (keys : List (List Bool)) :
    (buckets es keys).value=keys.map (fun key => es.filter (fun e => decide (e.packet=key))) := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [buckets,ih,bucket_value,List.map_cons]

/-- Number of child factor vertices is the actual observed packet count. -/
theorem factors_length {n F r a : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) :
    (fromReplay inputOwner source q g).factors.length=source.state.packets.length := by
  change (buckets _ _).value.length=_
  rw [buckets_value,List.length_map]

/-- Physical colour comparison of original palette bytes, without a getter oracle. -/
theorem test_fields {r a : ℕ} (word : OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word r a)
    (q : Fin a) (g : Fin r) :
    (testColour (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits q.val
      (SemiprimeD1OrientationPalette.fields word)).value=true ↔ word q=g := by
  rw [testColour_correct]
  simp only [SemiprimeD1OrientationPalette.fields,List.getElem?_ofFn,q.isLt,↓reduceDIte,
    Option.getD_some,SemiprimeSourceHistogramHeadRefinement.numberKey_value,
    SemiprimeSourceHistogramPortKeys.encodeKey_value,Fin.ext_iff]

/-- Exact two original selected-colour endpoint tests for one actual occurrence. -/
theorem one_original (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (q : Fin a) (g : Fin r) (i : (e : Fin F)×Fin (inputArity e)) (out : Placement)
    (hs : out.source=SemiprimeD1IncidenceAcquisition.originalKey n F r a inputArity inputOwner i) :
    (one inputOwner
      (SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).selection.cache.rows.source.dictionary
      a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i out).value=
      (if (SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).1 q=g
        then [(endpoints inputOwner i out).1] else [])++
      (if (SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).2 q=g
        then [(endpoints inputOwner i out).2] else []) := by
  have hrows := SemiprimeD1PacketRowsOriginal.original_read n F r a inputArity inputOwner i
  dsimp only [SemiprimeD1PacketRowsOriginal.originalRead] at hrows
  have hlt := test_fields (SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).1 q g
  have hrt := test_fields (SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).2 q g
  simp only [one,hs,hrows.1,hrows.2.1]
  simp only [hlt,hrt]

/-- Same-order scan semantics, with all original repeated occurrences retained. -/
theorem scan_value {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) :
    (scan inputOwner dict a q target pairs).value=
      pairs.flatMap (fun p => (one inputOwner dict a q target p.1 p.2).value) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simp only [scan,ih,List.flatMap_cons]

/-- Source-map equality supplies exact original pairing, not a zip oracle. -/
theorem zip_alignment {I : Type*} (is : List I) (ps : List Placement) (key : I→List Bool)
    (hs : ps.map Placement.source=is.map key) :
    ∀ pair∈is.zip ps,pair.2.source=key pair.1 := by
  induction is generalizing ps with
  | nil => simp
  | cons i is ih =>
    cases ps with
    | nil => simp at hs
    | cons p ps =>
      simp only [List.map_cons,List.cons.injEq] at hs
      intro pair hp
      rcases List.mem_cons.mp hp with he|he
      · subst pair
        exact hs.1
      · exact ih ps hs.2 pair he

/-- Original metadata stream in the retained replay is the actual port list. -/
theorem original_ports (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).padding.source.selection.cache.data.metadata.incidences=
      ports n F a inputArity := by
  change (SemiprimeSourceHistogramSetup.acquire n F r a 0 inputArity inputOwner).data.metadata.incidences=_
  rw [SemiprimeSourceHistogramSetup.metadata_actual]
  rfl

/-- A full original pairing preserves counts of every original-port predicate. -/
theorem zip_countP {I : Type*} (is : List I) (ps : List Placement)
    (hl : is.length=ps.length) (pred : I→Bool) :
    (is.zip ps).countP (fun pair => pred pair.1)=is.countP pred := by
  induction is generalizing ps with
  | nil => simp
  | cons i is ih =>
    cases ps with
    | nil => simp at hl
    | cons p ps =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simpa only [List.zip_cons_cons,List.countP_cons] using
        congrArg (fun n => n+(if pred i then 1 else 0)) (ih ps hl)

/-- Each actual source occurrence contributes precisely its selected two endpoints. -/
theorem scan_length_original (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (q : Fin a) (g : Fin r) (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement))
    (hp : ∀ pair∈pairs,pair.2.source=
      SemiprimeD1IncidenceAcquisition.originalKey n F r a inputArity inputOwner pair.1) :
    (scan inputOwner
      (SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).selection.cache.rows.source.dictionary
      a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits pairs).value.length=
    pairs.countP (fun pair => decide
      ((SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner pair.1).1 q=g))+
    pairs.countP (fun pair => decide
      ((SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner pair.1).2 q=g)) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    have hh := one_original n F r a inputArity inputOwner q g pair.1 pair.2
      (hp pair List.mem_cons_self)
    have ht := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    change ((one _ _ _ _ _ _ _).value++(scan _ _ _ _ _ pairs).value).length=_
    rw [List.length_append,hh,ht,List.length_append,List.countP_cons,List.countP_cons]
    split_ifs <;> simp_all <;> omega

/-- Exact original child endpoint count; no balancing/count answer is supplied. -/
theorem endpoint_count (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (acquire n F r a inputArity inputOwner q g).endpoints.length=
      SemiprimeD1GroupBalance.selectedGroupCount n F r a inputArity inputOwner true q g+
      SemiprimeD1GroupBalance.selectedGroupCount n F r a inputArity inputOwner false q g := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hs := SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner
  rw [SemiprimeD1IncidenceAcquisition.keys_original] at hs
  have hl : (ports n F a inputArity).length=source.placements.length := by
    have h := congrArg List.length hs
    simp only [List.length_map] at h
    exact h.symm
  have hp := zip_alignment (ports n F a inputArity) source.placements
    (SemiprimeD1IncidenceAcquisition.originalKey n F r a inputArity inputOwner) hs
  have he := scan_length_original n F r a inputArity inputOwner q g _ hp
  rw [zip_countP _ _ hl (fun i => decide ((SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).1 q=g)),
    zip_countP _ _ hl (fun i => decide ((SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).2 q=g))] at he
  change (scan _ _ _ _ _ _).value.length=_
  rw [original_ports]
  change (scan inputOwner
      (SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).selection.cache.rows.source.dictionary
      a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
      ((ports n F a inputArity).zip source.placements)).value.length=_
  simpa only [SemiprimeD1GroupBalance.selectedGroupCount,SemiprimeD1GroupBalance.groupCount,
    SemiprimeD1GroupBalance.colour,ite_true,Bool.false_eq_true,ite_false] using he

end RiemannGaussian.SemiprimeD1ChildGraphSemantics
