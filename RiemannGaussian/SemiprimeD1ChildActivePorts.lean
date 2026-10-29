/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildActivationOriginal

/-! # Exact old-vertex port restriction by the acquired activation vector
The actual graph endpoint stream is precisely the original two-sided port list
filtered by physical activation. This includes isolated old vertices correctly;
no tensor truth callback or desired port permutation is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildActivePorts
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics SemiprimeD1ChildGraphPartition
open SemiprimeD1PacketInventory SemiprimeD1CollisionOriginal

/-- Read the actual acquired activation bit for one typed old vertex. -/
def maskAt {V : ℕ} (mask : SemiprimeSourceCompactBits.Report) (e : Endpoint V) : Bool :=
  (mask.bits[e.vertex.val]?).getD false

/-- Actual unmasked original two-sided endpoint stream, including parallel ports. -/
def fullEndpoints {n F a : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) : List (Endpoint (n+F)) :=
  (source.padding.source.selection.cache.data.metadata.incidences.zip source.placements).flatMap
    (fun p => [(endpoints inputOwner p.1 p.2).1,(endpoints inputOwner p.1 p.2).2])

/-- Both actual per-port tests agree with the actual independently read old-vertex mask. -/
theorem one_mask (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (i : (e : Fin F)×Fin (inputArity e)) (out : Placement)
    (hs : out.source=SemiprimeD1IncidenceAcquisition.originalKey n F r a inputArity inputOwner i) :
    (one inputOwner
      (SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).selection.cache.rows.source.dictionary
      a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i out).value=
      [(endpoints inputOwner i out).1,(endpoints inputOwner i out).2].filter
        (maskAt (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)) := by
  have hl := SemiprimeD1ChildActivationOriginal.mask_value n F r a inputArity inputOwner q g
    (endpoints inputOwner i out).1.vertex
  have hr := SemiprimeD1ChildActivationOriginal.mask_value n F r a inputArity inputOwner q g
    (endpoints inputOwner i out).2.vertex
  have hleft : maskAt (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
      (endpoints inputOwner i out).1=decide
        ((SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).1 q=g) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simpa only [maskAt,endpoints,SemiprimeD1SelectedCollision.selectedLabel] using hl
  have hright : maskAt (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)
      (endpoints inputOwner i out).2=decide
        ((SemiprimeD1SelectedCollision.selectedLabel n F r a inputArity inputOwner i).2 q=g) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simpa only [maskAt,endpoints,SemiprimeD1SelectedCollision.selectedLabel] using hr
  rw [one_original n F r a inputArity inputOwner q g i out hs]
  simp only [List.filter_cons,List.filter_nil,hleft,hright,decide_eq_true_eq]
  split_ifs <;> rfl

/-- Original same-order scan equals the full endpoint stream filtered by activation. -/
theorem scan_mask (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement))
    (hs : ∀ p∈pairs,p.2.source=SemiprimeD1IncidenceAcquisition.originalKey n F r a inputArity inputOwner p.1) :
    (scan inputOwner
      (SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).selection.cache.rows.source.dictionary
      a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits pairs).value=
      (pairs.flatMap (fun p => [(endpoints inputOwner p.1 p.2).1,(endpoints inputOwner p.1 p.2).2])).filter
        (maskAt (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    have hh := one_mask n F r a inputArity inputOwner q g p.1 p.2 (hs p List.mem_cons_self)
    have ht := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    change (one _ _ _ _ _ _ _).value++(scan _ _ _ _ _ _).value=_
    rw [hh,ht,List.flatMap_cons,List.filter_append]

/-- No old incident port is lost at an active vertex, and no inactive port is emitted. -/
theorem endpoints_mask (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (acquire n F r a inputArity inputOwner q g).endpoints=
      (fullEndpoints inputOwner (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner)).filter
        (maskAt (SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g)) := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  have hs := SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner
  rw [SemiprimeD1IncidenceAcquisition.keys_original] at hs
  have hz := zip_alignment (ports n F a inputArity) source.placements
    (SemiprimeD1IncidenceAcquisition.originalKey n F r a inputArity inputOwner) hs
  have he := scan_mask n F r a inputArity inputOwner q g _ hz
  change (scan _ _ _ _ _ _).value=_
  simp only [fullEndpoints,original_ports]
  change (scan inputOwner
    (SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).selection.cache.rows.source.dictionary
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
    ((ports n F a inputArity).zip source.placements)).value=_
  exact he

/-- Actual packet grouping is a genuine permutation of the selected endpoint list. -/
theorem graph_perm (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (acquire n F r a inputArity inputOwner q g).factors.flatten.Perm
      (acquire n F r a inputArity inputOwner q g).endpoints := by
  classical
  apply List.perm_iff_count.mpr
  intro key
  have he := graph_countP n F r a inputArity inputOwner q g (fun e => e==key)
  simpa only [List.count_eq_countP] using he

/-- Vertex restriction of an activation filter has no hidden incident-port loss. -/
theorem filter_vertex {V : ℕ} (es : List (Endpoint V)) (mask : SemiprimeSourceCompactBits.Report)
    (v : Fin V) :
    (es.filter (maskAt mask)).filter (fun e => decide (e.vertex=v))=
      if (mask.bits[v.val]?).getD false then es.filter (fun e => decide (e.vertex=v)) else [] := by
  rw [List.filter_filter]
  by_cases hb : (mask.bits[v.val]?).getD false=true
  · rw [ite_eq_left hb]
    congr 1
    funext e
    by_cases he : e.vertex=v <;> simp [maskAt,he,hb]
  · rw [ite_eq_right hb]
    apply List.filter_eq_nil_iff.mpr
    intro e _ hh
    have he : e.vertex=v := of_decide_eq_true (Bool.and_eq_true_iff.mp hh).1
    have hm := (Bool.and_eq_true_iff.mp hh).2
    simp only [maskAt,he] at hm
    exact hb hm

/-- Every selected old vertex receives ALL its original ports, permuted once;
every offgroup vertex has no child incidences. This includes isolated vertices. -/
theorem vertex_ports (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) (v : Fin (n+F)) :
    ((acquire n F r a inputArity inputOwner q g).factors.flatten.filter (fun e => decide (e.vertex=v))).Perm
      (if ((SemiprimeD1ChildActivation.acquire n F r a inputArity inputOwner q g).bits[v.val]?).getD false then
        (fullEndpoints inputOwner (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner)).filter
          (fun e => decide (e.vertex=v)) else []) := by
  have hp := (graph_perm n F r a inputArity inputOwner q g).filter (fun e => decide (e.vertex=v))
  rw [endpoints_mask,filter_vertex] at hp
  exact hp

end RiemannGaussian.SemiprimeD1ChildActivePorts
