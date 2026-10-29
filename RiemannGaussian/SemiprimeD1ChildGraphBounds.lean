/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraphPartition

/-! # Actual child incidence count and packet arity bounds
The graph is the concrete physically tested original endpoint list and cached
observed-packet partition. No child cardinality or desired incidence map is input.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1ChildGraphBounds
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics SemiprimeD1ChildGraphPartition
open SemiprimeD1PacketInventory SemiprimeD1CollisionOriginal

/-- A fixed-length byte slot is determined by its Boolean coordinate function. -/
theorem slot_ext (a : ℕ) (left right : List Bool) (hl : left.length=a) (hr : right.length=a)
    (he : (fun q : Fin a => (left[q.val]?).getD false)=
      (fun q : Fin a => (right[q.val]?).getD false)) : left=right := by
  apply List.ext_getElem (hl.trans hr.symm)
  intro i hi hj
  have h := congrFun he ⟨i,by omega⟩
  simpa only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using h

/-- Actual unique original placement slots give at most2^a real ports per packet. -/
theorem placement_bucket_bound (a : ℕ) (ps : List Placement) (key : List Bool)
    (hn : (ps.map slotAddress).Nodup) (hs : ∀ p∈ps,p.slot.length=a) :
    (ps.filter (fun p => decide (p.packet=key))).length≤2^a := by
  let selected := ps.filter (fun p => decide (p.packet=key))
  have hp : selected.Nodup := (List.Nodup.of_map slotAddress hn).filter _
  let tag := fun p : Placement => fun q : Fin a => (p.slot[q.val]?).getD false
  have ht : (selected.map tag).Nodup := by
    apply hp.map_on
    intro left hl right hr he
    have hleft := List.mem_filter.mp hl
    have hright := List.mem_filter.mp hr
    have hls : left.packet=key := of_decide_eq_true hleft.2
    have hrs : right.packet=key := of_decide_eq_true hright.2
    have hslot := slot_ext a left.slot right.slot (hs left hleft.1) (hs right hright.1) he
    apply List.inj_on_of_nodup_map hn hleft.1 hright.1
    simp only [slotAddress,hls,hrs,hslot]
  have hc := ht.length_le_card
  simpa only [List.length_map,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using hc

/-- Both selected old endpoints of one real occurrence contribute at most two. -/
theorem one_packet_bound {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (inputArity e)) (out : Placement) (packet : List Bool) :
    ((one inputOwner dict a q target i out).value.filter (fun e => decide (e.packet=packet))).length≤
      2*(if out.packet=packet then 1 else 0) := by
  unfold one
  dsimp only
  by_cases hp : out.packet=packet
  · split_ifs <;> simp [endpoints,hp]
  · split_ifs <;> simp [endpoints,hp]

/-- Actual physical endpoint scan never exceeds twice its real-port packet fibre. -/
theorem scan_packet_bound {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (pairs : List (((e : Fin F)×Fin (inputArity e))×Placement)) (packet : List Bool) :
    ((scan inputOwner dict a q target pairs).value.filter (fun e => decide (e.packet=packet))).length≤
      2*pairs.countP (fun p => decide (p.2.packet=packet)) := by
  induction pairs with
  | nil => simp [scan]
  | cons p pairs ih =>
    have hh := one_packet_bound inputOwner dict a q target p.1 p.2 packet
    change (((one _ _ _ _ _ _ _).value++(scan _ _ _ _ _ pairs).value).filter _).length≤_
    rw [List.filter_append,List.length_append,List.countP_cons]
    by_cases hp : p.2.packet=packet <;> simp only [hp,decide_true,decide_false,ite_true,ite_false] at hh ⊢ <;> omega

/-- Full source pairing preserves every placement-only fibre count. -/
theorem zip_snd_countP {I : Type*} (is : List I) (ps : List Placement)
    (hl : is.length=ps.length) (pred : Placement→Bool) :
    (is.zip ps).countP (fun p => pred p.2)=ps.countP pred := by
  have h := List.map_snd_zip hl.symm.le
  have hc := congrArg (List.countP pred) h
  simpa only [List.countP_map,Function.comp_def] using hc

/-- Every actual observed packet factor has at most twice its2^a slots. -/
theorem packet_arity (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (f : Fin (acquire n F r a inputArity inputOwner q g).factors.length) :
    arity (acquire n F r a inputArity inputOwner q g) f≤2*2^a := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
  let is := source.padding.source.selection.cache.data.metadata.incidences
  have hl : is.length=source.placements.length := by
    rw [show is=ports n F a inputArity from original_ports n F r a inputArity inputOwner]
    have h := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at h
    exact h.symm
  have hn := SemiprimeD1PacketReplayOriginal.slots_nodup n F r a inputArity inputOwner
  have hs : ∀ p∈source.placements,p.slot.length=a := by
    intro p hp
    exact (SemiprimeD1PacketReplayOriginal.placement_valid n F r a inputArity inputOwner p hp).2
  have hmem := List.getElem_mem f.isLt
  change ((acquire n F r a inputArity inputOwner q g).factors[f.val])∈
    (buckets _ source.state.packets).value at hmem
  rw [buckets_value] at hmem
  obtain ⟨packet,_,hbucket⟩ := List.mem_map.mp hmem
  have hp := placement_bucket_bound a source.placements packet hn hs
  have he := scan_packet_bound inputOwner source.padding.source.selection.cache.rows.source.dictionary
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits (is.zip source.placements) packet
  rw [zip_snd_countP _ _ hl (fun p => decide (p.packet=packet)),List.countP_eq_length_filter] at he
  change ((acquire n F r a inputArity inputOwner q g).factors[f.val]).length≤_
  rw [←hbucket]
  exact he.trans (Nat.mul_le_mul_left 2 hp)

/-- Exact original group count in the concrete Sigma/Fin child representation. -/
theorem edge_count (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (∑ f,arity (acquire n F r a inputArity inputOwner q g) f)=
      SemiprimeD1GroupBalance.selectedGroupCount n F r a inputArity inputOwner true q g+
      SemiprimeD1GroupBalance.selectedGroupCount n F r a inputArity inputOwner false q g := by
  rw [arity_sum,graph_port_count,endpoint_count]

/-- Original degree guards give the actual child at most4M/r incidences. -/
theorem edge_scaled_bound (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (inputOwner i).val)
        (ports n F a inputArity) (inputOwner i).val≤Δ)
    (hf : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a inputArity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a inputArity).length) (q : Fin a) (g : Fin r) :
    r*(∑ f,arity (acquire n F r a inputArity inputOwner q g) f)≤4*(ports n F a inputArity).length := by
  rw [edge_count]
  exact SemiprimeD1GroupBalance.selected_both_le n F r a inputArity inputOwner Δ ho hf hsmall q g

/-- With64 groups the actual constructed child already shrinks by16. -/
theorem child64_shrink (n F a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (inputOwner i).val)
        (ports n F a inputArity) (inputOwner i).val≤Δ)
    (hf : ∀ i∈ports n F a inputArity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a inputArity) (n+i.1.val)≤Δ)
    (hsmall : 2*(64^(2*a))^2*Δ≤(ports n F a inputArity).length) (q : Fin a) (g : Fin 64) :
    16*(∑ f,arity (acquire n F 64 a inputArity inputOwner q g) f)≤(ports n F a inputArity).length := by
  rw [edge_count]
  exact SemiprimeD1GroupBalance.selected64_shrink n F a inputArity inputOwner Δ ho hf hsmall q g

/-- A literal finite colour partition counts each original endpoint once. -/
theorem colour_sum {I C : Type*} [Fintype C] [DecidableEq C] (xs : List I) (label : I→C) :
    (∑ c,xs.countP (fun i => decide (label i=c)))=xs.length := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.countP_cons,Finset.sum_add_distrib,decide_eq_true_eq]
    rw [ih]
    have hh : (∑ c : C,if label i=c then (1:ℕ) else 0)=1 := by simp [eq_comm]
    rw [hh,List.length_cons]

/-- Across all actual colour children each original row/factor endpoint appears once. -/
theorem all_groups_count (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) :
    (∑ g : Fin r,∑ f,arity (acquire n F r a inputArity inputOwner q g) f)=
      2*(ports n F a inputArity).length := by
  simp only [edge_count,Finset.sum_add_distrib,SemiprimeD1GroupBalance.selectedGroupCount,
    SemiprimeD1GroupBalance.groupCount,SemiprimeD1GroupBalance.colour,ite_true,Bool.false_eq_true,ite_false]
  rw [colour_sum,colour_sum]
  omega

end RiemannGaussian.SemiprimeD1ChildGraphBounds
