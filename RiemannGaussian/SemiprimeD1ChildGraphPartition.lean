/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraphSemantics

/-! # Actual packet-bucket partition of child incidences
No endpoint is lost or duplicated by the observed-packet grouping. Empty packet
factors and isolated old vertices are retained as ordinary finite graph metadata.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildGraphPartition
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics
open SemiprimeD1PacketInventory SemiprimeSourceHistogramTrie

/-- Exact discovery-list update from the already acquired marker invariant. -/
theorem step_packets (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) (hg : SeenGood state) :
    (step dict a state key).2.packets=
      if (step dict a state key).1.packet∈state.packets then state.packets
      else (step dict a state key).1.packet::state.packets := by
  let packet := (step dict a state key).1.packet
  have hp : (lookup state.seen packet).bits=if packet∈state.packets then [true] else [] := by
    rw [lookup_bits,hg.2]
  change (if (lookup state.seen packet).bits.isEmpty then
    (SemiprimeSourceCompactBits.copy packet).bits::state.packets else state.packets)=
      if packet∈state.packets then state.packets else packet::state.packets
  rw [hp,SemiprimeSourceCompactBits.copy_bits]
  by_cases hm : packet∈state.packets <;> simp only [hm,ite_true,ite_false,List.isEmpty_cons,
    List.isEmpty_nil,Bool.false_eq_true]

/-- Subsequent real ports never remove an already observed packet key. -/
theorem replay_packets_mono (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (hg : SeenGood state) :
    ∀ packet∈state.packets,packet∈(replay dict a keys state).2.packets := by
  induction keys generalizing state with
  | nil => exact fun _ h => h
  | cons key keys ih =>
    intro packet hp
    apply ih _ (step_seen dict a state key hg)
    rw [step_packets dict a state key hg]
    split_ifs
    · exact hp
    · exact List.mem_cons_of_mem _ hp

/-- Every real placement's packet is in the final observed packet list. -/
theorem replay_covers (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (hg : SeenGood state)
    (out : Placement) (ho : out∈(replay dict a keys state).1) :
    out.packet∈(replay dict a keys state).2.packets := by
  induction keys generalizing state with
  | nil => simp [replay] at ho
  | cons key keys ih =>
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at ho
    rcases List.mem_cons.mp ho with he|he
    · subst out
      apply replay_packets_mono dict a keys _ (step_seen dict a state key hg)
      rw [step_packets dict a state key hg]
      split_ifs with hm
      · exact hm
      · exact List.mem_cons_self
    · exact ih _ (step_seen dict a state key hg) he

/-- Source original placements have actual observed packet-factor vertices. -/
theorem placement_covered (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (out : Placement)
    (ho : out∈(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements) :
    out.packet∈(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets :=
  replay_covers _ _ _ _ (initial_seen _) out ho

/-- Both emitted endpoint records use their actual original placement's packet. -/
theorem one_packet {n F : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (inputArity e)) (out : Placement) (e : Endpoint (n+F))
    (he : e∈(one inputOwner dict a q target i out).value) : e.packet=out.packet := by
  unfold one at he
  dsimp only at he
  rcases List.mem_append.mp he with he|he
  · split_ifs at he with h
    · have hh := List.mem_singleton.mp he
      subst e
      rfl
    · simp at he
  · split_ifs at he with h
    · have hh := List.mem_singleton.mp he
      subst e
      rfl
    · simp at he

/-- Every actual selected child endpoint belongs to an actually observed packet. -/
theorem endpoint_covered (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (e : Endpoint (n+F)) (he : e∈(acquire n F r a inputArity inputOwner q g).endpoints) :
    e.packet∈(acquire n F r a inputArity inputOwner q g).packetKeys := by
  change e∈(scan _ _ _ _ _ _).value at he
  rw [scan_value] at he
  obtain ⟨pair,hpair,he⟩ := List.mem_flatMap.mp he
  have hh := one_packet inputOwner _ _ _ _ pair.1 pair.2 e he
  rw [hh]
  exact placement_covered n F r a inputArity inputOwner pair.2 (List.of_mem_zip hpair).2

/-- A sparse duplicate-free key list gives exactly one membership indicator. -/
theorem onehot (keys : List (List Bool)) (hn : keys.Nodup) (key : List Bool) :
    (keys.map (fun k => if key=k then (1:ℕ) else 0)).sum=if key∈keys then 1 else 0 := by
  induction keys with
  | nil => simp
  | cons k keys ih =>
    have hnd := List.nodup_cons.mp hn
    by_cases he : key=k
    · subst key
      simp only [List.map_cons,List.sum_cons,ite_true]
      rw [ih hnd.2]
      simp [hnd.1]
    · simp only [List.map_cons,List.sum_cons,he,ite_false,Nat.zero_add]
      rw [ih hnd.2]
      simp [he]

/-- Literal list bucket partition, retaining all endpoint multiplicities. -/
theorem partition_length {V : ℕ} (keys : List (List Bool)) (es : List (Endpoint V))
    (hn : keys.Nodup) (hc : ∀ e∈es,e.packet∈keys) :
    (keys.map (fun k => es.filter (fun e => decide (e.packet=k)))).flatten.length=es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have ht := ih (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    have he := onehot keys hn e.packet
    rw [ite_eq_left (hc e List.mem_cons_self)] at he
    rw [List.length_flatten,List.map_map] at ht ⊢
    have hpoint : (fun k => ((e::es).filter (fun x => decide (x.packet=k))).length)=
        (fun k => (if e.packet=k then 1 else 0)+(es.filter (fun x => decide (x.packet=k))).length) := by
      funext k
      by_cases h : e.packet=k
      · simp only [List.filter_cons,h,decide_true,ite_true,List.length_cons]
        omega
      · simp [h]
    change (keys.map (fun k => ((e::es).filter (fun x => decide (x.packet=k))).length)).sum=_
    simp only [Function.comp_def] at ht
    rw [hpoint,List.sum_map_add,he,ht,List.length_cons]
    omega

/-- Concrete graph arity sum counts each cached endpoint exactly once. -/
theorem graph_port_count (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (acquire n F r a inputArity inputOwner q g).factors.flatten.length=
      (acquire n F r a inputArity inputOwner q g).endpoints.length := by
  have hkeys := SemiprimeD1PacketReplayOriginal.packets_nodup n F r a inputArity inputOwner
  have hc := endpoint_covered n F r a inputArity inputOwner q g
  change (buckets _ _).value.flatten.length=_
  rw [buckets_value]
  exact partition_length _ _ hkeys hc

/-- The concrete Sigma/Fin incidence representation has the same exact port count. -/
theorem arity_sum {vertices : ℕ} (graph : Graph vertices) :
    (∑ f,arity graph f)=graph.factors.flatten.length := by
  rw [List.length_flatten]
  unfold arity
  have h := List.sum_ofFn (f:=fun f : Fin graph.factors.length => (graph.factors[f.val]).length)
  rw [←h]
  congr 1
  have he : List.ofFn (fun f : Fin graph.factors.length => graph.factors[f.val])=graph.factors :=
    List.ofFn_getElem
  have hm := congrArg (List.map List.length) he
  simpa only [List.map_ofFn,Function.comp_def] using hm

/-- Every endpoint predicate, including original edge/side and vertex degree,
is preserved with its exact multiplicity by the actual list partition. -/
theorem partition_countP {V : ℕ} (keys : List (List Bool)) (es : List (Endpoint V))
    (hn : keys.Nodup) (hc : ∀ e∈es,e.packet∈keys) (pred : Endpoint V→Bool) :
    (keys.map (fun k => es.filter (fun e => decide (e.packet=k)))).flatten.countP pred=es.countP pred := by
  rw [List.countP_eq_length_filter,List.countP_eq_length_filter]
  rw [List.filter_flatten,List.map_map]
  have he : (List.filter pred ∘ fun k => es.filter (fun e => decide (e.packet=k)))=
      (fun k => (es.filter pred).filter (fun e => decide (e.packet=k))) := by
    funext k
    exact List.filter_comm pred (fun e => decide (e.packet=k)) es
  rw [he]
  exact partition_length keys (es.filter pred) hn (fun e he => hc e (List.mem_filter.mp he).1)

/-- Exact counts in the actual child graph, with no assumed graph equivalence. -/
theorem graph_countP (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (pred : Endpoint (n+F)→Bool) :
    (acquire n F r a inputArity inputOwner q g).factors.flatten.countP pred=
      (acquire n F r a inputArity inputOwner q g).endpoints.countP pred := by
  have hkeys := SemiprimeD1PacketReplayOriginal.packets_nodup n F r a inputArity inputOwner
  have hc := endpoint_covered n F r a inputArity inputOwner q g
  change (buckets _ _).value.flatten.countP pred=_
  rw [buckets_value]
  exact partition_countP _ _ hkeys hc pred

end RiemannGaussian.SemiprimeD1ChildGraphPartition
