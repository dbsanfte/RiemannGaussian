/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketRowExpansion

/-! # Actual original packet endpoint/assignment partition
A single arbitrary global endpoint assignment is restricted by the literal
acquired child buckets. Original port multiplicity and order are retained;
semantic selected colours occur only in proofs of the executed filters.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace RiemannGaussian.SemiprimeD1PacketColumnPartition
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics SemiprimeD1PacketEntryInputs
open SemiprimeD1PacketInventory SemiprimeD1CollisionOriginal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Restriction of one common endpoint assignment to an actual packet and side. -/
def packetWires {V : ℕ} (a : ℕ) (side : Bool) (key : List Bool)
    (assignment : Endpoint V→Bool) (es : List (Endpoint V)) : List (Wire a) :=
  es.filterMap (fun e => if e.packet=key ∧ e.side=side then
    some (wire a e (assignment e)).1 else none)

/-- A global assignment is read in exactly the actual bucket order. -/
theorem gather_assignment {V : ℕ} (a : ℕ) (es : List (Endpoint V))
    (assignment : Endpoint V→Bool) :
    (gather a es (es.map assignment)).rows=
      es.filterMap (fun e => if e.side then some (wire a e (assignment e)).1 else none) ∧
    (gather a es (es.map assignment)).columns=
      es.filterMap (fun e => if e.side then none else some (wire a e (assignment e)).1) := by
  induction es with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
    cases hs : e.side <;> simp only [gather,List.map_cons,List.head?_cons,Option.getD_some,
      List.tail_cons,hs,Bool.false_eq_true,ite_false,ite_true,List.filterMap_cons,ih.1,ih.2,and_self]

/-- Physical packet filtering followed by row acquisition is exactly a single
same-order packet-and-side restriction of the original endpoint stream. -/
theorem gather_packet_rows {V : ℕ} (a : ℕ) (es : List (Endpoint V)) (key : List Bool)
    (assignment : Endpoint V→Bool) :
    let bucket := es.filter (fun e => decide (e.packet=key))
    (gather a bucket (bucket.map assignment)).rows=packetWires a true key assignment es := by
  dsimp only
  rw [(gather_assignment a _ assignment).1]
  unfold packetWires
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases hp : e.packet=key <;> cases hs : e.side <;>
      simp only [List.filter_cons,hp,decide_true,decide_false,
        Bool.false_eq_true,ite_true,ite_false,List.filterMap_cons,hs,and_true,
        and_false,ih]

/-- Complementary physical factor-side restriction, without occurrence loss. -/
theorem gather_packet_columns {V : ℕ} (a : ℕ) (es : List (Endpoint V)) (key : List Bool)
    (assignment : Endpoint V→Bool) :
    let bucket := es.filter (fun e => decide (e.packet=key))
    (gather a bucket (bucket.map assignment)).columns=packetWires a false key assignment es := by
  dsimp only
  rw [(gather_assignment a _ assignment).2]
  unfold packetWires
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases hp : e.packet=key <;> cases hs : e.side <;>
      simp only [List.filter_cons,hp,decide_true,decide_false,Bool.true_eq_false,
        Bool.false_eq_true,ite_true,ite_false,List.filterMap_cons,hs,and_true,
        and_false,ih]

/-- Literal endpoint selected by a side flag; the occurrence ID is unchanged. -/
def chosenEndpoint {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (side : Bool) (pair : ((e : Fin F)×Fin (arity e))×Placement) : Endpoint (n+F) :=
  if side then (endpoints owner pair.1 pair.2).1 else (endpoints owner pair.1 pair.2).2

/-- Original selected colour of that same occurrence-side, proof-only. -/
def chosenColour (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (side : Bool) (q : Fin a) (port : (e : Fin F)×Fin (arity e)) : Fin r :=
  if side then (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner port).1 q
  else (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner port).2 q

/-- The actual group stream is precisely the original same-order restriction,
including parallel occurrences and both possible copies of a real port. -/
theorem scan_packet_original (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (side : Bool) (key : List Bool) (assignment : Endpoint (n+F)→Bool)
    (pairs : List (((e : Fin F)×Fin (arity e))×Placement))
    (hp : ∀pair∈pairs,pair.2.source=
      SemiprimeD1IncidenceAcquisition.originalKey n F r a arity owner pair.1) :
    packetWires a side key assignment
      (scan owner (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary
        a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits pairs).value=
      pairs.filterMap (fun pair =>
        if pair.2.packet=key ∧ chosenColour n F r a arity owner side q pair.1=g then
          some (wire a (chosenEndpoint owner side pair) (assignment (chosenEndpoint owner side pair))).1 else none) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    have hh := one_original n F r a arity owner q g pair.1 pair.2 (hp pair List.mem_cons_self)
    have ht := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    change packetWires a side key assignment ((one _ _ _ _ _ _ _).value++(scan _ _ _ _ _ pairs).value)=_
    unfold packetWires at *
    rw [List.filterMap_append,hh,ht]
    cases side <;>
      by_cases hl : (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner pair.1).1 q=g <;>
      by_cases hr : (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner pair.1).2 q=g <;>
      by_cases hk : pair.2.packet=key <;>
      simp only [hl,hr,hk,ite_true,ite_false,List.filterMap_cons,
        List.filterMap_nil,List.nil_append,List.append_nil,List.singleton_append,chosenColour,chosenEndpoint,
        endpoints,Bool.false_eq_true,Bool.true_eq_false,and_true,and_false]

/-- Exact original occurrence/placement stream, with no advised pairing. -/
def originalPairs (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :=
  (ports n F a arity).zip (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements

/-- Every original pair is aligned by the actual replay source map. -/
theorem originalPairs_source (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ∀pair∈originalPairs n F r a arity owner,pair.2.source=
      SemiprimeD1IncidenceAcquisition.originalKey n F r a arity owner pair.1 := by
  have hs := SemiprimeD1PacketReplayOriginal.sources n F r a arity owner
  rw [SemiprimeD1IncidenceAcquisition.keys_original] at hs
  exact zip_alignment _ _ _ hs

/-- Actual original child buckets are the cached packet restriction of the
physically tested selected endpoint stream. -/
theorem original_bucket (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length) :
    ((acquire n F r a arity owner q g).factors[packet.val]?).getD []=
      ((scan owner
        (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary
        a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
        (originalPairs n F r a arity owner)).value.filter (fun e => decide
          (e.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val]))) := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  change ((buckets _ source.state.packets).value[packet.val]?).getD []=_
  rw [buckets_value]
  have hp : packet.val<source.state.packets.length := packet.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hp,Option.map_some,Option.getD_some]
  rw [original_ports]
  rfl

/-- Closed original rows/columns restriction theorem. One arbitrary global
endpoint assignment supplies all actual local assignment lists. -/
theorem original_wires (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) :
    let bucket := ((acquire n F r a arity owner q g).factors[packet.val]?).getD []
    let key := (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val]
    (gather a bucket (bucket.map assignment)).rows=
      (originalPairs n F r a arity owner).filterMap (fun pair =>
        if pair.2.packet=key ∧ chosenColour n F r a arity owner true q pair.1=g then
          some (wire a (chosenEndpoint owner true pair) (assignment (chosenEndpoint owner true pair))).1 else none) ∧
    (gather a bucket (bucket.map assignment)).columns=
      (originalPairs n F r a arity owner).filterMap (fun pair =>
        if pair.2.packet=key ∧ chosenColour n F r a arity owner false q pair.1=g then
          some (wire a (chosenEndpoint owner false pair) (assignment (chosenEndpoint owner false pair))).1 else none) := by
  dsimp only
  rw [original_bucket]
  constructor
  · rw [gather_packet_rows]
    exact scan_packet_original n F r a arity owner q g true _ assignment _
      (originalPairs_source n F r a arity owner)
  · rw [gather_packet_columns]
    exact scan_packet_original n F r a arity owner q g false _ assignment _
      (originalPairs_source n F r a arity owner)

/-- Generic same-order colour restriction of an optional list payload. -/
def partitionMap {A B : Type*} {r : ℕ} (xs : List A) (colour : A→Fin r)
    (value : A→Option B) (g : Fin r) : List B :=
  xs.filterMap (fun x => if colour x=g then value x else none)

/-- Every list occurrence contributes once across the complete finite palette.
This counts multiplicities, so parallel ports and equal payloads are retained. -/
theorem partition_count {A B : Type*} [DecidableEq B] {r : ℕ}
    (xs : List A) (colour : A→Fin r) (value : A→Option B) (b : B) :
    (∑g : Fin r,(partitionMap xs colour value g).count b)=(xs.filterMap value).count b := by
  induction xs with
  | nil => simp only [partitionMap,List.filterMap_nil,List.count_nil,Finset.sum_const_zero]
  | cons x xs ih =>
    have hc (g : Fin r) : (partitionMap (x::xs) colour value g).count b=
        (if colour x=g then ((value x).toList.count b) else 0)+(partitionMap xs colour value g).count b := by
      cases hv : value x <;> by_cases h : colour x=g <;>
        simp [partitionMap,h,hv,List.count_cons,Nat.add_comm]
    simp_rw [hc]
    rw [Finset.sum_add_distrib,ih]
    have hs : (∑g : Fin r,if colour x=g then (value x).toList.count b else 0)=(value x).toList.count b := by
      simp only [eq_comm (a:=colour x),Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [hs]
    cases hv : value x <;> simp [hv,List.count_cons,Nat.add_comm]

/-- Concatenating all actual colour restrictions is a permutation of the full
payload list, with exact occurrence multiplicity rather than mere coverage. -/
theorem partition_perm {A B : Type*} {r : ℕ} (xs : List A) (colour : A→Fin r)
    (value : A→Option B) :
    ((List.finRange r).flatMap (partitionMap xs colour value)).Perm (xs.filterMap value) := by
  classical
  apply List.perm_iff_count.mpr
  intro b
  rw [List.count_flatMap]
  change (List.map (fun g : Fin r => (partitionMap xs colour value g).count b) (List.finRange r)).sum=_
  rw [←List.ofFn_eq_map, List.sum_ofFn]
  exact partition_count xs colour value b

/-- Literal full original packet side, before any selected-colour restriction. -/
def originalSideWires (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (side : Bool)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) : List (Wire a) :=
  (originalPairs n F r a arity owner).filterMap (fun pair =>
    if pair.2.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] then
      some (wire a (chosenEndpoint owner side pair) (assignment (chosenEndpoint owner side pair))).1 else none)

/-- Uniform side form of the actual child assignment restriction. -/
theorem original_side (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) (side : Bool)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) :
    let bucket := ((acquire n F r a arity owner q g).factors[packet.val]?).getD []
    let assigned :=  gather a bucket (bucket.map assignment)
    (if side then assigned.rows else assigned.columns)=
      partitionMap (originalPairs n F r a arity owner)
        (fun pair => chosenColour n F r a arity owner side q pair.1)
        (fun pair => if pair.2.packet=
          (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] then
          some (wire a (chosenEndpoint owner side pair) (assignment (chosenEndpoint owner side pair))).1 else none) g := by
  dsimp only
  cases hs : side
  · simp only [Bool.false_eq_true,ite_false]
    rw [(original_wires n F r a arity owner q g packet assignment).2]
    unfold partitionMap
    apply List.filterMap_congr
    intro pair _
    by_cases hp : pair.2.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] <;>
      by_cases hc : chosenColour n F r a arity owner false q pair.1=g <;> simp only [hp,hc,and_true,and_false,ite_true,ite_false]
  · simp only [ite_true]
    rw [(original_wires n F r a arity owner q g packet assignment).1]
    unfold partitionMap
    apply List.filterMap_congr
    intro pair _
    by_cases hp : pair.2.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] <;>
      by_cases hc : chosenColour n F r a arity owner true q pair.1=g <;> simp only [hp,hc,and_true,and_false,ite_true,ite_false]

/-- All actual source-group column lists (or target-group row lists) cover the
full original packet side exactly once. Only group order is permuted; within
each group the original factor-major occurrence order is unchanged. -/
theorem original_groups_perm (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (side : Bool)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) :
    ((List.finRange r).flatMap (fun g =>
      let bucket := ((acquire n F r a arity owner q g).factors[packet.val]?).getD []
      let assigned :=  gather a bucket (bucket.map assignment)
      if side then assigned.rows else assigned.columns)).Perm
        (originalSideWires n F r a arity owner side packet assignment) := by
  simp_rw [original_side]
  exact partition_perm _ _ _

end
end RiemannGaussian.SemiprimeD1PacketColumnPartition
