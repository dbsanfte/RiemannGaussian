/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildActivationBudget
import RiemannGaussian.SemiprimeD1ChildOrderBudget

/-! # Actual original child port-bank/pullback/order supplier reports
All original ID bytes, scan lengths and report reuse come from the actual
retained source. No permutation, successful lookup, or returned row is advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1ChildPullbackBudget
open scoped BigOperators
open SemiprimeD1ChildPortPullback SemiprimeD1PacketInventory
open SemiprimeD1OriginalChildGraphBudget

/-- Actual physical ID-bank construction pays all copied bytes and pair cells. -/
theorem bank_work {I : Type*} (xs : List (I×Placement)) (W : ℕ)
    (h : ∀x∈xs,x.2.edge.length ≤ W) : (bank xs).work ≤ xs.length*(3*W+7)+2 := by
  induction xs with
  | nil => simp [bank]
  | cons x xs ih =>
    have hh:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [bank,SemiprimeSourceCompactBits.copy_clock,List.length_cons]
    nlinarith

/-- Actual bank length is the number of original occurrence/placement pairs. -/
theorem bank_length {I : Type*} (xs : List (I×Placement)) : (bank xs).value.length=xs.length := by
  rw [bank_value,List.length_map]

/-- Literal byte-ID search, including the missing-result branch. -/
theorem findPort_work {I : Type*} (key : List Bool) (ids : List (List Bool×I)) (W : ℕ)
    (h : ∀id∈ids,id.1.length ≤ W) :
    (findPort key ids).work ≤ ids.length*(6*W+10)+2 := by
  induction ids with
  | nil => simp [findPort]
  | cons id ids ih =>
    have hc:=SemiprimeD1ChildGraph.equalBytes_work id.1 key
    have hh:=h id List.mem_cons_self
    have ht:=ih (fun x hx=>h x (List.mem_cons_of_mem id hx))
    simp only [findPort,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

/-- Every actual endpoint query retains a physically found or missing option. -/
theorem pull_length {I : Type*} {V : ℕ} (ids : List (List Bool×I))
    (es : List (SemiprimeD1ChildGraph.Endpoint V)) : (pull ids es).value.length=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [pull,List.length_cons,ih]

/-- Full physical original-ID scans are paid for every actual endpoint. -/
theorem pull_work {I : Type*} {V : ℕ} (ids : List (List Bool×I))
    (es : List (SemiprimeD1ChildGraph.Endpoint V)) (W : ℕ)
    (h : ∀id∈ids,id.1.length ≤ W) :
    (pull ids es).work ≤ es.length*(ids.length*(6*W+10)+7)+2 := by
  induction es with
  | nil => simp [pull]
  | cons e es ih =>
    have hh:=findPort_work e.edge ids W h
    simp only [pull,List.length_cons]
    nlinarith

/-- Literal original occurrence list length, before any group restriction. -/
theorem metadata_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (source n F r a arity owner).padding.source.selection.cache.data.metadata.incidences.length=∑e,arity e := by
  rw [SemiprimeD1ChildGraphSemantics.original_ports]
  exact (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1

/-- Actual original real-placement list length, preserving parallel ports. -/
theorem placements_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (source n F r a arity owner).placements.length=∑e,arity e :=
  (SemiprimeD1OriginalModeAcquisition.original_size n F r a arity owner).trans
    (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1

/-- Every original ID-bank payload inherits its physically produced width. -/
theorem original_bank_width (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ∀id∈(bank ((source n F r a arity owner).padding.source.selection.cache.data.metadata.incidences.zip
      (source n F r a arity owner).placements)).value,
      id.1.length ≤ replayCap n F r a (∑e,arity e) := by
  intro id hid
  rw [bank_value] at hid
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hid
  exact ((SemiprimeD1ReplayMetadataBounds.original_placements n F r a arity owner x.2
    (List.of_mem_zip hx).2).2.1).trans (SemiprimeD1PacketReplayBudget.acquire_work n F r a arity owner)

/-- Original fixed-polynomial supplier overhead; no global word/slot sweep. -/
def overhead (n F r a M : ℕ) : ℕ :=
  SemiprimeD1OriginalChildGraphBudget.overhead n F r a M+
    SemiprimeD1ChildActivationBudget.overhead n F r a+
    M*(3*replayCap n F r a M+7)+2+
    (2*M^2)*(M*(6*replayCap n F r a M+10)+7)+2+50*M+30

/-- Cached endpoint option count is bounded from original stream dimensions. -/
theorem links_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay owner (source n F r a arity owner) q g).links.length ≤ 2*(∑e,arity e)^2 := by
  change (pull _ _).value.length ≤ _
  rw [pull_length]
  exact factors_flatten_length n F r a arity owner q g

/-- CLOSED original prepared child report, preserving the source report exactly
as the frozen constructor's explicit sharing/subtraction formula does. -/
theorem fromReplay_work (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay owner (source n F r a arity owner) q g).work ≤
      (source n F r a arity owner).state.clock+overhead n F r a (∑e,arity e) := by
  let src:=source n F r a arity owner
  let graph:=SemiprimeD1ChildGraph.fromReplay owner src q g
  let activation:=SemiprimeD1ChildActivation.fromReplay src q g
  let xs:=src.padding.source.selection.cache.data.metadata.incidences.zip src.placements
  let ids:=bank xs
  let W:=replayCap n F r a (∑e,arity e)
  have hg:=SemiprimeD1OriginalChildGraphBudget.fromReplay_work n F r a arity owner q g
  have ha:=SemiprimeD1ChildActivationBudget.fromReplay_clock n F r a arity owner q g
  change graph.work ≤ src.state.clock+_ at hg
  change activation.clock ≤ src.state.clock+_ at ha
  have hd : activation.clock-src.state.clock ≤ SemiprimeD1ChildActivationBudget.overhead n F r a := by omega
  have hlen : xs.length=∑e,arity e:=pairs_length n F r a arity owner
  have hb:=bank_work xs W (by
    intro x hx
    exact ((SemiprimeD1ReplayMetadataBounds.original_placements n F r a arity owner x.2
      (List.of_mem_zip hx).2).2.1).trans (SemiprimeD1PacketReplayBudget.acquire_work n F r a arity owner))
  rw [hlen] at hb
  have hidlen : ids.value.length=∑e,arity e:=(bank_length xs).trans hlen
  have hp:=pull_work ids.value graph.factors.flatten W (original_bank_width n F r a arity owner)
  rw [hidlen] at hp
  have hflat:=factors_flatten_length n F r a arity owner q g
  change graph.factors.flatten.length ≤ _ at hflat
  have hp' : (pull ids.value graph.factors.flatten).work ≤
      (2*(∑e,arity e)^2)*((∑e,arity e)*(6*W+10)+7)+2 := hp.trans (by gcongr)
  have hf:=factors_length n F r a arity owner q g
  have he:=endpoints_length n F r a arity owner q g
  have hm : metadataAllowance src graph ≤ 50*(∑e,arity e)+10 := by
    unfold metadataAllowance
    rw [metadata_length,placements_length]
    change graph.factors.length ≤ _ at hf
    change graph.endpoints.length ≤ _ at he
    omega
  change graph.work+(activation.clock-src.state.clock)+ids.work+
    (pull ids.value graph.factors.flatten).work+metadataAllowance src graph+20 ≤ src.state.clock+_
  change ids.work ≤ _ at hb
  change _ ≤ src.state.clock+(SemiprimeD1OriginalChildGraphBudget.overhead n F r a (∑e,arity e)+
    SemiprimeD1ChildActivationBudget.overhead n F r a+
    (∑e,arity e)*(3*W+7)+2+(2*(∑e,arity e)^2)*((∑e,arity e)*(6*W+10)+7)+2+50*(∑e,arity e)+30)
  omega

/-- Original per-vertex searched order report: no port-map or successful-search advice. -/
theorem order_clock (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) (v : Fin (n+F)) :
    (SemiprimeD1ChildTableOrder.acquire owner (fromReplay owner (source n F r a arity owner) q g) v).clock ≤
      (source n F r a arity owner).state.clock+overhead n F r a (∑e,arity e)+
        SemiprimeD1ChildOrderBudget.overhead (∑e,arity e) (2*(∑e,arity e)^2) := by
  have h:=SemiprimeD1ChildOrderBudget.acquire_clock owner (fromReplay owner (source n F r a arity owner) q g) v
  have hdata:=fromReplay_work n F r a arity owner q g
  have hl:=links_length n F r a arity owner q g
  have hM : (fromReplay owner (source n F r a arity owner) q g).source.padding.source.selection.cache.data.metadata.incidences.length=
      ∑e,arity e:=metadata_length n F r a arity owner
  rw [hM] at h
  exact h.trans (Nat.add_le_add hdata (SemiprimeD1ChildOrderBudget.overhead_mono le_rfl hl))

end RiemannGaussian.SemiprimeD1ChildPullbackBudget
