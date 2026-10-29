/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkTape

/-! # Complete active old-table tape-copy report bounds
Repeated alignment, individual lifts and recopy scans remain in the actual
budget. Degree guards concern literal input/output scopes, never clock advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1ChildNetworkTapeBudget
open SemiprimeD1JetAxes SemiprimeD1TensorTables SemiprimeD1ChildNetworkTape
open SemiprimeD1ChildNetwork (Pullback parentVertex parentVertex_good)
open SemiprimeD1ChildTableCopyTape (tapeBudget tableCap)

/-- Every canonical-port table recopy serializes and scans its actual source each time. -/
theorem copyTable_clock {d : ℕ} (ports : List ℕ) (table : Table d) :
    (copyTable ports table).2 ≤ (tapeBudget (storage table)+7)*2^ports.length := by
  have h:=build_clock ports.length (tapeBudget (storage table))
    (fun bits => SemiprimeD1TensorTapeLookup.fromTable table bits)
    (fun bits _ => SemiprimeD1ChildTableCopyTape.fromTable_clock table bits)
  change (build ports.length (fun bits => SemiprimeD1TensorTapeLookup.fromTable table bits)).clock+3 ≤ _
  omega

/-- Actual parent storage is contained in the literal current network inventory. -/
theorem parent_storage_le (net : SemiprimeD1TensorNetwork.Network)
    (v : Fin (net.leftCount+net.rows.length)) :
    storage (parentVertex net v).table ≤ SemiprimeD1NetworkStateResources.inventory net := by
  have h:=SemiprimeD1TensorTapeOriginal.member_le_sum (SemiprimeD1TensorNetwork.vertices net)
    (fun w => storage w.table+w.ports.length+1) (parentVertex net v) (List.getElem_mem _)
  unfold SemiprimeD1NetworkStateResources.inventory
  omega

/-- Fixed positive-polynomial overhead in input inventory and explicit local table caps. -/
def leftBudget (old : Context) (extra : List ℕ) (p D O I v : ℕ) : ℕ :=
  2*O+(tapeBudget I+7)*2^D+
    SemiprimeD1ChildTensorTablesTape.cacheBudget old extra p D (tableCap old D)+
    (tapeBudget (tableCap ⟨extra++old.axes,p⟩ D)+7)*2^D+D+v+12

/-- Actual leftOne pays two routing acquisitions, full eager alignment, every
per-entry integer lift, and full canonical recopy, with no external work supplier. -/
theorem leftOne_clock {a : ℕ} (net : SemiprimeD1TensorNetwork.Network)
    (data : Pullback net a) (old : Context) (extra : List ℕ) (p D : ℕ)
    (v : Fin (net.leftCount+net.rows.length))
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod)
    (ho : (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).old.length ≤ D)
    (hc : (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).child.length ≤ D)
    (hp : (SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length ≤ D) :
    (leftOne net data old extra p v).2 ≤ leftBudget old extra p D
      (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).clock
      (SemiprimeD1NetworkStateResources.inventory net) v.val := by
  let order:=SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v
  let parent:=parentVertex net v
  let aligned:=build order.old.length (fun bits => SemiprimeD1TensorTapeLookup.fromTable parent.table bits)
  let copied:=SemiprimeD1ChildTensorTablesTape.fromCache
    (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p aligned.table
  let ports:=SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v
  have hparent:=parentVertex_good old net hg v
  have haligned:=build_clock order.old.length (tapeBudget (storage parent.table))
    (fun bits => SemiprimeD1TensorTapeLookup.fromTable parent.table bits)
    (fun bits _ => SemiprimeD1ChildTableCopyTape.fromTable_clock parent.table bits)
  have haGood : Good old aligned.table := build_good old _ _ (by
    intro bits _
    rw [SemiprimeD1TensorTapeLookup.fromTable_words]
    exact lookup_good old parent.table hparent bits)
  have hcClock:=SemiprimeD1ChildTensorTablesTape.fromCache_clock
    (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p D aligned.table haGood he ho hc
  have hcGood:=SemiprimeD1ChildTensorTablesTape.fromCache_good
    (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p aligned.table haGood he
  have hcopy:=copyTable_clock ports copied.table
  have hdegree : copied.degree ≤ D := by
    dsimp only [copied,SemiprimeD1ChildTensorTablesTape.fromCache]
    split
    · exact hc
    · exact Nat.zero_le _
  have hAS:=SemiprimeD1ChildTableCopyTape.storage_le_cap old aligned.table haGood D ho
  have hCS:=SemiprimeD1ChildTableCopyTape.storage_le_cap ⟨extra++old.axes,p⟩ copied.table hcGood D hdegree
  have hA : (tapeBudget (storage parent.table)+7)*2^order.old.length ≤
      (tapeBudget (SemiprimeD1NetworkStateResources.inventory net)+7)*2^D := by
    apply Nat.mul_le_mul
    · exact Nat.add_le_add_right (SemiprimeD1ChildTableCopyTape.tapeBudget_mono (parent_storage_le net v)) 7
    · exact Nat.pow_le_pow_right (by decide) ho
  have hC : (tapeBudget (storage copied.table)+7)*2^ports.length ≤
      (tapeBudget (tableCap ⟨extra++old.axes,p⟩ D)+7)*2^D := by
    apply Nat.mul_le_mul
    · exact Nat.add_le_add_right (SemiprimeD1ChildTableCopyTape.tapeBudget_mono hCS) 7
    · exact Nat.pow_le_pow_right (by decide) hp
  have ha' : aligned.clock ≤ (tapeBudget (SemiprimeD1NetworkStateResources.inventory net)+7)*2^D :=
    (Nat.le_trans (Nat.le_add_right aligned.clock 5) haligned).trans hA
  have hc' : copied.clock ≤ order.clock+
      SemiprimeD1ChildTensorTablesTape.cacheBudget old extra p D (tableCap old D) :=
    hcClock.trans (Nat.add_le_add_left
      (SemiprimeD1ChildTensorTablesTape.cacheBudget_mono old extra p D hAS) order.clock)
  have hr' : (copyTable ports copied.table).2 ≤
      (tapeBudget (tableCap ⟨extra++old.axes,p⟩ D)+7)*2^D := hcopy.trans hC
  have hleft : (leftOne net data old extra p v).2=
      order.clock+aligned.clock+copied.clock+(copyTable ports copied.table).2+ports.length+v.val+12 := rfl
  have hports : ports.length ≤ D := hp
  rw [hleft]
  calc
    _ ≤ order.clock+(tapeBudget (SemiprimeD1NetworkStateResources.inventory net)+7)*2^D+
        (order.clock+SemiprimeD1ChildTensorTablesTape.cacheBudget old extra p D (tableCap old D))+
        (tapeBudget (tableCap ⟨extra++old.axes,p⟩ D)+7)*2^D+D+v.val+12 := by omega
    _ = _ := by unfold leftBudget;ring

/-- A computed literal scope cap, not a supplied degree/clock certificate. -/
def localDegree {a : ℕ} (net : SemiprimeD1TensorNetwork.Network) (data : Pullback net a)
    (v : Fin (net.leftCount+net.rows.length)) : ℕ :=
  let order:=SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v
  order.old.length+order.child.length+
    (SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length

/-- Closed actual old-vertex report from literal network/routing data only. -/
theorem leftOne_clock_closed {a : ℕ} (net : SemiprimeD1TensorNetwork.Network)
    (data : Pullback net a) (old : Context) (extra : List ℕ) (p : ℕ)
    (v : Fin (net.leftCount+net.rows.length))
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod) :
    (leftOne net data old extra p v).2 ≤ leftBudget old extra p (localDegree net data v)
      (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).clock
      (SemiprimeD1NetworkStateResources.inventory net) v.val := by
  apply leftOne_clock net data old extra p _ v hg he
  all_goals unfold localDegree;dsimp only;omega

/-- The complete static left cache retains every actual repeated eager-copy report. -/
theorem acquireLeft_clock_bound {a : ℕ} (net : SemiprimeD1TensorNetwork.Network)
    (data : Pullback net a) (old : Context) (extra : List ℕ) (p : ℕ)
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod) :
    (acquireLeft net data old extra p).clock ≤
      (List.ofFn (fun v : Fin (net.leftCount+net.rows.length) =>
        leftBudget old extra p (localDegree net data v)
          (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).clock
          (SemiprimeD1NetworkStateResources.inventory net) v.val)).sum+
      10*(net.leftCount+net.rows.length+1) := by
  rw [acquireLeft_clock]
  apply Nat.add_le_add_right
  simp only [Vector.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  apply Finset.sum_le_sum
  intro v hv
  exact leftOne_clock_closed net data old extra p v hg he

end RiemannGaussian.SemiprimeD1ChildNetworkTapeBudget
