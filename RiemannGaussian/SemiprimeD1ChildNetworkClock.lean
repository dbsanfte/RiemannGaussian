/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildClockFactor

/-! # Concrete child-network table/report composition
This internal composition theorem is followed by original-constructor supplier
bounds. It retains every source, pullback, graph, header and fresh report at the
multiplicity of the existing runtime; there is no silent sharing of reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildNetworkClock
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1ChildNetwork
open SemiprimeD1ChildTableClock SemiprimeD1PacketTableClock SemiprimeD1ChildClockFactor

/-- A finite cached vector report sum is bounded by its literal number of entries. -/
theorem ofFn_sum_le (n : ℕ) (f : Fin n → ℕ) (B : ℕ) (h : ∀i,f i ≤ B) :
    (List.ofFn f).sum ≤ n*B := by
  induction n with
  | zero => simp only [List.ofFn_zero,List.sum_nil,Nat.zero_mul,le_refl]
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons]
    have hh := h 0
    have ht := ih (fun i => f i.succ) (fun i => h i.succ)
    calc
      _ ≤ B+n*B := Nat.add_le_add hh ht
      _ = _ := by ring

/-- Fixed arithmetic prefactor; source/header/routing costs occur at their
actual vertex multiplicities, not once for the entire network. -/
def prefactor (old : Context) (extra : List ℕ) (p a D A K P T B L E NF Fchild links S W G Z O H : ℕ) : ℕ :=
  S+W+G+Z+NF*leftPolynomial old extra p D O NF+
    Fchild*rightPolynomial ⟨extra++old.axes,p⟩ a A K P T B L E H Z G Fchild+
    10*(NF+Fchild+links+1)^3

/-- Complete actual child-network report at the global eager degree scale. -/
def budget (old : Context) (extra : List ℕ) (p a D A K P T B L E NF Fchild links S W G Z O H : ℕ) : ℕ :=
  prefactor old extra p a D A K P T B L E NF Fchild links S W G Z O H*2^D

/-- Concrete table composition. Original numeric/table-field and metadata
supplier premises are all discharged by the original-source wrapper; no
requested entry/coefficient or intermediate physical Fits answer occurs here. -/
theorem fromSource_clock {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (D A K P T B E O H : ℕ) (hg : Good old net) (he : 0 < extra.prod)
    (hz : SemiprimeD1JetAffineCoefficientBounds.Good ⟨extra++old.axes,p⟩ z.words)
    (hbeta : ∀b∈beta,b ≤ B)
    (hcoefficient : 2^A*(K+1)^A ≤ 2^D)
    (hleft : ∀v : Fin (net.leftCount+net.rows.length),
      let data := SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) source.packets i g
      let order := SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v
      order.old.length ≤ D ∧ order.child.length ≤ D ∧
        (leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length ≤ D ∧
        (parentVertex net v).ports.length ≤ D ∧ order.clock ≤ O)
    (hright : ∀e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length,
      let header := SemiprimeD1PacketTensorTables.prepare (owner net.rows) source (packetIndex net source i g e) i g
      header.endpoints.length ≤ A ∧ header.masks.items.length=K ∧
      (∀item∈header.masks.items,item.mode.order ≤ P) ∧
      (∀item∈header.masks.items,item.tile ≤ T) ∧
      (∀endpoint∈header.endpoints,endpoint.slot.length ≤ a) ∧
      (∀endpoint∈header.endpoints,endpoint.edge.length ≤ E) ∧ header.clock ≤ H) :
    let data := SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) source.packets i g
    let childGraph := graph net source i g
    let Fchild := (SemiprimeD1TensorNetworkLayout.childRows childGraph).length
    (fromSource net source i g old extra p z t beta).clock ≤
      budget old extra p a D A K P T B beta.length E (net.leftCount+net.rows.length) Fchild
        data.links.length source.work data.work childGraph.work z.clock O H := by
  dsimp only
  let data := SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) source.packets i g
  let childGraph := graph net source i g
  let rows := SemiprimeD1TensorNetworkLayout.childRows childGraph
  let L := leftPolynomial old extra p D O (net.leftCount+net.rows.length)
  let R := rightPolynomial ⟨extra++old.axes,p⟩ a A K P T B beta.length E H z.clock childGraph.work rows.length
  have hleftClock (v : Fin (net.leftCount+net.rows.length)) :
      (leftOne net data old extra p v).2 ≤ L*2^D := by
    have hv := hleft v
    have hc := leftOne_clock net data old extra p D v hg he hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    have hp := leftBudget_factor old extra p D
      (SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v).clock v.val
    have hm : leftPolynomial old extra p D
        (SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v).clock v.val ≤ L := by
      dsimp only [L,leftPolynomial]
      gcongr
      · exact hv.2.2.2.2
      · exact v.isLt.le
    exact hc.trans (hp.trans (Nat.mul_le_mul_right _ hm))
  have hrightClock (e : Fin rows.length) :
      (rightOne net source i g ⟨extra++old.axes,p⟩ z t beta e).2 ≤ R*2^D := by
    have hv := hright e
    have hc := rightOne_clock net source i g ⟨extra++old.axes,p⟩ z hz t beta e A K P T B E
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hbeta hv.2.2.2.2.1 hv.2.2.2.2.2.1
    have hp := rightClock_factor ⟨extra++old.axes,p⟩ a A K P T B beta.length E
      (SemiprimeD1PacketTensorTables.prepare (owner net.rows) source (packetIndex net source i g e) i g).clock
      z.clock childGraph.work e.val
    have hm : rightPolynomial ⟨extra++old.axes,p⟩ a A K P T B beta.length E
      (SemiprimeD1PacketTensorTables.prepare (owner net.rows) source (packetIndex net source i g e) i g).clock
      z.clock childGraph.work e.val ≤ R := by
      dsimp only [R,rightPolynomial,rightControls]
      gcongr
      · exact hv.2.2.2.2.2.2
      · exact e.isLt.le
    exact hc.trans (hp.trans (Nat.mul_le_mul hm hcoefficient))
  have hls := ofFn_sum_le (net.leftCount+net.rows.length)
    (fun v => (leftOne net data old extra p v).2) (L*2^D) hleftClock
  have hrs := ofFn_sum_le rows.length
    (fun e => (rightOne net source i g ⟨extra++old.axes,p⟩ z t beta e).2) (R*2^D) hrightClock
  have hdecomp : (fromSource net source i g old extra p z t beta).clock =
      source.work+data.work+childGraph.work+z.clock+
      (List.ofFn (fun v => (leftOne net data old extra p v).2)).sum+
      (List.ofFn (fun e => (rightOne net source i g ⟨extra++old.axes,p⟩ z t beta e).2)).sum+
      10*(net.leftCount+net.rows.length+rows.length+data.links.length+1)^3 := by
    simp only [fromSource,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
    rfl
  rw [hdecomp]
  have hsum := Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add_left hls (source.work+data.work+childGraph.work+z.clock)) hrs)
    (10*(net.leftCount+net.rows.length+rows.length+data.links.length+1)^3)
  apply hsum.trans
  have hq : 1 ≤ (2:ℕ)^D := Nat.one_le_pow _ _ (by decide)
  have ho : source.work+data.work+childGraph.work+z.clock+
      10*(net.leftCount+net.rows.length+rows.length+data.links.length+1)^3 ≤
      (source.work+data.work+childGraph.work+z.clock+
      10*(net.leftCount+net.rows.length+rows.length+data.links.length+1)^3)*2^D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ hq
  calc
    _ = source.work+data.work+childGraph.work+z.clock+
        10*(net.leftCount+net.rows.length+rows.length+data.links.length+1)^3+
        ((net.leftCount+net.rows.length)*L+rows.length*R)*2^D := by ring
    _ ≤ (source.work+data.work+childGraph.work+z.clock+
        10*(net.leftCount+net.rows.length+rows.length+data.links.length+1)^3)*2^D+
        ((net.leftCount+net.rows.length)*L+rows.length*R)*2^D := Nat.add_le_add_right ho _
    _ = _ := by unfold budget prefactor L R;ring

end RiemannGaussian.SemiprimeD1ChildNetworkClock
