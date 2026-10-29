/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordPacketTableClock
import RiemannGaussian.SemiprimeD1ChildOriginalClock

/-! # Original-input word/tape child acquisition report
All original metadata, source fields and mode bounds are derived internally.
The displayed computed envelope keeps every source/header/fresh repetition;
no entry, inverse, Fits, metadata-clock or solved child answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildWordOriginalClock
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1ChildNetwork (graph packetIndex)
open SemiprimeD1ChildOriginalClock (source ports dataCap graphCap orderCap)
open SemiprimeD1WordPacketTableClock

/-- Literal original-derived child budget, preserving all source/header multiplicities.
The table and requested-coefficient exponential factors remain explicit. -/
def budget (net : Network) (old : Context) (extra : List ℕ) (D a u : ℕ) (i : Fin a) (Z : ℕ) : ℕ :=
  let src:=source net old a u i
  let M:=ports net
  let NF:=net.leftCount+net.rows.length
  let K:=SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
  let E:=SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
  let H:=src.work+SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
  src.work+dataCap net a+graphCap net a+Z+
    (NF*SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra src.precision D (orderCap net a)
      (SemiprimeD1NetworkStateResources.inventory net) NF+10*(NF+1))+
    M*rightClock ⟨extra++old.axes,src.precision⟩ a (2*2^a) K src.precision (2^a) src.precision K E H Z (graphCap net a) M+
    10*(NF+M+2*M^2+1)^3

/-- Pure routing/index monotonicity avoids unfolding any acquired source report. -/
theorem left_mono (old : Context) (extra : List ℕ) (p D O O' I v v' : ℕ)
    (hO:O ≤ O') (hv:v ≤ v') :
    SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra p D O I v ≤ 
      SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra p D O' I v' := by
  unfold SemiprimeD1ChildNetworkTapeBudget.leftBudget
  omega

/-- Pure header/graph/index monotonicity preserves all original repetitions. -/
theorem right_mono (ctx : Context) (a A K P T B L E H H' Z G G' e e' : ℕ)
    (hH:H ≤ H') (hG:G ≤ G') (he:e ≤ e') :
    rightClock ctx a A K P T B L E H Z G e ≤ rightClock ctx a A K P T B L E H' Z G' e' := by
  unfold rightClock tableClock
  omega

/-- All actual child-word/tape reports satisfy their computed original-input envelope. -/
theorem fromSource_clock (net : Network) (old : Context) (extra : List ℕ) (D a u : ℕ)
    (i : Fin a) (g : Fin 64) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hbeta:beta∈(source net old a u i).modes.values)
    (hw:WellFormed net) (hg:Good old net) (he:0<extra.prod)
    (hz:SemiprimeD1JetAffineCoefficientBounds.Good
      ⟨extra++old.axes,(source net old a u i).precision⟩ z.words)
    (hd:DegreeBound net D) (hslots:2*2^a  ≤  D) :
    (SemiprimeD1ChildWordNetwork.fromSource net (source net old a u i) i g old extra
      (source net old a u i).precision z t beta).clock  ≤  budget net old extra D a u i z.clock := by
  let src:=source net old a u i
  let M:=ports net
  let NF:=net.leftCount+net.rows.length
  let K:=SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
  let data:=SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) src.packets i g
  let G:=graph net src i g
  let rows:=SemiprimeD1TensorNetworkLayout.childRows G
  let ctx:Context:=⟨extra++old.axes,src.precision⟩
  let E:=SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
  let H:=src.work+SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
  let L:=SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra src.precision D (orderCap net a)
    (SemiprimeD1NetworkStateResources.inventory net) NF
  let R:=rightClock ctx a (2*2^a) K src.precision (2^a) src.precision K E H z.clock (graphCap net a) M
  have hbs:=SemiprimeD1PhysicalSourceBudget.mode_bounds net.leftCount net.rows.length 64 a u i.val old.precision
    (arity net.rows) (owner net.rows) beta hbeta
  have hbetaLength:beta.length=K:=by
    dsimp only [K,SemiprimeD1ChildModeResources.catalogueLength]
    rw [SemiprimeD1ModeCatalog.catalog_length]
    exact hbs.1
  have hb:∀b∈beta,b  ≤  src.precision:=fun b hm=>(hbs.2 b hm).trans (Nat.sub_le _ _)
  have hdata:data.work  ≤  dataCap net a:=by
    have h:=SemiprimeD1ChildPullbackBudget.fromReplay_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
    have hs:=SemiprimeD1PacketReplayBudget.acquire_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)
    exact h.trans (Nat.add_le_add_right hs _)
  have hgraph:G.work  ≤  graphCap net a:=by
    have h:=SemiprimeD1OriginalChildGraphBudget.fromReplay_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
    have hs:=SemiprimeD1PacketReplayBudget.acquire_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)
    exact h.trans (Nat.add_le_add_right hs _)
  have hlinks:data.links.length  ≤  2*M^2:=SemiprimeD1ChildPullbackBudget.links_length
    net.leftCount net.rows.length 64 a (arity net.rows) (owner net.rows) i g
  have hrows:rows.length  ≤  M:=by
    rw [SemiprimeD1TensorNetworkLayout.childRows_length]
    exact SemiprimeD1OriginalChildGraphBudget.factors_length net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
  have hleft (v:Fin NF):(SemiprimeD1ChildNetworkTape.leftOne net data old extra src.precision v).2  ≤  L:=by
    have hf:=SemiprimeD1ChildOriginalFields.left_fields net a u i g old extra src.precision z t beta D hw hd hslots v
    have hc:=SemiprimeD1ChildNetworkTapeBudget.leftOne_clock net data old extra src.precision D v hg he
      hf.1 hf.2.1 hf.2.2.1
    have ho:=SemiprimeD1ChildPullbackBudget.order_clock net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g v
    have hs:=SemiprimeD1PacketReplayBudget.acquire_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)
    have ho':(SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v).clock  ≤  orderCap net a:=
      ho.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) _)
    exact hc.trans (left_mono old extra src.precision D _ (orderCap net a)
      (SemiprimeD1NetworkStateResources.inventory net) v.val NF ho' v.isLt.le)
  have hright (e:Fin rows.length):
      (SemiprimeD1ChildWordNetwork.rightOne net src i g ctx z t beta e).2  ≤  R:=by
    let packet:=packetIndex net src i g e
    let header:=SemiprimeD1PacketTensorTables.prepare (owner net.rows) src packet i g
    have hA:=SemiprimeD1PacketTensorTables.original_degree_bound net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hK:=SemiprimeD1ChildOriginalFields.header_items_length net src i g packet
    have hc:=SemiprimeD1PacketModeMaskBudget.prepare_item_caps net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hpayload:=SemiprimeD1PacketModeMaskBudget.prepare_payload net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hh:=SemiprimeD1PacketModeMaskBudget.prepare_clock net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hr:=rightOne_clock net src i g ctx z hz t beta e (2*2^a) K src.precision (2^a) src.precision E
      hA hK (fun item hm=>(hc item hm).1) (fun item hm=>(hc item hm).2) hb
      (fun endpoint hm=>(hpayload endpoint hm).2.2) (fun endpoint hm=>(hpayload endpoint hm).2.1)
    rw [hbetaLength] at hr
    exact hr.trans (right_mono ctx a (2*2^a) K src.precision (2^a) src.precision K E
      header.clock H z.clock G.work (graphCap net a) e.val M hh hgraph (e.isLt.le.trans hrows))
  have hleftSum:(SemiprimeD1ChildNetworkTape.acquireLeft net data old extra src.precision).clock  ≤  NF*L+10*(NF+1):=by
    rw [SemiprimeD1ChildNetworkTape.acquireLeft_clock]
    simp only [Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
    exact Nat.add_le_add_right (SemiprimeD1ChildNetworkClock.ofFn_sum_le NF _ L hleft) _
  have hrightSum:((Vector.ofFn (fun e:Fin rows.length=>
      SemiprimeD1ChildWordNetwork.rightOne net src i g ctx z t beta e)).toList.map Prod.snd).sum  ≤  M*R:=by
    simp only [Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
    exact (SemiprimeD1ChildNetworkClock.ofFn_sum_le rows.length _ R hright).trans
      (Nat.mul_le_mul_right _ hrows)
  have hcontrol:10*(NF+rows.length+data.links.length+1)^3 ≤ 10*(NF+M+2*M^2+1)^3:=
    Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hrows NF) hlinks) 1) 3)
  change src.work+data.work+G.work+z.clock+
    (SemiprimeD1ChildNetworkTape.acquireLeft net data old extra src.precision).clock+
    ((Vector.ofFn (fun e:Fin rows.length=>SemiprimeD1ChildWordNetwork.rightOne net src i g ctx z t beta e)).toList.map Prod.snd).sum+
    10*(NF+rows.length+data.links.length+1)^3  ≤  _
  unfold budget
  change src.work+data.work+G.work+z.clock+
    (SemiprimeD1ChildNetworkTape.acquireLeft net data old extra src.precision).clock+
    ((Vector.ofFn (fun e:Fin rows.length=>SemiprimeD1ChildWordNetwork.rightOne net src i g ctx z t beta e)).toList.map Prod.snd).sum+
    10*(NF+rows.length+data.links.length+1)^3  ≤  
    src.work+dataCap net a+graphCap net a+z.clock+(NF*L+10*(NF+1))+M*R+10*(NF+M+2*M^2+1)^3
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add_left hdata src.work) hgraph) z.clock) hleftSum) hrightSum)
    hcontrol
end RiemannGaussian.SemiprimeD1ChildWordOriginalClock
