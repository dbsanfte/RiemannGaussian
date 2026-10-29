/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordPacketEntryClock
import RiemannGaussian.SemiprimeD1ChildWordNetwork
import RiemannGaussian.SemiprimeD1ChildNetworkTapeBudget
import RiemannGaussian.SemiprimeD1ChildTableClock

/-! # Actual eager packet-table acquisition and canonical recopy clock
The actual header and fresh producer are retained per table. Every assignment
executes the concrete packet evaluator; its coefficient-recursion factor is
kept explicit until the original schedule absorbs it.
-/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordPacketTableClock
open SemiprimeD1JetAxes SemiprimeD1JetAffineCoefficient SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1JetWordPacketEntryBits SemiprimeD1WordPacketEntryClock
open SemiprimeD1PacketEntryBits (borrow)
open SemiprimeD1ChildNetworkTapeBudget (copyTable_clock)
open SemiprimeD1ChildTableCopyTape (tapeBudget tableCap)
open SemiprimeD1ChildNetwork

/-- Actual complete eager packet table, with producer/header retained once. -/
def tableClock (ctx : Context) (a A K P T B L E H Z : ℕ) : ℕ :=
  H+Z+(entryClock ctx a A K P T B L E+7)*2^A+L+12

/-- Every actual assignment is charged; numerical caps describe original
acquired data only, never desired table/entry/clock answers. -/
theorem acquire_clock {V : ℕ} (header : SemiprimeD1PacketTensorTables.Header V)
    (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) (A K P T B E : ℕ)
    (hA : header.endpoints.length  ≤  A) (hK : header.masks.items.length=K)
    (hmode : ∀item∈header.masks.items,item.mode.order  ≤  P)
    (htile : ∀item∈header.masks.items,item.tile  ≤  T) (hbeta : ∀b∈beta,b  ≤  B)
    (hslot : ∀e∈header.endpoints,e.slot.length  ≤  a) (hedge : ∀e∈header.endpoints,e.edge.length  ≤  E) :
    (SemiprimeD1JetWordPacketTables.acquire header ctx z a i t beta).clock  ≤ 
      tableClock ctx a A K P T B beta.length E header.clock z.clock := by
  have hbuild := SemiprimeD1TensorTables.build_clock header.endpoints.length
    (entryClock ctx a A K P T B beta.length E)
    (evaluate ctx (borrow z) a i t header.masks header.endpoints beta) (by
      intro bits _
      have h := evaluate_clock ctx (borrow z) hz a i t header.masks header.endpoints beta bits P T B E
        hmode htile hbeta hslot hedge
      rw [hK] at h
      exact h.trans (entryClock_mono_arity ctx a _ A K P T B beta.length E hA))
  have hpow : 2^header.endpoints.length  ≤  (2:ℕ)^A := Nat.pow_le_pow_right (by decide) hA
  have hcap := Nat.mul_le_mul_left (entryClock ctx a A K P T B beta.length E+7) hpow
  have hout : (SemiprimeD1TensorTables.build header.endpoints.length
      (evaluate ctx (borrow z) a i t header.masks header.endpoints beta)).clock  ≤ 
      (entryClock ctx a A K P T B beta.length E+7)*2^A :=
    (Nat.le_trans (Nat.le_add_right _ 5) hbuild).trans hcap
  change header.clock+z.clock+
    (SemiprimeD1TensorTables.build header.endpoints.length
      (evaluate ctx (borrow z) a i t header.masks header.endpoints beta)).clock+beta.length+12  ≤  _
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left hout (header.clock+z.clock)) beta.length) 12

/-- Whole actual new-factor vertex, including repeated graph acquisition and table recopy. -/
def rightClock (ctx : Context) (a A K P T B L E H Z G e : ℕ) : ℕ :=
  tableClock ctx a A K P T B L E H Z+G+(tapeBudget (tableCap ctx A)+7)*2^A+A+e+10

/-- Actual right-vertex acquisition retains its header, fresh input, graph and
full canonical-port recopy reports separately. -/
theorem rightOne_clock {r a : ℕ} (net : SemiprimeD1TensorNetwork.Network) (source : Source net a)
    (i : Fin a) (g : Fin r) (ctx : Context) (z : JetRun) (hz : Good ctx z.words)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length)
    (A K P T B E : ℕ)
    (hA : (SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).endpoints.length  ≤  A)
    (hK : (SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).masks.items.length=K)
    (hmode : ∀item∈(SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).masks.items,item.mode.order  ≤  P)
    (htile : ∀item∈(SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).masks.items,item.tile  ≤  T)
    (hbeta : ∀b∈beta,b  ≤  B)
    (hslot : ∀endpoint∈(SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).endpoints,endpoint.slot.length  ≤  a)
    (hedge : ∀endpoint∈(SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).endpoints,endpoint.edge.length  ≤  E) :
    (SemiprimeD1ChildWordNetwork.rightOne net source i g ctx z t beta e).2  ≤ 
      rightClock ctx a A K P T B beta.length E
        (SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
          source (packetIndex net source i g e) i g).clock z.clock (graph net source i g).work e.val := by
  let header := SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
    source (packetIndex net source i g e) i g
  let table := SemiprimeD1JetWordPacketTables.acquire header ctx z a i t beta
  let ports := SemiprimeD1TensorNetwork.rightPorts
    (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)) e
  have htable := acquire_clock header ctx z hz a i t beta A K P T B E hA hK hmode htile hbeta hslot hedge
  have hgood := SemiprimeD1JetWordPacketTables.acquire_good header ctx z a i t beta
  have hcopy := copyTable_clock ports table.table
  have hports : ports.length  ≤  A := (rightOne_degree net source i g e).le.trans hA
  have hstorage:=SemiprimeD1ChildTableCopyTape.storage_le_cap ctx table.table hgood A hA
  have hlookup:=Nat.add_le_add_right (SemiprimeD1ChildTableCopyTape.tapeBudget_mono hstorage) 7
  have hpow : 2^ports.length  ≤  (2:ℕ)^A := Nat.pow_le_pow_right (by decide) hports
  have hcopyCap : (SemiprimeD1ChildNetworkTape.copyTable ports table.table).2  ≤  (tapeBudget (tableCap ctx A)+7)*2^A :=
    hcopy.trans (Nat.mul_le_mul hlookup hpow)
  change table.clock+(graph net source i g).work+(SemiprimeD1ChildNetworkTape.copyTable ports table.table).2+ports.length+e.val+10  ≤  _
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add htable (le_refl _)) hcopyCap) hports) e.val) 10

end RiemannGaussian.SemiprimeD1WordPacketTableClock
