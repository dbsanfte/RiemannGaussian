/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryExecution
import RiemannGaussian.SemiprimeD1StackPacketInventoryRowCost
/-! # Whole sparse inventory clock from the SAME actual source
The log reversal is charged from the real prehalt execution's cell bound.
No native inventory, dictionary or acquisition report supplies machine time.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryClock
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryEncoding
open SemiprimeD1StackPacketInventoryStepEncoding SemiprimeD1StackPacketInventoryWidths
open SemiprimeD1StackPacketInventoryRowCost SemiprimeD1StackPacketInventoryLoop
open SemiprimeD1StackPacketInventoryExecution SemiprimeD1StackPacketInventoryPrepare
open SemiprimeD1StackPacketInventoryPrimitives SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All actual two-input bytes and one source boundary cell. -/
def inputSize (a:Nat) (pairs:Pairs):Nat:=(vectorBits (keys pairs)).length+(alphabet a).length+1
/-- Fixed fourth-degree whole-source cap, independent of the graph, alphabet width and all values. -/
def polynomial (a:Nat) (pairs:Pairs):Nat:=1000000000000*(inputSize a pairs)^4
/-- Every retained original input role is bounded by the two actually provided words. -/
theorem initial_length (keys alphabet:List Bool) (k:Stack):
    ((initial keys alphabet).data k).length ≤ keys.length+alphabet.length+1:=by
  simp only [initial,input,Function.update_apply]
  split_ifs <;> first | omega | exact Nat.zero_le _
/-- The actual chronological loop sums only real per-occurrence caps. -/
theorem replayBound_le (a S m:Nat) (hS:1 ≤ S) (pairs:Pairs) (hv:Valid a pairs)
    (hm:m+pairs.length ≤ S) (ha:(alphabet a).length ≤ S) (s:Summary) (hs:Sized m S s)
    (hk:∀p∈pairs,(key p.1 p.2).length ≤ S):
    replayBound a s pairs ≤ pairs.length*(1000000000*S^3)+2:=by
  induction pairs generalizing m s with
  | nil=>simp only [replayBound,List.length_nil,Nat.zero_mul,Nat.zero_add];exact le_rfl
  | cons p ps ih=>
    have hp:=hv p List.mem_cons_self
    have hkey:=hk p List.mem_cons_self
    have hm':m+1 ≤ S:=by simp only [List.length_cons] at hm;omega
    have hrow:=rowBound_le a S m hS hm' ha s hs p.1 p.2 hp.1 hp.2 hkey
    have hnext:=ih (m+1) (fun q hq=>hv q (List.mem_cons_of_mem p hq))
      (by simp only [List.length_cons] at hm;omega)
      (step a s (key p.1 p.2)) (step_sized a m S s p.1 p.2 hp.1 hp.2 hS hm' ha hs hkey)
      (fun q hq=>hk q (List.mem_cons_of_mem p hq))
    simp only [replayBound,List.length_cons]
    nlinarith only [hrow,hnext]
/-- Actual same-source prefix bounds the retained reverse placement history before final transfer. -/
theorem history_paid (a:Nat) (pairs:Pairs) (hv:Valid a pairs):
    (history (acquire a (keys pairs)).placements).length ≤ inputSize a pairs+
      (5*(vectorBits (keys pairs)).length+8)+replayBound a empty pairs:=by
  have h0:=prepare_run (vectorBits (keys pairs)) (alphabet a)
  have hm:SemiprimeD1StackPacketInventorySeen.Markers empty.seen:=by intro r hr;cases hr
  obtain ⟨t,ht,h1⟩:=replay_run a pairs hv empty hm (vectorBits (keys pairs))
  have h:=join h0 h1
  obtain ⟨out,hr,hAt⟩:=h [] (source a (keys pairs)) ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program _ (inputSize a pairs) _ out
    (initial_length (vectorBits (keys pairs)) (alphabet a)) hr
  rw [hAt.2.1] at hd
  have hc:=hd placementHistory
  change (history (acquire a (keys pairs)).placements).reverse.length ≤ inputSize a pairs+
    (5*(vectorBits (keys pairs)).length+8+t) at hc
  simp only [List.length_reverse] at hc
  omega
/-- Entire actual successful source cap is a fixed polynomial in its own two physical input words. -/
theorem timeBound_le (a:Nat) (pairs:Pairs) (hv:Valid a pairs):timeBound a pairs ≤ polynomial a pairs:=by
  let S:=inputSize a pairs
  have hS:1 ≤ S:=by dsimp [S,inputSize];omega
  have hvlen:(vectorBits (keys pairs)).length ≤ S:=by dsimp [S,inputSize];omega
  have ha:(alphabet a).length ≤ S:=by dsimp [S,inputSize];omega
  have hm:pairs.length ≤ S:=by
    have hh:=SemiprimeD1TensorTapeCodec.vectorBits_length (keys pairs)
    have he:(keys pairs).length=pairs.length:=List.length_map _
    omega
  have hk:∀p∈pairs,(key p.1 p.2).length ≤ S:=by
    intro p hp
    have hh:=SemiprimeD1StackSourceKeyFrequencyBytes.raw_length_le (keys pairs) (key p.1 p.2)
      (List.mem_map.mpr ⟨p,hp,rfl⟩)
    exact hh.trans hvlen
  have hr:=replayBound_le a S 0 hS pairs hv (by omega) ha empty (empty_sized S) hk
  have hp:=Nat.mul_le_mul_right (1000000000*S^3) hm
  have hr':replayBound a empty pairs ≤ 1000000000*S^4+2:=by nlinarith only [hr,hp]
  have hh:=history_paid a pairs hv
  change (history (acquire a (keys pairs)).placements).length ≤ S+_+_ at hh
  have hpow:S ≤ S^4:=Nat.le_pow (by decide:0<(4:Nat))
  change timeBound a pairs ≤ 1000000000000*S^4
  unfold timeBound
  omega
/-- Same complete source and stopped bank with its own fixed physical-byte polynomial. -/
theorem source_run_bounded (a:Nat) (pairs:Pairs) (hv:Valid a pairs):
    ∃t ≤ polynomial a pairs,SemiprimeD1StackCalls.run program t (source a (keys pairs))=
      some (done (vectorBits (keys pairs)) (alphabet a) (acquire a (keys pairs))):=by
  obtain ⟨t,ht,hr⟩:=source_run a pairs hv
  exact ⟨t,ht.trans (timeBound_le a pairs hv),hr⟩
end RiemannGaussian.SemiprimeD1StackPacketInventoryClock
