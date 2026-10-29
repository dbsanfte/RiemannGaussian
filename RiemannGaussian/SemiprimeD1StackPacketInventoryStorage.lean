/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBounds
/-! # Every actual sparse inventory data role and real return cell at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryStorage
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryExecution
open SemiprimeD1StackPacketInventoryClock
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackPacketInventoryEncoding
/-- No reached prefix passes the actual same-program successful final halt. -/
theorem prefix_fuel (a:Nat) (pairs:SemiprimeD1StackPacketInventoryLoop.Pairs) (hv:SemiprimeD1StackPacketInventoryLoop.Valid a pairs)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (source a (SemiprimeD1StackPacketInventoryLoop.keys pairs))=some out):
    fuel ≤ polynomial a pairs :=by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded a pairs hv
  have hf:fuel ≤ t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hp
    have hh:SemiprimeD1StackCalls.run program 1 (done (vectorBits (SemiprimeD1StackPacketInventoryLoop.keys pairs)) (alphabet a) (acquire a (SemiprimeD1StackPacketInventoryLoop.keys pairs)))=none:=rfl
    rw [hh,Option.bind_none] at hp
    cases hp
  exact hf.trans ht
/-- SAME source trace counts all59 actual Bool stacks and every genuine nested return frame. -/
theorem prefix_cells (a:Nat) (pairs:SemiprimeD1StackPacketInventoryLoop.Pairs) (hv:SemiprimeD1StackPacketInventoryLoop.Valid a pairs)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (source a (SemiprimeD1StackPacketInventoryLoop.keys pairs))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      1000000000000000*(inputSize a pairs)^4 :=by
  let S:=inputSize a pairs
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ out (initial_length _ _) hp
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hp
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 59*(S+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(S+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel a pairs hv fuel out hp
  change fuel ≤ 1000000000000*S^4 at ht
  have hp:S≤S^4:=Nat.le_pow (by decide:0<(4:Nat))
  change _ ≤ 1000000000000000*S^4
  omega
/-- Every genuine compiled prefix includes the physical none-labelled return stack in the same polynomial byte cap. -/
theorem machine_prefix_cells (a:Nat) (pairs:SemiprimeD1StackPacketInventoryLoop.Pairs) (hv:SemiprimeD1StackPacketInventoryLoop.Valid a pairs)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (source a (SemiprimeD1StackPacketInventoryLoop.keys pairs))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000000000000*(inputSize a pairs)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct SemiprimeD1StackPacketInventory.source output (SemiprimeD1StackPacketInventory.Label.local .start)
    program fuel (source a (SemiprimeD1StackPacketInventoryLoop.keys pairs))
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel (source a (SemiprimeD1StackPacketInventoryLoop.keys pairs)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a pairs hv fuel out hout
/-- Every actual source prefix, specified directly from the two existing physical input words. -/
theorem prefix_cells_keys (a:Nat) (rawKeys:List (List Bool))
    (hv:SemiprimeD1StackPacketInventoryBounds.ValidKeys a rawKeys)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (vectorBits rawKeys) (alphabet a))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      1000000000000000*((vectorBits rawKeys).length+(alphabet a).length+1)^4:=by
  obtain ⟨pairs,hv,hkeys⟩:=SemiprimeD1StackPacketInventoryBounds.describe a rawKeys hv
  have hh:=prefix_cells a pairs hv fuel out (by simpa only [SemiprimeD1StackPacketInventoryEncoding.source,hkeys] using hp)
  simpa only [inputSize,hkeys] using hh
/-- Every actual compiled prefix counts all59 physical roles and the none-labelled genuine return stack. -/
theorem machine_prefix_cells_keys (a:Nat) (rawKeys:List (List Bool))
    (hv:SemiprimeD1StackPacketInventoryBounds.ValidKeys a rawKeys)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (vectorBits rawKeys) (alphabet a))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000000000000*((vectorBits rawKeys).length+(alphabet a).length+1)^4:=by
  obtain ⟨pairs,hv,hkeys⟩:=SemiprimeD1StackPacketInventoryBounds.describe a rawKeys hv
  have hh:=machine_prefix_cells a pairs hv fuel cfg (by simpa only [SemiprimeD1StackPacketInventoryEncoding.source,hkeys] using hp)
  simpa only [inputSize,hkeys] using hh
end RiemannGaussian.SemiprimeD1StackPacketInventoryStorage
