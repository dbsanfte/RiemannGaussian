/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryStep
/-! # Whole physical source-vector replay
The pair list describes the already acquired literal source bytes only. Neither
this list nor any native inventory or budget occurs in the runtime program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryLoop
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryClass
open SemiprimeD1StackPacketInventoryStepEncoding SemiprimeD1StackPacketInventoryStep
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Proof description of physical compact-ID source fields. -/
abbrev Pairs:=List (List Bool × List Bool)
/-- Exact chronological raw joint keys; the factor ID is the unframed tail. -/
def keys (pairs:Pairs):List (List Bool):=pairs.map (fun p=>key p.1 p.2)
/-- Both IDs really belong to the acquired original alphabet catalogue. -/
def Valid (a:Nat) (pairs:Pairs):Prop:=∀p∈pairs,
    p.1∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids ∧
    p.2∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids
/-- Sum of caps of the same actual per-occurrence source fragments. -/
def replayBound (a:Nat) (s:Summary):Pairs → Nat
  | []=>2
  | p::ps=>rowBound a s p.1 p.2+replayBound a (step a s (key p.1 p.2)) ps
local notation "ctl"=>Label.local
/-- Actual false terminator pop and actual EOF check finish an exhausted source cursor. -/
theorem empty_run (source alphabet:List Bool) (s:Summary):
    Runs program 2 (ctl .header) (boundary source alphabet [false] s)
      (ctl .seedOutput) (boundary source alphabet [] s):=by
  let f:=fresh source [false] [] (Dict.dictionary s.classes) s.edge
  let r:=reader (vectorBits s.packets) (history s.placements).reverse [] [] []
  let o:=orientation alphabet (Dict.dictionary s.seen) (Dict.dictionary s.slots) [] [] [] []
  have h0:=pop_run .header (ctl .abort) (ctl .eof) (ctl .parse) stream (view f r o) [false] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view f r o) (frequencyStack (F.aux .reader)) []) at h0
  rw [update_reader] at h0
  have h1:=peek_run .eof (ctl .seedOutput) (ctl .abort) (ctl .abort) stream
    (view ({f with reader:=[]}) r o) [] rfl rfl
  exact join h0 h1
/-- The complete actual source loop, including every repeated key and the final physical terminator. -/
theorem replay_run (a:Nat) (pairs:Pairs) (hv:Valid a pairs) (s:Summary)
    (hm:SemiprimeD1StackPacketInventorySeen.Markers s.seen) (source:List Bool):
    ∃t ≤ replayBound a s pairs,Runs program t (ctl .header)
      (boundary source (alphabet a) (vectorBits (keys pairs)) s) (ctl .seedOutput)
      (boundary source (alphabet a) [] ((keys pairs).foldl (step a) s)):=by
  induction pairs generalizing s with
  | nil=>exact ⟨2,le_rfl,empty_run source (alphabet a) s⟩
  | cons p ps ih=>
    have hp:=hv p (List.mem_cons_self)
    have htail:Valid a ps:=fun q hq=>hv q (List.mem_cons_of_mem p hq)
    obtain ⟨t0,ht0,h0⟩:=row_run a s p.1 p.2 source (vectorBits (keys ps)) hp.1 hp.2 hm
    obtain ⟨t1,ht1,h1⟩:=ih htail (step a s (key p.1 p.2)) (step_markers a s (key p.1 p.2) hm)
    refine ⟨t0+t1,?_,join h0 h1⟩
    exact Nat.add_le_add ht0 ht1
end RiemannGaussian.SemiprimeD1StackPacketInventoryLoop
