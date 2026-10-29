/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryClock
/-! # Two physical input words, with original ID lineage used only in proofs -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryBounds
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryEncoding
open SemiprimeD1StackPacketInventoryStepEncoding SemiprimeD1StackPacketInventoryLoop
open SemiprimeD1StackPacketInventoryClock
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Proof-only acquired source lineage: each raw key contains two actual original catalogue IDs. -/
def ValidKeys (a:Nat) (rawKeys:List (List Bool)):Prop:=∀raw∈rawKeys,
  ∃owner factor,owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids ∧
    factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids ∧ raw=key owner factor
/-- Source lineage describes the existing physical key bytes; no pair, index or answer is installed into runtime. -/
theorem describe (a:Nat) (rawKeys:List (List Bool)) (hv:ValidKeys a rawKeys):
    ∃pairs:Pairs,Valid a pairs ∧ keys pairs=rawKeys:=by
  induction rawKeys with
  | nil=>
    refine ⟨[],?_,rfl⟩
    intro p hp;cases hp
  | cons raw rest ih=>
    obtain ⟨owner,factor,ho,hf,hkey⟩:=hv raw List.mem_cons_self
    obtain ⟨pairs,hpairs,heq⟩:=ih (fun q hq=>hv q (List.mem_cons_of_mem raw hq))
    refine ⟨(owner,factor)::pairs,?_,?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with hp|hp
      · cases hp;exact ⟨ho,hf⟩
      · exact hpairs p hp
    · change key owner factor::keys pairs=raw::rest
      rw [heq,←hkey]
/-- Own fixed fourth-degree cap expressed solely in the two actual physical input byte lengths. -/
def byteBound (keyBytes alphabet:List Bool):Nat:=1000000000000*(keyBytes.length+alphabet.length+1)^4
/-- Entire successful two-input actual source, without decoded pairs among runtime operands. -/
theorem source_run_keys (a:Nat) (rawKeys:List (List Bool)) (hv:ValidKeys a rawKeys):
    ∃t ≤ byteBound (vectorBits rawKeys) (alphabet a),SemiprimeD1StackCalls.run program t
      (initial (vectorBits rawKeys) (alphabet a))=
      some (done (vectorBits rawKeys) (alphabet a) (acquire a rawKeys)):=by
  obtain ⟨pairs,hpairs,hkeys⟩:=describe a rawKeys hv
  obtain ⟨t,ht,hr⟩:=source_run_bounded a pairs hpairs
  rw [hkeys] at hr
  refine ⟨t,?_,hr⟩
  simpa only [polynomial,inputSize,hkeys,byteBound] using ht
/-- SAME literal-source time certificate with exact physically acquired result. -/
noncomputable def sourceInventory (a:Nat) (rawKeys:List (List Bool)) (hv:ValidKeys a rawKeys):
    StateTransition.EvalsToInTime (SemiprimeD1StackCalls.step program)
      (initial (vectorBits rawKeys) (alphabet a))
      (some (done (vectorBits rawKeys) (alphabet a) (acquire a rawKeys)))
      (byteBound (vectorBits rawKeys) (alphabet a)):=by
  let h:=source_run_keys a rawKeys hv
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine fixed finite compiled source, with its own entire source clock. -/
noncomputable def machineInventory (a:Nat) (rawKeys:List (List Bool)) (hv:ValidKeys a rawKeys):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (vectorBits rawKeys) (alphabet a)))
      (some (SemiprimeD1StackCalls.configuration (done (vectorBits rawKeys) (alphabet a) (acquire a rawKeys))))
      (byteBound (vectorBits rawKeys) (alphabet a)):=
  SemiprimeD1StackCalls.evalsCorrect SemiprimeD1StackPacketInventory.source output (Label.local .start) program _ _ _ (sourceInventory a rawKeys hv)
end RiemannGaussian.SemiprimeD1StackPacketInventoryBounds
