/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataPrimitives
/-! # Actual bootstrap and repeated add-two calls with real return frames -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadataCalls
open SemiprimeD1StackPackedRootMetadata SemiprimeD1StackPackedRootMetadataEncoding
open SemiprimeD1StackPackedRootMetadataPrimitives SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
local notation "ctl" => Label.local
/-- Whole binary bootstrap physically restores N and acquires its actual width. -/
theorem boot_call (bits : List Bool) :
    Runs program (5*bits.length+5) (ctl .start) (input bits) (ctl .seedBase)
      (bank (B.done bits).store (fun _ => []) (fun _ => [])) := by
  let before := input bits
  let source := SemiprimeD1BinaryBootstrap.state .scan false none bits [] [] []
  let after := bank (B.done bits).store (fun _ => []) (fun _ => [])
  have hi : Link.DataRel boot before source.store before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel boot before (B.done bits).store after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
  have h := included_call program boot Label.boot boot_injective B.code (.scan,false) (fun _ => rfl)
    (ctl .start) (ctl .seedBase) rfl (5*bits.length+4) source (B.done bits) before after rfl rfl
    (SemiprimeD1BinaryBootstrap.bootstrap_run bits) hi ho
  exact h

/-- Exact physically executed add-two source clock plus its real caller return. -/
def addTime (word : List Bool) : ℕ :=
  3*(max word.length [false,true].length+1)+2*(addBits word [false,true] false).bits.length+3

/-- Complete real add-two consumes the actual running binary precision and
literal two, clears its real scratch, and retains the entire bootstrap bank. -/
theorem add_call (b : B.Stack→List Bool) (u : Aux→List Bool) (word : List Bool)
    (hp : u .precision=word) :
    Runs program (addTime word) (ctl .add) (bank b (A.store [] [false,true] [] []) u) (ctl .copySum)
      (bank b (A.store [] [] [] (addBits word [false,true] false).bits) (Function.update u .precision [])) := by
  let before := bank b (A.store [] [false,true] [] []) u
  let source := SemiprimeD1StackAdder.state (some (.start false)) none word [false,true] [] []
  let out := SemiprimeD1StackAdder.state none none [] [] [] (addBits word [false,true] false).bits
  let after := bank b (A.store [] [] [] (addBits word [false,true] false).bits) (Function.update u .precision [])
  have hi : Link.DataRel adder before source.store before := by
    constructor
    · intro k;cases k
      · exact hp
      · rfl
      · rfl
      · rfl
    · intro k _;rfl
  have ho : Link.DataRel adder before out.store after := by
    constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · cases k with
        | left => rfl
        | right => exact False.elim (hk .right rfl)
        | scratch => exact False.elim (hk .scratch rfl)
        | output => exact False.elim (hk .output rfl)
      · cases k with
        | precision => exact False.elim (hk .left rfl)
        | reader | copyScratch | base | template => rfl
  exact included_call program adder Label.add adder_injective A.code (.start false) (fun _ => rfl)
    (ctl .add) (ctl .copySum) rfl _ source out before after rfl rfl
    (SemiprimeD1StackAdderExecution.source_run word [false,true] false) hi ho

/-- Linear actual per-call clock in the number of already consumed width cells. -/
theorem addTime_le (n : ℕ) : addTime (precisionWord n) ≤ 15*n+18 := by
  have h0 := precision_length n
  have h1 := precision_length (n+1)
  have hm : max (precisionWord n).length [false,true].length ≤ 3*n+2 := max_le (by omega) (by simp)
  change 3*(max (precisionWord n).length [false,true].length+1)+2*(precisionWord (n+1)).length+3 ≤ 15*n+18
  omega
end RiemannGaussian.SemiprimeD1StackPackedRootMetadataCalls
