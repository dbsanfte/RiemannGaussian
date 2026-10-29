/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputBody
/-! # Complete original-input marked coefficient execution -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputExecution
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputCalls SemiprimeD1StackMarkedPublicInputBody
open SemiprimeD1StackMarkedPublicInputPrimitives SemiprimeD1StackProcedureTrace
/-- Own complete clock: one real52-role source, actual branch and final halt. -/
def runBound (bits raw indexWord : List Bool) : Nat :=
  SemiprimeD1StackPublicInputBounds.runBound bits raw indexWord+1+
    bodyBound bits raw indexWord+1
/-- Every operand and verdict is acquired in this SAME literal program. -/
theorem source_run (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    ∃ t ≤ runBound bits raw indexWord,
      SemiprimeD1StackCalls.run program t (initial bits raw indexWord [side])=
        some (done bits raw indexWord side) := by
  obtain ⟨a,ha,h0⟩ := checker_call bits raw indexWord hb {side := [side]}
  obtain ⟨b,hbTime,h1⟩ := body_run bits raw indexWord side hb
  have hh := join h0 h1
  have hi : At (ctl .start) (data (P.initial bits raw indexWord).data {side := [side]}) []
      (initial bits raw indexWord [side]) := ⟨rfl,initial_data bits raw indexWord side,rfl⟩
  obtain ⟨stop,hr,hs⟩ := hh [] (initial bits raw indexWord [side]) hi
  have hf := halt_run program (ctl .done) rfl (result bits raw indexWord side) [] stop hs
  refine ⟨a+b+1,?_,?_⟩
  · unfold runBound; omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    exact hf
/-- The exact physical coefficient output at the actual source halt. -/
theorem output_bytes (bits raw indexWord : List Bool) (side : Bool) :
    (done bits raw indexWord side).data (aux .output)=coefficient bits raw indexWord side := rfl
/-- Every checker cache, including all original inputs and shadows, survives. -/
theorem checker_preserved (bits raw indexWord : List Bool) (side : Bool) (k : P.Stack) :
    (done bits raw indexWord side).data (checker k)=acquired bits raw indexWord k := rfl
/-- The allocated extractor-template shadow remains physically empty. -/
theorem shadow_empty (bits raw indexWord : List Bool) (side : Bool) :
    (done bits raw indexWord side).data (word 1)=[] := rfl
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputExecution

