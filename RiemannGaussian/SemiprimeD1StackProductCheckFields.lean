/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckReject

/-! # Actual three-field parsing inside the product checker
These are literal enclosing-program traces. Framing hypotheses identify the
actual acquired cache layout; no operand value or parser verdict is an input.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckFields
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckAcquisition
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- An actual vector-entry tag is consumed before its field parser executes. -/
theorem tag_run (i : Fin 3) (data : Stack→List Bool) (tail : List Bool)
    (hvec : data vectorRole=true::tail) :
    Runs program 1 (.tag i) data (.read i) (Function.update data vectorRole tail) := by
  apply one_base program (.tag i) (.read i) (.pop vectorRole .bad .bad (.read i)) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,hvec,SemiprimeD1StackBytecode.choose]
  · simp only [SemiprimeD1StackBytecode.execute,hvec,List.tail_cons]

/-- Physical output of one real field call; shared parser scratch is cleared. -/
def fieldData (i : Fin 3) (data : Stack→List Bool) (word tail : List Bool) : Stack→List Bool :=
  Function.update (Function.update (Function.update data vectorRole tail) (operand i) word) (auxiliary 1) [true]

/-- Complete actual Field bytecode obtains exactly the raw payload and true
validity cell, preserving every other physical caller cell. -/
theorem field_call (i : Fin 3) (data : Stack→List Bool) (word tail : List Bool)
    (hvec : data vectorRole=frame word tail) (hop : data (operand i)=[])
    (hscratch : data (auxiliary 0)=[]) (hvalid : data (auxiliary 1)=[]) :
    Runs program (8*word.length+7) (.read i) data (.parsed i) (fieldData i data word tail) := by
  apply included_call program (fieldStack i) (Label.field i) (fieldStack_injective i)
    F.code (F.active .tagPop (none,false)) (fun _=>rfl) (.read i) (.parsed i) rfl (8*word.length+6)
    (SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
    data (fieldData i data word tail)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> simpa only [fieldStack,vectorRole] using (by first | exact hvec | exact hscratch | exact hop)
      · cases k;exact hvalid
    · intro k _;rfl
  · constructor
    · intro k
      simp only [auxiliary] at hscratch
      fin_cases i <;> rcases k with k|k <;> cases k <;>
        simp [fieldData,Function.update,fieldStack,operand,vectorRole,vectorStack,SemiprimeD1StackWordVector.output,
          auxiliary,equalPrivate,multiplyStack,multiplyLeft,multiplyRight,SemiprimeD1TensorTapeFieldMachine.contents,
          hscratch]
    · intro k hk
      have hv : k≠vectorRole := by intro h;subst k;exact hk (.inl .input) rfl
      have ho : k≠operand i := by intro h;subst k;exact hk (.inl .output) rfl
      have hf : k≠auxiliary 1 := by intro h;subst k;exact hk (.inr ()) rfl
      simp only [fieldData,Function.update_of_ne hv,Function.update_of_ne ho,Function.update_of_ne hf]

/-- The actual parser's singleton validity flag is physically consumed. -/
theorem parsed_run (i : Fin 3) (data : Stack→List Bool) (hvalid : data (auxiliary 1)=[true]) :
    Runs program 1 (.parsed i) data (afterField i) (Function.update data (auxiliary 1) []) := by
  apply one_base program (.parsed i) (afterField i)
    (.pop (auxiliary 1) .bad .bad (afterField i)) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,hvalid,SemiprimeD1StackBytecode.choose]
  · simp only [SemiprimeD1StackBytecode.execute,hvalid,List.tail_cons]

end RiemannGaussian.SemiprimeD1StackProductCheckFields
