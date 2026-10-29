/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Primitives
/-! # Real framed assignment parser and one complete actual binary-counter enumeration call -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Calls
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Real parser consumes its physical field and validity flag; no decoded row enters runtime. -/
theorem parse_call (bank:Stack→List Bool) (word tail:List Bool)
    (hi:bank (aux .reader)=frame word tail) (ho:bank (aux .raw)=[])
    (hs:bank (aux .fieldScratch)=[]) (hv:bank (aux .valid)=[]) :
    Runs program (8*word.length+7) .parse bank .valid
      (Function.update (Function.update (Function.update bank (aux .reader) tail) (aux .raw) word) (aux .valid) [true]) :=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel fieldStack bank before.store bank:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program fieldStack Label.parser field_injective Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) .parse .valid rfl (8*word.length+6)
    before after _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update fieldStack field_injective bank before.store bank hin (.inl .input) tail
  have h1:=Link.data_update fieldStack field_injective bank _ _ h0 (.inl .output) word
  have h2:=Link.data_update fieldStack field_injective bank _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack] using h2
/-- The actual enumeration inclusion has a literal static inverse. -/
theorem enum_injective :Function.Injective enumStack :=Sum.inl_injective
/-- One REAL complete6a-bit enumeration call; all caller/power fields are retained.
The width appears only in this specification, never as a runtime operand. -/
theorem enumerate_call (width:Nat) (privateWords:Aux→List Bool) :
    ∃q ≤ 100*(width+1)*2^width+10,
      Runs program (q+1) .enumerate
        (Sum.elim (SemiprimeD1StackAssignmentLoop.data (List.replicate width false) [] [] [] []) privateWords)
        .copyStream
        (Sum.elim (SemiprimeD1StackAssignmentLoop.data [] [] [] []
          (SemiprimeD1TensorTapeCodec.vectorBits
            (SemiprimeD1StackAssignmentOrder.assignments (2^width) (List.replicate width false)))) privateWords) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackAssignmentEnumerationBounds.zero_source_run width
  refine ⟨q,hq,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program enumStack Label.enumerator enum_injective E.code
    (E.control .bodyCall) (fun _=>rfl) .enumerate .copyStream rfl q
    (SemiprimeD1StackCalls.initial (.word :E.Stack) (E.control .bodyCall) (List.replicate width false))
    (SemiprimeD1StackCalls.final (.output :E.Stack) (SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1StackAssignmentOrder.assignments (2^width) (List.replicate width false))))
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Calls
