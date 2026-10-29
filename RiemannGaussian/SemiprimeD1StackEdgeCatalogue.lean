/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueBounds
import RiemannGaussian.SemiprimeD1StackReverseWord

/-! # Actual original half-edge descriptor acquisition
The closed machine obtains the original vertex tape from N, physically parses
its five fields, selects equality constructors and emits the two half edges.
No graph enumeration or decoded descriptor is executed as an instruction.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogue
namespace Cat
export SemiprimeD1StackVertexCatalogue (Stack Label program originalInput kernelStack)
end Cat
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction Rel run_rel)
end LinkC
/-- Nine static physical transducer work roles. -/
inductive Aux where
  | frameBuffer | frameScratch | fieldScratch | valid | tagReader | copyScratch | reversed | output | side
  deriving DecidableEq,Repr
instance : Fintype Aux where
  elems:={.frameBuffer,.frameScratch,.fieldScratch,.valid,.tagReader,.copyScratch,.reversed,.output,.side}
  complete:=by intro k;cases k <;> simp
/-- Original metadata roles, five parsed fields, and nine physical work stacks. -/
abbrev Stack := Cat.Stack⊕(Fin 5⊕Aux)
instance : DecidableEq Stack := inferInstanceAs (DecidableEq (Cat.Stack⊕(Fin 5⊕Aux)))
instance : Fintype Stack := inferInstanceAs (Fintype (Cat.Stack⊕(Fin 5⊕Aux)))
/-- Static parse/emit control; no numeric payload is held in control. -/
inductive Control where
  | main | parse | copyTag | pushSide | clearSide | finalReverse | halt
  | field (part:Fin 5) | popValid (part:Fin 5) | test (count:Fin 10)
  | clearTest (emit:Bool) | emitFrame (side:Bool) (part:Fin 6)
  | emitReverse (side:Bool) (part:Fin 6) | clearCache (part:Fin 5)
  deriving DecidableEq,Fintype
/-- Literal source, parser, framer, reversal and Copy labels. -/
abbrev Label := Control⊕(Cat.Label⊕((Fin 5×Field.Label)⊕((Fin 6×Fin 11)⊕((Bool×Fin 4)⊕Fin 9))))
instance : Fintype Label := inferInstanceAs (Fintype (Control⊕(Cat.Label⊕((Fin 5×Field.Label)⊕((Fin 6×Fin 11)⊕((Bool×Fin 4)⊕Fin 9))))))
/-- Literal original catalogue stack inclusion. -/
def catStack (k:Cat.Stack) : Stack := .inl k
/-- Actual parsed field cache. -/
def cache (part:Fin 5) : Stack := .inr (.inl part)
/-- Actual finite work role. -/
def aux (role:Aux) : Stack := .inr (.inr role)
/-- The actual acquired descriptor tape is the parser input. -/
def reader : Stack := catStack (Cat.kernelStack (SemiprimeD1StackCartesian4.aux 2))
/-- Static original-source procedure labels. -/
def catLabel (pc:Cat.Label) : Label := .inr (.inl pc)
/-- Physical parser operand inclusion for one of five actual fields. -/
def fieldStack (part:Fin 5) : Field.Stack→Stack
  | .inl .input => reader
  | .inl .scratch => aux .fieldScratch
  | .inl .output => cache part
  | .inr _ => aux .valid
/-- Static parser labels. -/
def fieldLabel (part:Fin 5) (pc:Field.Label) : Label := .inr (.inr (.inl (part,pc)))
/-- Actual side word or parsed descriptor word, without decoding. -/
def frameSource (part:Fin 6) : Stack := if h:part.val=0 then aux .side else cache ⟨part.val-1,by omega⟩
/-- Real source-preserving frame into an actual empty buffer. -/
def frameStack (part:Fin 6) (k:Fin 3) : Stack :=
  if k=0 then frameSource part else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Static frame labels. -/
def frameLabel (part:Fin 6) (pc:Fin 11) : Label := .inr (.inr (.inr (.inl (part,pc))))
/-- Reversal either transfers one framed field or finishes the whole ordered tape. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then aux .reversed else aux .frameBuffer)
  else if finish then aux .output else aux .reversed
/-- Static real reversal labels. -/
def reverseLabel (finish:Bool) (pc:Fin 4) : Label := .inr (.inr (.inr (.inr (.inl (finish,pc)))))
/-- Copy the ACTUAL unary tag before the ten-marker constructor test. -/
def copyStack (k:Fin 3) : Stack := if k=0 then cache 0 else if k=1 then aux .tagReader else aux .copyScratch
/-- Static included Copy labels. -/
def copyLabel (pc:Fin 9) : Label := .inr (.inr (.inr (.inr (.inr pc))))
/-- The first field after a real validity-cell pop. -/
def afterField (part:Fin 5) : Label :=
  if h:part.val<4 then .inl (.field ⟨part.val+1,by omega⟩) else .inl .copyTag
/-- One fixed complete original-input acquisition and edge-transduction program. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => LinkC.instruction catStack catLabel (Cat.program pc)
  | .inr (.inr (.inl (part,pc))) => LinkB.instruction (fieldStack part) (fieldLabel part) (Field.code pc)
  | .inr (.inr (.inr (.inl (part,pc)))) => LinkB.instruction (frameStack part) (frameLabel part) (SemiprimeD1StackFrame.code pc)
  | .inr (.inr (.inr (.inr (.inl (finish,pc))))) =>
      LinkB.instruction (reverseStack finish) (reverseLabel finish) (SemiprimeD1StackReverseWord.code pc)
  | .inr (.inr (.inr (.inr (.inr pc)))) => LinkB.instruction copyStack copyLabel (SemiprimeD1StackCopy.code pc)
  | .inl .main => .call (catLabel (.inl .main)) (.inl .parse)
  | .inl .parse => .base (.peek reader (.inl .finalReverse) (.inl (.field 0)) (.inl (.field 0)))
  | .inl (.field part) => .call (fieldLabel part (Field.active .tagPop (none,false))) (.inl (.popValid part))
  | .inl (.popValid part) => .base (.pop (aux .valid) (afterField part) (afterField part) (afterField part))
  | .inl .copyTag => .call (copyLabel 0) (.inl (.test 0))
  | .inl (.test count) =>
      let next:Label:=if h:count.val<9 then .inl (.test ⟨count.val+1,by omega⟩) else .inl (.clearTest true)
      .base (.pop (aux .tagReader) (.inl (.clearTest false)) next next)
  | .inl (.clearTest emit) =>
      let next:Label:=if emit then .inl (.emitFrame false 0) else .inl (.clearCache 0)
      .base (.pop (aux .tagReader) next (.inl (.clearTest emit)) (.inl (.clearTest emit)))
  | .inl (.emitFrame side part) => .call (frameLabel part 0) (.inl (.emitReverse side part))
  | .inl (.emitReverse side part) =>
      let next:Label:=if h:part.val<5 then .inl (.emitFrame side ⟨part.val+1,by omega⟩)
        else if side then .inl .clearSide else .inl .pushSide
      .call (reverseLabel false 0) next
  | .inl .pushSide => .base (.push (aux .side) true (.inl (.emitFrame true 0)))
  | .inl .clearSide => .base (.pop (aux .side) (.inl (.clearCache 0)) (.inl (.clearCache 0)) (.inl (.clearCache 0)))
  | .inl (.clearCache part) =>
      let next:Label:=if h:part.val<4 then .inl (.clearCache ⟨part.val+1,by omega⟩) else .inl .parse
      .base (.pop (cache part) next (.inl (.clearCache part)) (.inl (.clearCache part)))
  | .inl .finalReverse => .call (reverseLabel true 0) (.inl .halt)
  | .inl .halt => .base .halt
/-- One fixed actual machine, before every N. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (catStack Cat.originalInput) (aux .output) (.inl .main) program
/-- Only original binary N is initially present. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (SemiprimeD1StackVertexCatalogue.input bits) (fun _=>[])
/-- Initial closed source configuration. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .main),none,none,input bits,[]⟩
/-- Every alphabet, including every actual call-frame tag, is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (catStack Cat.originalInput) (aux .output) (.inl .main) program
/-- Sixty-seven physical Boolean data stacks, fixed independently of N. -/
theorem stack_card : Fintype.card Stack=67 := by decide
end RiemannGaussian.SemiprimeD1StackEdgeCatalogue
