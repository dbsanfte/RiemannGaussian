/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityOriginal

/-! # Actual original-N local-port descriptor acquisition
The fixed caller acquires vertices once, physically copies their tape, acquires
edges from the original tape, then parses the copy and computes every arity by
real arithmetic procedures. It emits local slots and factor-major occurrence
ordinals from physical counters. Ordinals are control fields, not an alternative
to the separate common-width global scope-ID bank.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogue
namespace E
export SemiprimeD1StackEdgeCatalogue (Stack Label program input catStack cache aux)
end E
namespace V
export SemiprimeD1StackVertexCatalogue (Stack Label program originalInput cacheStack rootStack countStack)
end V
namespace A
export SemiprimeD1StackVertexArity (Stack Label Source Aux program)
end A
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction Rel run_rel)
end LinkC
/-- Eleven private physical reader/output/counter/arithmetic roles. -/
inductive Aux where
  | reader | output | factorOrdinal | occurrenceOrdinal | remaining | multiplier | mulScratch
  | compareLeft | compareRight | compareLimit | compareResult
  deriving DecidableEq,Repr
instance : Fintype Aux where
  elems:={.reader,.output,.factorOrdinal,.occurrenceOrdinal,.remaining,.multiplier,.mulScratch,
    .compareLeft,.compareRight,.compareLimit,.compareResult}
  complete:=by intro k;cases k <;> simp
/-- Original sixty-seven roles plus eleven private Boolean work roles. -/
abbrev Stack := E.Stack⊕Aux
instance : DecidableEq Stack := inferInstanceAs (DecidableEq (E.Stack⊕Aux))
instance : Fintype Stack := inferInstanceAs (Fintype (E.Stack⊕Aux))
/-- Literal original edge-source stack inclusion. -/
def edgeStack (k:E.Stack) : Stack := .inl k
/-- Shared original vertex-source roles, without a second metadata acquisition. -/
def vertexStack (k:V.Stack) : Stack := edgeStack (E.catStack k)
/-- Shared five-field parser cache. -/
def cache (part:Fin 5) : Stack := edgeStack (E.cache part)
/-- Shared edge/parser/frame work role. -/
def oldAux (key:SemiprimeD1StackEdgeCatalogue.Aux) : Stack := edgeStack (E.aux key)
/-- Private physical role. -/
def aux (key:Aux) : Stack := .inr key
/-- Original N stays binary on its original acquired input stack. -/
def originalInput : Stack := vertexStack V.originalInput
/-- Actual original catalogue output, copied before the edge stage consumes it. -/
def vertexReader : Stack := vertexStack (SemiprimeD1StackVertexCatalogue.kernelStack (SemiprimeD1StackCartesian4.aux 2))
/-- Shared public axis counter at its actual physical metadata address. -/
def axisStack (i:Fin 3) : Stack := vertexStack (V.rootStack (SemiprimeD1BinaryPublicAcquisition.axesStack (.inr i)))
/-- Arity source operands alias only actual parsed fields and acquired readonly metadata. -/
def aritySource : A.Source→Stack
  | .tag => cache 0
  | .index => cache 2
  | .radiusSucc => vertexStack (V.cacheStack 4)
  | .firstAxis => axisStack 0
  | .secondAxis => axisStack 1
  | .digits => vertexStack (V.countStack .count)
/-- Real arity work: its output is the physically consumed remaining-port tally. -/
def arityAux : A.Aux→Stack
  | .arity => aux .remaining
  | .tagReader => oldAux .tagReader
  | .copyScratch => oldAux .copyScratch
  | .multiplier => aux .multiplier
  | .mulScratch => aux .mulScratch
  | .compareLeft => aux .compareLeft
  | .compareRight => aux .compareRight
  | .compareLimit => aux .compareLimit
  | .compareResult => aux .compareResult
/-- Literal shared-stack arity inclusion. -/
def arityStack : A.Stack→Stack := Sum.elim aritySource arityAux
/-- Actual five-field parser operands over the physically copied tape. -/
def fieldStack (part:Fin 5) : Field.Stack→Stack
  | .inl .input => aux .reader
  | .inl .scratch => oldAux .fieldScratch
  | .inl .output => cache part
  | .inr _ => oldAux .valid
/-- Actual original tape copy, preserving the source for the edge stage. -/
def copyStack (k:Fin 3) : Stack := if k=0 then vertexReader else if k=1 then aux .reader else oldAux .copyScratch
/-- Eight physical emitted fields: occurrence/factor/local ordinals, then original descriptor. -/
def frameSource (part:Fin 8) : Stack :=
  if part.val=0 then aux .occurrenceOrdinal
  else if part.val=1 then aux .factorOrdinal
  else if part.val=2 then oldAux .side
  else cache ⟨part.val-3,by omega⟩
/-- Every actual field is framed in the real shared buffer. -/
def frameStack (part:Fin 8) (k:Fin 3) : Stack :=
  if k=0 then frameSource part else if k=1 then oldAux .frameBuffer else oldAux .frameScratch
/-- Real reversal into the port work tape or into its final output. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then oldAux .reversed else oldAux .frameBuffer)
  else if finish then aux .output else oldAux .reversed
/-- Finite first-order caller control, fixed before N and all graph dimensions. -/
inductive Control where
  | main | callVertex | copyVertex | callEdges | parse | arity | loop | clearSlot | factorTick
  | incrementSlot | incrementOccurrence | finalReverse | halt
  | field (part:Fin 5) | popValid (part:Fin 5) | clearCache (part:Fin 5)
  | emitFrame (part:Fin 8) | emitReverse (part:Fin 8)
  deriving DecidableEq,Fintype
/-- All source/procedure/control labels are static finite types.
Only Fintype is needed: the unary product's dependent locations have no label equality instance. -/
inductive Label where
  | local (pc:Control)
  | vertex (pc:V.Label)
  | edges (pc:E.Label)
  | arity (pc:A.Label)
  | copy (pc:Fin 9)
  | field (part:Fin 5) (pc:Field.Label)
  | frame (part:Fin 8) (pc:Fin 11)
  | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- Literal first-order graph/port acquisition, with actual calls and counter loops. -/
def program : Label→C.Instruction Stack Label
  | .vertex pc => LinkC.instruction vertexStack Label.vertex (V.program pc)
  | .edges pc => LinkC.instruction edgeStack Label.edges (E.program pc)
  | .arity pc => LinkC.instruction arityStack Label.arity (A.program pc)
  | .copy pc => LinkB.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field part pc => LinkB.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .frame part pc => LinkB.instruction (frameStack part) (Label.frame part) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc => LinkB.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
  | .local .main => .base (.peek originalInput (.local .halt) (.local .callVertex) (.local .callVertex))
  | .local .callVertex => .call (.vertex (.inl .main)) (.local .copyVertex)
  | .local .copyVertex => .call (.copy 0) (.local .callEdges)
  | .local .callEdges => .call (.edges (.inl .parse)) (.local .parse)
  | .local .parse => .base (.peek (aux .reader) (.local .finalReverse) (.local (.field 0)) (.local (.field 0)))
  | .local (.field part) => .call (.field part (Field.active .tagPop (none,false))) (.local (.popValid part))
  | .local (.popValid part) =>
      let next:Label:=if h:part.val<4 then .local (.field ⟨part.val+1,by omega⟩) else .local .arity
      .base (.pop (oldAux .valid) next next next)
  | .local .arity => .call (.arity (.inl .main)) (.local .loop)
  | .local .loop => .base (.pop (aux .remaining) (.local .clearSlot) (.local (.emitFrame 0)) (.local (.emitFrame 0)))
  | .local (.emitFrame part) => .call (.frame part 0) (.local (.emitReverse part))
  | .local (.emitReverse part) =>
      let next:Label:=if h:part.val<7 then .local (.emitFrame ⟨part.val+1,by omega⟩) else .local .incrementSlot
      .call (.reverse false 0) next
  | .local .incrementSlot => .base (.push (oldAux .side) true (.local .incrementOccurrence))
  | .local .incrementOccurrence => .base (.push (aux .occurrenceOrdinal) true (.local .loop))
  | .local .clearSlot => .base (.pop (oldAux .side) (.local (.clearCache 0)) (.local .clearSlot) (.local .clearSlot))
  | .local (.clearCache part) =>
      let next:Label:=if h:part.val<4 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .factorTick
      .base (.pop (cache part) next (.local (.clearCache part)) (.local (.clearCache part)))
  | .local .factorTick => .base (.push (aux .factorOrdinal) true (.local .parse))
  | .local .finalReverse => .call (.reverse true 0) (.local .halt)
  | .local .halt => .base .halt
/-- One actual fixed finite original-binary-input machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .output) (.local .main) program
/-- Only original binary N is present before the first real source call. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (E.input bits) (fun _=>[])
/-- Initial original-N source state. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.local .main),none,none,input bits,[]⟩
/-- Every actual data/return alphabet is finite, without an infinite internal symbol trap. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput (aux .output) (.local .main) program
/-- Seventy-eight actual Boolean data stacks, before every N. -/
theorem stack_card : Fintype.card Stack=78 := by decide
end RiemannGaussian.SemiprimeD1StackPortCatalogue
