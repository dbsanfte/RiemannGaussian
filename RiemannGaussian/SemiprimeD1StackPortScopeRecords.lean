/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalBankBounds
/-! # Physical one-pass association of original ordered ports and acquired occurrence IDs
The original-N source runs once. Actual copies preserve its port and ID caches.
The parser takes one real ID-vector field per real eight-field port record and
emits the ID followed by that same record. No ordinal getter, ID list, M or
wire-major permutation is supplied to the program.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeRecords
namespace S
export SemiprimeD1StackPortOrdinalBank (Stack Label program input portStack ids)
end S
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction)
end LinkC
/-- Nine fixed physical reader/buffer/output roles. -/
inductive Aux where
  | readerPorts | readerIds | copyScratch | fieldScratch | valid | frameBuffer | frameScratch | reversed | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList
  [.readerPorts,.readerIds,.copyScratch,.fieldScratch,.valid,.frameBuffer,.frameScratch,.reversed,.output]
  (by intro k;cases k <;> simp)
/-- All source data, nine literal parsed fields and nine fresh Boolean work roles. -/
abbrev Stack := S.Stack ⊕ (Fin 9 ⊕ Aux)
/-- Actual entire source inclusion, retaining its original caches. -/
def sourceStack : S.Stack→Stack := Sum.inl
/-- Actual private parsed-field cache. -/
def cache (part:Fin 9) : Stack := .inr (.inl part)
/-- Actual private work role. -/
def aux (role:Aux) : Stack := .inr (.inr role)
/-- Only original binary N is loaded initially. -/
def originalInput : Stack := sourceStack (S.portStack SemiprimeD1StackPortCatalogue.originalInput)
/-- Literal acquired factor-major original port tape. -/
def sourcePorts : Stack := sourceStack (S.portStack (SemiprimeD1StackPortCatalogue.aux .output))
/-- Literal acquired M-word ID bank. -/
def sourceIds : Stack := sourceStack S.ids
/-- Two actual source-preserving copies, never an advised reader tape. -/
def copyStack (ids:Bool) (k:Fin 3) : Stack :=
  if k=0 then (if ids then sourceIds else sourcePorts)
  else if k=1 then (if ids then aux .readerIds else aux .readerPorts) else aux .copyScratch
/-- Port fields zero through seven and bank field eight share a real parser. -/
def fieldStack (part:Fin 9) : Field.Stack→Stack
  | .inl .input => if part.val=8 then aux .readerIds else aux .readerPorts
  | .inl .scratch => aux .fieldScratch
  | .inl .output => cache part
  | .inr _ => aux .valid
/-- Actual output order is scope ID, then all eight original port fields. -/
def frameSource (part:Fin 9) : Stack := if part.val=0 then cache 8 else cache ⟨part.val-1,by omega⟩
/-- Actual field framing operates on its cached source and physical scratch. -/
def frameStack (part:Fin 9) (k:Fin 3) : Stack :=
  if k=0 then frameSource part else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Actual per-field or final output reversal. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then aux .reversed else aux .frameBuffer)
  else if finish then aux .output else aux .reversed
/-- Finite static control, including real mismatched-input abort branches. -/
inductive Control where
  | main | copyPorts | copyIds | parse | bankTag | bankEnd | bankEOF | finalReverse | halt | abort
  | field (part:Fin 9) | popValid (part:Fin 9) | emitFrame (part:Fin 9) | emitReverse (part:Fin 9)
  | clearCache (part:Fin 9)
  deriving DecidableEq,Fintype
/-- Every included source and procedure label is fixed before N. -/
inductive Label where
  | local (pc:Control) | source (pc:S.Label) | copy (ids:Bool) (pc:Fin 9)
  | field (part:Fin 9) (pc:Field.Label) | frame (part:Fin 9) (pc:Fin 11)
  | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- Literal one-pass physical port/ID zipper with actual copies and finite field loops. -/
def program : Label→C.Instruction Stack Label
  | .source pc => LinkC.instruction sourceStack Label.source (S.program pc)
  | .copy ids pc => LinkB.instruction (copyStack ids) (Label.copy ids) (SemiprimeD1StackCopy.code pc)
  | .field part pc => LinkB.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .frame part pc => LinkB.instruction (frameStack part) (Label.frame part) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc => LinkB.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
  | .local .main => .call (.source (.inl .start)) (.local .copyPorts)
  | .local .copyPorts => .call (.copy false 0) (.local .copyIds)
  | .local .copyIds => .call (.copy true 0) (.local .parse)
  | .local .parse => .base (.peek (aux .readerPorts) (.local .bankEnd) (.local (.field 0)) (.local (.field 0)))
  | .local (.field part) => .call (.field part (Field.active .tagPop (none,false))) (.local (.popValid part))
  | .local (.popValid part) =>
      let next:Label:=if h:part.val<7 then .local (.field ⟨part.val+1,by omega⟩)
        else if part.val=7 then .local .bankTag else .local (.emitFrame 0)
      .base (.pop (aux .valid) next next next)
  | .local .bankTag => .base (.pop (aux .readerIds) (.local .abort) (.local .abort) (.local (.field 8)))
  | .local (.emitFrame part) => .call (.frame part 0) (.local (.emitReverse part))
  | .local (.emitReverse part) =>
      let next:Label:=if h:part.val<8 then .local (.emitFrame ⟨part.val+1,by omega⟩) else .local (.clearCache 0)
      .call (.reverse false 0) next
  | .local (.clearCache part) =>
      let next:Label:=if h:part.val<8 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .parse
      .base (.pop (cache part) next (.local (.clearCache part)) (.local (.clearCache part)))
  | .local .bankEnd => .base (.pop (aux .readerIds) (.local .abort) (.local .bankEOF) (.local .abort))
  | .local .bankEOF => .base (.peek (aux .readerIds) (.local .finalReverse) (.local .abort) (.local .abort))
  | .local .finalReverse => .call (.reverse true 0) (.local .halt)
  | .local .halt | .local .abort => .base .halt
/-- One fixed finite original-N machine, returning actual ID-tagged original port records. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .output) (.local .main) program
/-- Original N alone, every fresh parser/reader/cache empty. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (S.input bits) (fun _=>[])
/-- Actual source initial state. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.local .main),none,none,input bits,[]⟩
/-- Finiteness holds on EVERY stack, not merely the input alphabet. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput (aux .output) (.local .main) program
/-- One hundred and five fixed Boolean data roles, independent of N or M. -/
theorem stack_card : Fintype.card Stack=105 := by decide
end RiemannGaussian.SemiprimeD1StackPortScopeRecords
