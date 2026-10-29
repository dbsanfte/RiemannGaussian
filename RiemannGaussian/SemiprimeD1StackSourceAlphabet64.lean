/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAssignmentEnumerationBounds
import RiemannGaussian.SemiprimeD1StackReduceExecution
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeSourceHistogramRows
/-! # Literal radix64 source-alphabet acquisition from actual unary coordinate width
The fixed program seeds an actual6a-bit zero counter, calls the real complete
assignment enumerator once, physically parses each word, trims its actual ID
and every six-bit colour, and frames the complete original-order catalogue.
Cached powers are BINARY words written by fixed literal pushes. No numeric
coordinate/cardinality/row/score callback enters control or source input.
This is prepared unary-width acquisition; no N-only selector is claimed here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace E
export SemiprimeD1StackAssignmentLoop (Stack Label code control)
end E
namespace R
export SemiprimeD1StackReduce (Label code)
export SemiprimeD1StackAdder (Stack)
end R
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Every actual width/parser/normalizer/colour/catalogue/power Boolean word. -/
inductive Aux where
  | source | todo | copyScratch | reader | raw | bits | bitsReverse
  | trimLeft | trimRight | trimScratch | id | colourRaw | colour
  | rowHistory | row | frameBuffer | frameScratch | history | output
  | square | cube | fourth | head | valid | fieldScratch
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.source,.todo,.copyScratch,.reader,.raw,.bits,.bitsReverse,.trimLeft,.trimRight,.trimScratch,
    .id,.colourRaw,.colour,.rowHistory,.row,.frameBuffer,.frameScratch,.history,.output,
    .square,.cube,.fourth,.head,.valid,.fieldScratch] (by intro k;cases k <;> simp)
/-- Five actual enumerator roles and all25 actual client roles; unused trim inputs remain counted. -/
abbrev Stack :=E.Stack⊕Aux
/-- Actual complete enumerator inclusion. -/
def enumStack :E.Stack→Stack :=Sum.inl
/-- Physical source/private word inclusion. -/
def aux :Aux→Stack :=Sum.inr
/-- Three preserving copies, each with three distinct physical operands. -/
inductive Copy where | width | stream | word deriving DecidableEq
instance :Fintype Copy :=Fintype.ofList [.width,.stream,.word] (by intro k;cases k <;> simp)
/-- Only actual retained source/stream/word bytes are copied. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with | .width=>aux .source | .stream=>enumStack .output | .word=>aux .raw
  else if k=1 then match part with | .width=>aux .todo | .stream=>aux .reader | .word=>aux .bits
  else aux .copyScratch
/-- The actual assignment-vector parser. -/
def fieldStack :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .fieldScratch
  | .inl .output=>aux .raw | .inr _=>aux .valid
/-- Two actual canonical-normalization destinations, never a semantic value argument. -/
inductive Trim where | id | colour deriving DecidableEq
instance :Fintype Trim :=Fintype.ofList [.id,.colour] (by intro k;cases k <;> simp)
/-- All FOUR real reducer roles exist; .trim starts with its left/right empty. -/
def trimStack (kind:Trim) :R.Stack→Stack
  | .left=>aux .trimLeft | .right=>aux .trimRight | .scratch=>aux .trimScratch
  | .output=>match kind with | .id=>aux .id | .colour=>aux .colour
/-- Actual two-role reversals preserve every unrelated source/cached power word. -/
inductive Reverse where | id | bits | colour | colourFrame | row | pair | catalogue deriving DecidableEq
instance :Fintype Reverse :=Fintype.ofList [.id,.bits,.colour,.colourFrame,.row,.pair,.catalogue]
  (by intro k;cases k <;> simp)
/-- Complete fixed physical reversal wiring. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match part with
    | .id=>aux .raw | .bits=>aux .bits | .colour=>aux .colourRaw | .colourFrame=>aux .frameBuffer
    | .row=>aux .rowHistory | .pair=>aux .frameBuffer | .catalogue=>aux .history
  else match part with
    | .id|.colour=>aux .trimScratch | .bits=>aux .bitsReverse | .colourFrame=>aux .rowHistory
    | .row=>aux .row | .pair=>aux .history | .catalogue=>aux .output
/-- Each physical field is framed from its actual preserved source word. -/
inductive Frame where | colour | row | id deriving DecidableEq
instance :Fintype Frame :=Fintype.ofList [.colour,.row,.id] (by intro k;cases k <;> simp)
/-- All actual Frame operands are distinct. -/
def frameStack (part:Frame) (k:Fin 3) :Stack :=
  if k=0 then match part with | .colour=>aux .colour | .row=>aux .row | .id=>aux .id
  else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Fixed literal zero-push lanes; these are finite compile-time choices, not numeric operands. -/
inductive Fill where | word | square | cube | fourth | head deriving DecidableEq
instance :Fintype Fill :=Fintype.ofList [.word,.square,.cube,.fourth,.head] (by intro k;cases k <;> simp)
/-- Literal target word of one fixed push lane. -/
def fillStack :Fill→Stack
  | .word=>enumStack .word | .square=>aux .square | .cube=>aux .cube | .fourth=>aux .fourth | .head=>aux .head
/-- Each source marker writes six counter bits and the honest binary power zeros. -/
def fillLength (first:Bool) :Fill→Nat
  | .word=>6 | .square=>12 | .cube=>18 | .fourth=>24 | .head=>if first then 18 else 24
/-- Literal finite seed destinations, each initially receiving binary ONE. -/
def seedStack (i:Fin 4) :Stack :=if i=0 then aux .square else if i=1 then aux .cube else if i=2 then aux .fourth else aux .head
/-- Fixed source/parser/six-bit/normalizer/logger control and real included return labels. -/
inductive Label where
  | start | seed (i:Fin 5) | fill (first:Bool) | pushes (first:Bool) (part:Fill) (i:Fin 25)
  | enumerate | copyStream | header | parse | valid | saveWord | reverseID | normalize (kind:Trim)
  | reverseBits | colourStart | readColour (i:Fin 7) | saveColour (i:Fin 6) (bit:Bool)
  | reverseColour | frameColour | reverseColourFrame | clearColour | reverseRow | frameRow | frameID
  | pairTag | reversePair | clearID | clearRow | finishSeed | reverseCatalogue | done | abort
  | enumerator (pc:E.Label) | copier (part:Copy) (pc:Fin 9) | parser (pc:Field.Label)
  | reducer (kind:Trim) (pc:R.Label) | reversal (part:Reverse) (pc:Fin 4) | framer (part:Frame) (pc:Fin 11)
  deriving Fintype
/-- Finite next-lane control, with no input-sized counter or callback. -/
def afterFill (first:Bool) :Fill→Label
  | .word=>.pushes first .square 0 | .square=>.pushes first .cube 0
  | .cube=>.pushes first .fourth 0 | .fourth=>.pushes first .head 0 | .head=>.fill false
/-- The SAME literal30-role program acquires actual compact candidate/colour rows and binary powers. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.copier .width 0) (.seed 0)
  | .seed i=>if h:i.val<4 then .base (.push (seedStack ⟨i.val,h⟩) true (.seed ⟨i.val+1,by omega⟩))
      else .base (.jump (.fill true))
  | .fill first=>.base (.pop (aux .todo) .enumerate .abort (.pushes first .word 0))
  | .pushes first part i=>if h:i.val<fillLength first part then
      .base (.push (fillStack part) false (.pushes first part ⟨i.val+1,by cases part <;> cases first <;> simp [fillLength] at h <;> omega⟩))
      else .base (.jump (afterFill first part))
  | .enumerate=>.call (.enumerator (E.control .bodyCall)) .copyStream
  | .copyStream=>.call (.copier .stream 0) .header
  | .header=>.base (.pop (aux .reader) .abort .finishSeed .parse)
  | .parse=>.call (.parser (Field.active .tagPop (none,false))) .valid
  | .valid=>.base (.pop (aux .valid) .abort .abort .saveWord)
  | .saveWord=>.call (.copier .word 0) .reverseID
  | .reverseID=>.call (.reversal .id 0) (.normalize .id)
  | .normalize kind=>.call (.reducer kind .trim) (match kind with | .id=>.reverseBits | .colour=>.frameColour)
  | .reverseBits=>.call (.reversal .bits 0) .colourStart
  | .colourStart=>.base (.peek (aux .bitsReverse) .reverseRow (.readColour 0) (.readColour 0))
  | .readColour i=>if h:i.val<6 then .base (.pop (aux .bitsReverse) .abort
      (.saveColour ⟨i.val,h⟩ false) (.saveColour ⟨i.val,h⟩ true)) else .base (.jump .reverseColour)
  | .saveColour i bit=>.base (.push (aux .colourRaw) bit (.readColour ⟨i.val+1,by omega⟩))
  | .reverseColour=>.call (.reversal .colour 0) (.normalize .colour)
  | .frameColour=>.call (.framer .colour 0) .reverseColourFrame
  | .reverseColourFrame=>.call (.reversal .colourFrame 0) .clearColour
  | .clearColour=>.base (.pop (aux .colour) .colourStart .clearColour .clearColour)
  | .reverseRow=>.call (.reversal .row 0) .frameRow
  | .frameRow=>.call (.framer .row 0) .frameID
  | .frameID=>.call (.framer .id 0) .pairTag
  | .pairTag=>.base (.push (aux .frameBuffer) true .reversePair)
  | .reversePair=>.call (.reversal .pair 0) .clearID
  | .clearID=>.base (.pop (aux .id) .clearRow .clearID .clearID)
  | .clearRow=>.base (.pop (aux .row) .header .clearRow .clearRow)
  | .finishSeed=>.base (.push (aux .output) false .reverseCatalogue)
  | .reverseCatalogue=>.call (.reversal .catalogue 0) .done
  | .done|.abort=>.base .halt
  | .enumerator pc=>SemiprimeD1StackValidationLink.instruction enumStack Label.enumerator (E.code pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .parser pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.parser (Field.code pc)
  | .reducer kind pc=>SemiprimeD1StackMultiplierLink.instruction (trimStack kind) (Label.reducer kind) (R.code pc)
  | .reversal part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reversal part) (SemiprimeD1StackReverseWord.code pc)
  | .framer part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.framer part) (SemiprimeD1StackFrame.code pc)
/-- Only the actual physically acquired unary width word is loaded on entry. -/
def input (markers:List Bool) :Stack→List Bool :=Sum.elim (fun _=>[]) (fun k=>if k=.source then markers else [])
/-- Genuine whole source entry has no candidate/menu/row/power/clock input. -/
def initial (markers:List Bool) :C.State Stack Label :=⟨some .start,none,none,input markers,[]⟩
/-- One fixed finite physical source; its prepared input is the actual unary coordinate-width word. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .source) (aux .output) .start program
/-- All30 allocated Boolean roles, including both unused reducer inputs, remain counted. -/
theorem stack_card :Fintype.card Stack=30 :=by rw [Fintype.card_sum];decide
/-- Actual copy operands never alias. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- Actual parser operands never alias. -/
theorem field_injective :Function.Injective fieldStack :=by decide
/-- All FOUR actual reducer roles remain distinct for both entry sites. -/
theorem trim_injective (kind:Trim) :Function.Injective (trimStack kind) :=by cases kind <;> decide
/-- Each real reversal has distinct source/destination words. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part) :=by cases part <;> decide
/-- Each actual Frame has three distinct source/destination/scratch words. -/
theorem frame_injective (part:Frame) :Function.Injective (frameStack part) :=by cases part <;> decide
/-- Only finite tags, fixed bounded digit positions and actual finite return labels inhabit control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual Boolean/real-return alphabet is fixed finite before all widths. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64
