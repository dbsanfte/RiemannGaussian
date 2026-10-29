/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyOriginal
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyStorage
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCounterEntry
import RiemannGaussian.SemiprimeD1PacketRoundBits
/-! # Actual frequency acquisition and binary rounding to an acquired packet multiple
The two physical inputs are raw-key vector and acquired unary exponent. The
whole source calls Frequency21 once. Its actual maximum is copied, low bits are
physically removed with a finite OR flag, the actual high suffix is optionally
incremented through the real counter entry, actual low zero bits are pushed,
and real reverse/trim returns the compact rounded word. No unary numerical
maximum, packet size, frequency, rounded answer or clock is an input/opcode.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPadding
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace F
export SemiprimeD1StackSourceKeyFrequency (Stack Label program input initial aux lookupStack oldCount copyScratch)
end F
namespace R
export SemiprimeD1StackReduce (Label code)
export SemiprimeD1StackAdder (Stack)
end R
/-- Four additional actual words: retained exponent, two consumed copies and compact output. -/
inductive Aux where | exponent | cutTodo | prefixTodo | padding deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.exponent,.cutTodo,.prefixTodo,.padding] (by intro k;cases k <;> simp)
/-- All21 frequency roles remain physical and retained; no component alias shadows are added. -/
abbrev Stack:=F.Stack⊕Aux
/-- Actual immutable frequency/counter program inclusion. -/
def frequencyStack :F.Stack→Stack:=Sum.inl
/-- Literal exponent/work/output addresses. -/
def aux :Aux→Stack:=Sum.inr
/-- Four actual preserving-copy sites, with no numerical reconstruction. -/
inductive Copy where | cut | prefix | maximum | high deriving DecidableEq,Repr
instance :Fintype Copy:=Fintype.ofList [.cut,.prefix,.maximum,.high] (by intro k;cases k <;> simp)
/-- The two acquired exponent copies, copied actual maximum and copied actual high suffix use distinct operands. -/
def copyStack (part:Copy) (k:Fin 3) :Stack:=
  if k=0 then match part with
    | .cut|.prefix=>aux .exponent | .maximum=>frequencyStack (F.aux .maximum) | .high=>frequencyStack F.oldCount
  else if k=1 then match part with
    | .cut=>aux .cutTodo | .prefix=>aux .prefixTodo | .maximum=>frequencyStack F.oldCount | .high=>frequencyStack (F.aux .count)
  else frequencyStack F.copyScratch
/-- Real reversal of the actual zero-prefixed high word into trim scratch. -/
def reverseStack (k:Fin 2) :Stack:=if k=0 then frequencyStack (F.aux .count) else frequencyStack (F.aux .trimScratch)
/-- Real compact trim uses the cleared physical lookup operands and returns only to the new padding role. -/
def trimStack :R.Stack→Stack
  | .left=>frequencyStack (F.lookupStack (.inl .left))
  | .right=>frequencyStack (F.lookupStack (.inl .right))
  | .scratch=>frequencyStack (F.aux .trimScratch)
  | .output=>aux .padding
/-- Only finite actual popped-bit OR/branch flags appear in the fixed control. -/
inductive Label where
  | start | copyCut | copyPrefix | copyMaximum | cut (low:Bool) | cutBit (low:Bool) | cutDone (low:Bool)
  | clearHigh | prefix | zero | reverse | trim | done | abort
  | frequency (pc:F.Label) | copier (part:Copy) (pc:Fin 9) | reversal (pc:Fin 4) | reducer (pc:R.Label)
  deriving Fintype
/-- Same fixed25-role whole source and separately callable acquired-maximum rounding entry. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.frequency .start) .copyCut
  | .copyCut=>.call (.copier .cut 0) .copyPrefix
  | .copyPrefix=>.call (.copier .prefix 0) .copyMaximum
  | .copyMaximum=>.call (.copier .maximum 0) (.cut false)
  | .cut low=>.base (.pop (aux .cutTodo) (.cutDone low) .abort (.cutBit low))
  | .cutBit low=>.base (.pop (frequencyStack F.oldCount) (.cut low) (.cut low) (.cut true))
  | .cutDone low=>if low then .call (.frequency .increment) .prefix else .call (.copier .high 0) .clearHigh
  | .clearHigh=>.base (.pop (frequencyStack F.oldCount) .prefix .clearHigh .clearHigh)
  | .prefix=>.base (.pop (aux .prefixTodo) .reverse .abort .zero)
  | .zero=>.base (.push (frequencyStack (F.aux .count)) false .prefix)
  | .reverse=>.call (.reversal 0) .trim
  | .trim=>.call (.reducer .trim) .done
  | .done|.abort=>.base .halt
  | .frequency pc=>SemiprimeD1StackValidationLink.instruction frequencyStack Label.frequency (F.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .reversal pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reversal (SemiprimeD1StackReverseWord.code pc)
  | .reducer pc=>SemiprimeD1StackMultiplierLink.instruction trimStack Label.reducer (R.code pc)
/-- Two actual prepared input words: raw key vector and acquired unary exponent; no supplied maximum or padding. -/
def input (bits exponent:List Bool) :Stack→List Bool:=Sum.elim (F.input bits)
  (fun k=>if k=.exponent then exponent else [])
/-- Whole source calls actual frequency acquisition once before rounding its actual maximum. -/
def initial (bits exponent:List Bool) :C.State Stack Label:=⟨some .start,none,none,input bits exponent,[]⟩
/-- Fixed finite compiled machine; the acquired exponent is an explicit second prepared physical field. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine (frequencyStack (F.aux .source)) (aux .padding) .start program
/-- Exactly25 actual Boolean words, including all retained original frequency records. -/
theorem stack_card :Fintype.card Stack=25:=by rw [Fintype.card_sum,SemiprimeD1StackSourceKeyFrequency.stack_card];decide
/-- Frequency and actual counter inclusion preserves every physical address. -/
theorem frequency_injective :Function.Injective frequencyStack:=Sum.inl_injective
/-- Every actual copy's source, destination and scratch are distinct. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part):=by cases part <;> decide
/-- Physical reverse source and trim destination are distinct. -/
theorem reverse_injective :Function.Injective reverseStack:=by decide
/-- All four physical trim operands, including retained cleared words, remain distinct. -/
theorem trim_injective :Function.Injective trimStack:=by decide
/-- Same finite program has no exponent/maximum/count-dependent alphabet or opcode. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data word and the real return stack have fixed finite alphabets. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourcePacketPadding
