/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPadding
/-! # All25 physical words and exact binary packet-ceiling meaning -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPadding
namespace FE
export SemiprimeD1StackSourceKeyFrequencyEncoding (Words bank Summary loopWords acquire done result inputSize)
end FE
/-- Actual25-role store, retaining all original21 frequency cells. -/
structure Words where
  /-- All actual frequency words, not an advised maximum operand. -/
  frequency:FE.Words
  /-- Actual retained acquired unary exponent. -/
  exponent:List Bool:=[]
  /-- First actual paid unary exponent copy. -/
  cutTodo:List Bool:=[]
  /-- Second actual paid unary exponent copy. -/
  prefixTodo:List Bool:=[]
  /-- Actual compact binary rounded output. -/
  padding:List Bool:=[]
/-- No physical data word in the inventory is hidden by the proof view. -/
def bank (w:Words) :Stack→List Bool:=Sum.elim (FE.bank w.frequency) (fun k=>match k with
  | .exponent=>w.exponent | .cutTodo=>w.cutTodo | .prefixTodo=>w.prefixTodo | .padding=>w.padding)
/-- A physical frequency source write preserves every other25-role word. -/
theorem update_source (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .source)) xs=bank {w with frequency:={w.frequency with source:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency reader write preserves every other25-role word. -/
theorem update_reader (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .reader)) xs=bank {w with frequency:={w.frequency with reader:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency raw write preserves every other25-role word. -/
theorem update_raw (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .raw)) xs=bank {w with frequency:={w.frequency with raw:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency dictionary write preserves every other25-role word. -/
theorem update_dictionary (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .dictionary)) xs=bank {w with frequency:={w.frequency with dictionary:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency count write preserves every other25-role word. -/
theorem update_count (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .count)) xs=bank {w with frequency:={w.frequency with count:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency maximum write preserves every other25-role word. -/
theorem update_maximum (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .maximum)) xs=bank {w with frequency:={w.frequency with maximum:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency incScratch write preserves every other25-role word. -/
theorem update_incScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .incScratch)) xs=bank {w with frequency:={w.frequency with incScratch:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency incNext write preserves every other25-role word. -/
theorem update_incNext (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .incNext)) xs=bank {w with frequency:={w.frequency with incNext:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency trimScratch write preserves every other25-role word. -/
theorem update_trimScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .trimScratch)) xs=bank {w with frequency:={w.frequency with trimScratch:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency frameScratch write preserves every other25-role word. -/
theorem update_frameScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.aux .frameScratch)) xs=bank {w with frequency:={w.frequency with frameScratch:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency query write preserves every other25-role word. -/
theorem update_query (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (SemiprimeD1StackSourceKeyFrequency.query)) xs=bank {w with frequency:={w.frequency with query:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency lookupReader write preserves every other25-role word. -/
theorem update_lookupReader (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inr .reader))) xs=bank {w with frequency:={w.frequency with lookupReader:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency left write preserves every other25-role word. -/
theorem update_left (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inl .left))) xs=bank {w with frequency:={w.frequency with left:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency right write preserves every other25-role word. -/
theorem update_right (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inl .right))) xs=bank {w with frequency:={w.frequency with right:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency eqScratch write preserves every other25-role word. -/
theorem update_eqScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inl .scratch))) xs=bank {w with frequency:={w.frequency with eqScratch:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency comparison write preserves every other25-role word. -/
theorem update_comparison (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inl .output))) xs=bank {w with frequency:={w.frequency with comparison:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency valid write preserves every other25-role word. -/
theorem update_valid (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inr .valid))) xs=bank {w with frequency:={w.frequency with valid:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency discard write preserves every other25-role word. -/
theorem update_discard (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inr .discard))) xs=bank {w with frequency:={w.frequency with discard:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency oldCount write preserves every other25-role word. -/
theorem update_oldCount (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.oldCount)) xs=bank {w with frequency:={w.frequency with oldCount:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency fieldScratch write preserves every other25-role word. -/
theorem update_fieldScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.lookupStack (.inr .fieldScratch))) xs=bank {w with frequency:={w.frequency with fieldScratch:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical frequency copyScratch write preserves every other25-role word. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (frequencyStack (F.copyScratch)) xs=bank {w with frequency:={w.frequency with copyScratch:=xs}} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A physical exponent write preserves all retained frequency cells and other actual fields. -/
theorem update_exponent (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .exponent) xs=bank {w with exponent:=xs} :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A physical cutTodo write preserves all retained frequency cells and other actual fields. -/
theorem update_cutTodo (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .cutTodo) xs=bank {w with cutTodo:=xs} :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A physical prefixTodo write preserves all retained frequency cells and other actual fields. -/
theorem update_prefixTodo (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .prefixTodo) xs=bank {w with prefixTodo:=xs} :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A physical padding write preserves all retained frequency cells and other actual fields. -/
theorem update_padding (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .padding) xs=bank {w with padding:=xs} :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Physically retained frequency bank and unary exponent at the prepared rounding entry. -/
def readyWords (src:List Bool) (s:FE.Summary) (a:Nat) :Words:=
  ⟨FE.loopWords src [] s,List.replicate a true,[],[],[]⟩
/-- Exact actual high suffix after the finite low-bit cut. -/
def high (a:Nat) (bits:List Bool) :List Bool:=(SemiprimeD1PacketRoundBits.cut a bits).high
/-- The physical counter is called exactly when an actually popped low bit was true. -/
def roundedHigh (a:Nat) (bits:List Bool) :List Bool:=
  if (SemiprimeD1PacketRoundBits.cut a bits).low then SemiprimeD1StackSourceEnvironmentEncoding.successor (high a bits) else high a bits
/-- Actual zero-prefix bytes before the paid final reverse and trim. -/
def prefixed (a:Nat) (bits:List Bool) :List Bool:=List.replicate a false++roundedHigh a bits
/-- Actual compact output of real reversal followed by real trim. -/
def rounded (a:Nat) (bits:List Bool) :List Bool:=SemiprimeD1StackReduceExecution.trimReverse (prefixed a bits).reverse
/-- Sole whole-entry fields are actual raw-key vector and already acquired unary exponent. -/
def source (keys:List (List Bool)) (a:Nat) :C.State Stack Label:=initial (SemiprimeD1TensorTapeCodec.vectorBits keys) (List.replicate a true)
/-- All21 frequency cells and the original unary exponent are retained after the real adapter. -/
def result (keys:List (List Bool)) (a:Nat) :Stack→List Bool:=bank
  {readyWords (SemiprimeD1TensorTapeCodec.vectorBits keys) (FE.acquire keys) a with padding:=rounded a (FE.acquire keys).maximum}
/-- Literal halted source, clear transient flags, empty own return stack and two physically consumed exponent copies. -/
def done (keys:List (List Bool)) (a:Nat) :C.State Stack Label:=⟨none,none,none,result keys a,[]⟩
/-- Own physical size includes key framing, every exponent marker and one unit. -/
def inputSize (keys:List (List Bool)) (a:Nat) :Nat:=FE.inputSize keys+a
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingEncoding
