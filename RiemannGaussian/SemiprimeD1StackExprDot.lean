/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprPowerBounds
import RiemannGaussian.SemiprimeD1StackUnaryProduct
import RiemannGaussian.SemiprimeD1StackJetReadExecution
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Physical source acquisition for the original DFT dot expression
The program obtains j by popping its counted loop, reads the actual cached word,
acquires stride*(j*frequency) through real unary products, and calls the actual
power-syntax builder and framer. No selected word, exponent, AST or answer is
supplied. All data and labels are fixed before every original input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprDot
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace U
export SemiprimeD1StackUnaryProduct (Stack Label code entry contents product_run)
end U
namespace Power
export SemiprimeD1StackExprPower (Stack Label program initial)
end Power
namespace Read
export SemiprimeD1StackJetRead (Stack Label program store state)
end Read

/-- Twenty-two fixed physical Boolean data roles. -/
inductive Stack where
  | base | stride | frequency | count | remaining | multiplier | productScratch | intermediate | exponent
  | powerCounter | powerScratch | cache | reader | index | parser | skipped | word | valid | readerCopy
  | frameScratch | copyScratch | output
  deriving DecidableEq,Repr
/-- Literal inventory, independent of all input sizes and values. -/
instance : Fintype Stack := Fintype.ofList
  [.base,.stride,.frequency,.count,.remaining,.multiplier,.productScratch,.intermediate,.exponent,
    .powerCounter,.powerScratch,.cache,.reader,.index,.parser,.skipped,.word,.valid,.readerCopy,
    .frameScratch,.copyScratch,.output] (by intro k;cases k <;> simp)

/-- Three static preserving-copy sites. -/
inductive CopyKind where | count | product | index deriving DecidableEq,Repr
instance : Fintype CopyKind := Fintype.ofList [.count,.product,.index] (by intro k;cases k <;> simp)
/-- Actual Copy source; loop indices come from the real remaining counter. -/
def copyInput : CopyKind→Stack | .count => .count | .product | .index => .remaining
/-- Actual Copy destination. -/
def copyOutput : CopyKind→Stack | .count => .remaining | .product => .multiplier | .index => .index
/-- Static real three-role Copy wiring. -/
def copyStack (kind : CopyKind) (k : Fin 3) : Stack :=
  if k=0 then copyInput kind else if k=1 then copyOutput kind else .copyScratch
/-- Two actual products share cleared scratch; first output is directly second input. -/
def productStack (stride : Bool) : U.Stack→Stack
  | .multiplier => if stride then .intermediate else .multiplier
  | .multiplicand => if stride then .stride else .frequency
  | .scratch => .productScratch
  | .product => if stride then .exponent else .intermediate
/-- Direct actual power-builder wiring; its exponent is the acquired product. -/
def powerStack (k : Power.Stack) : Stack :=
  if k=0 then .base else if k=1 then .exponent else if k=2 then .powerCounter
  else if k=3 then .powerScratch else .output
/-- Actual preserved vector cache, physical index, selected word and parsing work. -/
def readStack : Read.Stack→Stack
  | .cache => .cache | .reader => .reader | .index => .index | .parser => .parser
  | .skipped => .skipped | .output => .word | .valid => .valid | .copy => .readerCopy
/-- The raw selected payload is actually framed before its literal constructor tags. -/
def frameStack (k : Fin 3) : Stack := if k=0 then .word else if k=1 then .output else .frameScratch

/-- Fixed local loop, cleanup and constructor phases. -/
inductive Control where
  | start | loop | copyProduct | productFirst | productSecond | powerCall | clearExponent | copyIndex
  | readCall | frameCall | literal0 | literal1 | mul0 | mul1 | clearWord
  | zero0 | zero1 | zero2 | copyAgain | addLoop | add0 | add1 | done
  deriving DecidableEq,Repr
instance : Fintype Control := Fintype.ofList
  [.start,.loop,.copyProduct,.productFirst,.productSecond,.powerCall,.clearExponent,.copyIndex,
    .readCall,.frameCall,.literal0,.literal1,.mul0,.mul1,.clearWord,
    .zero0,.zero1,.zero2,.copyAgain,.addLoop,.add0,.add1,.done] (by intro k;cases k <;> simp)
/-- Every nested component label is finite and fixed before the data. -/
inductive Label where
  | control (pc : Control) | copy (kind : CopyKind) (pc : Fin 9) | product (stride : Bool) (pc : U.Label)
  | power (pc : Power.Label) | read (pc : Read.Label) | frame (pc : Fin 11)
  deriving Fintype

/-- Complete actual source-acquisition table, with every included call literal. -/
def program : Label→C.Instruction Stack Label
  | .copy kind pc => SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .product stride pc => SemiprimeD1StackMultiplierLink.instruction (productStack stride) (Label.product stride) (U.code pc)
  | .power pc => SemiprimeD1StackValidationLink.instruction powerStack Label.power (Power.program pc)
  | .read pc => SemiprimeD1StackValidationLink.instruction readStack Label.read (Read.program pc)
  | .frame pc => SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)
  | .control pc => match pc with
    | .start => .call (.copy .count 0) (.control .loop)
    | .loop => .base (.pop .remaining (.control .zero0) (.control .copyProduct) (.control .copyProduct))
    | .copyProduct => .call (.copy .product 0) (.control .productFirst)
    | .productFirst => .call (.product false U.entry) (.control .productSecond)
    | .productSecond => .call (.product true U.entry) (.control .powerCall)
    | .powerCall => .call (.power .start) (.control .clearExponent)
    | .clearExponent => .base (.pop .exponent (.control .copyIndex) (.control .clearExponent) (.control .clearExponent))
    | .copyIndex => .call (.copy .index 0) (.control .readCall)
    | .readCall => .call (.read .start) (.control .frameCall)
    | .frameCall => .call (.frame 0) (.control .literal0)
    | .literal0 => .base (.push .output false (.control .literal1))
    | .literal1 => .base (.push .output false (.control .mul0))
    | .mul0 => .base (.push .output true (.control .mul1))
    | .mul1 => .base (.push .output true (.control .clearWord))
    | .clearWord => .base (.pop .word (.control .loop) (.control .clearWord) (.control .clearWord))
    | .zero0 => .base (.push .output false (.control .zero1))
    | .zero1 => .base (.push .output false (.control .zero2))
    | .zero2 => .base (.push .output false (.control .copyAgain))
    | .copyAgain => .call (.copy .count 0) (.control .addLoop)
    | .addLoop => .base (.pop .remaining (.control .done) (.control .add0) (.control .add0))
    | .add0 => .base (.push .output true (.control .add1))
    | .add1 => .base (.push .output false (.control .addLoop))
    | .done => .base .halt

/-- Persistent physical argument caches; these are NOT transient machine control. -/
structure Cache where
  /-- Encoded base expression, actually copied by Power. -/
  base : List Bool
  /-- Original physical unary stride metadata. -/
  stride : List Bool
  /-- Original physical unary frequency metadata. -/
  frequency : List Bool
  /-- Original physical unary number of terms. -/
  count : List Bool
  /-- Actual encoded input word vector, read through the real cache reader. -/
  words : List Bool

/-- Exact finite work-bank view; all defaults mean physically empty stacks. -/
structure Work where
  /-- Descending original term-index counter. -/
  remaining : List Bool := []
  /-- Disposable copied multiplier for the first physical product. -/
  multiplier : List Bool := []
  /-- Shared restored unary-product scratch. -/
  productScratch : List Bool := []
  /-- Actual first product, directly consumed by the second. -/
  intermediate : List Bool := []
  /-- Actual complete power exponent, drained after construction. -/
  exponent : List Bool := []
  /-- Power builder's disposable count copy. -/
  powerCounter : List Bool := []
  /-- Power builder's real restoration scratch. -/
  powerScratch : List Bool := []
  /-- Preserving reader's actual cache copy. -/
  reader : List Bool := []
  /-- Reader's disposable physical index. -/
  index : List Bool := []
  /-- Reader's field-parser scratch. -/
  parser : List Bool := []
  /-- Actual skipped word, physically erased by the reader. -/
  skipped : List Bool := []
  /-- Actual selected payload, erased after framing. -/
  word : List Bool := []
  /-- Reader's physically computed parser status. -/
  valid : List Bool := []
  /-- Reader's preserving-copy restoration scratch. -/
  readerCopy : List Bool := []
  /-- Literal framer's physical reversal scratch. -/
  frameScratch : List Bool := []
  /-- Inter-component preserving-copy restoration scratch. -/
  copyScratch : List Bool := []
  /-- Actually produced syntax with the retained physical suffix. -/
  output : List Bool := []

/-- Mathematical reached-payload view; runtime still has only physical Bool stacks. -/
def bank (c : Cache) (w : Work) : Stack→List Bool
  | .base => c.base | .stride => c.stride | .frequency => c.frequency | .count => c.count | .cache => c.words
  | .remaining => w.remaining | .multiplier => w.multiplier | .productScratch => w.productScratch
  | .intermediate => w.intermediate | .exponent => w.exponent | .powerCounter => w.powerCounter
  | .powerScratch => w.powerScratch | .reader => w.reader | .index => w.index | .parser => w.parser
  | .skipped => w.skipped | .word => w.word | .valid => w.valid | .readerCopy => w.readerCopy
  | .frameScratch => w.frameScratch | .copyScratch => w.copyScratch | .output => w.output
/-- Literal source entry with only argument caches and a physical output suffix. -/
def initial (c : Cache) (tail : List Bool) : C.State Stack Label :=
  ⟨some (.control .start),none,none,bank c {output:=tail},[]⟩
/-- Fixed actual machine, never dependent on a native graph or source oracle. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.base Stack.output (.control .start) program

/-- Every real Copy instance has disjoint operands. -/
theorem copyStack_injective (kind : CopyKind) : Function.Injective (copyStack kind) := by cases kind <;> decide
/-- Every actual unary-product role is disjoint within its physical inclusion. -/
theorem productStack_injective (stride : Bool) : Function.Injective (productStack stride) := by cases stride <;> decide
/-- Direct power-builder roles are disjoint. -/
theorem powerStack_injective : Function.Injective powerStack := by decide
/-- The cached-vector reader has distinct data and work roles. -/
theorem readStack_injective : Function.Injective readStack := by intro i j h;cases i <;> cases j <;> simp_all [readStack]
/-- Framed literal operands are physically disjoint. -/
theorem frameStack_injective : Function.Injective frameStack := by decide
/-- All data and actual return-tag alphabets are finite before any original N. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.base Stack.output (.control .start) program
/-- Runtime transient control is finite, carrying no Expr/Nat/List/function data. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.base Stack.output (.control .start) program
/-- Twenty-two fixed Boolean data roles. -/
theorem stack_card : Fintype.card Stack=22 := by decide

end RiemannGaussian.SemiprimeD1StackExprDot
