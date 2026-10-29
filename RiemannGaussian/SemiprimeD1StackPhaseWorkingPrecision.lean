/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataOriginal
import RiemannGaussian.SemiprimeD1StackIncrementBytecode
import RiemannGaussian.SemiprimeD1StackAdderExecution
/-! # Actual original working precision with BINARY D and P
The whole source first acquires the actual guarded h/q/r/delta metadata.
Accepted paths convert only bounded unary h/r by REAL binary increments, shift
binary words and execute two REAL adders. Neither numeric precision nor2^a is
expanded into unary cells. The same ready entry reuses the ACTUALLY acquired cache.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecision
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace M
export SemiprimeD1StackPhaseWorkingPrecisionMetadata (Stack Label program input guardStack divStack aux)
end M
namespace Inc
export SemiprimeD1TensorTapeFieldMachine (Stack contents)
export SemiprimeD1StackIncrementBytecode (Label code entry)
end Inc
namespace Add
export SemiprimeD1StackAdder (Stack Label code store state)
end Add
/-- Eleven actual binary accumulator/counter/work/output roles. -/
inductive Aux where | left | right | scratch | output | counter | next | todo | zeroTodo | shiftTodo | copyScratch | power
  deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.left,.right,.scratch,.output,.counter,.next,.todo,.zeroTodo,.shiftTodo,.copyScratch,.power]
  (by intro k;cases k <;> simp)
/-- Entire37-role acquired metadata bank plus eleven fresh physical binary fields. -/
abbrev Stack :=M.Stack⊕Aux
/-- Literal inclusion of ALL original/acquired metadata fields. -/
def metadataStack : M.Stack→Stack :=Sum.inl
/-- Literal binary output/work inclusion. -/
def aux : Aux→Stack :=Sum.inr
/-- Actual counter increment input/scratch/output fields. -/
def incrementStack : Inc.Stack→Stack
  | .input=>aux .counter | .scratch=>aux .scratch | .output=>aux .next
/-- Two actual adders share an entirely consuming physical bank. -/
def adderStack : Add.Stack→Stack
  | .left=>aux .left | .right=>aux .right | .scratch=>aux .scratch | .output=>aux .output
/-- Fixed finite source sites, including three paid binary low-zero writes per term. -/
inductive Label where
  | start | branch | copyZero (second : Bool) | seedZero (second : Bool)
  | allocate (second : Bool) | pushZero (second : Bool) | copyTodo (second : Bool)
  | loop (second : Bool) | increment (second : Bool) | popOverflow (second : Bool)
  | restore (second : Bool) | clearNext (second : Bool) | finish (second : Bool) | clearCounter (second : Bool)
  | copyDelta | seedPower | shift | shiftPower | shiftHeight | leftShift (position : Fin 3)
  | copyPrecision | add (second : Bool) | rightShift (position : Fin 3) | copyPartial | clearPartial | done
  | metadata (pc : M.Label) | copy (kind : Fin 10) (pc : Fin 9)
  | counter (pc : Inc.Label) | adder (pc : Add.Label)
  deriving Fintype
/-- Only actual acquired h/r/delta or original p/counter words are read by copy sites. -/
def copySource (kind : Fin 10) : Stack :=
  if kind=0 ∨ kind=2 then metadataStack (M.divStack .quotient)
  else if kind=1 ∨ kind=3 then metadataStack (M.aux .r)
  else if kind=4 then aux .next else if kind=5 ∨ kind=6 then aux .counter
  else if kind=7 then metadataStack (M.aux .delta)
  else if kind=8 then metadataStack (M.aux .precision) else aux .output
/-- Physical conversion/accumulator destinations, all empty at each actual copy call. -/
def copyTarget (kind : Fin 10) : Stack :=
  if kind=0 ∨ kind=1 then aux .zeroTodo else if kind=2 ∨ kind=3 then aux .todo
  else if kind=4 then aux .counter else if kind=5 then aux .left else if kind=6 then aux .right
  else if kind=7 then aux .shiftTodo else if kind=8 then aux .right else aux .left
/-- Copy restoration scratch is separate from actual source/destination fields. -/
def copyStack (kind : Fin 10) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .copyScratch
/-- ONE parameterless fixed finite literal working-precision program. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.metadata .start) .branch
  | .branch=>.base (.peek (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .output))) .done .done (.copyZero false))
  | .copyZero second=>.call (.copy (if second then 1 else 0) 0) (.seedZero second)
  | .seedZero second=>.base (.push (aux .counter) false (.allocate second))
  | .allocate second=>.base (.pop (aux .zeroTodo) (.copyTodo second) (.pushZero second) (.pushZero second))
  | .pushZero second=>.base (.push (aux .counter) false (.allocate second))
  | .copyTodo second=>.call (.copy (if second then 3 else 2) 0) (.loop second)
  | .loop second=>.base (.pop (aux .todo) (.finish second) (.increment second) (.increment second))
  | .increment second=>.call (.counter Inc.entry) (.popOverflow second)
  | .popOverflow second=>.base (.pop (aux .next) (.restore second) (.restore second) (.restore second))
  | .restore second=>.call (.copy 4 0) (.clearNext second)
  | .clearNext second=>.base (.pop (aux .next) (.loop second) (.clearNext second) (.clearNext second))
  | .finish second=>.call (.copy (if second then 6 else 5) 0) (.clearCounter second)
  | .clearCounter second=>.base (.pop (aux .counter) (if second then .rightShift 0 else .copyDelta)
      (.clearCounter second) (.clearCounter second))
  | .copyDelta=>.call (.copy 7 0) .seedPower
  | .seedPower=>.base (.push (aux .power) true .shift)
  | .shift=>.base (.pop (aux .shiftTodo) (.leftShift 0) .shiftPower .shiftPower)
  | .shiftPower=>.base (.push (aux .power) false .shiftHeight)
  | .shiftHeight=>.base (.push (aux .left) false .shift)
  | .leftShift p=>.base (.push (aux .left) false
      (if h:p.val<2 then .leftShift ⟨p.val+1,by omega⟩ else .copyPrecision))
  | .copyPrecision=>.call (.copy 8 0) (.add false)
  | .add second=>.call (.adder (.start false)) (if second then .done else .copyZero true)
  | .rightShift p=>.base (.push (aux .right) false
      (if h:p.val<2 then .rightShift ⟨p.val+1,by omega⟩ else .copyPartial))
  | .copyPartial=>.call (.copy 9 0) .clearPartial
  | .clearPartial=>.base (.pop (aux .output) (.add true) .clearPartial .clearPartial)
  | .done=>.base .halt
  | .metadata pc=>SemiprimeD1StackValidationLink.instruction metadataStack Label.metadata (M.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .counter pc=>SemiprimeD1StackMultiplierLink.instruction incrementStack Label.counter (Inc.code pc)
  | .adder pc=>SemiprimeD1StackMultiplierLink.instruction adderStack Label.adder (Add.code pc)
/-- Complete physical payload view; no native arithmetic result is a runtime object. -/
def store (metadata : M.Stack→List Bool) (binary : Aux→List Bool) : Stack→List Bool :=Sum.elim metadata binary
/-- Literal eleven binary/work words. -/
def words (left right scratch output counter next todo zeroTodo shiftTodo copyScratch power : List Bool) : Aux→List Bool
  | .left=>left | .right=>right | .scratch=>scratch | .output=>output | .counter=>counter | .next=>next
  | .todo=>todo | .zeroTodo=>zeroTodo | .shiftTodo=>shiftTodo | .copyScratch=>copyScratch | .power=>power
/-- ONLY original a/u/M and original BINARY t/p are initially populated. -/
def input (a u edges : Nat) (t p : List Bool) : Stack→List Bool :=store (M.input a u edges t p) (fun _=>[])
/-- Whole original-input entry before any geometry/order/guard/height/product acquisition. -/
def initial (a u edges : Nat) (t p : List Bool) : C.State Stack Label :=⟨some .start,none,none,input a u edges t p,[]⟩
/-- Ready entry reuses EXACTLY the ACTUALLY acquired37-role metadata cache. -/
def ready (a u edges : Nat) (t p : List Bool) : C.State Stack Label :=
  ⟨some .branch,none,none,store (SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result a u edges t p) (fun _=>[]),[]⟩
/-- One genuine fixed finite binary working-precision machine. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (metadataStack (M.aux .edges)) (aux .output) .start program
/-- ALL48 actual physical role slots are counted. -/
theorem stack_card : Fintype.card Stack=48 :=by rw [Fintype.card_sum,SemiprimeD1StackPhaseWorkingPrecisionMetadata.stack_card];decide
/-- The entire old metadata bank is injectively retained. -/
theorem metadata_injective : Function.Injective metadataStack :=Sum.inl_injective
/-- Actual increment input, scratch and output are distinct. -/
theorem increment_injective : Function.Injective incrementStack :=by decide
/-- Actual consuming adder has four distinct physical fields. -/
theorem adder_injective : Function.Injective adderStack :=by decide
/-- Every preserving copy has disjoint source, destination and scratch. -/
theorem copy_injective (kind : Fin 10) : Function.Injective (copyStack kind) :=by fin_cases kind <;> decide
/-- Internal control contains only finite labels/flags, never numeric operands or counts. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All payload and actual return alphabets are fixed finite before every original input. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecision
