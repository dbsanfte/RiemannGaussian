/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDividerExecution
import RiemannGaussian.SemiprimeD1StackReduceExecution
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeBitGcd
/-! # Actual finite-stack Euclid from two original binary words
The source physically constructs two fuel markers per original byte plus one.
Real trimming makes numeric-zero divisor exactly empty; only actual fuel/word
heads select iterations. Every positive step is the real fixed restoring
Divider11 followed by paid quotient erasure, Euclid swapping and remainder
trimming. No natural, supplied fuel, GCD answer or operation clock is an operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCD
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace D
export SemiprimeD1StackDivider (Stack Label code)
end D
namespace R
export SemiprimeD1StackReduce (Label code)
export SemiprimeD1StackAdder (Stack)
end R
/-- Two retained original inputs, genuinely acquired byte fuel, and four actual work/result words. -/
inductive Aux where | left | right | fuel | scan | next | trimScratch | output deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.left,.right,.fuel,.scan,.next,.trimScratch,.output] (by intro k;cases k <;> simp)
/-- All11 actual divider roles and seven actual caller words are counted, without alias shadows. -/
abbrev Stack:=D.Stack⊕Aux
/-- Complete injective physical divider inclusion. -/
def dividerStack :D.Stack→Stack:=Sum.inl
/-- Literal original/fuel/work/output addresses. -/
def aux :Aux→Stack:=Sum.inr
/-- Actual current Euclid first operand. -/
def x :Stack:=dividerStack (.inr .input)
/-- Actual current Euclid second operand, physically trimmed before every zero test. -/
def y :Stack:=dividerStack (.inr .divisor)
/-- Actual restoring-division remainder word. -/
def remainder :Stack:=dividerStack (.inr .remainder)
/-- Actual quotient is physically erased after each Euclid step. -/
def quotient :Stack:=dividerStack (.inr .quotient)
/-- Actual copy scratch is shared only between completed real procedure calls. -/
def copyScratch :Stack:=dividerStack (.inr .copyScratch)
/-- Six literal restoring-copy sites before byte counting, initialization and Euclid swapping. -/
inductive Copy where | fuelLeft | fuelRight | initialX | initialY | backupY | restoreX deriving DecidableEq,Repr
instance :Fintype Copy:=Fintype.ofList [.fuelLeft,.fuelRight,.initialX,.initialY,.backupY,.restoreX] (by intro k;cases k <;> simp)
/-- Every copied operand is a genuinely acquired original/current word. -/
def copyStack (part:Copy) (k:Fin 3) :Stack:=
  if k=0 then match part with
    | .fuelLeft|.initialX=>aux .left | .fuelRight|.initialY=>aux .right | .backupY=>y | .restoreX=>aux .next
  else if k=1 then match part with
    | .fuelLeft|.fuelRight=>aux .scan | .initialX|.restoreX=>x | .initialY=>y | .backupY=>aux .next
  else copyScratch
/-- Initial divisor, actual remainder and terminal GCD candidate are reversed by literal byte loops. -/
inductive Reverse where | initialY | remainder | finish deriving DecidableEq,Repr
instance :Fintype Reverse:=Fintype.ofList [.initialY,.remainder,.finish] (by intro k;cases k <;> simp)
/-- Real reverse sources all feed the shared physically cleared trim scratch. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack:=
  if k=0 then match part with | .initialY=>y | .remainder=>remainder | .finish=>x
  else aux .trimScratch
/-- Only the actual divisor or public output is the real reducer destination. -/
inductive Trim where | divisor | output deriving DecidableEq,Repr
instance :Fintype Trim:=Fintype.ofList [.divisor,.output] (by intro k;cases k <;> simp)
/-- Four distinct actual reducer operands, including two reused cleared divider operands. -/
def trimStack (part:Trim) :R.Stack→Stack
  | .left=>dividerStack (.inl .left) | .right=>dividerStack (.inl .right)
  | .scratch=>aux .trimScratch | .output=>if part=.divisor then y else aux .output
/-- Finite byte-scan/Euclid control, independent of all operand values and lengths. -/
inductive Label where
  | start | copyFuelLeft | copyFuelRight | scan (right:Bool) | pushOne (right:Bool) | pushTwo (right:Bool)
  | initialX | initialY | reverseInitial | trimInitial | loop | check | backup | divide | clearQuotient
  | restoreX | clearNext | reverseRemainder | trimRemainder | reverseFinish | trimFinish | clearFuel | done | abort
  | divider (pc:D.Label) | copier (part:Copy) (pc:Fin 9) | reversal (part:Reverse) (pc:Fin 4) | reducer (part:Trim) (pc:R.Label)
  deriving Fintype
/-- One parameterless literal source; all length markers, divisions, moves and final normalization execute here. -/
def program :Label→C.Instruction Stack Label
  | .start=>.base (.push (aux .fuel) true .copyFuelLeft)
  | .copyFuelLeft=>.call (.copier .fuelLeft 0) (.scan false)
  | .copyFuelRight=>.call (.copier .fuelRight 0) (.scan true)
  | .scan right=>.base (.pop (aux .scan) (if right then .initialX else .copyFuelRight) (.pushOne right) (.pushOne right))
  | .pushOne right=>.base (.push (aux .fuel) true (.pushTwo right))
  | .pushTwo right=>.base (.push (aux .fuel) true (.scan right))
  | .initialX=>.call (.copier .initialX 0) .initialY
  | .initialY=>.call (.copier .initialY 0) .reverseInitial
  | .reverseInitial=>.call (.reversal .initialY 0) .trimInitial
  | .trimInitial=>.call (.reducer .divisor .trim) .loop
  | .loop=>.base (.pop (aux .fuel) .abort .abort .check)
  | .check=>.base (.peek y .reverseFinish .backup .backup)
  | .backup=>.call (.copier .backupY 0) .divide
  | .divide=>.call (.divider (.control .start)) .clearQuotient
  | .clearQuotient=>.base (.pop quotient .restoreX .clearQuotient .clearQuotient)
  | .restoreX=>.call (.copier .restoreX 0) .clearNext
  | .clearNext=>.base (.pop (aux .next) .reverseRemainder .clearNext .clearNext)
  | .reverseRemainder=>.call (.reversal .remainder 0) .trimRemainder
  | .trimRemainder=>.call (.reducer .divisor .trim) .loop
  | .reverseFinish=>.call (.reversal .finish 0) .trimFinish
  | .trimFinish=>.call (.reducer .output .trim) .clearFuel
  | .clearFuel=>.base (.pop (aux .fuel) .done .clearFuel .clearFuel)
  | .done|.abort=>.base .halt
  | .divider pc=>SemiprimeD1StackValidationLink.instruction dividerStack Label.divider (D.code pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .reversal part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reversal part) (SemiprimeD1StackReverseWord.code pc)
  | .reducer part pc=>SemiprimeD1StackMultiplierLink.instruction (trimStack part) (Label.reducer part) (R.code pc)
/-- Two actual original binary words, with all16 derived/work/result words initially empty. -/
def input (left right:List Bool) :Stack→List Bool:=Sum.elim (fun _=>[]) (fun k=>match k with
  | .left=>left | .right=>right | _=>[])
/-- Complete two-word front door; fuel and every arithmetic/cache word are produced inside the program. -/
def initial (left right:List Bool) :C.State Stack Label:=⟨some .start,none,none,input left right,[]⟩
/-- Fixed finite18-role machine, returning the compact GCD word. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .left) (aux .output) .start program
/-- All11 divider and seven caller roles remain actual Boolean words. -/
theorem stack_card :Fintype.card Stack=18:=by decide
/-- Actual divider calls preserve the full physical inclusion. -/
theorem divider_injective :Function.Injective dividerStack:=Sum.inl_injective
/-- Every real copy has three distinct source/destination/scratch addresses. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part):=by cases part <;> decide
/-- Every actual reversal has a source distinct from its scratch destination. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part):=by cases part <;> decide
/-- Every actual reducer inclusion has four distinct physical operands. -/
theorem trim_injective (part:Trim) :Function.Injective (trimStack part):=by cases part <;> decide
/-- Runtime control contains only fixed finite labels and actual Boolean flags. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual Bool/data and finite-label return alphabet is fixed finite before the original words. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackEuclidGCD
