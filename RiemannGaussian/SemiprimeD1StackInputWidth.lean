/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryProductRaw
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops

/-! # Actual active-digit bound from acquired physical counters
The public caller shares its actually acquired original bitwidth/radix caches
and actual descriptor index. Real copies and the frozen physical product
acquire i*B; literal paired pops compute min(B,ell-i*B), and actual bit pushes
construct its power-of-two bound. No width, bound, comparison or work answer
is supplied; all caches are preserved, all workspace is actually cleared.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackInputWidth
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace U
export SemiprimeD1StackUnaryProduct (Stack Label code entry)
end U
/-- Nine fixed Boolean roles, before all original inputs and indices. -/
inductive Stack where
  | widthCache | radixCache | indexCache | remaining | multiplier | scratch | skip | limit | output
  deriving DecidableEq,Repr
instance : Fintype Stack := Fintype.ofList
  [.widthCache,.radixCache,.indexCache,.remaining,.multiplier,.scratch,.skip,.limit,.output]
  (by intro k;cases k <;> simp)
/-- Physical source cache view; list lengths occur only in proofs. -/
structure Cache where
  /-- Original bitwidth markers produced by preprocessing. -/
  width : List Bool
  /-- Actual radix markers produced by preprocessing. -/
  radix : List Bool
  /-- Actual descriptor index markers, supplied by the upstream parser. -/
  index : List Bool
/-- Every preserving copy uses the same restored scratch, never a native copy. -/
def copyStack (kind : Fin 3) (k : Fin 3) : Stack :=
  if k=0 then (if kind=0 then .widthCache else if kind=1 then .indexCache else .radixCache)
  else if k=1 then (if kind=0 then .remaining else if kind=1 then .multiplier else .limit)
  else .scratch
/-- Real product registers directly share the actual retained radix cache. -/
def productStack : U.Stack→Stack
  | .multiplier=>.multiplier
  | .multiplicand=>.radixCache
  | .scratch=>.scratch
  | .product=>.skip
/-- Fixed local and included procedure labels, with no arithmetic payload. -/
inductive Label where
  | start | copyIndex | multiply | skipLoop | dropWidth | clearSkip | copyLimit | initBound
  | minLoop | minWidth | grow | clearRemaining | clearLimit | done
  | copy (kind : Fin 3) (pc : Fin 9) | product (pc : U.Label)
  deriving Fintype
/-- ONE literal instruction table. Every read and cleanup byte is executed. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.copy 0 0) .copyIndex
  | .copyIndex=>.call (.copy 1 0) .multiply
  | .multiply=>.call (.product U.entry) .skipLoop
  | .skipLoop=>.base (.pop .skip .copyLimit .dropWidth .dropWidth)
  | .dropWidth=>.base (.pop .remaining .clearSkip .skipLoop .skipLoop)
  | .clearSkip=>.base (.pop .skip .copyLimit .clearSkip .clearSkip)
  | .copyLimit=>.call (.copy 2 0) .initBound
  | .initBound=>.base (.push .output true .minLoop)
  | .minLoop=>.base (.pop .limit .clearRemaining .minWidth .minWidth)
  | .minWidth=>.base (.pop .remaining .clearLimit .grow .grow)
  | .grow=>.base (.push .output false .minLoop)
  | .clearRemaining=>.base (.pop .remaining .done .clearRemaining .clearRemaining)
  | .clearLimit=>.base (.pop .limit .done .clearLimit .clearLimit)
  | .done=>.base .halt
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .product pc=>SemiprimeD1StackMultiplierLink.instruction productStack Label.product (U.code pc)
/-- Physical state view at actual procedure boundaries; scratch is empty there. -/
def store (c : Cache) (remaining multiplier skip limit output : List Bool) : Stack→List Bool
  | .widthCache=>c.width
  | .radixCache=>c.radix
  | .indexCache=>c.index
  | .remaining=>remaining
  | .multiplier=>multiplier
  | .scratch=>[]
  | .skip=>skip
  | .limit=>limit
  | .output=>output
/-- Initial source contains ONLY the three actual retained physical caches. -/
def initial (c : Cache) : C.State Stack Label := ⟨some .start,none,none,store c [] [] [] [] [],[]⟩
/-- The THREE preserving copy-register inclusions are all physically injective. -/
theorem copy_injective (kind : Fin 3) : Function.Injective (copyStack kind) := by fin_cases kind <;> decide
/-- The real product shares the radix, while all four of its roles stay distinct. -/
theorem product_injective : Function.Injective productStack := by decide
/-- Actual fixed finite-alphabet machine, not a width/bound evaluator. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine .widthCache .output .start program
/-- All actual data/return alphabets are fixed and finite before all caches. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite .widthCache .output Label.start program
/-- No integer, list, width, bound or elapsed-count value occurs in control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite .widthCache .output Label.start program
/-- Exact physical data-role inventory, including shared restoration scratch. -/
theorem stack_card : Fintype.card Stack=9 := by decide
end RiemannGaussian.SemiprimeD1StackInputWidth
