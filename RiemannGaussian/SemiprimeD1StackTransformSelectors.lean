/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
import RiemannGaussian.SemiprimeD1StackCopy
/-! # Physical finite constructor and transform selector acquisition
The original unary tag and coord0 words are preserved by actual copies. Both
copies are consumed by bounded literal control BEFORE either Boolean selector
is pushed. There is no native length, decision or decoded-mode instruction.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformSelectors
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
/-- Seven actual physical words, including the two original read-only fields. -/
inductive Stack where | tag | transform | tagReader | transformReader | scratch | stage | inverse
  deriving DecidableEq,Repr
instance : Fintype Stack :=Fintype.ofList [.tag,.transform,.tagReader,.transformReader,.scratch,.stage,.inverse]
  (by intro k;cases k <;> simp)
/-- Literal bounded marker counters and actual one-bit push stages. -/
inductive Label where
  | start | clearInverse | copyTag | tag (count : Fin 18)
  | copyTransform (second : Bool) | transform (second : Bool) (count : Fin 3)
  | emitStage (second inverse : Bool) | emitInverse (inverse : Bool) | done | abort
  | copy (transform : Bool) (pc : Fin 9)
  deriving Fintype
/-- Each actual copy has disjoint original, reader and scratch operands. -/
def copyStack (transform : Bool) (i : Fin 3) : Stack :=
  if i=0 then if transform then .transform else .tag
  else if i=1 then if transform then .transformReader else .tagReader else .scratch
/-- Actual constructor1/2/3 dispatch; scale2 uses the unused false stage. -/
def tagDispatch (count : Fin 18) : Label :=
  if count.val=1 then .copyTransform false else if count.val=2 then .copyTransform false
  else if count.val=3 then .copyTransform true else .abort
/-- One next actual constructor-marker read, bounded by the literal inventory. -/
def nextTag (count : Fin 18) : Label :=
  if h:count.val<17 then .tag ⟨count.val+1,by omega⟩ else .abort
/-- Literal inverse mapping: original transform0/1 false, transform2 true. -/
def transformDispatch (second : Bool) (count : Fin 3) : Label :=.emitStage second (count.val==2)
/-- One next actual transform-marker read, bounded by the original three codes. -/
def nextTransform (second : Bool) (count : Fin 3) : Label :=
  if h:count.val<2 then .transform second ⟨count.val+1,by omega⟩ else .abort
/-- Fixed physical source: clear stale selectors, copy/read both original fields,
then push two real singleton Boolean words; unknown codes really abort. -/
def program : Label→C.Instruction Stack Label
  | .start=>.base (.pop .stage .clearInverse .start .start)
  | .clearInverse=>.base (.pop .inverse .copyTag .clearInverse .clearInverse)
  | .copyTag=>.call (.copy false 0) (.tag 0)
  | .tag n=>.base (.pop .tagReader (tagDispatch n) .abort (nextTag n))
  | .copyTransform second=>.call (.copy true 0) (.transform second 0)
  | .transform second n=>.base (.pop .transformReader (transformDispatch second n) .abort (nextTransform second n))
  | .emitStage second inverse=>.base (.push .stage second (.emitInverse inverse))
  | .emitInverse inverse=>.base (.push .inverse inverse .done)
  | .done|.abort=>.base .halt
  | .copy field pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack field) (Label.copy field)
      (SemiprimeD1StackCopy.code pc)
/-- Exact full physical store, with actual copy scratch empty. -/
def data (tag transform tagReader transformReader stage inverse : List Bool) : Stack→List Bool
  | .tag=>tag | .transform=>transform | .tagReader=>tagReader | .transformReader=>transformReader
  | .stage=>stage | .inverse=>inverse | .scratch=>[]
/-- Only acquired original words and arbitrary charged stale selector words. -/
def initial (tag transform oldStage oldInverse : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,data tag transform [] [] oldStage oldInverse,[]⟩
/-- Original fields retained; both readers/scratch clear; selectors physically present. -/
def done (tag transform : List Bool) (second inverse : Bool) : C.State Stack Label :=
  ⟨none,none,none,data tag transform [] [] [second] [inverse],[]⟩
/-- One genuine finite machine, independent of all original inputs and descriptors. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine .tag .stage .start program
/-- Complete physical role count, including the original fields and copy scratch. -/
theorem stack_card : Fintype.card Stack=7 :=by decide
/-- Per-copy disjointness holds independently of descriptor bytes or numeric values. -/
theorem copy_injective (field : Bool) : Function.Injective (copyStack field) :=by
  cases field <;> decide
end RiemannGaussian.SemiprimeD1StackTransformSelectors
