/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextOriginal
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Physical original fresh-generator allocation from the actual child-context cache
The source derives old/new rank from real header acquisition, consumes paid copies
of those actual counters, emits each coefficient's literal codec bytes, and makes
one actual reversal. No q/P/rank/vector answer is supplied at either entry.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFresh
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace H
export SemiprimeD1StackPhaseChildContext (Stack Label program initial input ready phaseStack oldStack childStack aux)
namespace J
export SemiprimeD1StackJetContext (rankCache widthCache axesCache)
end J
end H
/-- Physical allocation counters, reverse byte history, output vector and restoration scratch. -/
inductive Aux where | remaining | skip | history | output | scratch deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.remaining,.skip,.history,.output,.scratch] (by intro k;cases k <;> simp)
/-- Retained actual80-role context cache and five literal allocator roles. -/
abbrev Stack :=H.Stack⊕Aux
/-- Entire actual cache remains disjoint from allocator storage. -/
def contextStack : H.Stack→Stack :=Sum.inl
/-- Literal allocator register inclusion. -/
def aux : Aux→Stack :=Sum.inr
/-- Actual new-rank counter acquired from the new header by the real context source. -/
def newRank : Stack :=contextStack (H.childStack H.J.rankCache)
/-- Actual old-rank counter acquired from the caller's old header by the real context source. -/
def oldRank : Stack :=contextStack (H.oldStack H.J.rankCache)
/-- Actual width VALUE markers determine the reduced scalar unit's bit. -/
def width : Stack :=contextStack (H.childStack H.J.widthCache)
/-- Physical child-context presence flag; no verdict operand is supplied. -/
def valid : Stack :=contextStack (H.aux .valid)
/-- Fixed finite allocation control; all counts live on actual Boolean tapes. -/
inductive Label where
  | start | phaseReady | guard | copyNew | copyOld | before | choose | unit
  | zeroBefore0 | zeroBefore1 | zeroAfter0 | zeroAfter1
  | one0 | one1 | one2 | one3 | after | clearSkip | seed | reverse | done
  | context (pc : H.Label) | copy (old : Bool) (pc : Fin 9) | reversal (pc : Fin 4)
  deriving Fintype
/-- Two real preserving copies read ACTUALLY acquired ranks. -/
def copyStack (old : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if old then oldRank else newRank)
  else if k=1 then (if old then aux .skip else aux .remaining) else aux .scratch
/-- Actual one-pass byte reversal consumes history into the actual output tape. -/
def reverseStack (k : Fin 2) : Stack :=if k=0 then aux .history else aux .output
/-- Literal original-source→header/cache→rank-counter→coefficient-byte pipeline. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.context .start) .guard
  | .phaseReady=>.call (.context .guard) .guard
  | .guard=>.base (.peek valid .done .done .copyNew)
  | .copyNew=>.call (.copy false 0) .copyOld
  | .copyOld=>.call (.copy true 0) .before
  | .before=>.base (.pop (aux .remaining) .clearSkip .choose .choose)
  | .choose=>.base (.pop (aux .skip) .unit .zeroBefore0 .zeroBefore0)
  | .unit=>.base (.peek width .zeroAfter0 .one0 .one0)
  | .zeroBefore0=>.base (.push (aux .history) true .zeroBefore1)
  | .zeroBefore1=>.base (.push (aux .history) false .before)
  | .zeroAfter0=>.base (.push (aux .history) true .zeroAfter1)
  | .zeroAfter1=>.base (.push (aux .history) false .after)
  | .one0=>.base (.push (aux .history) true .one1)
  | .one1=>.base (.push (aux .history) true .one2)
  | .one2=>.base (.push (aux .history) true .one3)
  | .one3=>.base (.push (aux .history) false .after)
  | .after=>.base (.pop (aux .remaining) .clearSkip .zeroAfter0 .zeroAfter0)
  | .clearSkip=>.base (.pop (aux .skip) .seed .clearSkip .clearSkip)
  | .seed=>.base (.push (aux .output) false .reverse)
  | .reverse=>.call (.reversal 0) .done
  | .done=>.base .halt
  | .context pc=>SemiprimeD1StackValidationLink.instruction contextStack Label.context (H.program pc)
  | .copy old pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack old) (Label.copy old) (SemiprimeD1StackCopy.code pc)
  | .reversal pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reversal (SemiprimeD1StackReverseWord.code pc)
/-- Exact bank views are proof invariants, absent from finite executed control. -/
def store (context : H.Stack→List Bool) (remaining skip history output scratch : List Bool) : Stack→List Bool :=
  Sum.elim context (fun k=>match k with
    | .remaining=>remaining | .skip=>skip | .history=>history | .output=>output | .scratch=>scratch)
/-- Original physical a/u/M and binary t/p plus original UNARY old-header only. -/
def input (a u edges : Nat) (t p axes : List Bool) : Stack→List Bool :=store (H.input a u edges t p axes) [] [] [] [] []
/-- Whole source starts before every phase/context/rank supplier. -/
def initial (a u edges : Nat) (t p axes : List Bool) : C.State Stack Label :=⟨some .start,none,none,input a u edges t p axes,[]⟩
/-- SAME-program ready entry retains the ACTUALLY acquired complete old/new context caches. -/
def ready (a u edges : Nat) (t p : List Bool) (axes : List Nat) : C.State Stack Label :=
  ⟨some .guard,none,none,store (SemiprimeD1StackPhaseChildContextComponents.result a u edges t p axes) [] [] [] [] [],[]⟩
/-- SAME program also accepts the exact actual P48 cache before old/new context acquisition. -/
def phaseReady (a u edges : Nat) (t p axes : List Bool) : C.State Stack Label :=
  ⟨some .phaseReady,none,none,store (H.ready a u edges t p axes).data [] [] [] [] [],[]⟩
/-- One fixed genuine finite machine, with Boolean data and finite actual returns. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (contextStack (H.oldStack H.J.axesCache)) (aux .output) .start program
/-- Complete allocator/context cache bank contains85 physical Boolean roles. -/
theorem stack_card : Fintype.card Stack=85 :=by rw [Fintype.card_sum,SemiprimeD1StackPhaseChildContext.stack_card];decide
/-- Actual context inclusion preserves every80-role field separately. -/
theorem context_injective : Function.Injective contextStack :=Sum.inl_injective
/-- Rank copy banks have distinct actual source/destination/restoration tapes. -/
theorem copy_injective (old : Bool) : Function.Injective (copyStack old) :=by cases old <;> decide
/-- Byte reversal has two distinct physical tapes. -/
theorem reverse_injective : Function.Injective reverseStack :=by decide
/-- Numeric axes/precision/rank do not occur in executed finite control. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every physical alphabet, including actual return cells, is fixed finite. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFresh
