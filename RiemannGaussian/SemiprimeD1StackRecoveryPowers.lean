/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationOriginal
import RiemannGaussian.SemiprimeD1StackRecoveryGridInventory
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Literal complete cached-power acquisition from four actual words
The only inputs are a sign-prefixed argument, its denominator, paid unary q,
and the paid width template. Every successor is the real normalized and twice
fitted multiplication, old power FIRST and original argument SECOND. Literal
ONE is emitted at index zero even at width zero; no native power is an operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowers
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRationalOperation (Stack Label program)
end R
/-- All original, counter, coefficient, chronological logging and scratch words. -/
inductive Aux where
  | argumentSigned | argumentDen | q | remaining | currentSigned | currentDen
  | history | output | row | copyScratch | frameScratch
  deriving DecidableEq,Repr
/-- Complete literal caller inventory. -/
instance :Fintype Aux:=Fintype.ofList [.argumentSigned,.argumentDen,.q,.remaining,.currentSigned,.currentDen,.history,.output,.row,.copyScratch,.frameScratch] (by intro k;cases k <;> simp)
/-- Every real rational-operation role and all eleven caller tapes are counted. -/
abbrev Stack:=R.Stack⊕Aux
/-- Injective actual rational-operation inclusion. -/
def rational:R.Stack→Stack:=Sum.inl
/-- Literal caller tape addresses. -/
def aux:Aux→Stack:=Sum.inr
/-- The actual caller width is directly the retained R36 template, with no shadow. -/
def template:Stack:=rational (SemiprimeD1StackRationalOperation.aux .template)
/-- Static35-role cleanup inventory excludes precisely the retained width. -/
def rationalRole:Fin 35→R.Stack:=SemiprimeD1StackRecoveryGrid.rationalRole
/-- Fixed preserving-copy sites; all four operands are copied before old output erasure. -/
inductive Copy where | count | input (right den:Bool) | save (den:Bool)
  deriving DecidableEq,Repr,Fintype
/-- Each source is an actual retained original or reached arithmetic output. -/
def copySource:Copy→Stack
  | .count=>aux .q
  | .input false false=>aux .currentSigned | .input false true=>aux .currentDen
  | .input true false=>aux .argumentSigned | .input true true=>aux .argumentDen
  | .save den=>rational (SemiprimeD1StackRationalOperation.aux (if den then .denominatorOutput else .numeratorOutput))
/-- Copies write only physically empty, distinct destinations. -/
def copyTarget:Copy→Stack
  | .count=>aux .remaining
  | .input right den=>rational (SemiprimeD1StackRationalOperation.aux
      (if right then (if den then .rightDen else .rightSigned) else (if den then .leftDen else .leftSigned)))
  | .save false=>aux .currentSigned | .save true=>aux .currentDen
/-- All three real preserving-copy operands are physical words. -/
def copyStack (site:Copy) (i:Fin 3):Stack:=if i=0 then copySource site else if i=1 then copyTarget site else aux .copyScratch
/-- Actual row fields are framed denominator first, then sign-prefixed numerator. -/
def frameStack (den:Bool) (i:Fin 3):Stack:=if i=0 then aux (if den then .currentDen else .currentSigned) else if i=1 then aux .row else aux .frameScratch
/-- Per-row bit reversal logs without copying the accumulated tail; one final reversal restores all row order. -/
def reverseStack (finish:Bool) (i:Fin 2):Stack:=if i=0 then aux (if finish then .history else .row) else aux (if finish then .output else .history)
/-- All finite local stages precede every original argument, q and width. -/
inductive Control where
  | start | first | seedMagnitude | seedSign | seedDen | frame (den:Bool) | tag | log | next
  | input (right den:Bool) | multiply | clearCurrent (den:Bool) | save (den:Bool)
  | sign | pushSign (negative:Bool) | clearRational (i:Fin 35)
  | finishCurrent (den:Bool) | terminal | reverse | done | abort
  deriving DecidableEq,Repr,Fintype
/-- Every included routine and return label is finite before the inputs. -/
inductive Label where
  | local (pc:Control) | rational (pc:R.Label) | copy (site:Copy) (pc:Fin 9)
  | frame (den:Bool) (pc:Fin 11) | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- ONE fixed finite program; no power/array/function/clock answer enters control. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.copy .count 0) (.local .first)
  | .local .first=>.base (.pop (aux .remaining) (.local .terminal) (.local .abort) (.local .seedMagnitude))
  | .local .seedMagnitude=>.base (.push (aux .currentSigned) true (.local .seedSign))
  | .local .seedSign=>.base (.push (aux .currentSigned) false (.local .seedDen))
  | .local .seedDen=>.base (.push (aux .currentDen) true (.local (.frame true)))
  | .local (.frame den)=>.call (.frame den 0) (.local (if den then .frame false else .tag))
  | .local .tag=>.base (.push (aux .row) true (.local .log))
  | .local .log=>.call (.reverse false 0) (.local .next)
  | .local .next=>.base (.pop (aux .remaining) (.local (.finishCurrent false)) (.local .abort) (.local (.input false false)))
  | .local (.input right den)=>.call (.copy (.input right den) 0)
      (.local (if den then (if right then .multiply else .input true false) else .input right true))
  | .local .multiply=>.call (.rational (SemiprimeD1StackRationalOperation.localLabel .start .mul false false)) (.local (.clearCurrent false))
  | .local (.clearCurrent den)=>.base (.pop (aux (if den then .currentDen else .currentSigned))
      (.local (if den then .save false else .clearCurrent true)) (.local (.clearCurrent den)) (.local (.clearCurrent den)))
  | .local (.save den)=>.call (.copy (.save den) 0) (.local (if den then .sign else .save true))
  | .local .sign=>.base (.pop (rational SemiprimeD1StackRationalOperation.signOutput) (.local .abort) (.local (.pushSign false)) (.local (.pushSign true)))
  | .local (.pushSign negative)=>.base (.push (aux .currentSigned) negative (.local (.clearRational 0)))
  | .local (.clearRational i)=>.base (.pop (rational (rationalRole i))
      (if h:i.val<34 then .local (.clearRational ⟨i.val+1,by omega⟩) else .local (.frame true))
      (.local (.clearRational i)) (.local (.clearRational i)))
  | .local (.finishCurrent den)=>.base (.pop (aux (if den then .currentDen else .currentSigned))
      (.local (if den then .terminal else .finishCurrent true)) (.local (.finishCurrent den)) (.local (.finishCurrent den)))
  | .local .terminal=>.base (.push (aux .output) false (.local .reverse))
  | .local .reverse=>.call (.reverse true 0) (.local .done)
  | .local .done|.local .abort=>.base .halt
  | .rational pc=>SemiprimeD1StackValidationLink.instruction rational Label.rational (R.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .frame den pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack den) (Label.frame den) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
/-- Actual R36 bank is empty except the supplied physical template. -/
def emptyRational (width:List Bool):R.Stack→List Bool:=fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then width else []
/-- Honest four-word initialization; no current power, answer, private bank or count cache is supplied. -/
def input (signed den q width:List Bool):Stack→List Bool:=Sum.elim (emptyRational width) (fun k=>match k with
  | .argumentSigned=>signed | .argumentDen=>den | .q=>q | _=>[])
/-- Source starts before the paid q-copy, literal seed and every real multiplication. -/
def initial (signed den q width:List Bool):C.State Stack Label:=⟨some (.local .start),none,none,input signed den q width,[]⟩
/-- Fixed genuine finite machine, with all return cells represented by its real finite alphabet. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .argumentSigned) (aux .output) (.local .start) program
/-- Every actual arithmetic, retained, logging, shadow and scratch role is counted. -/
theorem stack_card:Fintype.card Stack=47:=by simp only [Stack,Fintype.card_sum];decide
/-- All physical copy sites have three distinct operands. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by
  cases site with
  | count=>decide
  | input right den=>cases right <;> cases den <;> decide
  | save den=>cases den <;> decide
/-- Both actual row-field frames have distinct source/destination/scratch words. -/
theorem frame_injective (den:Bool):Function.Injective (frameStack den):=by cases den <;> decide
/-- Both consuming reversals have distinct input and output words. -/
theorem reverse_injective (finish:Bool):Function.Injective (reverseStack finish):=by cases finish <;> decide
/-- Control is finite before all original inputs and power counts. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every Boolean and real saved-return alphabet is finite. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryPowers
