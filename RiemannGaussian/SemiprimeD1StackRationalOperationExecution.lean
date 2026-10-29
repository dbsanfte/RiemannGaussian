/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationRaw
import RiemannGaussian.SemiprimeD1StackRationalOperationFinish
/-! # Whole five-input rational-operation source and exact legacy fitted bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationExecution
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackRationalOperationSetup
open SemiprimeD1StackRationalOperationRaw SemiprimeD1StackRationalOperationFinish
open SemiprimeD1StackProcedureTrace
/-- Complete actual stopped bank retains all five original tapes and only three output words. -/
def result (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :Stack→List Bool:=
  let raw:=rawWord op sx xn xd sy yn yd
  bank (finishResult (originals (sx::xn) xd (sy::yn) yd template)
    raw.numerator.negative raw.numerator.magnitude raw.denominator)
/-- Actual true halt with every transient flag and genuine return cell empty. -/
def done (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :C.State Stack Label:=
  ⟨none,none,none,result op sx xn xd sy yn yd template,[]⟩
/-- Own whole elapsed clock includes sign-word acquisition, actual raw arithmetic, every cleanup, real normalization, both fits and halt. -/
def runBound (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :Nat:=
  let raw:=rawWord op sx xn xd sy yn yd
  setupTime op xn yn+rawTime op sx xn xd sy yn yd+cleanupTime (rawResult op sx xn xd sy yn yd template)+
    finishTime raw.numerator.magnitude raw.denominator template+1
/-- The physically cleared raw bank is exactly Normalize22's honest two-word initial bank. -/
theorem clean_ready (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    clean (rawResult op sx xn xd sy yn yd template)=
      normalizeReady (originals (sx::xn) xd (sy::yn) yd template)
        ((rawWord op sx xn xd sy yn yd).numerator.negative::(rawWord op sx xn xd sy yn yd).numerator.magnitude)
        (rawWord op sx xn xd sy yn yd).denominator:=by
  cases op <;> rfl
/-- Whole actual finite source acquires every intermediate from the five original words; there is no raw-answer operand. -/
theorem source_trace (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program (runBound op sx xn xd sy yn yd template-1) (localLabel .start op false false)
      (input (sx::xn) xd (sy::yn) yd template)
      (localLabel .done op sx (if binary op then sy else false)) (result op sx xn xd sy yn yd template):=by
  let raw:=rawWord op sx xn xd sy yn yd
  have h0:=setup_run op sx xn xd sy yn yd template
  have h1:=raw_run op sx xn xd sy yn yd template
  have h2:=cleanup_run op sx (if binary op then sy else false) (rawResult op sx xn xd sy yn yd template)
  rw [clean_ready] at h2
  have h3:=finish_run op sx (if binary op then sy else false)
    (originals (sx::xn) xd (sy::yn) yd template) raw.numerator.negative raw.numerator.magnitude raw.denominator rfl rfl
  have h:=P.join (P.join (P.join h0 h1) h2) h3
  simpa only [runBound,raw,result,originals,Nat.add_sub_cancel] using h
/-- Exact entire execution, ending at actual halt and retaining only original tapes plus fitted outputs. -/
theorem source_run (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    SemiprimeD1StackCalls.run program (runBound op sx xn xd sy yn yd template)
      (initial op (sx::xn) xd (sy::yn) yd template)=some (done op sx xn xd sy yn yd template):=by
  obtain ⟨finish,hfin,hAt⟩:=source_trace op sx xn xd sy yn yd template []
    (initial op (sx::xn) xd (sy::yn) yd template) ⟨rfl,rfl,rfl⟩
  have he:runBound op sx xn xd sy yn yd template=(runBound op sx xn xd sy yn yd template-1)+1:=by
    simp only [runBound,Nat.add_sub_cancel]
  rw [he,SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
  exact halt_run program (localLabel .done op sx (if binary op then sy else false)) rfl
    (result op sx xn xd sy yn yd template) [] finish hAt
/-- Genuine finite36-role machine, from the honest five physical inputs, follows the SAME source trace. -/
noncomputable def operationInTime (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    StateTransition.EvalsToInTime (machine op).step
      (SemiprimeD1StackCalls.configuration (initial op (sx::xn) xd (sy::yn) yd template))
      (some (SemiprimeD1StackCalls.configuration (done op sx xn xd sy yn yd template)))
      (runBound op sx xn xd sy yn yd template):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .leftSigned) (aux .numeratorOutput) (localLabel .start op false false) program
  exact ⟨⟨_,source_run op sx xn xd sy yn yd template⟩,le_rfl⟩
/-- Exact executeOperation bytes for every raw padding, signed zero, zero denominator and empty template. -/
theorem output_legacy (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    outputWord (done op sx xn xd sy yn yd template).data=
      (SemiprimeRationalBits.executeOperation (operation op) ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩ template).word:=by
  let raw:=rawWord op sx xn xd sy yn yd
  change (⟨⟨(normalized raw.numerator.negative raw.numerator.magnitude raw.denominator).numerator.negative,
      (SemiprimeBitDivision.fitBits (normalized raw.numerator.negative raw.numerator.magnitude raw.denominator).numerator.magnitude template).bits⟩,
      (SemiprimeBitDivision.fitBits (normalized raw.numerator.negative raw.numerator.magnitude raw.denominator).denominator template).bits⟩:SemiprimeRationalBits.RationalWord)=_
  rw [normalized,SemiprimeD1StackRationalNormalizeSpec.word_legacy]
  have hr:(⟨⟨raw.numerator.negative,raw.numerator.magnitude⟩,raw.denominator⟩:SemiprimeRationalBits.RationalWord)=
      (SemiprimeRationalBits.rawOperation (operation op) ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩).word:=rawWord_legacy op sx xn xd sy yn yd
  rw [hr]
  rfl
/-- The legacy value/positive-denominator theorem applies to the actual stopped result under honest operand and fit premises. -/
theorem output_correct (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool)
    (hx:(⟨⟨sx,xn⟩,xd⟩:SemiprimeRationalBits.RationalWord).Valid)
    (hy:(⟨⟨sy,yn⟩,yd⟩:SemiprimeRationalBits.RationalWord).Valid)
    (hf:SemiprimeRationalBits.Fits ((operation op).value
      (⟨⟨sx,xn⟩,xd⟩:SemiprimeRationalBits.RationalWord).value
      (⟨⟨sy,yn⟩,yd⟩:SemiprimeRationalBits.RationalWord).value) template.length) :
    let out:=outputWord (done op sx xn xd sy yn yd template).data
    out.value=(operation op).value (⟨⟨sx,xn⟩,xd⟩:SemiprimeRationalBits.RationalWord).value
      (⟨⟨sy,yn⟩,yd⟩:SemiprimeRationalBits.RationalWord).value ∧ out.Valid ∧
      SemiprimeRationalBits.Width out template.length:=by
  rw [output_legacy]
  exact SemiprimeRationalBits.executeOperation_correct (operation op) _ _ template hx hy hf
end RiemannGaussian.SemiprimeD1StackRationalOperationExecution
