/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationOutput
import RiemannGaussian.SemiprimeD1StackRecoveryPowersCleanup
/-! # Entire actual sequential successor, including all35 private drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersOperation
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackRecoveryPowersOperationOutput
open SemiprimeD1StackRecoveryPowersCleanup SemiprimeD1StackProcedureTrace
/-- Own elapsed prefix pays the four inputs, SAME whole R36, two old-current drains, two copies and actual sign. -/
def prefixTime (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool):Nat:=
  inputsTime (sx::xn) xd (sy::yn) yd+
  (SemiprimeD1StackRationalOperationExecution.runBound .mul sx xn xd sy yn yd width+1)+
  ((w.added .currentSigned).length+1+(w.added .currentDen).length+1)+
  saveTime (word .mul sx xn xd sy yn yd width)
/-- Actual complete prefix endpoint, with the current result physically acquired. -/
def beforeCleanup (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool):Words:=
  saved {w with rational:=SemiprimeD1StackRationalOperationExecution.result .mul sx xn xd sy yn yd width}
    (word .mul sx xn xd sy yn yd width)
/-- Every physical operand copy precedes either aliased destination drain. -/
theorem prefix_run (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.added .copyScratch=[])
    (hls:w.added .currentSigned=sx::xn) (hld:w.added .currentDen=xd)
    (hrs:w.added .argumentSigned=sy::yn) (hrd:w.added .argumentDen=yd):
    Runs program (prefixTime w sx xn xd sy yn yd width) (.local (.input false false)) (bank w)
      (.local (.clearRational 0)) (bank (beforeCleanup w sx xn xd sy yn yd width)):=by
  let ready:Words:={w with rational:=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width}
  let stopped:Words:={w with rational:=SemiprimeD1StackRationalOperationExecution.result .mul sx xn xd sy yn yd width}
  have h0:=inputs_run w width (sx::xn) xd (sy::yn) yd hr hs hls hld hrs hrd
  have h1:=rational_call ready sx xn xd sy yn yd width rfl
  have h2:=erase_run stopped
  have hshape:=word_shape .mul sx xn xd sy yn yd width
  have h3:=save_run stopped (word .mul sx xn xd sy yn yd width) hs hshape.1 hshape.2.1 hshape.2.2
  exact PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
/-- Saved W is literally retained through output acquisition and real sign consumption. -/
theorem beforeCleanup_template (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool):
    (beforeCleanup w sx xn xd sy yn yd width).rational (SemiprimeD1StackRationalOperation.aux .template)=width:=by
  change Function.update (SemiprimeD1StackRationalOperationExecution.result .mul sx xn xd sy yn yd width)
    SemiprimeD1StackRationalOperation.signOutput [] (SemiprimeD1StackRationalOperation.aux .template)=width
  rw [Function.update_of_ne (by decide)]
  rfl
/-- Every actual arithmetic word/shadow is physically empty after cleanup, while W and all11 caller words survive. -/
theorem cleanup_result (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width):
    cleared (fun i:Fin 35=>rational (rationalRole i)) (bank (beforeCleanup w sx xn xd sy yn yd width)) 35=
      bank (putCurrent w (word .mul sx xn xd sy yn yd width)):=by
  rw [rational_cleared]
  have he:(fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then
      (beforeCleanup w sx xn xd sy yn yd width).rational k else [])=emptyRational width:=by
    funext k
    by_cases hk:k=SemiprimeD1StackRationalOperation.aux .template
    · subst k
      simp only [ite_true]
      exact beforeCleanup_template w sx xn xd sy yn yd width
    · simp only [hk,ite_false,emptyRational]
  rw [he]
  change bank {putCurrent w (word .mul sx xn xd sy yn yd width) with rational:=emptyRational width}=_
  rw [←hr]
  rfl
/-- Literal inventory sum counts ALL47 physical words. -/
theorem word_sum (data:Stack→List Bool) (cap:Nat) (h:∀slot,(data slot).length≤cap):mass data≤47*cap:=by
  unfold mass
  calc
    _≤∑_slot:Stack,cap:=Finset.sum_le_sum (fun slot _=>h slot)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- The SAME actual prefix bounds physical stopped mass; no old clock is substituted. -/
theorem trace_mass (time:Nat) (pc stopped:Label) (before after:Stack→List Bool)
    (hr:Runs program time pc before stopped after):mass after≤47*(mass before+time):=by
  let start:C.State Stack Label:=⟨some pc,none,none,before,[]⟩
  obtain ⟨finish,hfinish,hAt⟩:=hr [] start ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program time (mass before) start finish (word_le_mass before) hfinish
  rw [hAt.2.1] at hd
  exact word_sum after (mass before+time) hd
/-- Complete actual successor budget, charging retained history by its current physical bytes only. -/
def timeBound (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool):Nat:=
  4000*(mass (bank w)+prefixTime w sx xn xd sy yn yd width+1)
/-- Complete actual successor updates only the current rational, preserving ALL original/counter/history words. -/
theorem operation_run (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.added .copyScratch=[])
    (hls:w.added .currentSigned=sx::xn) (hld:w.added .currentDen=xd)
    (hrs:w.added .argumentSigned=sy::yn) (hrd:w.added .argumentDen=yd):
    ∃q≤timeBound w sx xn xd sy yn yd width,Runs program q (.local (.input false false)) (bank w)
      (.local (.frame true)) (bank (putCurrent w (word .mul sx xn xd sy yn yd width))):=by
  have hp:=prefix_run w sx xn xd sy yn yd width hr hs hls hld hrs hrd
  obtain ⟨q,hq,hclear⟩:=rational_cleanup (bank (beforeCleanup w sx xn xd sy yn yd width))
  rw [cleanup_result w sx xn xd sy yn yd width hr] at hclear
  refine ⟨prefixTime w sx xn xd sy yn yd width+q,?_,PTrace.join hp hclear⟩
  have hm:=trace_mass _ _ _ _ _ hp
  unfold timeBound
  nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryPowersOperation
