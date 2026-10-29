/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationInput
import RiemannGaussian.SemiprimeD1StackRecoveryPowersSpec
/-! # Actual complete R36 call, old-current drains, fitted output copies and sign acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationOutput
open SemiprimeD1StackRecoveryPowers SemiprimeD1StackRecoveryPowersView
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackProcedureTrace
namespace R
export SemiprimeD1StackRationalOperation (Op)
end R
/-- Exact two cache fields acquired after a real operation. -/
def putCurrent (w:Words) (x:SemiprimeRationalBits.RationalWord):Words:=
  {w with added:=Function.update (Function.update w.added .currentSigned (SemiprimeD1StackRecoveryPowersSpec.signed x)) .currentDen x.denominator}
/-- Whole real multiplication call, retaining every caller tape and the actual original operands. -/
theorem rational_call (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hi:w.rational=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width):
    Runs program (SemiprimeD1StackRationalOperationExecution.runBound .mul sx xn xd sy yn yd width+1)
      (.local .multiply) (bank w) (.local (.clearCurrent false))
      (bank {w with rational:=SemiprimeD1StackRationalOperationExecution.result .mul sx xn xd sy yn yd width}):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rational Label.rational Sum.inl_injective R.program
    (SemiprimeD1StackRationalOperation.localLabel .start .mul false false) (fun _=>rfl)
    (.local .multiply) (.local (.clearCurrent false)) rfl _
    (SemiprimeD1StackRationalOperation.initial .mul (sx::xn) xd (sy::yn) yd width)
    (SemiprimeD1StackRationalOperationExecution.done .mul sx xn xd sy yn yd width) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackRationalOperationExecution.source_run .mul sx xn xd sy yn yd width)
  · exact ⟨fun slot=>congrFun hi slot,fun _ _=>rfl⟩
  · constructor
    · intro slot;rfl
    · intro role hk;rcases role with role|role
      · exact (hk role rfl).elim
      · rfl
/-- Exact interpretation of actual stopped R36 outputs; no legacy result is an operand. -/
def word (op:R.Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :SemiprimeRationalBits.RationalWord:=
  SemiprimeD1StackRationalOperationEncoding.outputWord
    (SemiprimeD1StackRationalOperationExecution.result op sx xn xd sy yn yd width)
/-- Physical R36 numerator, denominator and singleton sign fields have this exact byte shape. -/
theorem word_shape (op:R.Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :
    let data:=SemiprimeD1StackRationalOperationExecution.result op sx xn xd sy yn yd width
    data (SemiprimeD1StackRationalOperation.aux .numeratorOutput)=(word op sx xn xd sy yn yd width).numerator.magnitude ∧
    data (SemiprimeD1StackRationalOperation.aux .denominatorOutput)=(word op sx xn xd sy yn yd width).denominator ∧
    data SemiprimeD1StackRationalOperation.signOutput=[(word op sx xn xd sy yn yd width).numerator.negative]:=⟨rfl,rfl,rfl⟩
/-- Exact bytes of the actual fitted source equal the authoritative legacy operation. -/
theorem word_legacy (op:R.Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :
    word op sx xn xd sy yn yd width=(SemiprimeRationalBits.executeOperation
      (SemiprimeD1StackRationalOperation.operation op) ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩ width).word:=
  SemiprimeD1StackRationalOperationExecution.output_legacy op sx xn xd sy yn yd width
/-- Exact two physical destination drains; source operands are already retained in the actual stopped R36 bank. -/
def emptyCurrent (w:Words) :Words:=
  {w with added:=Function.update (Function.update w.added .currentSigned []) .currentDen []}
/-- Both destination fields are truly empty before actual output copies. -/
theorem emptyCurrent_fields (w:Words) :
    (emptyCurrent w).added .currentSigned=[] ∧ (emptyCurrent w).added .currentDen=[]:=by
  simp only [emptyCurrent,Function.update_apply,reduceCtorEq,ite_false,ite_true,true_and]
/-- Destination replacement visits every actual old signed/denominator byte and both empty branches. -/
theorem erase_run (w:Words) :
    Runs program ((w.added .currentSigned).length+1+(w.added .currentDen).length+1)
      (.local (.clearCurrent false)) (bank w) (.local (.save false)) (bank (emptyCurrent w)):=by
  let w1:Words:={w with added:=Function.update w.added .currentSigned []}
  have h0:=PTrace.drain_loop (.local (.clearCurrent false)) (.local (.clearCurrent true)) (aux .currentSigned) rfl
    (bank w) (w.added .currentSigned) rfl
  rw [update_added w .currentSigned] at h0
  have hx:w1.added .currentDen=w.added .currentDen:=by
    dsimp only [w1]
    exact Function.update_of_ne (by decide) _ _
  have h1:=PTrace.drain_loop (.local (.clearCurrent true)) (.local (.save false)) (aux .currentDen) rfl
    (bank w1) (w.added .currentDen) hx
  rw [update_added w1 .currentDen] at h1
  have h:=PTrace.join h0 h1
  simpa only [Nat.add_assoc,w1,emptyCurrent] using h
/-- Two preserving result copies and literal actual-sign pop/push leave only fixed35-role cleanup outstanding. -/
def saveTime (out:SemiprimeRationalBits.RationalWord) :Nat:=
  (5*out.numerator.magnitude.length+4)+(5*out.denominator.length+4)+1+1
/-- Actual saved output bank before the real35-role cleanup; sign prefix is already copied into the register. -/
def saved (w:Words) (out:SemiprimeRationalBits.RationalWord) :Words:=
  {putCurrent w out with rational:=Function.update w.rational SemiprimeD1StackRationalOperation.signOutput []}
/-- Actual output copies/sign read preserve exact bytes, including negative zero and zero-width fields. -/
theorem save_run (w:Words) (out:SemiprimeRationalBits.RationalWord)
    (hs:w.added .copyScratch=[])
    (hn:w.rational (SemiprimeD1StackRationalOperation.aux .numeratorOutput)=out.numerator.magnitude)
    (hd:w.rational (SemiprimeD1StackRationalOperation.aux .denominatorOutput)=out.denominator)
    (hsg:w.rational SemiprimeD1StackRationalOperation.signOutput=[out.numerator.negative]) :
    Runs program (saveTime out) (.local (.save false)) (bank (emptyCurrent w))
      (.local (.clearRational 0)) (bank (saved w out)):=by
  let w0:=emptyCurrent w
  let w1:Words:={w0 with added:=Function.update w0.added .currentSigned out.numerator.magnitude}
  let w2:Words:={w1 with added:=Function.update w1.added .currentDen out.denominator}
  let w3:Words:={w2 with rational:=Function.update w2.rational SemiprimeD1StackRationalOperation.signOutput []}
  have h0:=PTrace.copy_call (.save false) (.local (.save false)) (.local (.save true)) rfl
    (bank w0) out.numerator.magnitude [] hn (emptyCurrent_fields w).1 hs
  change Runs _ _ _ _ _ (Function.update (bank w0) (aux .currentSigned) (out.numerator.magnitude++[])) at h0
  rw [List.append_nil,update_added w0 .currentSigned] at h0
  have hz:w1.added .currentDen=[]:=by
    change Function.update w0.added .currentSigned out.numerator.magnitude .currentDen=[]
    rw [Function.update_of_ne (by decide)]
    exact (emptyCurrent_fields w).2
  have h1:=PTrace.copy_call (.save true) (.local (.save true)) (.local .sign) rfl
    (bank w1) out.denominator [] hd hz hs
  change Runs _ _ _ _ _ (Function.update (bank w1) (aux .currentDen) (out.denominator++[])) at h1
  rw [List.append_nil,update_added w1 .currentDen] at h1
  have h2:=PTrace.pop_run (.local .sign) (.local .abort)
    (.local (.pushSign false)) (.local (.pushSign true))
    (rational SemiprimeD1StackRationalOperation.signOutput) (bank w2) [out.numerator.negative] rfl hsg
  rw [update_rational] at h2
  have hc:SemiprimeD1StackBytecode.choose (Label.local .abort)
      (Label.local (.pushSign false)) (Label.local (.pushSign true)) [out.numerator.negative].head?=
      Label.local (.pushSign out.numerator.negative):=by cases out.numerator.negative <;> rfl
  rw [hc] at h2
  have h3:=PTrace.push_run (.local (.pushSign out.numerator.negative)) (.local (.clearRational 0))
    (aux .currentSigned) out.numerator.negative (bank w3) rfl
  rw [update_added w3 .currentSigned] at h3
  have hnum:w3.added .currentSigned=out.numerator.magnitude:=by
    change Function.update (Function.update w0.added .currentSigned out.numerator.magnitude) .currentDen out.denominator .currentSigned=_
    rw [Function.update_of_ne (by decide),Function.update_self]
  change Runs program 1 _ _ _ (bank {w3 with added:=Function.update w3.added .currentSigned (out.numerator.negative::w3.added .currentSigned)}) at h3
  rw [hnum] at h3
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  have he:{w3 with added:=Function.update w3.added .currentSigned (out.numerator.negative::out.numerator.magnitude)}=
      saved w out:=by
    dsimp only [w3,w2,w1,w0,emptyCurrent,saved,putCurrent]
    congr 1
    funext k
    cases k <;> simp [SemiprimeD1StackRecoveryPowersSpec.signed]
  change Runs program _ _ _ _ (bank _) at h
  rw [he] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationOutput
