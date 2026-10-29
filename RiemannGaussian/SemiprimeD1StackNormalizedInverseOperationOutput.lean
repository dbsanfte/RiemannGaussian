/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationInput
/-! # Physical destination replacement after actual fitted rational execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationOutput
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView SemiprimeD1StackNormalizedInverseCalls
open SemiprimeD1StackNormalizedInverseOperationInput SemiprimeD1StackProcedureTrace
namespace R
export SemiprimeD1StackRationalOperation (Op)
end R
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
/-- Destination replacement visits every actual old signed/denominator byte and both empty branches. -/
theorem erase_run (site:Site) (w:Words) :
    Runs program ((w.registers (destination site,false)).length+1+(w.registers (destination site,true)).length+1)
      (.operation site (.clearDestination false)) (store w) (.operation site (.copyOutput false)) (store (emptyReg w (destination site))):=by
  let r:=destination site
  let w1:Words:={w with registers:=Function.update w.registers (r,false) []}
  have h0:=PTrace.drain_loop (.operation site (.clearDestination false)) (.operation site (.clearDestination true)) (reg r false) rfl
    (store w) (w.registers (r,false)) rfl
  rw [update_register w r false] at h0
  have hx:w1.registers (r,true)=w.registers (r,true):=by
    dsimp only [w1]
    exact Function.update_of_ne (by intro h;have hh:=congrArg Prod.snd h;cases hh) _ _
  have h1:=PTrace.drain_loop (.operation site (.clearDestination true)) (.operation site (.copyOutput false)) (reg r true) rfl
    (store w1) (w.registers (r,true)) hx
  rw [update_register w1 r true] at h1
  have h:=PTrace.join h0 h1
  simpa only [Nat.add_assoc,r,w1,emptyReg] using h
/-- Two preserving result copies and literal actual-sign pop/push leave only fixed35-role cleanup outstanding. -/
def saveTime (out:SemiprimeRationalBits.RationalWord) :Nat:=
  (5*out.numerator.magnitude.length+4)+(5*out.denominator.length+4)+1+1
/-- Actual saved output bank before the real35-role cleanup; sign prefix is already copied into the register. -/
def saved (w:Words) (site:Site) (out:SemiprimeRationalBits.RationalWord) :Words:=
  {putReg w (destination site) out with rational:=Function.update w.rational SemiprimeD1StackRationalOperation.signOutput []}
/-- Actual output copies/sign read preserve exact bytes, including negative zero and zero-width fields. -/
theorem save_run (site:Site) (w:Words) (out:SemiprimeRationalBits.RationalWord)
    (hs:w.auxiliary .copyScratch=[])
    (hn:w.rational (SemiprimeD1StackRationalOperation.aux .numeratorOutput)=out.numerator.magnitude)
    (hd:w.rational (SemiprimeD1StackRationalOperation.aux .denominatorOutput)=out.denominator)
    (hsg:w.rational SemiprimeD1StackRationalOperation.signOutput=[out.numerator.negative]) :
    Runs program (saveTime out) (.operation site (.copyOutput false)) (store (emptyReg w (destination site)))
      (.operation site (.clear 0)) (store (saved w site out)):=by
  let r:=destination site
  let w0:=emptyReg w r
  let w1:Words:={w0 with registers:=Function.update w0.registers (r,false) out.numerator.magnitude}
  let w2:Words:={w1 with registers:=Function.update w1.registers (r,true) out.denominator}
  let w3:Words:={w2 with rational:=Function.update w2.rational SemiprimeD1StackRationalOperation.signOutput []}
  have h0:=PTrace.copy_call (.output site false) (.operation site (.copyOutput false)) (.operation site (.copyOutput true)) rfl
    (store w0) out.numerator.magnitude [] hn (emptyReg_fields w r).1 hs
  change Runs _ _ _ _ _ (Function.update (store w0) (reg r false) (out.numerator.magnitude++[])) at h0
  rw [List.append_nil,update_register w0 r false] at h0
  have hz:w1.registers (r,true)=[]:=by
    change Function.update w0.registers (r,false) out.numerator.magnitude (r,true)=[]
    rw [Function.update_of_ne (by intro h;have hh:=congrArg Prod.snd h;cases hh)]
    exact (emptyReg_fields w r).2
  have h1:=PTrace.copy_call (.output site true) (.operation site (.copyOutput true)) (.operation site .sign) rfl
    (store w1) out.denominator [] hd hz hs
  change Runs _ _ _ _ _ (Function.update (store w1) (reg r true) (out.denominator++[])) at h1
  rw [List.append_nil,update_register w1 r true] at h1
  have h2:=PTrace.pop_run (.operation site .sign) (.operation site .failed)
    (.operation site (.writeSign false)) (.operation site (.writeSign true))
    (rational SemiprimeD1StackRationalOperation.signOutput) (store w2) [out.numerator.negative] rfl hsg
  rw [update_rational] at h2
  have hc:SemiprimeD1StackBytecode.choose (Label.operation site .failed)
      (Label.operation site (.writeSign false)) (Label.operation site (.writeSign true)) [out.numerator.negative].head?=
      Label.operation site (.writeSign out.numerator.negative):=by cases out.numerator.negative <;> rfl
  rw [hc] at h2
  have h3:=PTrace.push_run (.operation site (.writeSign out.numerator.negative)) (.operation site (.clear 0))
    (reg r false) out.numerator.negative (store w3) rfl
  rw [update_register w3 r false] at h3
  have hnum:w3.registers (r,false)=out.numerator.magnitude:=by
    change Function.update (Function.update w0.registers (r,false) out.numerator.magnitude) (r,true) out.denominator (r,false)=_
    rw [Function.update_of_ne (by intro h;have hh:=congrArg Prod.snd h;cases hh),Function.update_self]
  change Runs program 1 _ _ _ (store {w3 with registers:=Function.update w3.registers (r,false) (out.numerator.negative::w3.registers (r,false))}) at h3
  rw [hnum] at h3
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  have he:{w3 with registers:=Function.update w3.registers (r,false) (out.numerator.negative::out.numerator.magnitude)}=
      saved w site out:=by
    dsimp only [w3,w2,w1,w0,emptyReg,saved,putReg,r]
    congr 1
    funext k
    by_cases hks:k=(destination site,false)
    · subst k
      simp [signed]
    · by_cases hkd:k=(destination site,true)
      · subst k
        simp
      · simp [hks,hkd]
  change Runs program _ _ _ _ (store _) at h
  rw [he] at h
  exact h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationOutput
