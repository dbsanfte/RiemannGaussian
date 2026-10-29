/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSite
/-! # Real literal/copy acquisition of all affine convolution factor words -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineFactor
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join copy_call push_run)
end T
/-- The finite factor class is exactly the original two-coefficient array with zero extension. -/
def value (part:Part) (c:SemiprimeRationalBits.RationalWord):SemiprimeRationalBits.RationalWord:=
  match part with | .unit=>SemiprimeJetBits.oneWord | .slope=>c | .zero=>SemiprimeRationalBits.zeroWord
/-- Own literal/copy clock of the physically chosen factor branch. -/
def runBound (part:Part) (c:SemiprimeRationalBits.RationalWord):Nat:=
  match part with | .unit=>3 | .slope=>(5*(signed c).length+4)+(5*c.denominator.length+4) | .zero=>2
/-- Literal ZERO uses actual Boolean pushes and preserves every other physical word. -/
theorem zero_run (w:Words) (hn:w.registers (.denBase,false)=[]) (hd:w.registers (.denBase,true)=[]):
    Runs program 2 (.local (.factor .zero)) (bank w) (.local (.multiply .zero))
      (bank (putReg w .denBase SemiprimeRationalBits.zeroWord)):=by
  let w1:Words:={w with registers:=Function.update w.registers (.denBase,true) [true]}
  have h0:=T.push_run (.local (.factor .zero)) (.local (.factorDen .zero)) (reg .denBase true) true (bank w) rfl
  change Runs program _ _ _ _ (Function.update (bank w) (reg .denBase true) (true::w.registers (.denBase,true))) at h0
  rw [hd,update_register] at h0
  change Runs program _ _ _ _ (bank w1) at h0
  have h1:=T.push_run (.local (.factorDen .zero)) (.local (.multiply .zero)) (reg .denBase false) false (bank w1) rfl
  have hx:w1.registers (.denBase,false)=[]:=by simp [w1,hn]
  change Runs program _ _ _ _ (Function.update (bank w1) (reg .denBase false) (false::w1.registers (.denBase,false))) at h1
  rw [hx,update_register] at h1
  have he:{w1 with registers:=Function.update w1.registers (.denBase,false) [false]}=
      putReg w .denBase SemiprimeRationalBits.zeroWord:=by
    dsimp only [w1,putReg]
    congr 1
    congr 1
    funext slot
    rcases slot with ⟨r,b⟩
    cases r <;> cases b <;> simp [signed,SemiprimeRationalBits.zeroWord]
  rw [he] at h1
  exact T.join h0 h1
/-- Literal UNIT uses actual Boolean pushes and preserves every other physical word. -/
theorem unit_run (w:Words) (hn:w.registers (.denBase,false)=[]) (hd:w.registers (.denBase,true)=[]):
    Runs program 3 (.local (.factor .unit)) (bank w) (.local (.multiply .unit))
      (bank (putReg w .denBase SemiprimeJetBits.oneWord)):=by
  let w1:Words:={w with registers:=Function.update w.registers (.denBase,true) [true]}
  have h0:=T.push_run (.local (.factor .unit)) (.local (.factorDen .unit)) (reg .denBase true) true (bank w) rfl
  change Runs program _ _ _ _ (Function.update (bank w) (reg .denBase true) (true::w.registers (.denBase,true))) at h0
  rw [hd,update_register] at h0
  change Runs program _ _ _ _ (bank w1) at h0
  let w2:Words:={w1 with registers:=Function.update w1.registers (.denBase,false) [true]}
  have h1:=T.push_run (.local (.factorDen .unit)) (.local .factorSign) (reg .denBase false) true (bank w1) rfl
  have hx:w1.registers (.denBase,false)=[]:=by simp [w1,hn]
  change Runs program _ _ _ _ (Function.update (bank w1) (reg .denBase false) (true::w1.registers (.denBase,false))) at h1
  rw [hx,update_register] at h1
  change Runs program _ _ _ _ (bank w2) at h1
  have h2:=T.push_run (.local .factorSign) (.local (.multiply .unit)) (reg .denBase false) false (bank w2) rfl
  change Runs program _ _ _ _ (Function.update (bank w2) (reg .denBase false) [false,true]) at h2
  rw [update_register] at h2
  have he:{w2 with registers:=Function.update w2.registers (.denBase,false) [false,true]}=
      putReg w .denBase SemiprimeJetBits.oneWord:=by
    dsimp only [w2,w1,putReg]
    congr 1
    congr 1
    funext slot
    rcases slot with ⟨r,b⟩
    cases r <;> cases b <;> simp [signed,SemiprimeJetBits.oneWord]
  rw [he] at h2
  exact T.join (T.join h0 h1) h2
/-- The slope factor is acquired by two actual preserving copies from the parsed original slope. -/
theorem slope_run (w:Words) (c:SemiprimeRationalBits.RationalWord)
    (hn:w.registers (.denBase,false)=[]) (hd:w.registers (.denBase,true)=[])
    (hc:w.auxiliary .copyScratch=[])
    (hs:w.registers (.slope,false)=signed c) (ht:w.registers (.slope,true)=c.denominator):
    Runs program (runBound .slope c) (.local (.factor .slope)) (bank w) (.local (.multiply .slope))
      (bank (putReg w .denBase c)):=by
  let w1:Words:={w with registers:=Function.update w.registers (.denBase,false) (signed c)}
  have h0:=T.copy_call (.slope false) (.local (.factor .slope)) (.local (.slopeFactor true)) rfl
    (bank w) (signed c) [] hs hn hc
  change Runs program _ _ _ _ (Function.update (bank w) (reg .denBase false) (signed c++[])) at h0
  rw [List.append_nil,update_register] at h0
  change Runs program _ _ _ _ (bank w1) at h0
  have hden:w1.registers (.denBase,true)=[]:=by simp [w1,hd]
  have hsrc:w1.registers (.slope,true)=c.denominator:=by simp [w1,ht]
  have h1:=T.copy_call (.slope true) (.local (.slopeFactor true)) (.local (.multiply .slope)) rfl
    (bank w1) c.denominator [] hsrc hden hc
  change Runs program _ _ _ _ (Function.update (bank w1) (reg .denBase true) (c.denominator++[])) at h1
  rw [List.append_nil,update_register] at h1
  exact T.join h0 h1
/-- All three branches are driven by fixed finite control and actual input bytes only. -/
theorem factor_run (part:Part) (w:Words) (c:SemiprimeRationalBits.RationalWord)
    (hn:w.registers (.denBase,false)=[]) (hd:w.registers (.denBase,true)=[])
    (hc:w.auxiliary .copyScratch=[])
    (hs:w.registers (.slope,false)=signed c) (ht:w.registers (.slope,true)=c.denominator):
    Runs program (runBound part c) (.local (.factor part)) (bank w) (.local (.multiply part))
      (bank (putReg w .denBase (value part c))):=by
  cases part with
  | unit=>exact unit_run w hn hd
  | slope=>exact slope_run w c hn hd hc hs ht
  | zero=>exact zero_run w hn hd
end RiemannGaussian.SemiprimeD1StackRecoveryAffineFactor
