/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridOperation
/-! # Exact physical rational register/cache updates used by actual grid power and row loops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRegisters
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
/-- Physical signed and unsigned destination fields are exactly the actual word's bytes. -/
theorem putReg_fields (w:Words) (r:Reg) (word:SemiprimeRationalBits.RationalWord) :
    (putReg w r word).registers (r,false)=signed word ∧
    (putReg w r word).registers (r,true)=word.denominator:=by
  simp only [putReg,Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.false_eq_true,
    Bool.true_eq_false,ite_true,ite_false]
/-- All other register words remain literally unchanged. -/
theorem putReg_other (w:Words) (r q:Reg) (word:SemiprimeRationalBits.RationalWord) (den:Bool) (hne:q≠r) :
    (putReg w r word).registers (q,den)=w.registers (q,den):=by
  simp only [putReg,Function.update_apply,Prod.mk.injEq,hne,false_and,ite_false]
/-- Proof-side interpretation of the actual saved two-word cache recovers the precise rational bytes. -/
theorem getReg_putReg (w:Words) (r:Reg) (word:SemiprimeRationalBits.RationalWord) :getReg (putReg w r word) r=word:=by
  unfold getReg
  rw [(putReg_fields w r word).1,(putReg_fields w r word).2]
  rfl
/-- Replacing the same two actual register fields twice preserves only the latest actual word. -/
theorem putReg_idem (w:Words) (r:Reg) (old word:SemiprimeRationalBits.RationalWord) :
    putReg (putReg w r old) r word=putReg w r word:=by
  dsimp only [putReg]
  congr 1
  funext k
  by_cases h0:k=(r,false)
  · subst k;simp [signed]
  · by_cases h1:k=(r,true)
    · subst k;simp
    · simp [h0,h1]
/-- Cache writes preserve the actual acquired width and all rational arithmetic fields. -/
theorem putReg_rational (w:Words) (r:Reg) (word:SemiprimeRationalBits.RationalWord) :(putReg w r word).rational=w.rational:=rfl
/-- Cache writes preserve every actual source/counter/copy/framing field. -/
theorem putReg_auxiliary (w:Words) (r:Reg) (word:SemiprimeRationalBits.RationalWord) :(putReg w r word).auxiliary=w.auxiliary:=rfl
/-- A physical counter update commutes with rational-cache replacement because their literal roles are disjoint. -/
theorem putReg_aux_update (w:Words) (r:Reg) (word:SemiprimeRationalBits.RationalWord) (k:Aux) (bits:List Bool) :
    {putReg w r word with auxiliary:=Function.update w.auxiliary k bits}=
      putReg {w with auxiliary:=Function.update w.auxiliary k bits} r word:=rfl
/-- Every fixed power's actual base survives initialization/replacement of its distinct accumulator register. -/
theorem power_base_ne_destination (part:PowerSite) :powerBase part≠powerDestination part:=by cases part <;> decide
/-- The actual base signed/denominator words are unaffected by its power accumulator updates. -/
theorem power_base_retained (w:Words) (part:PowerSite) (word:SemiprimeRationalBits.RationalWord) (den:Bool) :
    (putReg w (powerDestination part) word).registers (powerBase part,den)=w.registers (powerBase part,den):=
  putReg_other w _ _ word den (power_base_ne_destination part)
end RiemannGaussian.SemiprimeD1StackRecoveryGridRegisters
