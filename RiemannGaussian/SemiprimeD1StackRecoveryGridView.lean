/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridInventory
/-! # Complete104-word physical source/cache boundary views
All functions here describe actual finite stores for trace proofs; no function,
word, natural or evaluator occurs in the finite runtime control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridView
open SemiprimeD1StackRecoveryGrid
/-- Every allocated physical source/cache/helper field, partitioned only for proof-side notation. -/
structure Words where
  /-- Complete actual rational word bank. -/
  rational:R.Stack→List Bool:=fun _=>[]
  /-- Complete actual geometry word bank. -/
  geometry:G.Aux→List Bool:=fun _=>[]
  /-- Complete actual division word bank. -/
  division:D.Stack→List Bool:=fun _=>[]
  /-- Complete actual product word bank. -/
  product:P.Stack→List Bool:=fun _=>[]
  /-- Complete actual registers word bank. -/
  registers:Reg×Bool→List Bool:=fun _=>[]
  /-- Complete actual auxiliary word bank. -/
  auxiliary:Aux→List Bool:=fun _=>[]
/-- Exact complete physical store; shared ripple fields are represented once in rational36. -/
def bank (w:Words) :Stack→List Bool:=
  Sum.elim w.rational (Sum.elim w.geometry (Sum.elim w.division (Sum.elim w.product (Sum.elim w.registers w.auxiliary))))
/-- One real rational bank write retains every other physical word. -/
theorem update_rational (w:Words) (k:R.Stack) (xs:List Bool) :
    Function.update (bank w) (rationalStack k) xs=bank {w with rational:=Function.update w.rational k xs}:=by
  funext p
  rcases p with p|p
  · simp only [bank,rationalStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- One real geometry bank write retains every other physical word. -/
theorem update_geometry (w:Words) (k:G.Aux) (xs:List Bool) :
    Function.update (bank w) (geometryAux k) xs=bank {w with geometry:=Function.update w.geometry k xs}:=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · simp only [bank,geometryAux,Function.update_apply,Sum.elim_inl,Sum.inl.injEq,Sum.elim_inr,Sum.inr.injEq]
    · rfl
/-- One real division bank write retains every other physical word. -/
theorem update_division (w:Words) (k:D.Stack) (xs:List Bool) :
    Function.update (bank w) (divisionStack k) xs=bank {w with division:=Function.update w.division k xs}:=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · simp only [bank,divisionStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq,Sum.elim_inr,Sum.inr.injEq]
      · rfl
/-- One real product bank write retains every other physical word. -/
theorem update_product (w:Words) (k:P.Stack) (xs:List Bool) :
    Function.update (bank w) (productStack k) xs=bank {w with product:=Function.update w.product k xs}:=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · simp only [bank,productStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq,Sum.elim_inr,Sum.inr.injEq]
        · rfl
/-- One real registers bank write retains every other physical word. -/
theorem update_registers (w:Words) (k:Reg×Bool) (xs:List Bool) :
    Function.update (bank w) (reg k.1 k.2) xs=bank {w with registers:=Function.update w.registers k xs}:=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · rfl
        · rcases p with p|p
          · simp only [bank,reg,Function.update_apply,Sum.elim_inl,Sum.inl.injEq,Sum.elim_inr,Sum.inr.injEq]
          · rfl
/-- One real auxiliary bank write retains every other physical word. -/
theorem update_auxiliary (w:Words) (k:Aux) (xs:List Bool) :
    Function.update (bank w) (aux k) xs=bank {w with auxiliary:=Function.update w.auxiliary k xs}:=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · rfl
        · rcases p with p|p
          · rfl
          · simp only [bank,aux,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- Literal four original metadata/index words; all actual helper fields are empty. -/
def originalAux (a M u t:List Bool) :Aux→List Bool
  | .originalA=>a | .originalM=>M | .originalU=>u | .originalT=>t | _=>[]
/-- Honest original five-tape physical bank, retaining actual W cells directly at R36.template. -/
def originals (a M u t width:List Bool) :Words:=
  {rational:=Function.update (fun _=>[]) (SemiprimeD1StackRationalOperation.aux .template) width,auxiliary:=originalAux a M u t}
/-- Exact signed binary bytes in every actual rational register. -/
def signed (word:SemiprimeRationalBits.RationalWord) :List Bool:=word.numerator.negative::word.numerator.magnitude
/-- Proof-side rational register write corresponding to paid signed/denominator field writes. -/
def putReg (w:Words) (r:Reg) (word:SemiprimeRationalBits.RationalWord) :Words:=
  {w with registers:=Function.update (Function.update w.registers (r,false) (signed word)) (r,true) word.denominator}
/-- Proof-side interpretation reads only the actual register words, never a runtime getter. -/
def getReg (w:Words) (r:Reg) :SemiprimeRationalBits.RationalWord:=
  ⟨⟨(w.registers (r,false)).head?.getD false,(w.registers (r,false)).tail⟩,w.registers (r,true)⟩
/-- Literal two-field physical slope row: vector tag, signed numerator field, denominator field, then unchanged tail. -/
def slopeRow (word:SemiprimeRationalBits.RationalWord) (tail:List Bool) :List Bool:=
  true::SemiprimeSourceHistogramKeyBits.frame (signed word) (SemiprimeSourceHistogramKeyBits.frame word.denominator tail)
/-- Exact chronological slope vector bytes; rational words remain binary, with every sign and delimiter retained. -/
def slopeTape (words:List SemiprimeRationalBits.RationalWord) :List Bool:=words.foldr slopeRow [false]
end RiemannGaussian.SemiprimeD1StackRecoveryGridView
