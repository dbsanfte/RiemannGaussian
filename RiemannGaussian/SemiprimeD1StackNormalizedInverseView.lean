/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverse
/-! # Whole physical normalized-inverse bank views and exact rational-cache bytes
All getters below are proof specifications of physical words, never instructions
or suppliers in the finite program. Actual fields are acquired by real parsers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverse
/-- Full58-word view; no caller source, output, helper or shadow is omitted. -/
structure Words where
  /-- All36 actual normalized-operation words. -/
  rational : R.Stack→List Bool:=fun _=>[]
  /-- All eight actual signed/denominator cache fields. -/
  registers : Reg×Bool→List Bool:=fun _=>[]
  /-- Every one of14 original/controller/prefix/output words. -/
  auxiliary : Aux→List Bool:=fun _=>[]
/-- Exact complete physical source bank. -/
def store (w : Words) : Stack→List Bool := bank w.rational w.registers w.auxiliary
/-- A clean R36 bank holds only the actually retained W template. -/
def emptyRational (width : List Bool) : R.Stack→List Bool := fun k=>if k=R.aux .template then width else []
/-- Honest three-input prepared source state, with no numeric size or coefficient answers. -/
def originals (array q width : List Bool) : Words := {rational:=emptyRational width,auxiliary:=originalAux array q}
/-- Proof-side view of an actual signed cache and its actual binary denominator. -/
def getReg (w : Words) (r : Reg) : SemiprimeRationalBits.RationalWord :=
  ⟨⟨(w.registers (r,false)).head?.getD false,(w.registers (r,false)).tail⟩,w.registers (r,true)⟩
/-- Exact two-field cache write corresponding to actual signed/denominator bytes. -/
def putReg (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) : Words :=
  {w with registers:=Function.update (Function.update w.registers (r,false) (signed word)) (r,true) word.denominator}
/-- Exact actual cache drain. -/
def emptyReg (w : Words) (r : Reg) : Words :=
  {w with registers:=Function.update (Function.update w.registers (r,false) []) (r,true) []}
/-- One actual R36 physical update leaves all coefficient and controller words unchanged. -/
theorem update_rational (w : Words) (k : R.Stack) (xs : List Bool) :
    Function.update (store w) (rational k) xs=store {w with rational:=Function.update w.rational k xs} :=
  Sum.update_elim_inl
/-- One actual coefficient-field update leaves all other physical banks unchanged. -/
theorem update_register (w : Words) (r : Reg) (den : Bool) (xs : List Bool) :
    Function.update (store w) (reg r den) xs=store {w with registers:=Function.update w.registers (r,den) xs} := by
  dsimp only [store,bank,reg]
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- One actual controller update retains every source and coefficient word outside that role. -/
theorem update_aux (w : Words) (k : Aux) (xs : List Bool) :
    Function.update (store w) (aux k) xs=store {w with auxiliary:=Function.update w.auxiliary k xs} := by
  dsimp only [store,bank,aux]
  rw [Sum.update_elim_inr,Sum.update_elim_inr]
/-- Actual acquired cached words always retain their sign prefix, including W=0. -/
theorem putReg_fields (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) :
    (putReg w r word).registers (r,false)=signed word ∧ (putReg w r word).registers (r,true)=word.denominator := by
  simp only [putReg,Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.false_eq_true,
    Bool.true_eq_false,ite_false,ite_true]
/-- A physically acquired word has exactly the same decoded signed/cache fields. -/
theorem getReg_put (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) : getReg (putReg w r word) r=word := by
  rw [getReg,(putReg_fields w r word).1,(putReg_fields w r word).2]
  cases word
  rfl
/-- Actual cache clearing empties BOTH data fields. -/
theorem emptyReg_fields (w : Words) (r : Reg) :
    (emptyReg w r).registers (r,false)=[] ∧ (emptyReg w r).registers (r,true)=[] := by
  simp only [emptyReg,Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.false_eq_true,
    Bool.true_eq_false,ite_false,ite_true]
/-- Other signed/denominator caches are retained byte for byte by this actual cache write. -/
theorem putReg_other (w : Words) (r other : Reg) (word : SemiprimeRationalBits.RationalWord)
    (den : Bool) (h : other≠r) : (putReg w r word).registers (other,den)=w.registers (other,den) := by
  have h0 : (other,den)≠(r,true) := by intro he;exact h (congrArg Prod.fst he)
  have h1 : (other,den)≠(r,false) := by intro he;exact h (congrArg Prod.fst he)
  dsimp only [putReg]
  rw [Function.update_of_ne h0,Function.update_of_ne h1]
/-- A nonempty actual signed field equals its full sign-plus-magnitude word specification. -/
theorem signed_getReg (w : Words) (r : Reg) (h : w.registers (r,false)≠[]) :
    w.registers (r,false)=signed (getReg w r) := by
  cases he:w.registers (r,false) with
  | nil=>exact (h he).elim
  | cons b xs=>simp only [getReg,signed,he,List.head?_cons,Option.getD_some,List.tail_cons]
/-- Physical original/ready source views agree on every one of58 tapes. -/
theorem initial_store (array q width : List Bool) : (initial array q width).data=store (originals array q width) := rfl
/-- Literal framed rational-row width includes both fields, both delimiters and the TRUE tag. -/
theorem row_length (word : SemiprimeRationalBits.RationalWord) (tail : List Bool) :
    (row word tail).length=2*(signed word).length+2*word.denominator.length+tail.length+3 := by
  simp only [row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Every physical typed array has its ONE final FALSE cell, even for zero coefficients. -/
theorem tape_length_pos (words : List SemiprimeRationalBits.RationalWord) : 0<(tape words).length := by
  induction words with
  | nil=>decide
  | cons word words ih=>
    change 0<(row word (tape words)).length
    rw [row_length]
    omega
/-- Proof-side total mass counts all58 physical roles. -/
def mass (w : Words) : ℕ := ∑k : Stack,(store w k).length
end RiemannGaussian.SemiprimeD1StackNormalizedInverseView
