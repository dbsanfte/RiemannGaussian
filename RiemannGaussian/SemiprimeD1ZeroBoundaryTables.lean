/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BooleanTreeStreamOriginal
import RiemannGaussian.SemiprimeD1StackPublicZeroOriginal
import RiemannGaussian.SemiprimeD1BooleanRootTablesOriginal
/-! # One physical true bit and EOF acquire the entire original zero boundary
All tables and predicates below are mathematical specifications. The source
will supply only literal true and an actually acquired physical depth word.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1ZeroBoundaryTables
open SemiprimeD1TensorTables SemiprimeBitArithmetic
namespace S
export SemiprimeD1BooleanTreeStream (table bytes words)
end S
/-- EOF produces a genuinely zero tensor at every remaining depth. -/
theorem nil_entry (n : ℕ) (input : Fin n→Bool) : valueAt (S.table n []) input=S.words false := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    cases h:input 0 <;> simp only [S.table,List.drop_nil,valueAt,h,Bool.false_eq_true,ite_false,ite_true] <;>
      exact ih (fun j=>input j.succ)
/-- There is at least one leaf at every physical depth, including depth zero. -/
theorem singleton_drop (n : ℕ) : ([true]:List Bool).drop (2^n)=[] := by
  apply List.drop_eq_nil_of_le
  have h:0<(2:ℕ)^n:=by positivity
  simp only [List.length_cons,List.length_nil]
  omega
/-- The one true stream entry accepts EXACTLY the original zero word, in the
original first-port-outermost false-first order; every later entry is EOF-false. -/
theorem zero_entry (n : ℕ) (input : Fin n→Bool) :
    valueAt (S.table n [true]) input=S.words (decide (bitValue (List.ofFn input)=0)) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    cases h:input 0
    · simp only [S.table,valueAt,h,Bool.false_eq_true,ite_false]
      rw [ih]
      congr 1
      apply decide_eq_decide.mpr
      simp only [List.ofFn_succ,bitValue,h,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add]
      omega
    · simp only [S.table,valueAt,h,ite_true,singleton_drop]
      rw [nil_entry]
      have hz : ¬bitValue (List.ofFn input)=0 := by
        simp only [List.ofFn_succ,bitValue,h,bitNat,ite_true]
        omega
      simp only [hz,decide_false]
/-- Original zero word means all original Boolean coordinates are false. -/
theorem zero_iff (n : ℕ) (input : Fin n→Bool) :
    bitValue (List.ofFn input)=0 ↔ ∀j,input j=false := by
  induction n with
  | zero=>simp [bitValue]
  | succ n ih=>
    rw [Fin.forall_fin_succ]
    cases h:input 0 <;> simp [List.ofFn_succ,bitValue,bitNat,h,←ih (fun j=>input j.succ)]
/-- Finite literal table entries uniquely determine the complete typed tree. -/
theorem table_ext {n : ℕ} (a b : Table n) (h : ∀input,valueAt a input=valueAt b input) : a=b := by
  induction a with
  | leaf ws=>
    cases b with
    | leaf vs=>exact congrArg Table.leaf (h (fun j=>Fin.elim0 j))
  | @fork n lo hi il ih=>
    cases b with
    | fork left right=>
      apply congrArg₂ Table.fork
      · apply il
        intro input
        simpa only [valueAt,Fin.cons_zero,Bool.false_eq_true,ite_false,Fin.cons_succ] using h (Fin.cons false input)
      · apply ih
        intro input
        simpa only [valueAt,Fin.cons_zero,ite_true,Fin.cons_succ] using h (Fin.cons true input)
/-- Whole old materialization is read in its exact original port order. -/
theorem build_entry (n : ℕ) (producer : List Bool→SemiprimeD1JetRingBits.Run) (input : Fin n→Bool) :
    valueAt (build n producer).table input=(producer (List.ofFn input)).words := by
  have h:=build_value n producer (List.ofFn input) (by simp)
  rw [lookup_value _ _ (by simp)] at h
  simpa only [List.getElem_ofFn] using h
/-- The old original initial-carry verdict is precisely unsigned word zero,
for EVERY original ordered finite assignment, including all high-zero padding. -/
theorem initial_zero (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (bitValue bits))+1)→Bool) :
    (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN .carryInitial input).accepted=
      decide (bitValue (List.ofFn input)=0) := by
  have hz:=SemiprimeD1StackPublicZeroOriginal.initial_original bits hc hN input
  change decide (bitValue (SemiprimeD1StackPublicZeroExecution.word bits (List.ofFn input))=0)=_ at hz
  rw [SemiprimeD1StackPublicZeroOriginal.word_full bits (List.ofFn input) (by
    rw [List.length_ofFn,SemiprimeD1StackPublicZeroOriginal.public_width bits hc])] at hz
  exact hz.symm
/-- The old original terminal-carry verdict has the SAME zero-word meaning. -/
theorem terminal_zero (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (bitValue bits))+1)→Bool) :
    (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN .carryTerminal input).accepted=
      decide (bitValue (List.ofFn input)=0) := by
  have hz:=SemiprimeD1StackPublicZeroOriginal.terminal_original bits hc hN input
  change decide (bitValue (SemiprimeD1StackPublicZeroExecution.word bits (List.ofFn input))=0)=_ at hz
  rw [SemiprimeD1StackPublicZeroOriginal.word_full bits (List.ofFn input) (by
    rw [List.length_ofFn,SemiprimeD1StackPublicZeroOriginal.public_width bits hc])] at hz
  exact hz.symm
/-- ENTIRE original initial-carry tensor, exact false-first/port-outermost order;
the actual entry source is still only ONE true bit and physical EOF. -/
theorem initial_reference (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    S.table (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (bitValue bits))+1) [true]=
      SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl .carryInitial) := by
  apply table_ext
  intro input
  rw [zero_entry]
  dsimp only [SemiprimeD1BooleanRootTablesOriginal.reference,SemiprimeMacroGraph.subdividedArity,SemiprimeMacroGraph.arity]
  rw [build_entry]
  have hget : (fun j=>((List.ofFn input).toArray[j.val]?).getD false)=input := by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  change S.words (decide (bitValue (List.ofFn input)=0))=
    S.words (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN .carryInitial
      (fun j=>((List.ofFn input).toArray[j.val]?).getD false)).accepted
  have he:=congrArg (fun f=>S.words (SemiprimeMacroEntryBitCheck.publicBitEntry
    (bitValue bits) hN .carryInitial f).accepted) hget
  exact (he.trans (congrArg S.words (initial_zero bits hc hN input))).symm
/-- ENTIRE original terminal-carry tensor is the SAME acquired tree. -/
theorem terminal_reference (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    S.table (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (bitValue bits))+1) [true]=
      SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl .carryTerminal) := by
  apply table_ext
  intro input
  rw [zero_entry]
  dsimp only [SemiprimeD1BooleanRootTablesOriginal.reference,SemiprimeMacroGraph.subdividedArity,SemiprimeMacroGraph.arity]
  rw [build_entry]
  have hget : (fun j=>((List.ofFn input).toArray[j.val]?).getD false)=input := by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  change S.words (decide (bitValue (List.ofFn input)=0))=
    S.words (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN .carryTerminal
      (fun j=>((List.ofFn input).toArray[j.val]?).getD false)).accepted
  have he:=congrArg (fun f=>S.words (SemiprimeMacroEntryBitCheck.publicBitEntry
    (bitValue bits) hN .carryTerminal f).accepted) hget
  exact (he.trans (congrArg S.words (terminal_zero bits hc hN input))).symm
/-- The ACTUAL integral coefficient of EACH boundary entry is its original
zero indicator, BEFORE any contraction/product or precision reduction. -/
theorem literal_entry_coefficient (n : ℕ) (input : Fin n→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (S.table n [true]) input))=
      if bitValue (List.ofFn input)=0 then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),zero_entry]
  by_cases hz:bitValue (List.ofFn input)=0 <;>
    simp [S.words,hz,bitValue,bitNat]

end RiemannGaussian.SemiprimeD1ZeroBoundaryTables
