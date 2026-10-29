/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafAddition
/-! # Actual catalogue reads, validity pops, sum copies and assignment cleanup -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafMoves
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)

/-- Real drain loop on an outer physical buffer. -/
theorem drain (p : PS.Values) (v : Values) (s : Slot) (pc next : Label)
    (hcode : program pc=.base (.pop (address s) next pc pc)) (he : v s=[]) (word : List Bool) :
    Runs program (word.length+1) pc (data p (Function.update v s word)) next (data p v) := by
  induction word with
  | nil =>
    have hd : Function.update v s []=v := Function.update_eq_self_iff.mpr he.symm
    rw [hd]
    apply one_base program pc next (.pop (address s) next pc pc) _ _ hcode
    · simp only [SemiprimeD1StackBytecode.execute,data_get,he,List.head?_nil,SemiprimeD1StackBytecode.choose]
    · change Function.update (data p v) (address s) ((data p v (address s)).tail)=data p v
      rw [data_get,he,List.tail_nil,←data_update,hd]
  | cons bit word ih =>
    have h1 : Runs program 1 pc (data p (Function.update v s (bit::word))) pc (data p (Function.update v s word)) := by
      apply one_base program pc pc (.pop (address s) next pc pc) _ _ hcode
      · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons]
        cases bit <;> rfl
      · change Function.update (data p (Function.update v s (bit::word))) (address s)
          ((data p (Function.update v s (bit::word)) (address s)).tail)=_
        rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h1 ih
    simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

/-- Current sum-result bytes are physically cleared, not discarded in a projection. -/
theorem clear_sum (p : PS.Values) (v : Values) :
    Runs program ((v .sumResult).length+1) .clearSumResult (data p v) .clearAssignment
      (data p (Function.update v .sumResult [])) := by
  have h:=drain p (Function.update v .sumResult []) .sumResult .clearSumResult .clearAssignment rfl (by simp) (v .sumResult)
  simpa only [Function.update_idem,Function.update_eq_self] using h

/-- Actual selected assignment bytes are physically cleared after use. -/
theorem clear_assignment (p : PS.Values) (v : Values) :
    Runs program ((p .assignment).length+1) .clearAssignment (data p v) .catalogueTag
      (data (Function.update p .assignment []) v) := by
  let base:=Function.update p .assignment []
  have he : base .assignment=[] := by simp [base]
  have h : ∀word, Runs program (word.length+1) .clearAssignment
      (data (Function.update base .assignment word) v) .catalogueTag (data base v) := by
    intro word
    induction word with
    | nil =>
      have hd : Function.update base .assignment []=base := Function.update_eq_self_iff.mpr he.symm
      rw [hd]
      apply one_base program .clearAssignment .catalogueTag
        (.pop (productStack (PS.address .assignment)) .catalogueTag .clearAssignment .clearAssignment) _ _ rfl
      · simp only [SemiprimeD1StackBytecode.execute,data_product_get,he,List.head?_nil,SemiprimeD1StackBytecode.choose]
      · change Function.update (data base v) (productStack (PS.address .assignment))
          ((data base v (productStack (PS.address .assignment))).tail)=_
        rw [data_product_get,he,List.tail_nil,←data_product_update,hd]
    | cons bit word ih =>
      have h1 : Runs program 1 .clearAssignment (data (Function.update base .assignment (bit::word)) v)
          .clearAssignment (data (Function.update base .assignment word) v) := by
        apply one_base program .clearAssignment .clearAssignment
          (.pop (productStack (PS.address .assignment)) .catalogueTag .clearAssignment .clearAssignment) _ _ rfl
        · simp only [SemiprimeD1StackBytecode.execute,data_product_get,Function.update_self,List.head?_cons]
          cases bit <;> rfl
        · change Function.update (data (Function.update base .assignment (bit::word)) v)
            (productStack (PS.address .assignment))
            ((data (Function.update base .assignment (bit::word)) v (productStack (PS.address .assignment))).tail)=_
          rw [data_product_get,Function.update_self,List.tail_cons,←data_product_update,Function.update_idem]
      have hh:=runs_trans program _ _ _ _ _ _ _ _ h1 ih
      simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
  simpa only [base,Function.update_idem,Function.update_eq_self] using h (p .assignment)

/-- Real retained-source sum copy; the current accumulator is a reached operand. -/
theorem copy_sum (p : PS.Values) (v : Values) :
    Runs program (5*(v .sumResult).length+4) .copySum (data p v) .clearSumResult
      (data p (Function.update v .sum (v .sumResult++v .sum))) := by
  apply SemiprimeD1StackProcedureTrace.included_call program (copyStack true) (Label.copy true)
    (copyStack_injective true) SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl) .copySum .clearSumResult rfl _
    (SemiprimeD1StackCopy.state 0 none (v .sumResult) (v .sum) [])
    (SemiprimeD1StackCopy.done (v .sumResult) (v .sumResult++v .sum))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words (v .sumResult) (v .sum) none
  · constructor
    · intro k
      fin_cases k
      · exact data_get p v .sumResult
      · exact data_get p v .sum
      · rfl
    · intro k hk; rfl
  · constructor
    · intro k
      fin_cases k
      · change data p (Function.update v .sum (v .sumResult++v .sum)) (address .sumResult)=v .sumResult
        rw [data_get,Function.update_of_ne (by decide : Slot.sumResult ≠ .sum)]
      · exact data_get p (Function.update v .sum (v .sumResult++v .sum)) .sum
      · rfl
    · intro k hk
      have hn : k ≠ address .sum := fun he=>hk 1 he.symm
      rw [data_update]
      exact Function.update_of_ne hn _ _

/-- Actual catalogue field parsing directly acquires the next assignment. -/
theorem field_call (p : PS.Values) (v : Values) (word tail : List Bool)
    (hr : v .catalogue=SemiprimeSourceHistogramKeyBits.frame word tail)
    (ha : p .assignment=[]) (hv : v .valid=[]) :
    Runs program (8*word.length+7) .parse (data p v) .parsed
      (data (Function.update p .assignment word)
        (Function.update (Function.update v .catalogue tail) .valid [true])) := by
  apply SemiprimeD1StackProcedureTrace.included_call program fieldStack Label.field fieldStack_injective
    F.code (F.active .tagPop (none,false)) (fun _=>rfl) .parse .parsed rfl (8*word.length+6)
    (SemiprimeD1TensorTapeFieldBytecode.initial (SemiprimeSourceHistogramKeyBits.frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      rw [field_project]
      fin_cases k <;> simp [SemiprimeD1TensorTapeFieldBytecode.initial,
        SemiprimeD1TensorTapeFieldMachine.contents,hr,ha,hv]
    · intro k hk; rfl
  · constructor
    · intro k
      rw [field_project]
      fin_cases k <;> simp [SemiprimeD1TensorTapeFieldMachine.contents]
    · intro k hk
      have hc : k ≠ address .catalogue := fun he=>hk (.inl .input) he.symm
      have ha : k ≠ productStack (PS.address .assignment) := fun he=>hk (.inl .output) he.symm
      have hv : k ≠ address .valid := fun he=>hk (.inr ()) he.symm
      rw [data_update,data_update,data_product_update]
      simp only [Function.update_of_ne hc,Function.update_of_ne ha,Function.update_of_ne hv]

/-- The actual acquired field-validity bit controls the next real call. -/
theorem field_flag (p : PS.Values) (v : Values) :
    Runs program 1 .parsed (data p (Function.update v .valid [true])) .callProduct
      (data p (Function.update v .valid [])) := by
  apply one_base program .parsed .callProduct (.pop (address .valid) .abort .abort .callProduct) _ _ rfl
  · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons,
      SemiprimeD1StackBytecode.choose]
  · change Function.update (data p (Function.update v .valid [true])) (address .valid)
      ((data p (Function.update v .valid [true]) (address .valid)).tail)=_
    rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]

end RiemannGaussian.SemiprimeD1StackLeafMoves
