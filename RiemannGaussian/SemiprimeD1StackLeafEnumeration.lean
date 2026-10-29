/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafAcquisition
/-! # Physical zero-assignment acquisition and full literal enumeration call -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafEnumeration
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Exact physical enumeration fields, including the actually constructed zero word. -/
theorem enumeration_project (p : PS.Values) (v : Values) (k : E.Stack) :
    data p v (enumerationStack k)=SemiprimeD1StackAssignmentLoop.data (v .zero) [] [] [] (v .catalogue) k := by
  cases k
  · exact data_get p v .zero
  · rfl
  · rfl
  · rfl
  · exact data_get p v .catalogue

/-- Actual width markers are consumed one by one to physically push the zero
assignment. No width-value or zero-word supplier occurs in the program. -/
theorem zero_run (p : PS.Values) (v : Values) (n : ℕ) (he : v .counter=[]) :
    Runs program (2*n+1) .makeZero (data p (Function.update v .counter (List.replicate n true)))
      .initializeSum (data p (Function.update v .zero (List.replicate n false++v .zero))) := by
  induction n generalizing v with
  | zero =>
    have hv : Function.update v .counter []=v := Function.update_eq_self_iff.mpr he.symm
    simp only [List.replicate_zero,Nat.mul_zero,Nat.zero_add,List.nil_append,hv,Function.update_eq_self]
    apply one_base program .makeZero .initializeSum (.pop (address .counter) .initializeSum .pushZero .pushZero) _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,data_get,he,List.head?_nil,SemiprimeD1StackBytecode.choose]
    · change Function.update (data p v) (address .counter) ((data p v (address .counter)).tail)=data p v
      rw [data_get,he,List.tail_nil,←data_update,hv]
  | succ n ih =>
    let next:=Function.update v .zero (false::v .zero)
    have h1 : Runs program 1 .makeZero
        (data p (Function.update v .counter (List.replicate (n+1) true))) .pushZero
        (data p (Function.update v .counter (List.replicate n true))) := by
      apply one_base program .makeZero .pushZero (.pop (address .counter) .initializeSum .pushZero .pushZero) _ _ rfl
      · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.replicate_succ,
          List.head?_cons,SemiprimeD1StackBytecode.choose]
      · change Function.update (data p (Function.update v .counter (List.replicate (n+1) true))) (address .counter)
          ((data p (Function.update v .counter (List.replicate (n+1) true)) (address .counter)).tail)=_
        rw [data_get,Function.update_self,List.replicate_succ,List.tail_cons,←data_update,Function.update_idem]
    have h2 : Runs program 1 .pushZero (data p (Function.update v .counter (List.replicate n true))) .makeZero
        (data p (Function.update next .counter (List.replicate n true))) := by
      apply one_base program .pushZero .makeZero (.push (address .zero) false .makeZero) _ _ rfl
      · rfl
      · change Function.update (data p (Function.update v .counter (List.replicate n true))) (address .zero)
          (false::data p (Function.update v .counter (List.replicate n true)) (address .zero))=_
        rw [data_get,Function.update_of_ne (by decide : Slot.zero ≠ .counter),←data_update]
        apply congrArg (data p)
        funext s
        cases s <;> simp [next]
    have h3:=ih next (by simpa [next] using he)
    have hc:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
    have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h3
    convert hc using 1
    · omega
    · apply congrArg (data p)
      funext s
      cases s <;> simp [next,List.replicate_succ',List.append_assoc]

/-- The original additive zero is a real literal vector-nil byte. -/
theorem initialize_sum (p : PS.Values) (v : Values) :
    Runs program 1 .initializeSum (data p v) .enumerate
      (data p (Function.update v .sum (false::v .sum))) := by
  apply one_base program .initializeSum .enumerate (.push (address .sum) false .enumerate) _ _ rfl
  · rfl
  · change Function.update (data p v) (address .sum) (false::data p v (address .sum))=_
    rw [data_get,←data_update]

/-- The fixed actual increment/body loop materializes all assignments. Its
input was acquired physically from the original binary width, not advised. -/
theorem enumeration_call (p : PS.Values) (v : Values) (M : ℕ)
    (hz : v .zero=List.replicate M false) (hc : v .catalogue=[]) :
    ∃ m ≤ 100*(M+1)*2^M+11,
      Runs program m .enumerate (data p v) .catalogueTag
        (data p (Function.update (Function.update v .zero []) .catalogue
          (vectorBits (SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false))))) := by
  obtain ⟨m,hm,hs⟩:=SemiprimeD1StackAssignmentEnumeration.zero_run M
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program enumerationStack Label.enumeration
    enumerationStack_injective E.code (E.control .bodyCall) (fun _=>rfl) .enumerate .catalogueTag rfl m
    (SemiprimeD1StackAssignmentLoop.state (E.control .bodyCall) none none (List.replicate M false) [] [] [] [] [])
    (⟨none,none,none,SemiprimeD1StackAssignmentLoop.data [] [] [] []
      (vectorBits (SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false))),[]⟩:
      SemiprimeD1StackCalls.State E.Stack E.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hs
  · constructor
    · intro k
      rw [enumeration_project]
      simp only [SemiprimeD1StackAssignmentLoop.state,hz,hc]
    · intro k hk; rfl
  · constructor
    · intro k
      rw [enumeration_project]
      cases k <;> simp [SemiprimeD1StackAssignmentLoop.data]
    · intro k hk
      have hz : k ≠ address .zero := fun he=>hk .word he.symm
      have hc : k ≠ address .catalogue := fun he=>hk .output he.symm
      rw [data_update,data_update]
      simp only [Function.update_of_ne hz,Function.update_of_ne hc]

end RiemannGaussian.SemiprimeD1StackLeafEnumeration
