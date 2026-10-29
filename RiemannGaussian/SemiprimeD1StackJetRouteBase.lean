/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteStep
/-! # Actual empty-record routing and zero-default rejection -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteBase
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls SemiprimeD1StackJetRouteStep
open SemiprimeD1StackJetRouteFailure (compose)
open SemiprimeD1StackUnaryDivmod (unary unary_succ)
local notation "ctl" => SemiprimeD1StackJetRoute.control

/-- Clean physical result bank: one validity bit and the retained sum only on success. -/
def answer (valid : Bool) (result : List Bool) : Stack→List Bool :=
  bank [] [] [] [] (if valid then result else []) [] [] [] [] [] [] [] [valid]

/-- Empty suffix records still perform the two physical zero tests. -/
theorem base (i j : ℕ) (result : List Bool) :
    ∃m≤400*(i+j+result.length+1),Trace.Runs code m (ctl .recordPeek)
      (bank [] [] (unary i) (unary j) result [] [] [] [] [] [] [] [])
      (ctl .halt) (answer (decide (i=0 ∧ j=0)) result) := by
  have h1 := SemiprimeD1StackPhysicalLoops.peek_empty code (ctl .recordPeek) (ctl .baseLeft)
    (ctl .readQ) (ctl .readQ) .records rfl
    (bank [] [] (unary i) (unary j) result [] [] [] [] [] [] [] []) rfl
  cases i with
  | zero =>
    have h2 := SemiprimeD1StackPhysicalLoops.peek_empty code (ctl .baseLeft) (ctl .baseRight)
      (ctl (.fail 0)) (ctl (.fail 0)) .left rfl
      (bank [] [] (unary 0) (unary j) result [] [] [] [] [] [] [] []) rfl
    cases j with
    | zero =>
      have h3 := SemiprimeD1StackPhysicalLoops.peek_empty code (ctl .baseRight) (ctl .success)
        (ctl (.fail 0)) (ctl (.fail 0)) .right rfl
        (bank [] [] (unary 0) (unary 0) result [] [] [] [] [] [] [] []) rfl
      have h4 : Trace.Runs code 1 (ctl .success)
          (bank [] [] [] [] result [] [] [] [] [] [] [] [])
          (ctl .halt) (answer true result) := by
        apply Trace.one_base code (ctl .success) (ctl .halt)
          (.push .valid true (ctl .halt)) _ _ rfl
        · rfl
        · funext k; cases k <;> simp [SemiprimeD1StackBytecode.execute,answer,bank]
      refine ⟨4,by omega,?_⟩
      simpa [unary] using compose h1 (compose h2 (compose h3 h4))
    | succ j =>
      have h3 := SemiprimeD1StackPhysicalLoops.peek_nonempty code (ctl .baseRight)
        (ctl .success) (ctl (.fail 0)) .right rfl
        (bank [] [] (unary 0) (unary (j+1)) result [] [] [] [] [] [] [] [])
        true (unary j) (by simp [unary_succ])
      have hw := bank_width [] [] (unary 0) (unary (j+1)) result [] [] [] [] [] [] [] []
      simp only [List.length_nil,unary,List.length_replicate,Nat.zero_add,Nat.add_zero] at hw
      obtain ⟨z,hz,h4⟩ := SemiprimeD1StackJetRouteFailure.reject_clean _ _ hw
      have h := compose h1 (compose h2 (compose h3 h4))
      refine ⟨1+(1+(1+z)),by omega,?_⟩
      simpa [answer] using h
  | succ i =>
    have h2 := SemiprimeD1StackPhysicalLoops.peek_nonempty code (ctl .baseLeft)
      (ctl .baseRight) (ctl (.fail 0)) .left rfl
      (bank [] [] (unary (i+1)) (unary j) result [] [] [] [] [] [] [] [])
      true (unary i) (by simp [unary_succ])
    have hw := bank_width [] [] (unary (i+1)) (unary j) result [] [] [] [] [] [] [] []
    simp only [List.length_nil,unary,List.length_replicate,Nat.zero_add,Nat.add_zero] at hw
    obtain ⟨z,hz,h3⟩ := SemiprimeD1StackJetRouteFailure.reject_clean _ _ hw
    have h := compose h1 (compose h2 h3)
    refine ⟨1+(1+z),by omega,?_⟩
    simpa [answer] using h
end RiemannGaussian.SemiprimeD1StackJetRouteBase
