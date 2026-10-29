/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteFields
/-! # Included physical division and digit compatibility calls -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteDigits
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl" => SemiprimeD1StackJetRoute.control

theorem divide_injective (b : Bool) : Function.Injective (divideStack b) := by
  intro x y h
  cases b <;> cases x <;> cases y <;> simp_all [divideStack]

theorem compare_injective : Function.Injective compareStack := by
  intro x y h
  cases x <;> cases y <;> simp_all [compareStack]

/-- Actual left quotient/remainder acquisition preserves the literal divisor. -/
theorem divide_left (i j d : ℕ) (records result q : List Bool) :
    ∃m≤100*(i+d+1)+1,Trace.Runs code m (ctl .divideLeft)
      (bank [] records (unary i) (unary j) result [] q (unary d) [] [] [] [] []) (ctl .divideRight) (bank [] records [] (unary j) result [] q (unary d) (unary (i/d)) (unary (i%d)) [] [] []) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackUnaryDivmodBytecode.divide_run i d
  refine ⟨m+1,by omega,?_⟩
  apply Trace.included_call code (divideStack false) divideLeftLabel (divide_injective false)
    SemiprimeD1StackUnaryDivmodBytecode.code SemiprimeD1StackUnaryDivmodBytecode.entry (fun _=>rfl)
    (ctl .divideLeft) (ctl .divideRight) rfl m _ _ _ _ rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk .input rfl).elim | exact (hk .quotient rfl).elim | exact (hk .remainder rfl).elim

/-- Actual right quotient/remainder acquisition preserves the literal divisor. -/
theorem divide_right (j d : ℕ) (records result q qi ri : List Bool) :
    ∃m≤100*(j+d+1)+1,Trace.Runs code m (ctl .divideRight)
      (bank [] records [] (unary j) result [] q (unary d) qi ri [] [] []) (ctl .compareCall) (bank [] records [] [] result [] q (unary d) qi ri (unary (j/d)) (unary (j%d)) []) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackUnaryDivmodBytecode.divide_run j d
  refine ⟨m+1,by omega,?_⟩
  apply Trace.included_call code (divideStack true) divideRightLabel (divide_injective true)
    SemiprimeD1StackUnaryDivmodBytecode.code SemiprimeD1StackUnaryDivmodBytecode.entry (fun _=>rfl)
    (ctl .divideRight) (ctl .compareCall) rfl m _ _ _ _ rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk .input rfl).elim | exact (hk .quotient rfl).elim | exact (hk .remainder rfl).elim

/-- Compatibility is the actual comparator output, never a supplied digit predicate. -/
theorem compare_digits (qi qj q : ℕ) (records result d ri rj : List Bool) :
    ∃m≤30*(qi+qj+q+1)+11,Trace.Runs code m (ctl .compareCall)
      (bank [] records [] [] result [] (unary q) d (unary qi) ri (unary qj) rj [])
      (ctl .compareDone) (bank [] records [] [] result [] [] d [] ri [] rj [decide (qi+qj<q)]) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackUnarySumLessBytecode.compare_run qi qj q
  refine ⟨m+1,by omega,?_⟩
  apply Trace.included_call code compareStack compareLabel compare_injective
    SemiprimeD1StackUnarySumLessBytecode.code SemiprimeD1StackUnarySumLessBytecode.entry (fun _=>rfl)
    (ctl .compareCall) (ctl .compareDone) rfl m _ _ _ _ rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk .left rfl).elim | exact (hk .right rfl).elim | exact (hk .limit rfl).elim | exact (hk .valid rfl).elim

end RiemannGaussian.SemiprimeD1StackJetRouteDigits
