/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityCopies

/-! # Real unary product and index comparison in original arity recipes -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityArithmetic
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityComponents
open SemiprimeD1StackVertexArityView SemiprimeD1StackVertexArityCopies
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1StackUnaryDivmod (unary unary_add unary_succ)

/-- Actual product on acquired counters, with clean caller work on return. -/
theorem product_store (h:Source→List Bool) (m radius:ℕ) (hr:h .radiusSucc=unary radius) :
    ∃time≤5*(m*(2*radius+3)+1)+1,Runs program time (.inl .product)
      (store h [] [] (unary m) [] [] []) (.inl .halt) (store h (unary (m*radius)) [] [] [] [] []) := by
  obtain ⟨time,ht,he⟩:=product_call (store h [] [] (unary m) [] [] []) m radius rfl hr rfl rfl
  refine ⟨time,ht,?_⟩
  change Runs program _ _ _ _ (Function.update
    (Function.update (data h (work [] [] (unary m) [] [] [])) (aux .multiplier) []) (aux .arity) (unary (m*radius))) at he
  rw [update_aux,work_multiplier,update_aux,work_arity] at he
  exact he
/-- Actual comparison consumes the copied counters and returns its actual one-bit result. -/
theorem compare_store (h:Source→List Bool) (arity:List Bool) (index digits:ℕ) :
    ∃time≤30*(index+digits+1)+11,Runs program time (.inl .compare)
      (store h arity [] [] (unary index) (unary digits) []) (.inl .verdict)
      (store h arity [] [] [] [] [decide (index<digits)]) := by
  obtain ⟨time,ht,he⟩:=compare_call (store h arity [] [] (unary index) (unary digits) []) index digits rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update
    (data h (work arity [] [] (unary index) (unary digits) [])) (aux .compareRight) []) (aux .compareLimit) [])
      (aux .compareResult) [decide (index<digits)]) at he
  rw [update_aux,work_compareRight,update_aux,work_compareLimit,update_aux,work_compareResult] at he
  exact he
/-- This branch reads the physical comparison bit; it never evaluates a native index predicate. -/
theorem verdict_run (h:Source→List Bool) (arity:List Bool) (bit:Bool) :
    Runs program (1+(if bit then 1 else 0)) (.inl .verdict) (store h arity [] [] [] [] [bit]) (.inl .halt)
      (store h (if bit then true::arity else arity) [] [] [] [] []) := by
  cases bit with
  | false =>
    apply one_base program _ _ (.pop (aux .compareResult) (.inl .halt) (.inl .halt) (.inl .inputFlag)) _ _ rfl
    · rfl
    · change Function.update (data h (work arity [] [] [] [] [false])) (aux .compareResult) []=_
      rw [update_aux,work_compareResult]
      rfl
  | true =>
    have h0:Runs program 1 (.inl .verdict) (store h arity [] [] [] [] [true]) (.inl .inputFlag)
        (store h arity [] [] [] [] []):=by
      apply one_base program _ _ (.pop (aux .compareResult) (.inl .halt) (.inl .halt) (.inl .inputFlag)) _ _ rfl
      · rfl
      · change Function.update (data h (work arity [] [] [] [] [true])) (aux .compareResult) []=_
        rw [update_aux,work_compareResult]
        rfl
    exact h0.trans (push_arity h arity [] [] [] [] [] (.inl .inputFlag) (.inl .halt) rfl)

/-- All actual copy, comparison and flag-branch transitions in an input arity. -/
def inputBudget (index radius digits:ℕ) : ℕ :=
  (5*radius+4)+(5*index+4)+(5*digits+4)+(30*(index+digits+1)+11)+2
/-- Original input arity is acquired by the actual cached-word comparison. -/
theorem input_run (code index radius first second digits:ℕ) :
    ∃ time ≤ inputBudget index radius digits,Runs program time (.inl .inputRadius)
      (store (header code index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code index radius first second digits) (unary (radius+(if index<digits then 1 else 0))) [] [] [] [] []) := by
  let h:=header code index radius first second digits
  have h0:=copy_radius code index radius first second digits [] [] [] [] [] [] (.inl .inputRadius) (.inl .inputIndex) rfl
  rw [List.append_nil] at h0
  have h1:=copy_index code index radius first second digits (unary radius) [] [] [] [] [] (.inl .inputIndex) (.inl .inputDigits) rfl
  rw [List.append_nil] at h1
  have h2:=copy_digits code index radius first second digits (unary radius) [] [] (unary index) [] [] (.inl .inputDigits) (.inl .compare) rfl
  rw [List.append_nil] at h2
  obtain ⟨time,ht,h3⟩:=compare_store h (unary radius) index digits
  have h4:=verdict_run h (unary radius) (decide (index<digits))
  have ho:(if decide (index<digits) then true::unary radius else unary radius)=
      unary (radius+(if index<digits then 1 else 0)):=by
    by_cases hi:index<digits <;> simp [hi,unary_succ]
  rw [ho] at h4
  have he:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  refine ⟨_,?_,he⟩
  have hv:(if decide (index<digits) then 1 else 0)≤1:=by split <;> omega
  unfold inputBudget
  omega

/-- Static choice of the first/second-transform multiplier source. -/
def axisValue (useFirst:Bool) (first second:ℕ) : ℕ := if useFirst then first else second
/-- Corresponding literal copy label. -/
def axisKind (useFirst:Bool) : CopyKind := if useFirst then .first else .second
/-- Actual static first/second multiplication-stage label. -/
def axisLabel (useFirst:Bool) (stage:Fin 2) : Label :=
  if useFirst then .inl (.multiplyFirst stage) else .inl (.multiplySecond stage)
/-- Both source choices execute actual readonly-counter Copy. -/
theorem axis_copy (useFirst:Bool) (code index radius first second digits:ℕ)
    (arity tag multiplier right limit result:List Bool) (pc next:Label)
    (hc:program pc=.call (copyLabel (axisKind useFirst) 0) next) :
    Runs program (5*axisValue useFirst first second+4) pc
      (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) arity tag
        (unary (axisValue useFirst first second)++multiplier) right limit result) := by
  cases useFirst with
  | false => exact copy_second code index radius first second digits arity tag multiplier right limit result pc next hc
  | true => exact copy_first code index radius first second digits arity tag multiplier right limit result pc next hc
/-- Every source reload and product transition is included. -/
def productBudget (axis radius:ℕ) : ℕ := 2*(5*axis+4)+(5*((axis+axis)*(2*radius+3)+1)+1)
/-- The first/second scope product is physically acquired, never a supplied multiplication answer. -/
theorem axis_run (useFirst:Bool) (code index radius first second digits:ℕ) :
    ∃time≤productBudget (axisValue useFirst first second) radius,Runs program time (axisLabel useFirst 0)
      (store (header code index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code index radius first second digits)
        (unary (axisValue useFirst first second*radius+axisValue useFirst first second*radius)) [] [] [] [] []) := by
  let axis:=axisValue useFirst first second
  have h0:=axis_copy useFirst code index radius first second digits [] [] [] [] [] []
    (axisLabel useFirst 0) (axisLabel useFirst 1) (by cases useFirst <;> rfl)
  rw [List.append_nil] at h0
  have h1:=axis_copy useFirst code index radius first second digits [] [] (unary axis) [] [] []
    (axisLabel useFirst 1) (.inl .product) (by cases useFirst <;> rfl)
  rw [←unary_add] at h1
  obtain ⟨time,ht,h2⟩:=product_store (header code index radius first second digits) (axis+axis) radius rfl
  rw [Nat.add_mul] at h2
  have he:=h0.trans (h1.trans h2)
  refine ⟨_,?_,he⟩
  unfold productBudget
  dsimp only [axis] at ht
  omega
end RiemannGaussian.SemiprimeD1StackVertexArityArithmetic
