/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityCopies

/-! # Actual fixed-copy and literal original arity recipes -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityStatic
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityView SemiprimeD1StackVertexArityCopies
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackUnaryDivmod (unary unary_add)

/-- One actual R+1 copy, used by both endpoint constraints. -/
theorem radius_one (code index radius first second digits:ℕ) :
    Runs program (5*radius+4) (.inl .oneRadius)
      (store (header code index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code index radius first second digits) (unary radius) [] [] [] [] []) := by
  have h:=copy_radius code index radius first second digits [] [] [] [] [] [] (.inl .oneRadius) (.inl .halt) rfl
  simpa only [List.append_nil] using h
/-- Two actual readonly-source copies, for a scale constraint. -/
theorem radius_two (code index radius first second digits:ℕ) :
    Runs program (10*radius+8) (.inl (.twoRadius 0))
      (store (header code index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code index radius first second digits) (unary (radius+radius)) [] [] [] [] []) := by
  have h0:=copy_radius code index radius first second digits [] [] [] [] [] [] (.inl (.twoRadius 0)) (.inl (.twoRadius 1)) rfl
  rw [List.append_nil] at h0
  have h1:=copy_radius code index radius first second digits (unary radius) [] [] [] [] []
    (.inl (.twoRadius 1)) (.inl .halt) rfl
  rw [←unary_add] at h1
  have h:=h0.trans h1
  convert h using 1;omega
/-- Three actual copies, for product and carry constraints. -/
theorem radius_three (code index radius first second digits:ℕ) :
    Runs program (15*radius+12) (.inl (.threeRadius 0))
      (store (header code index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code index radius first second digits) (unary (radius+(radius+radius))) [] [] [] [] []) := by
  have h0:=copy_radius code index radius first second digits [] [] [] [] [] [] (.inl (.threeRadius 0)) (.inl (.threeRadius 1)) rfl
  rw [List.append_nil] at h0
  have h1:=copy_radius code index radius first second digits (unary radius) [] [] [] [] []
    (.inl (.threeRadius 1)) (.inl (.threeRadius 2)) rfl
  rw [←unary_add] at h1
  have h2:=copy_radius code index radius first second digits (unary (radius+radius)) [] [] [] [] []
    (.inl (.threeRadius 2)) (.inl .halt) rfl
  rw [←unary_add] at h2
  have h:=h0.trans (h1.trans h2)
  convert h using 1;omega
/-- One physically pushed marker; no count/word answer is an input. -/
theorem literal_one (h:Source→List Bool) (arity:List Bool) :
    Runs program 1 (.inl (.literal 0)) (store h arity [] [] [] [] []) (.inl .halt)
      (store h (true::arity) [] [] [] [] []) :=
  push_arity h arity [] [] [] [] [] (.inl (.literal 0)) (.inl .halt) rfl
/-- Two literal marker pushes implement every equality-vertex scope. -/
theorem literal_two (h:Source→List Bool) (arity:List Bool) :
    Runs program 2 (.inl (.literal 1)) (store h arity [] [] [] [] []) (.inl .halt)
      (store h (true::true::arity) [] [] [] [] []) := by
  have h0:=push_arity h arity [] [] [] [] [] (.inl (.literal 1)) (.inl (.literal 0)) rfl
  exact h0.trans (literal_one h (true::arity))
/-- Three literal marker pushes implement every Boolean OR scope. -/
theorem literal_three (h:Source→List Bool) (arity:List Bool) :
    Runs program 3 (.inl (.literal 2)) (store h arity [] [] [] [] []) (.inl .halt)
      (store h (true::true::true::arity) [] [] [] [] []) := by
  have h0:=push_arity h arity [] [] [] [] [] (.inl (.literal 2)) (.inl (.literal 1)) rfl
  exact h0.trans (literal_two h (true::arity))
end RiemannGaussian.SemiprimeD1StackVertexArityStatic
