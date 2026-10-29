/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAxesComponents

/-! # Actual exponent copying, initialization and depth acquisition -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAxesStages
open SemiprimeD1StackAxes SemiprimeD1StackAxesComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)

/-- A real included Copy call acquires exponent work. -/
theorem copy_exponent (base:Meta.Stack→List Bool) (E:ℕ)
    (he:base .exponent=List.replicate E true) (P Q D:List Bool) :
    Runs program (5*E+4) (.inl .copyE) (data base [] [] [] P Q D) (.inl .first)
      (data base (List.replicate E true) [] [] P Q D) := by
  have h:=copy_call 0 (data base [] [] [] P Q D) rfl (.inl .copyE) (.inl .first) rfl
  have hd:Function.update (data base [] [] [] P Q D) (copyOutput 0)
      ((data base [] [] [] P Q D) (copyInput 0)++(data base [] [] [] P Q D) (copyOutput 0))=
      data base (List.replicate E true) [] [] P Q D:=by
    change Function.update (data base [] [] [] P Q D) (.inl .squareWork) (base .exponent++[])=_
    rw [he,List.append_nil]
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr k => fin_cases k <;> simp [data,Function.update]
  rw [hd] at h
  change Runs program (5*(base .exponent).length+4) _ _ _ _ at h
  simpa only [he,List.length_replicate] using h

/-- The depth source is also acquired by a real call, not by a native subtraction. -/
theorem copy_depth (base:Meta.Stack→List Bool) (E:ℕ)
    (he:base .exponent=List.replicate E true) (P Q:List Bool) :
    Runs program (5*E+4) (.inl .copyDepth) (data base [] [] [] P Q []) (.inl .popDepth)
      (data base [] [] [] P Q (List.replicate E true)) := by
  have h:=copy_call 3 (data base [] [] [] P Q []) rfl (.inl .copyDepth) (.inl .popDepth) rfl
  have hd:Function.update (data base [] [] [] P Q []) (copyOutput 3)
      ((data base [] [] [] P Q []) (copyInput 3)++(data base [] [] [] P Q []) (copyOutput 3))=
      data base [] [] [] P Q (List.replicate E true):=by
    change Function.update (data base [] [] [] P Q []) (.inr 2) (base .exponent++[])=_
    rw [he,List.append_nil]
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr k => fin_cases k <;> simp [data,Function.update]
  rw [hd] at h
  change Runs program (5*(base .exponent).length+4) _ _ _ _ at h
  simpa only [he,List.length_replicate] using h

/-- Two actual pushes initialize both counters to one. -/
theorem initialize_axes (base:Meta.Stack→List Bool) :
    Runs program 2 (.inl .ready) (data base [] [] [] [] [] []) (.inl .copyE)
      (data base [] [] [] [true] [true] []) := by
  have h0:Runs program 1 (.inl .ready) (data base [] [] [] [] [] []) (.inl .initQ) (data base [] [] [] [true] [] []):=by
    apply one_base program _ _ (.push (.inr 0) true (.inl .initQ)) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .initQ) (data base [] [] [] [true] [] []) (.inl .copyE) (data base [] [] [] [true] [true] []):=by
    apply one_base program _ _ (.push (.inr 1) true (.inl .copyE)) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  exact h0.trans h1

/-- Exactly one physical pop removes the final depth marker, including empty E. -/
theorem pop_depth (base:Meta.Stack→List Bool) (E:ℕ) (P Q:List Bool) :
    Runs program 1 (.inl .popDepth) (data base [] [] [] P Q (List.replicate E true)) (.inl .halt)
      (data base [] [] [] P Q (List.replicate (E-1) true)) := by
  cases E with
  | zero =>
    apply one_base program _ _ (.pop (.inr 2) (.inl .halt) (.inl .halt) (.inl .halt)) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  | succ E =>
    apply one_base program _ _ (.pop (.inr 2) (.inl .halt) (.inl .halt) (.inl .halt)) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]

/-- Complete depth acquisition retains both axes and clears every work stack. -/
theorem finish_depth (base:Meta.Stack→List Bool) (E:ℕ)
    (he:base .exponent=List.replicate E true) (P Q:List Bool) :
    Runs program (5*E+5) (.inl .copyDepth) (data base [] [] [] P Q []) (.inl .halt)
      (data base [] [] [] P Q (List.replicate (E-1) true)) := by
  have h:=(copy_depth base E he P Q).trans (pop_depth base E P Q)
  simpa only [show (5*E+4)+1=5*E+5 by omega] using h
end RiemannGaussian.SemiprimeD1StackAxesStages
