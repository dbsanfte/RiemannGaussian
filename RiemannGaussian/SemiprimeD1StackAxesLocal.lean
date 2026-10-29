/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAxesComponents

/-! # Physically copied and restored axis doubling -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAxesLocal
open SemiprimeD1StackAxes SemiprimeD1StackAxesComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)

/-- A proof-side view selecting the actual doubled axis; no allocation opcode. -/
def axisData (mode:Fin 3) (base:Meta.Stack→List Bool) (ew mw tmp A other D:List Bool) : Stack→List Bool :=
  data base ew mw tmp (if mode=0 then A else other) (if mode=0 then other else A) D

/-- Two literal instructions move one actual copied marker back onto its axis. -/
theorem move_bit (mode:Fin 3) (base:Meta.Stack→List Bool) (ew mw A other D:List Bool) :
    Runs program 2 (.inl (.moveAxis mode)) (axisData mode base ew (true::mw) [] A other D)
      (.inl (.moveAxis mode)) (axisData mode base ew mw [] (true::A) other D) := by
  have h0:Runs program 1 (.inl (.moveAxis mode)) (axisData mode base ew (true::mw) [] A other D)
      (.inl (.pushAxis mode)) (axisData mode base ew mw [] A other D):=by
    apply one_base program _ _ (.pop (.inl .thresholdWork) (afterAxis mode) (.inl (.pushAxis mode)) (.inl (.pushAxis mode))) _ _ rfl
    · rfl
    · fin_cases mode <;> funext k <;> cases k with
      | inl k => cases k <;> simp [B.execute,axisData,data,Function.update]
      | inr k => fin_cases k <;> simp [B.execute,axisData,data,Function.update]
  have h1:Runs program 1 (.inl (.pushAxis mode)) (axisData mode base ew mw [] A other D)
      (.inl (.moveAxis mode)) (axisData mode base ew mw [] (true::A) other D):=by
    apply one_base program _ _ (.push (axis mode) true (.inl (.moveAxis mode))) _ _ rfl
    · rfl
    · fin_cases mode <;> funext k <;> cases k with
      | inl k => cases k <;> simp [B.execute,axisData,data,axis,Function.update]
      | inr k => fin_cases k <;> simp [B.execute,axisData,data,axis,Function.update]
  exact h0.trans h1

/-- The complete actual move includes the physical EOF test and clears its work stack. -/
theorem move_all (n:ℕ) (mode:Fin 3) (base:Meta.Stack→List Bool) (ew A other D:List Bool) :
    Runs program (2*n+1) (.inl (.moveAxis mode)) (axisData mode base ew (List.replicate n true) [] A other D)
      (afterAxis mode) (axisData mode base ew [] [] (List.replicate n true++A) other D) := by
  induction n generalizing A with
  | zero =>
    apply one_base program _ _ (.pop (.inl .thresholdWork) (afterAxis mode) (.inl (.pushAxis mode)) (.inl (.pushAxis mode))) _ _ rfl
    · rfl
    · fin_cases mode <;> funext k <;> cases k with
      | inl k => cases k <;> simp [B.execute,axisData,data,Function.update]
      | inr k => fin_cases k <;> simp [B.execute,axisData,data,Function.update]
  | succ n ih =>
    have h:=(move_bit mode base ew (List.replicate n true) A other D).trans (ih (true::A))
    have hd:List.replicate n true++true::A=List.replicate (n+1) true++A:=by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hd] at h
    simpa only [List.replicate_succ,show 2+(2*n+1)=2*(n+1)+1 by omega] using h

/-- The actual copied counter is restored onto its retained original, producing twice its length. -/
theorem double_axis (n:ℕ) (mode:Fin 3) (base:Meta.Stack→List Bool) (ew other D:List Bool) :
    Runs program (7*n+5) (.inl (.copyAxis mode)) (axisData mode base ew [] [] (List.replicate n true) other D)
      (afterAxis mode) (axisData mode base ew [] [] (List.replicate (2*n) true) other D) := by
  have h0:=copy_call (axisCopy mode) (axisData mode base ew [] [] (List.replicate n true) other D)
    (by fin_cases mode <;> rfl) (.inl (.copyAxis mode)) (.inl (.moveAxis mode)) rfl
  have hdata:Function.update (axisData mode base ew [] [] (List.replicate n true) other D)
      (copyOutput (axisCopy mode))
      ((axisData mode base ew [] [] (List.replicate n true) other D) (copyInput (axisCopy mode))++
        (axisData mode base ew [] [] (List.replicate n true) other D) (copyOutput (axisCopy mode)))=
      axisData mode base ew (List.replicate n true) [] (List.replicate n true) other D:=by
    fin_cases mode <;> funext k <;> cases k with
    | inl k => cases k <;> simp [axisData,data,axisCopy,copyInput,copyOutput,Function.update]
    | inr k => fin_cases k <;> simp [axisData,data,axisCopy,copyOutput,Function.update]
  rw [hdata] at h0
  have hlen:((axisData mode base ew [] [] (List.replicate n true) other D) (copyInput (axisCopy mode))).length=n:=by
    fin_cases mode <;> simp [axisData,data,axisCopy,copyInput]
  rw [hlen] at h0
  have h:=h0.trans (move_all n mode base ew (List.replicate n true) other D)
  simpa only [List.replicate_append_replicate,show n+n=2*n by omega,
    show (5*n+4)+(2*n+1)=7*n+5 by omega] using h
end RiemannGaussian.SemiprimeD1StackAxesLocal
