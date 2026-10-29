/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackGraphIndicesComponents

/-! # Literal descending framing produces exact ascending graph indices -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackGraphIndicesLoop
open SemiprimeD1StackGraphIndices SemiprimeD1StackGraphIndicesComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Proof-side catalogue of n unary indices in increasing order; not a machine opcode. -/
def catalogue : ℕ→List Bool→List Bool
  | 0,tail => tail
  | n+1,tail => catalogue n (frame (List.replicate n true) tail)

/-- Actual framing executes the included code and leaves its index intact. -/
theorem emit_frame (base:Meta.Stack→List Bool) (remaining index output:List Bool) :
    Runs program (6*index.length+5) (.inl .emit) (data base remaining index [] output []) (.inl .check)
      (data base remaining index [] (frame index output) []) := by
  have h:=frame_call (data base remaining index [] output []) rfl
  have hd:Function.update (data base remaining index [] output []) (.inr false)
      (frame ((data base remaining index [] output []) (.inl .thresholdWork))
        ((data base remaining index [] output []) (.inr false)))=
      data base remaining index [] (frame index output) []:=by
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr k => cases k <;> simp [data,Function.update]
  rw [hd] at h
  exact h

/-- The complete loop emits every exact index once, in canonical ascending order. -/
theorem loop_run (n:ℕ) (base:Meta.Stack→List Bool) (output:List Bool) :
    Runs program (3*n^2+10*n+6) (.inl .emit)
      (data base (List.replicate n true) (List.replicate n true) [] output []) (.inl .halt)
      (data base [] [] [] (catalogue (n+1) output) []) := by
  induction n generalizing output with
  | zero =>
    have h0:=emit_frame base [] [] output
    have h1:Runs program 1 (.inl .check) (data base [] [] [] (frame [] output) []) (.inl .halt)
        (data base [] [] [] (frame [] output) []):=by
      apply one_base program _ _ (.pop (.inl .squareWork) (.inl .halt) (.inl .dec) (.inl .dec)) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    exact h0.trans h1
  | succ n ih =>
    have h0:=emit_frame base (List.replicate (n+1) true) (List.replicate (n+1) true) output
    have h1:Runs program 1 (.inl .check)
        (data base (true::List.replicate n true) (List.replicate (n+1) true) []
          (frame (List.replicate (n+1) true) output) []) (.inl .dec)
        (data base (List.replicate n true) (List.replicate (n+1) true) []
          (frame (List.replicate (n+1) true) output) []):=by
      apply one_base program _ _ (.pop (.inl .squareWork) (.inl .halt) (.inl .dec) (.inl .dec)) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    have h2:Runs program 1 (.inl .dec)
        (data base (List.replicate n true) (true::List.replicate n true) []
          (frame (List.replicate (n+1) true) output) []) (.inl .emit)
        (data base (List.replicate n true) (List.replicate n true) []
          (frame (List.replicate (n+1) true) output) []):=by
      apply one_base program _ _ (.pop (.inl .thresholdWork) (.inl .emit) (.inl .emit) (.inl .emit)) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    have h:=h0.trans (h1.trans (h2.trans (ih (frame (List.replicate (n+1) true) output))))
    simpa only [List.length_replicate,List.replicate_succ,List.length_cons,catalogue,
      show (6*(n+1)+5)+(1+(1+(3*n^2+10*n+6)))=3*(n+1)^2+10*(n+1)+6 by ring] using h

/-- No ordering or multiplicity is erased: the tape is the exact literal ascending range fold. -/
theorem catalogue_range (n:ℕ) (tail:List Bool) :
    catalogue n tail=(List.range n).foldr (fun i rest=>frame (List.replicate i true) rest) tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [catalogue,ih,List.range_succ,List.foldr_append,List.foldr_cons,List.foldr_nil]

/-- The physical tape has exactly the squared range size, including every terminator. -/
theorem catalogue_length (n:ℕ) (tail:List Bool) : (catalogue n tail).length=n^2+tail.length := by
  induction n generalizing tail with
  | zero => simp [catalogue]
  | succ n ih =>
    rw [catalogue,ih,SemiprimeSourceHistogramKeyBits.frame_length,List.length_replicate]
    ring
end RiemannGaussian.SemiprimeD1StackGraphIndicesLoop
