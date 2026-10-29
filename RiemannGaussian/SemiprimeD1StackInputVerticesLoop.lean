/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputVerticesComponents

/-! # Executed tagged input-vertex records in exact original order -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackInputVerticesLoop
open SemiprimeD1StackInputVertices SemiprimeD1StackInputVerticesComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Physical schema: constructor input, actual side, literal unary word index. -/
def record (side:Bool) (index tail:List Bool) : List Bool := frame [false] (frame [side] (frame index tail))
/-- Proof-side ordered one-side family; it is not a machine/list opcode. -/
def catalogue (side:Bool) : ℕ→List Bool→List Bool
  | 0,tail => tail
  | n+1,tail => catalogue side n (record side (List.replicate n true) tail)

/-- Six literal pushes emit both exact finite constructor/side fields. -/
theorem push_tags (side:Bool) (base:Meta.Stack→List Bool) (remaining index output:List Bool) :
    Runs program 6 (.inl (.tag side 0)) (data base remaining index [] output []) (.inl (.check side))
      (data base remaining index [] (frame [false] (frame [side] output)) []) := by
  have h0:Runs program 1 (.inl (.tag side 0)) (data base remaining index [] (output) [])
      (.inl (.tag side 1)) (data base remaining index [] (false::output) []):=by
    apply one_base program _ _ (.push (.inr false) false (.inl (.tag side 1))) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr k => cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl (.tag side 1)) (data base remaining index [] (false::output) [])
      (.inl (.tag side 2)) (data base remaining index [] (side::false::output) []):=by
    apply one_base program _ _ (.push (.inr false) side (.inl (.tag side 2))) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr k => cases k <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl (.tag side 2)) (data base remaining index [] (side::false::output) [])
      (.inl (.tag side 3)) (data base remaining index [] (true::side::false::output) []):=by
    apply one_base program _ _ (.push (.inr false) true (.inl (.tag side 3))) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr k => cases k <;> simp [B.execute,data,Function.update]
  have h3:Runs program 1 (.inl (.tag side 3)) (data base remaining index [] (true::side::false::output) [])
      (.inl (.tag side 4)) (data base remaining index [] (false::true::side::false::output) []):=by
    apply one_base program _ _ (.push (.inr false) false (.inl (.tag side 4))) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr k => cases k <;> simp [B.execute,data,Function.update]
  have h4:Runs program 1 (.inl (.tag side 4)) (data base remaining index [] (false::true::side::false::output) [])
      (.inl (.tag side 5)) (data base remaining index [] (false::false::true::side::false::output) []):=by
    apply one_base program _ _ (.push (.inr false) false (.inl (.tag side 5))) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr k => cases k <;> simp [B.execute,data,Function.update]
  have h5:Runs program 1 (.inl (.tag side 5)) (data base remaining index [] (false::false::true::side::false::output) [])
      (.inl (.check side)) (data base remaining index [] (true::false::false::true::side::false::output) []):=by
    apply one_base program _ _ (.push (.inr false) true (.inl (.check side))) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr k => cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

/-- Actual included Frame plus the finite tag pushes acquire one whole descriptor. -/
theorem emit_record (side:Bool) (base:Meta.Stack→List Bool) (remaining index output:List Bool) :
    Runs program (6*index.length+11) (.inl (.emit side)) (data base remaining index [] output []) (.inl (.check side))
      (data base remaining index [] (record side index output) []) := by
  have h0:=frame_call side (data base remaining index [] output []) rfl
  have hd:Function.update (data base remaining index [] output []) (.inr false)
      (frame ((data base remaining index [] output []) (.inl .thresholdWork))
        ((data base remaining index [] output []) (.inr false)))=
      data base remaining index [] (frame index output) []:=by
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr k => cases k <;> simp [data,Function.update]
  rw [hd] at h0
  have h:=h0.trans (push_tags side base remaining index (frame index output))
  change Runs program ((6*index.length+5)+6) _ _ _ _ at h
  simpa only [record,show (6*index.length+5)+6=6*index.length+11 by omega] using h

/-- Whole one-side descriptor loop with every emitted index, actual tag and EOF. -/
theorem loop_run (n:ℕ) (side:Bool) (base:Meta.Stack→List Bool) (output:List Bool) :
    Runs program (3*n^2+16*n+12) (.inl (.emit side))
      (data base (List.replicate n true) (List.replicate n true) [] output []) (afterSide side)
      (data base [] [] [] (catalogue side (n+1) output) []) := by
  induction n generalizing output with
  | zero =>
    have h0:=emit_record side base [] [] output
    have h1:Runs program 1 (.inl (.check side)) (data base [] [] [] (record side [] output) []) (afterSide side)
        (data base [] [] [] (record side [] output) []):=by
      apply one_base program _ _ (.pop (.inl .squareWork) (afterSide side) (.inl (.dec side)) (.inl (.dec side))) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    exact h0.trans h1
  | succ n ih =>
    have h0:=emit_record side base (List.replicate (n+1) true) (List.replicate (n+1) true) output
    have h1:Runs program 1 (.inl (.check side))
        (data base (true::List.replicate n true) (List.replicate (n+1) true) []
          (record side (List.replicate (n+1) true) output) []) (.inl (.dec side))
        (data base (List.replicate n true) (List.replicate (n+1) true) []
          (record side (List.replicate (n+1) true) output) []):=by
      apply one_base program _ _ (.pop (.inl .squareWork) (afterSide side) (.inl (.dec side)) (.inl (.dec side))) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    have h2:Runs program 1 (.inl (.dec side))
        (data base (List.replicate n true) (true::List.replicate n true) []
          (record side (List.replicate (n+1) true) output) []) (.inl (.emit side))
        (data base (List.replicate n true) (List.replicate n true) []
          (record side (List.replicate (n+1) true) output) []):=by
      apply one_base program _ _ (.pop (.inl .thresholdWork) (.inl (.emit side)) (.inl (.emit side)) (.inl (.emit side))) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    have h:=h0.trans (h1.trans (h2.trans (ih (record side (List.replicate (n+1) true) output))))
    simpa only [List.length_replicate,List.replicate_succ,List.length_cons,catalogue,
      show (6*(n+1)+11)+(1+(1+(3*n^2+16*n+12)))=3*(n+1)^2+16*(n+1)+12 by ring] using h

/-- Exact ordered one-side records, retaining all duplicates of the supplied index list. -/
theorem catalogue_range (side:Bool) (n:ℕ) (tail:List Bool) :
    catalogue side n tail=(List.range n).foldr (fun i rest=>record side (List.replicate i true) rest) tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [catalogue,ih,List.range_succ,List.foldr_append,List.foldr_cons,List.foldr_nil]

/-- Exact allocated descriptor tape size, with both finite fields and every terminator. -/
theorem catalogue_length (side:Bool) (n:ℕ) (tail:List Bool) :
    (catalogue side n tail).length=n^2+6*n+tail.length := by
  induction n generalizing tail with
  | zero => simp [catalogue]
  | succ n ih =>
    rw [catalogue,ih]
    simp only [record,SemiprimeSourceHistogramKeyBits.frame_length,List.length_singleton,List.length_replicate]
    ring
end RiemannGaussian.SemiprimeD1StackInputVerticesLoop
