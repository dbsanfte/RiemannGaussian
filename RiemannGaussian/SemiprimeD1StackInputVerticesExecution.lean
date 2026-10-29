/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputVerticesLoop

/-! # Original-input physical graph-index acquisition and reusable stage -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackInputVerticesExecution
open SemiprimeD1StackInputVertices SemiprimeD1StackInputVerticesComponents SemiprimeD1StackInputVerticesLoop
open SemiprimeD1StackProcedureFragments (At Runs)
open SemiprimeMacroParameters
namespace MetaOut
export SemiprimeD1StackTransformExecution (result)
end MetaOut

/-- The remaining counter is acquired by copying the actual retained radius. -/
theorem copy_remaining (side:Bool) (base:Meta.Stack→List Bool) (R:ℕ)
    (hr:base .radius=List.replicate R true) (output:List Bool) :
    Runs program (5*R+4) (.inl (.ready side)) (data base [] [] [] output []) (.inl (.copyIndex side))
      (data base (List.replicate R true) [] [] output []) := by
  have h:=copy_call false (data base [] [] [] output []) rfl (.inl (.ready side)) (.inl (.copyIndex side)) rfl
  have hd:Function.update (data base [] [] [] output []) (copyOutput false)
      ((data base [] [] [] output []) (.inl .radius)++(data base [] [] [] output []) (copyOutput false))=
      data base (List.replicate R true) [] [] output []:=by
    change Function.update (data base [] [] [] output []) (.inl .squareWork) (base .radius++[])=_
    rw [hr,List.append_nil]
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr k => cases k <;> simp [data,Function.update]
  rw [hd] at h
  change Runs program (5*(base .radius).length+4) _ _ _ _ at h
  simpa only [hr,List.length_replicate] using h

/-- The current graph index is separately acquired; neither copy is supplied for free. -/
theorem copy_index (side:Bool) (base:Meta.Stack→List Bool) (R:ℕ)
    (hr:base .radius=List.replicate R true) (remaining output:List Bool) :
    Runs program (5*R+4) (.inl (.copyIndex side)) (data base remaining [] [] output []) (.inl (.dropRemaining side))
      (data base remaining (List.replicate R true) [] output []) := by
  have h:=copy_call true (data base remaining [] [] output []) rfl (.inl (.copyIndex side)) (.inl (.dropRemaining side)) rfl
  have hd:Function.update (data base remaining [] [] output []) (copyOutput true)
      ((data base remaining [] [] output []) (.inl .radius)++(data base remaining [] [] output []) (copyOutput true))=
      data base remaining (List.replicate R true) [] output []:=by
    change Function.update (data base remaining [] [] output []) (.inl .thresholdWork) (base .radius++[])=_
    rw [hr,List.append_nil]
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr k => cases k <;> simp [data,Function.update]
  rw [hd] at h
  change Runs program (5*(base .radius).length+4) _ _ _ _ at h
  simpa only [hr,List.length_replicate] using h

/-- Proof-side mathematical output; no range/list constructor is executed as an opcode. -/
def result (bits:List Bool) : Stack→List Bool :=
  data (MetaOut.result bits) [] [] [] (catalogue false (transformLength bits.length)
    (catalogue true (transformLength bits.length) [])) []
/-- Actual no-continuation stopped state. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Exact complete instruction count. -/
def totalTime (n:ℕ) : ℕ := SemiprimeD1StackTransformArithmetic.totalTime n+
  6*(transformLength n)^2+40*transformLength n+20

/-- A complete side block physically acquires both counters and handles empty range by EOF. -/
theorem one_side (side:Bool) (base:Meta.Stack→List Bool) (R:ℕ)
    (hr:base .radius=List.replicate R true) (output:List Bool) :
    Runs program (3*R^2+20*R+9) (.inl (.ready side)) (data base [] [] [] output []) (afterSide side)
      (data base [] [] [] (catalogue side R output) []) := by
  have h0:=copy_remaining side base R hr output
  have h1:=copy_index side base R hr (List.replicate R true) output
  cases R with
  | zero =>
    have h2:Runs program 1 (.inl (.dropRemaining side)) (data base [] [] [] output []) (afterSide side)
        (data base [] [] [] output []):=by
      apply SemiprimeD1StackProcedureFragments.one_base program _ _
        (.pop (.inl .squareWork) (afterSide side) (.inl (.dropIndex side)) (.inl (.dropIndex side))) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    exact h0.trans (h1.trans h2)
  | succ n =>
    have h2:Runs program 1 (.inl (.dropRemaining side))
        (data base (true::List.replicate n true) (List.replicate (n+1) true) [] output [])
        (.inl (.dropIndex side)) (data base (List.replicate n true) (List.replicate (n+1) true) [] output []):=by
      apply SemiprimeD1StackProcedureFragments.one_base program _ _
        (.pop (.inl .squareWork) (afterSide side) (.inl (.dropIndex side)) (.inl (.dropIndex side))) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    have h3:Runs program 1 (.inl (.dropIndex side))
        (data base (List.replicate n true) (true::List.replicate n true) [] output [])
        (.inl (.emit side)) (data base (List.replicate n true) (List.replicate n true) [] output []):=by
      apply SemiprimeD1StackProcedureFragments.one_base program _ _
        (.pop (.inl .thresholdWork) (.inl (.emit side)) (.inl (.emit side)) (.inl (.emit side))) _ _ rfl
      · rfl
      · funext k;cases k with
        | inl k => cases k <;> simp [B.execute,data,Function.update]
        | inr k => cases k <;> simp [B.execute,data,Function.update]
    have h:=h0.trans (h1.trans (h2.trans (h3.trans (loop_run n side base output))))
    simpa only [List.replicate_succ,
      show (5*(n+1)+4)+((5*(n+1)+4)+(1+(1+(3*n^2+16*n+12))))=
        3*(n+1)^2+20*(n+1)+9 by ring] using h

/-- Reusable actual metadata stage emits side0 then side1, with original inner order. -/
theorem ready (bits:List Bool) :
    Runs program (6*(transformLength bits.length)^2+40*transformLength bits.length+18)
      (.inl (.ready true)) (data (MetaOut.result bits) [] [] [] [] []) (.inl .halt) (result bits) := by
  let R:=transformLength bits.length
  have hr:(MetaOut.result bits) .radius=List.replicate R true:=rfl
  have h0:=one_side true (MetaOut.result bits) R hr []
  have h1:=one_side false (MetaOut.result bits) R hr (catalogue true R [])
  simp only [afterSide,Bool.false_eq_true,ite_true,ite_false] at h0 h1
  have h:=h0.trans h1
  simpa only [result,show (3*R^2+20*R+9)+(3*R^2+20*R+9)=6*R^2+40*R+18 by omega] using h

/-- Complete real execution from original binary N alone, including actual metadata and halt. -/
theorem acquire_run (bits:List Bool) :
    C.run program (totalTime bits.length) (initial bits)=some (done bits) := by
  have h:=(metadata_call bits).trans (ready bits)
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have ht:totalTime bits.length=(SemiprimeD1StackTransformArithmetic.totalTime bits.length+1+
      (6*(transformLength bits.length)^2+40*transformLength bits.length+18))+1:=by
    unfold totalTime;omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done bits)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]

/-- Actual machine initialization contains no supplied graph index or prepared radius. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial (.inl .input) (.inl .start) bits:=by
    dsimp only [initial,SemiprimeD1StackCalls.initial]
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> simp [input,Meta.input]
    | inr k => cases k <;> simp [input]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct (.inl .input) (.inr false) (.inl .start) program bits).symm

/-- One fixed original-input quadratic transition cap. -/
theorem totalTime_le (n:ℕ) : totalTime n≤200000*(n+1)^2 := by
  have hm:=SemiprimeD1StackTransformArithmetic.totalTime_le n
  have hr:=(SemiprimeD1StackTransformArithmetic.prefix_powers n (transformExponent n) (le_refl _)).1
  have hR:transformLength n≤64*n+1:=hr
  unfold totalTime
  nlinarith [Nat.pow_le_pow_left hR 2]

/-- Actual finite-machine time, not a list/control retained report. -/
def acquireInTime (bits:List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (200000*(bits.length+1)^2) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (.inl .input) (.inr false) (.inl .start) program
  exact ⟨⟨totalTime bits.length,acquire_run bits⟩,totalTime_le bits.length⟩
end RiemannGaussian.SemiprimeD1StackInputVerticesExecution
