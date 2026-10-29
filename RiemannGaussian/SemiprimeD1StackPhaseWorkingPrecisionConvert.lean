/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionCounter
/-! # Closed bounded-metadata-to-BINARY conversion on the actual precision source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionConvert
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeD1StackPhaseWorkingPrecisionPrimitives SemiprimeD1StackProcedureTrace
/-- Actual retained bounded source field, acquired by the whole metadata source. -/
def source (second : Bool) : M.Stack :=if second then M.aux .r else M.divStack .quotient
/-- A real preserving source copy physically supplies every allocation marker. -/
theorem copy_zero (second : Bool) (old : M.Stack→List Bool) (out power : List Bool) (n : Nat)
    (hs : old (source second)=List.replicate n true) :
    Runs program (5*n+4) (.copyZero second) (data old [] [] out [] [] [] [] [] power)
      (.seedZero second) (data old [] [] out [] [] [] (List.replicate n true) [] power) :=by
  have h:=copy_call (if second then 1 else 0) (.copyZero second) (.seedZero second) rfl
    (data old [] [] out [] [] [] [] [] power) rfl (by cases second <;> rfl)
  have hsource:data old [] [] out [] [] [] [] [] power (copySource (if second then 1 else 0))=List.replicate n true:=by
    cases second <;> exact hs
  rw [hsource,List.length_replicate] at h
  have he:Function.update (data old [] [] out [] [] [] [] [] power) (copyTarget (if second then 1 else 0))
      (List.replicate n true)=data old [] [] out [] [] [] (List.replicate n true) [] power:=by
    cases second <;> funext k <;> rcases k with k|k
    all_goals first | rfl | (cases k <;> rfl)
  rw [he] at h
  exact h
/-- One real low-zero seed guarantees physical capacity above all n increment rounds. -/
theorem seed_zero (second : Bool) (old : M.Stack→List Bool) (out zeros power : List Bool) :
    Runs program 1 (.seedZero second) (data old [] [] out [] [] [] zeros [] power)
      (.allocate second) (data old [] [] out [false] [] [] zeros [] power) :=by
  apply one_base program (.seedZero second) (.allocate second) (.push (aux .counter) false (.allocate second)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Every allocation marker physically writes one counter bit and is consumed. -/
theorem allocate_step (second : Bool) (old : M.Stack→List Bool) (out counter power : List Bool) (n : Nat) :
    Runs program 2 (.allocate second) (data old [] [] out counter [] [] (List.replicate (n+1) true) [] power)
      (.allocate second) (data old [] [] out (false::counter) [] [] (List.replicate n true) [] power) :=by
  have h0:Runs program 1 (.allocate second) (data old [] [] out counter [] [] (List.replicate (n+1) true) [] power)
      (.pushZero second) (data old [] [] out counter [] [] (List.replicate n true) [] power):=by
    apply one_base program (.allocate second) (.pushZero second)
      (.pop (aux .zeroTodo) (.copyTodo second) (.pushZero second) (.pushZero second)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 (.pushZero second) (data old [] [] out counter [] [] (List.replicate n true) [] power)
      (.allocate second) (data old [] [] out (false::counter) [] [] (List.replicate n true) [] power):=by
    apply one_base program (.pushZero second) (.allocate second) (.push (aux .counter) false (.allocate second)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  exact join h0 h1
/-- Complete paid width allocation, including the actual empty-marker branch. -/
theorem allocate_run (second : Bool) (old : M.Stack→List Bool) (out counter power : List Bool) (n : Nat) :
    Runs program (2*n+1) (.allocate second) (data old [] [] out counter [] [] (List.replicate n true) [] power)
      (.copyTodo second) (data old [] [] out (List.replicate n false++counter) [] [] [] [] power) :=by
  induction n generalizing counter with
  | zero=>
    apply one_base program (.allocate second) (.copyTodo second)
      (.pop (aux .zeroTodo) (.copyTodo second) (.pushZero second) (.pushZero second)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  | succ n ih=>
    have hh:=join (allocate_step second old out counter power n) (ih (false::counter))
    have he:List.replicate n false++(false::counter)=List.replicate (n+1) false++counter:=by
      rw [List.replicate_succ']
      simp only [List.append_assoc,List.singleton_append]
    rw [he] at hh
    convert hh using 1
    omega
/-- A second preserving source copy supplies EXACTLY n real increment-control markers. -/
theorem copy_todo (second : Bool) (old : M.Stack→List Bool) (out counter power : List Bool) (n : Nat)
    (hs : old (source second)=List.replicate n true) :
    Runs program (5*n+4) (.copyTodo second) (data old [] [] out counter [] [] [] [] power)
      (.loop second) (data old [] [] out counter [] (List.replicate n true) [] [] power) :=by
  have h:=copy_call (if second then 3 else 2) (.copyTodo second) (.loop second) rfl
    (data old [] [] out counter [] [] [] [] power) rfl (by cases second <;> rfl)
  have hsource:data old [] [] out counter [] [] [] [] power (copySource (if second then 3 else 2))=List.replicate n true:=by
    cases second <;> exact hs
  rw [hsource,List.length_replicate] at h
  have he:Function.update (data old [] [] out counter [] [] [] [] power) (copyTarget (if second then 3 else 2))
      (List.replicate n true)=data old [] [] out counter [] (List.replicate n true) [] [] power:=by
    cases second <;> funext k <;> rcases k with k|k
    all_goals first | rfl | (cases k <;> rfl)
  rw [he] at h
  exact h
/-- The actual acquired BINARY counter is copied to the selected operand, then erased. -/
theorem finish_run (second : Bool) (old : M.Stack→List Bool) (out word power : List Bool) :
    Runs program ((5*word.length+4)+(word.length+1)) (.finish second)
      (data old [] [] out word [] [] [] [] power)
      (if second then .rightShift 0 else .copyDelta)
      (data old (if second then [] else word) (if second then word else []) out [] [] [] [] [] power) :=by
  have h0:=copy_call (if second then 6 else 5) (.finish second) (.clearCounter second) rfl
    (data old [] [] out word [] [] [] [] power) rfl (by cases second <;> rfl)
  have hsource:data old [] [] out word [] [] [] [] power (copySource (if second then 6 else 5))=word:=by cases second <;> rfl
  rw [hsource] at h0
  have he:Function.update (data old [] [] out word [] [] [] [] power) (copyTarget (if second then 6 else 5)) word=
      data old (if second then [] else word) (if second then word else []) out word [] [] [] [] power:=by
    cases second <;> funext k <;> rcases k with k|k
    all_goals first | rfl | (cases k <;> rfl)
  rw [he] at h0
  let d:=data old (if second then [] else word) (if second then word else []) out word [] [] [] [] power
  have h1:=SemiprimeD1StackPhysicalLoops.drain program (.clearCounter second)
    (if second then .rightShift 0 else .copyDelta) (aux .counter) rfl d word
  have hi:Function.update d (aux .counter) word=d:=Function.update_eq_self _ _
  have ho:Function.update d (aux .counter) []=
      data old (if second then [] else word) (if second then word else []) out [] [] [] [] [] power:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [hi,ho] at h1
  exact join h0 h1
/-- Closed conversion uses ONLY the physically supplied acquired unary word.
Its proof premise is instantiated by the frozen whole metadata source, never an unknown supplier. -/
theorem source_run (second : Bool) (old : M.Stack→List Bool) (out power : List Bool) (n : Nat)
    (hs : old (source second)=List.replicate n true) :
    ∃q≤200*(n+1)^2,Runs program q (.copyZero second) (data old [] [] out [] [] [] [] [] power)
      (if second then .rightShift 0 else .copyDelta)
      (data old (if second then [] else counterWord n) (if second then counterWord n else []) out [] [] [] [] [] power) :=by
  have h0:=copy_zero second old out power n hs
  have h1:=seed_zero second old out (List.replicate n true) power
  have h2:=allocate_run second old out [false] power n
  have he:List.replicate n false++[false]=List.replicate (n+1) false:=by rw [List.replicate_succ']
  rw [he] at h2
  have h3:=copy_todo second old out (List.replicate (n+1) false) power n hs
  obtain ⟨b,hb,h4⟩:=SemiprimeD1StackPhaseWorkingPrecisionCounter.loop_run second old [] [] out
    (List.replicate (n+1) false) power n
  have h5:=finish_run second old out (counterWord n) power
  have hh:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  refine ⟨_,?_,hh⟩
  rw [List.length_replicate] at hb
  rw [counterWord_length]
  nlinarith
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionConvert
