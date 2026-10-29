/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootLoop
/-! # Actual final consuming reversal and compact binary square-root output -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootFinish
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackProcedureTrace
/-- Actual final reversed root occupies the consumed power word temporarily. -/
def reversed (bits r : List Bool) : Stack→List Bool :=
  bank (retained bits r.reverse) (fun _ => []) (fun _ => []) (fun _ => []) (words [] [])
/-- Exact final full bank with only the compact root and the twelve retained metadata words. -/
def finished (bits r : List Bool) : Stack→List Bool :=
  bank (retained bits []) (fun _ => []) (fun _ => []) (fun _ => [])
    (words [] (SemiprimeD1StackReduceExecution.trimReverse r.reverse))
/-- Actual consuming reverse moves every raw root cell, with its real return. -/
theorem reverse_call (bits r : List Bool) :
    Runs program (2*r.length+3) (ctl .reverse) (idle bits [] r) (ctl .trim) (reversed bits r) := by
  let source:=SemiprimeD1StackReverseWord.state none r []
  let stop:=SemiprimeD1StackReverseWord.done r.reverse
  let before:=idle bits [] r
  have hi : Link.DataRel reverseStack before source.store before := by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  have h0:=Link.data_update reverseStack reverse_injective before source.store before hi (0:Fin 2) []
  have h1:=Link.data_update reverseStack reverse_injective before _ _ h0 (1:Fin 2) r.reverse
  have he : Function.update (Function.update source.store 0 []) 1 r.reverse=stop.store := by
    funext k;fin_cases k <;> rfl
  rw [he] at h1
  have he0 : Function.update before (reverseStack 0) []=idle bits [] [] := by
    change Function.update (idle bits [] r) (aux .root) []=idle bits [] []
    rw [idle,bank_aux,words_update]
    rfl
  have he1 : Function.update (idle bits [] []) (reverseStack 1) r.reverse=reversed bits r := by
    change Function.update (idle bits [] []) (metadata (M.aux .base)) r.reverse=reversed bits r
    rw [idle,bank_metadata,retained_update]
    rfl
  rw [he0,he1] at h1
  exact included_call program reverseStack reverseLabel reverse_injective SemiprimeD1StackReverseWord.code 0
    (fun _ => rfl) (ctl .reverse) (ctl .trim) rfl (2*r.length+2) source stop before _ rfl rfl
    (by simpa only [List.append_nil] using SemiprimeD1StackReverseWord.reverse_run r [] none) hi h1
/-- Actual final trimming restores the borrowed power role to empty and leaves every private role empty. -/
theorem trim_call (bits r : List Bool) :
    Runs program (SemiprimeD1StackReduceExecution.trimTime r.reverse+1) (ctl .trim) (reversed bits r)
      (ctl .done) (finished bits r) := by
  let source:=SemiprimeD1StackReduce.state (some .trim) none [] [] r.reverse []
  let stop:=SemiprimeD1StackReduce.state none none [] [] [] (SemiprimeD1StackReduceExecution.trimReverse r.reverse)
  let before:=reversed bits r
  have hi : Link.DataRel trimStack before source.store before := by
    constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  have ho : Link.DataRel trimStack before stop.store (finished bits r) := by
    constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k|k|k|k
      · rcases k with k|k|k
        · cases k <;> rfl
        · cases k <;> rfl
        · cases k with
          | base => exact False.elim (hk .scratch rfl)
          | reader | copyScratch | precision | template => rfl
      · cases k with
        | left => exact False.elim (hk .left rfl)
        | right => exact False.elim (hk .right rfl)
        | scratch | output => rfl
      · rfl
      · rfl
      · cases k with
        | root => rfl
        | output => exact False.elim (hk .output rfl)
  exact included_call program trimStack trimLabel trim_injective SemiprimeD1StackReduce.code .trim
    (fun _ => rfl) (ctl .trim) (ctl .done) rfl _ source stop before _ rfl rfl
    (by simpa only [List.append_nil] using SemiprimeD1StackReduceExecution.trim_run r.reverse [] none) hi ho
/-- Exact own time includes the two real final word traversals and returns. -/
def finishTime (r : List Bool) : ℕ := 2*r.length+3+(SemiprimeD1StackReduceExecution.trimTime r.reverse+1)
/-- Complete actual compact output adapter, with all33 words accounted for. -/
theorem finish_run (bits r : List Bool) :
    Runs program (finishTime r) (ctl .reverse) (idle bits [] r) (ctl .done) (finished bits r) :=
  join (reverse_call bits r) (trim_call bits r)
end RiemannGaussian.SemiprimeD1StackBinarySquareRootFinish
