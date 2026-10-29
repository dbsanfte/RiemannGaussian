/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryPrimitives
/-! # Actual factor reversal and high-zero trimming, with borrowed words restored -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCompaction
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
/-- Actual chosen factor address is a fixed finite selector only. -/
def factorWord (large : Bool) : Stack := aux (if large then .large else .small)
/-- Every factor reversal consumes the complete original word and pays its real return. -/
theorem reverse_call (large : Bool) (before : Stack→List Bool) (xs : List Bool)
    (hx : before (factorWord large)=xs) (hp : before (squareRoot S.power)=[]) :
    Runs program (2*xs.length+3) (ctl (.reverse large)) before (ctl (.trim large))
      (Function.update (Function.update before (factorWord large) []) (squareRoot S.power) xs.reverse) := by
  let source:=SemiprimeD1StackReverseWord.state none xs []
  let stop:=SemiprimeD1StackReverseWord.done xs.reverse
  have hi : Link.DataRel (reverseStack large) before source.store before := by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hp
    · intro k _;rfl
  have ho0:=Link.data_update (reverseStack large) (reverse_injective large) before source.store before hi (0:Fin 2) []
  have ho1:=Link.data_update (reverseStack large) (reverse_injective large) before
    (Function.update source.store 0 []) (Function.update before (reverseStack large 0) []) ho0 (1:Fin 2) xs.reverse
  have he : Function.update (Function.update source.store 0 []) 1 xs.reverse=stop.store := by
    funext k;fin_cases k <;> rfl
  rw [he] at ho1
  have hr:=SemiprimeD1StackReverseWord.reverse_run xs [] none
  rw [List.append_nil] at hr
  exact included_call program (reverseStack large) (reverseLabel large) (reverse_injective large)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl (.reverse large)) (ctl (.trim large)) rfl
    (2*xs.length+2) source stop before _ rfl rfl hr hi ho1
/-- The trim call physically empties its borrowed scratch and emits the compact factor. -/
theorem trim_call (large : Bool) (before : Stack→List Bool) (xs : List Bool)
    (hl : before (adder .left)=[]) (hr : before (adder .right)=[])
    (hp : before (squareRoot S.power)=xs) (ho : before (factorWord large)=[]) :
    Runs program (SemiprimeD1StackReduceExecution.trimTime xs+1) (ctl (.trim large)) before
      (if large then ctl (.copy .checkSmall) else ctl (.reverse true))
      (Function.update (Function.update before (squareRoot S.power) []) (factorWord large)
        (SemiprimeD1StackReduceExecution.trimReverse xs)) := by
  let source:=SemiprimeD1StackReduce.state (some .trim) none [] [] xs []
  let stop:=SemiprimeD1StackReduce.state none none [] [] [] (SemiprimeD1StackReduceExecution.trimReverse xs)
  have hi : Link.DataRel (trimStack large) before source.store before := by
    constructor
    · intro k;cases k
      · exact hl
      · exact hr
      · exact hp
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update (trimStack large) (trim_injective large) before source.store before hi (.scratch : A.Stack) []
  have h1:=Link.data_update (trimStack large) (trim_injective large) before
    (Function.update source.store .scratch []) (Function.update before (trimStack large .scratch) []) h0
    (.output : A.Stack) (SemiprimeD1StackReduceExecution.trimReverse xs)
  have he : Function.update (Function.update source.store .scratch []) .output
      (SemiprimeD1StackReduceExecution.trimReverse xs)=stop.store := by funext k;cases k <;> rfl
  rw [he] at h1
  have ht:=SemiprimeD1StackReduceExecution.trim_run xs [] none
  rw [List.append_nil] at ht
  exact included_call program (trimStack large) (trimLabel large) (trim_injective large)
    SemiprimeD1StackReduce.code .trim (fun _=>rfl) (ctl (.trim large))
    (if large then ctl (.copy .checkSmall) else ctl (.reverse true)) rfl
    (SemiprimeD1StackReduceExecution.trimTime xs) source stop before _ rfl rfl ht hi h1
/-- Exact own cost for real reversal and real trim with both physical returns. -/
def time (xs : List Bool) : ℕ := 2*xs.length+3+(SemiprimeD1StackReduceExecution.trimTime xs.reverse+1)
/-- Complete actual compaction changes only the chosen factor, restoring every borrowed word. -/
theorem compact_call (large : Bool) (before : Stack→List Bool) (xs : List Bool)
    (hx : before (factorWord large)=xs) (hp : before (squareRoot S.power)=[])
    (hl : before (adder .left)=[]) (hr : before (adder .right)=[]) :
    Runs program (time xs) (ctl (.reverse large)) before
      (if large then ctl (.copy .checkSmall) else ctl (.reverse true))
      (Function.update before (factorWord large) (SemiprimeD1StackReduceExecution.trimReverse xs.reverse)) := by
  have h0:=reverse_call large before xs hx hp
  let middle:=Function.update (Function.update before (factorWord large) []) (squareRoot S.power) xs.reverse
  have ne : factorWord large≠squareRoot S.power := by cases large <;> decide
  have nl : adder .left≠factorWord large ∧ adder .left≠squareRoot S.power := by cases large <;> decide
  have nr : adder .right≠factorWord large ∧ adder .right≠squareRoot S.power := by cases large <;> decide
  have hl' : middle (adder .left)=[] := by simpa only [middle,Function.update_of_ne nl.2,Function.update_of_ne nl.1] using hl
  have hr' : middle (adder .right)=[] := by simpa only [middle,Function.update_of_ne nr.2,Function.update_of_ne nr.1] using hr
  have hp' : middle (squareRoot S.power)=xs.reverse := by simp only [middle,Function.update_same]
  have ho' : middle (factorWord large)=[] := by simp only [middle,Function.update_of_ne ne,Function.update_same]
  have h1:=trim_call large middle xs.reverse hl' hr' hp' ho'
  have he : Function.update (Function.update middle (squareRoot S.power) []) (factorWord large)
      (SemiprimeD1StackReduceExecution.trimReverse xs.reverse)=
      Function.update before (factorWord large) (SemiprimeD1StackReduceExecution.trimReverse xs.reverse) := by
    funext k
    by_cases hf:k=factorWord large
    · subst k;simp only [Function.update_same]
    · by_cases hpower:k=squareRoot S.power
      · subst k;simpa only [Function.update_of_ne hf,Function.update_same] using hp.symm
      · simp [Function.update,middle,hf,hpower]
  rw [he] at h1
  exact join h0 h1
/-- Every raw factor byte and both returns fit this linear actual compaction cap. -/
theorem time_le (xs : List Bool) : time xs≤4*xs.length+6 := by
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le xs.reverse
  rw [List.length_reverse] at ht
  unfold time
  omega
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCompaction
