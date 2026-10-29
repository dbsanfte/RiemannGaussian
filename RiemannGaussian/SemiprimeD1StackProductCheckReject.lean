/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckGuard

/-! # Whole actual rejecting product-checker path
Invalid raw words are rejected by the computed guard. Every vector/count byte
is physically drained; only original input/modulus/suffix and false verdict
remain. No positivity, canonicality or intended arithmetic answer is supplied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckReject
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckAcquisition
open SemiprimeD1StackProductCheckGuard SemiprimeD1StackProcedureTrace

/-- Exact final physical payload with original input/cache/suffix and one verdict. -/
def finalData (raw cached : List Bool) (bit : Bool) : Stack→List Bool :=
  Function.update (Function.update (input raw cached) readerRole (raw.drop (3*cached.length))) output [bit]
/-- Exact whole checker halt, with no parser/operand/source work or return frames. -/
def done (raw cached : List Bool) (bit : Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData raw cached bit,[]⟩

/-- The computed rejecting branch physically writes its singleton false result. -/
theorem reject_push (raw cached : List Bool) :
    Runs program 1 .reject (afterAcquire raw cached) (.clearVector false)
      (Function.update (afterAcquire raw cached) output [false]) := by
  apply one_base program .reject (.clearVector false) (.push output false (.clearVector false)) _ _ rfl
  · rfl
  · rfl

/-- Actual complete vector cleanup works for either literal continuation. -/
theorem clear_vector (compute : Bool) (data : Stack→List Bool) :
    Runs program ((data vectorRole).length+1) (.clearVector compute) data
      (if compute then .multiply else .clearCount) (Function.update data vectorRole []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.clearVector compute)
    (if compute then .multiply else .clearCount) vectorRole rfl data (data vectorRole)
  rw [Function.update_eq_self] at h
  exact h
/-- Every literal count-cache byte is actually erased before the final halt. -/
theorem clear_count (data : Stack→List Bool) :
    Runs program ((data countRole).length+1) .clearCount data .done (Function.update data countRole []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearCount .done countRole rfl data (data countRole)
  rw [Function.update_eq_self] at h
  exact h

/-- Complete rejection cleanup is exactly the promised retained-input payload. -/
theorem cleanup_data (raw cached : List Bool) :
    Function.update (Function.update (Function.update (afterAcquire raw cached) output [false]) vectorRole []) countRole []=
      finalData raw cached false := by
  funext k
  by_cases hc:k=countRole
  · subst k;rfl
  by_cases hv:k=vectorRole
  · subst k;rfl
  by_cases hr:k=readerRole
  · subst k;rfl
  by_cases ho:k=output
  · subst k;rfl
  simp only [Function.update_of_ne hc,Function.update_of_ne hv,Function.update_of_ne hr,Function.update_of_ne ho,
    finalData,afterAcquire,beforeAcquire]

/-- Own complete rejecting-path budget includes actual acquisition/guard and
every unneeded vector/count byte, plus branch, write and caller halt. -/
def rejectBudget (raw cached : List Bool) : ℕ :=
  (3+SemiprimeD1StackWordVectorExecution.timeBound raw cached countWord+1)+
    (SemiprimeD1StackVectorCanonicalExecution.timeBound (words raw cached) cached+1)+
    (SemiprimeD1StackWordVectorExecution.result raw cached countWord).length+8

/-- COMPLETE actual rejection for every raw assignment/modulus, including zero
modulus. The sole premise names the ACTUALLY computed guard outcome. -/
theorem source_run (raw cached : List Bool) (ha : accepted raw cached=false) :
    ∃t ≤ rejectBudget raw cached,C.run program t (initial raw cached)=some (done raw cached false) := by
  obtain ⟨a,haTime,h0⟩:=checked_prefix raw cached
  have h1:=branch_run raw cached
  simp only [ha,Bool.false_eq_true,ite_false] at h1
  have h2:=reject_push raw cached
  let data1:=Function.update (afterAcquire raw cached) output [false]
  let data2:=Function.update data1 vectorRole []
  have h3:=clear_vector false data1
  have h4:=clear_count data2
  change Runs program ((SemiprimeD1StackWordVectorExecution.result raw cached countWord).length+1)
    (.clearVector false) data1 .clearCount data2 at h3
  change Runs program 4 .clearCount data2 .done (Function.update data2 countRole []) at h4
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4
  have hd : Function.update data2 countRole []=finalData raw cached false := cleanup_data raw cached
  rw [hd] at h
  obtain ⟨finish,hr,ho⟩:=h [] (initial raw cached) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (finalData raw cached false) [] finish ho
  refine ⟨(((a+1)+1)+((SemiprimeD1StackWordVectorExecution.result raw cached countWord).length+1))+4+1,?_,?_⟩
  · unfold rejectBudget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl

end RiemannGaussian.SemiprimeD1StackProductCheckReject
