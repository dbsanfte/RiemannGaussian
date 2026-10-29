/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDCalls
/-! # Actual positive Euclid iteration and actual terminal zero-divisor cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDBody
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding SemiprimeD1StackEuclidGCDCalls
open SemiprimeD1StackProcedureTrace
/-- Actual time for one complete positive-divisor step, including every return and erased quotient/backup byte. -/
def stepTime (xs ys:List Bool) :Nat:=
  2+(5*ys.length+4)+(SemiprimeD1StackDividerExecution.executionTime xs ys+1)+
    ((SemiprimeBitDivision.divideLoop xs ys).quotient.length+1)+(5*ys.length+4)+(ys.length+1)+
    (2*(SemiprimeBitDivision.divideLoop xs ys).remainder.length+3)+
    (SemiprimeD1StackReduceExecution.trimTime (SemiprimeBitDivision.divideLoop xs ys).remainder.reverse+1)
/-- The actual fuel head and actual nonempty divisor drive a complete restoring division, swap and trim. -/
theorem step_run (left right fuel xs ys:List Bool) (hne:ys≠[]) :
    Runs program (stepTime xs ys) .loop (bank (loopWords left right (true::fuel) xs ys)) .loop
      (bank (loopWords left right fuel ys
        (SemiprimeD1StackSourceEnvironmentEncoding.normalize (SemiprimeBitDivision.divideLoop xs ys).remainder))) :=by
  have h0:=P.pop_run .loop .abort .abort .check (aux .fuel)
    (bank (loopWords left right (true::fuel) xs ys)) (true::fuel) rfl rfl
  rw [update_fuel] at h0
  have h1:=P.peek_run .check .reverseFinish .backup .backup y
    (bank (loopWords left right fuel xs ys)) ys rfl rfl
  have he:SemiprimeD1StackBytecode.choose Label.reverseFinish .backup .backup ys.head?=.backup:=by
    cases ys with
    | nil=>exact False.elim (hne rfl)
    | cons b ys=>cases b <;> rfl
  rw [he] at h1
  have h2:=P.copy_call .backupY .backup .divide rfl (bank (loopWords left right fuel xs ys)) ys [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .next) (ys++[])) at h2
  rw [List.append_nil,update_next] at h2
  have h3:=divide_call left right fuel xs ys ys
  let rem:=(SemiprimeBitDivision.divideLoop xs ys).remainder
  let quo:=(SemiprimeBitDivision.divideLoop xs ys).quotient
  have h4:=P.drain_loop .clearQuotient .restoreX quotient rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,next:=ys,remainder:=rem,quotient:=quo}) quo rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .quotient)) []) at h4
  rw [update_quotient] at h4
  have h5:=P.copy_call .restoreX .restoreX .clearNext rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,next:=ys,remainder:=rem}) ys [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .input)) (ys++[])) at h5
  rw [List.append_nil,update_x] at h5
  have h6:=P.drain_loop .clearNext .reverseRemainder (aux .next) rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,next:=ys,remainder:=rem,x:=ys}) ys rfl
  rw [update_next] at h6
  have h7:=P.reverse_call .remainder .reverseRemainder .trimRemainder rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,remainder:=rem,x:=ys}) rem [] rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank _) (dividerStack (.inr .remainder)) [])
    (aux .trimScratch) (rem.reverse++[])) at h7
  rw [List.append_nil,update_remainder,update_trimScratch] at h7
  have h8:=P.trim_call .divisor .trimRemainder .loop rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=ys,trimScratch:=rem.reverse}) rem.reverse [] rfl rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank _) (aux .trimScratch) [])
    (dividerStack (.inr .divisor)) (SemiprimeD1StackReduceExecution.trimReverse rem.reverse++[])) at h8
  rw [List.append_nil,update_trimScratch,update_y] at h8
  exact P.join (P.join (P.join (P.join (P.join (P.join (P.join (P.join h0 h1) h2) h3) h4) h5) h6) h7) h8
/-- Actual zero-divisor terminal fragment includes remaining fuel erasure and its EOF. -/
def finishTime (fuel xs:List Bool) :Nat:=
  2+(2*xs.length+3)+(SemiprimeD1StackReduceExecution.trimTime xs.reverse+1)+(fuel.length+1)
/-- Both actual original words survive final normalization and every remaining fuel marker is physically popped. -/
theorem finish_run (left right fuel xs:List Bool) :
    Runs program (finishTime fuel xs) .loop (bank (loopWords left right (true::fuel) xs [])) .done
      (bank {originalLeft:=left,originalRight:=right, output:=SemiprimeD1StackSourceEnvironmentEncoding.normalize xs}) :=by
  have h0:=P.pop_run .loop .abort .abort .check (aux .fuel)
    (bank (loopWords left right (true::fuel) xs [])) (true::fuel) rfl rfl
  rw [update_fuel] at h0
  have h1:=P.peek_run .check .reverseFinish .backup .backup y
    (bank (loopWords left right fuel xs [])) [] rfl rfl
  have h2:=P.reverse_call .finish .reverseFinish .trimFinish rfl
    (bank (loopWords left right fuel xs [])) xs [] rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank _) (dividerStack (.inr .input)) [])
    (aux .trimScratch) (xs.reverse++[])) at h2
  rw [List.append_nil,update_x,update_trimScratch] at h2
  have h3:=P.trim_call .output .trimFinish .clearFuel rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,trimScratch:=xs.reverse}) xs.reverse [] rfl rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank _) (aux .trimScratch) [])
    (aux .output) (SemiprimeD1StackReduceExecution.trimReverse xs.reverse++[])) at h3
  rw [List.append_nil,update_trimScratch,update_output] at h3
  have h4:=P.drain_loop .clearFuel .done (aux .fuel) rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel, output:=SemiprimeD1StackSourceEnvironmentEncoding.normalize xs}) fuel rfl
  rw [update_fuel] at h4
  exact P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
end RiemannGaussian.SemiprimeD1StackEuclidGCDBody
