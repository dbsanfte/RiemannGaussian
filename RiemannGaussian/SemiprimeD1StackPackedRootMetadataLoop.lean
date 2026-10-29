/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataCalls
/-! # Complete actual width-marker loop, with physical precision/base growth -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadataLoop
open SemiprimeD1StackPackedRootMetadata SemiprimeD1StackPackedRootMetadataEncoding
open SemiprimeD1StackPackedRootMetadataPrimitives SemiprimeD1StackPackedRootMetadataCalls
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
local notation "ctl" => Label.local
/-- The full empty allocated adder includes its real unused left shadow. -/
theorem empty_adder : A.store [] [] [] []=(fun _ => []) := by funext k;cases k <;> rfl
/-- Exact actual per-iteration bank, including the retained bootstrap bank. -/
def work (b : B.Stack→List Bool) (reader p base template right sum : List Bool) : Stack→List Bool :=
  bank b (A.store [] right [] sum) (words reader [] p base template)
/-- The invariant names actual words only; no decoded natural enters code. -/
theorem loop_work (b : B.Stack→List Bool) (n t : ℕ) :
    loop b n t=work b (List.replicate t true) (precisionWord n) (baseWord n) (List.replicate (2*n) false) [] [] := by
  unfold loop work
  rw [empty_adder]
/-- Exact single-cell base growth. -/
theorem base_succ (n : ℕ) : baseWord (n+1)=false::baseWord n := by
  simp only [baseWord,List.replicate_succ,List.cons_append]
/-- The two actual width writes count both physical cells. -/
theorem template_succ (n : ℕ) : List.replicate (2*(n+1)) false=false::false::List.replicate (2*n) false := by
  rw [show 2*(n+1)=2*n+2 by omega,List.replicate_succ,List.replicate_succ]
/-- Exact sum of the five local pushes/pop, REAL add, preserving copy and drain. -/
def stepTime (n : ℕ) : ℕ :=
  6+addTime (precisionWord n)+(5*(precisionWord (n+1)).length+4)+((precisionWord (n+1)).length+1)
/-- One complete real marker iteration acquires the NEXT binary precision,
one base shift and TWO width cells, with all private/shadow words cleared. -/
theorem step_run (b : B.Stack→List Bool) (n t : ℕ) :
    Runs program (stepTime n) (ctl .read) (loop b n (t+1)) (ctl .read) (loop b (n+1) t) := by
  rw [loop_work,loop_work]
  let r := List.replicate t true
  let p := precisionWord n
  let base := baseWord n
  let width := List.replicate (2*n) false
  have h0 := pop_run .read (ctl .done) (ctl .growBase) (ctl .growBase) (aux .reader)
    (work b (true::r) p base width [] []) (true::r) rfl rfl
  dsimp only [work] at h0
  rw [update_aux,words_update] at h0
  change Runs program 1 (ctl .read) (work b (true::r) p base width [] []) (ctl .growBase) (work b r p base width [] []) at h0
  have h1 := push_run .growBase (ctl .growFirst) (aux .base) false (work b r p base width [] []) rfl
  dsimp only [work] at h1
  rw [update_aux,words_update] at h1
  change Runs program 1 _ _ _ (work b r p (false::base) width [] []) at h1
  have h2 := push_run .growFirst (ctl .growSecond) (aux .template) false (work b r p (false::base) width [] []) rfl
  dsimp only [work] at h2
  rw [update_aux,words_update] at h2
  change Runs program 1 _ _ _ (work b r p (false::base) (false::width) [] []) at h2
  have h3 := push_run .growSecond (ctl .seedHigh) (aux .template) false (work b r p (false::base) (false::width) [] []) rfl
  dsimp only [work] at h3
  rw [update_aux,words_update] at h3
  change Runs program 1 _ _ _ (work b r p (false::base) (false::false::width) [] []) at h3
  have h4 := push_run .seedHigh (ctl .seedLow) (adder .right) true (work b r p (false::base) (false::false::width) [] []) rfl
  change Runs program 1 _ _ _ (Function.update (work b r p (false::base) (false::false::width) [] []) (adderAllocation .right) [true]) at h4
  dsimp only [work] at h4
  rw [update_adder,SemiprimeD1StackAdder.store_right] at h4
  have h5 := push_run .seedLow (ctl .add) (adder .right) false (work b r p (false::base) (false::false::width) [true] []) rfl
  change Runs program 1 _ _ _ (Function.update (work b r p (false::base) (false::false::width) [true] []) (adderAllocation .right) [false,true]) at h5
  dsimp only [work] at h5
  rw [update_adder,SemiprimeD1StackAdder.store_right] at h5
  have h6 := add_call b (words r [] p (false::base) (false::false::width)) p rfl
  rw [words_update] at h6
  change Runs program (addTime p) _ _ _ (work b r [] (false::base) (false::false::width) [] (precisionWord (n+1))) at h6
  have h7 := copy_call .sum .copySum .clearSum rfl (work b r [] (false::base) (false::false::width) [] (precisionWord (n+1)))
    (precisionWord (n+1)) [] rfl rfl rfl
  rw [List.append_nil] at h7
  change Runs program _ _ _ _ (Function.update (work b r [] (false::base) (false::false::width) [] (precisionWord (n+1)))
    (aux .precision) (precisionWord (n+1))) at h7
  dsimp only [work] at h7
  rw [update_aux,words_update] at h7
  have h8 := drain_loop .clearSum (ctl .read) (adder .output) rfl
    (work b r (precisionWord (n+1)) (false::base) (false::false::width) [] (precisionWord (n+1))) (precisionWord (n+1)) rfl
  change Runs program _ _ _ _ (Function.update
    (work b r (precisionWord (n+1)) (false::base) (false::false::width) [] (precisionWord (n+1))) (adderAllocation .output) []) at h8
  dsimp only [work] at h8
  rw [update_adder,SemiprimeD1StackAdder.store_output] at h8
  have h := join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8
  have ht : 1+1+1+1+1+1+addTime p+(5*(precisionWord (n+1)).length+4)+((precisionWord (n+1)).length+1)=stepTime n := by
    dsimp only [p,stepTime]
  rw [ht] at h
  simpa only [stepTime,base_succ,template_succ,List.replicate_succ,r,p,base,width,work,Nat.add_assoc] using h

/-- Literal transition count of the ACTUAL repeated marker loop. -/
def loopTime : ℕ→ℕ→ℕ
  | _,0 => 1
  | n,t+1 => stepTime n+loopTime (n+1) t
/-- Complete loop physically visits every acquired marker and its final EOF. -/
theorem loop_run (b : B.Stack→List Bool) (n t : ℕ) :
    Runs program (loopTime n t) (ctl .read) (loop b n t) (ctl .done) (loop b (n+t) 0) := by
  induction t generalizing n with
  | zero =>
    have h := pop_run .read (ctl .done) (ctl .growBase) (ctl .growBase) (aux .reader) (loop b n 0) [] rfl rfl
    have he : Function.update (loop b n 0) (aux .reader) []=loop b n 0 := by
      apply Function.update_eq_self_iff.mpr
      rfl
    change Runs program 1 (ctl .read) (loop b n 0) (ctl .done) (Function.update (loop b n 0) (aux .reader) []) at h
    rw [he] at h
    exact h
  | succ t ih =>
    have h := join (step_run b n t) (ih (n+1))
    simpa only [loopTime,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

/-- Fixed linear per-marker cost in actual counter bytes, not a native report. -/
theorem stepTime_le (n : ℕ) : stepTime n ≤ 50*(n+1) := by
  have h0 := addTime_le n
  have h1 := precision_length (n+1)
  unfold stepTime
  omega
/-- Whole actual loop has a fixed quadratic cap; dimensions are paid by VALUE. -/
theorem loopTime_le (n t : ℕ) : loopTime n t ≤ 50*t*(n+t+1)+1 := by
  induction t generalizing n with
  | zero => simpa only [loopTime,Nat.mul_zero,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
  | succ t ih =>
    have h0 := stepTime_le n
    have h1 := ih (n+1)
    rw [loopTime]
    nlinarith only [h0,h1]
end RiemannGaussian.SemiprimeD1StackPackedRootMetadataLoop
