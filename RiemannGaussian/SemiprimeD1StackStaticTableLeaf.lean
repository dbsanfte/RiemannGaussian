/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTableLeafCalls
/-! # Whole actual reusable static-checker leaf and its own bit clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticTableLeaf
open SemiprimeD1StackStaticTable SemiprimeD1StackStaticTableSpec
open SemiprimeD1StackStaticTableLeafCalls SemiprimeD1StackStaticTableCleanup SemiprimeD1StackStaticTableEmit
open SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
open SemiprimeD1BooleanTreeStream (leafBytes)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : Static K L)
/-- Actual template, prefix, checker, codec and complete cleanup allowance.
The budget is a PROVED checker trace bound, never an executed source operand. -/
def leafBound (original : K→List Bool) (budget : Nat→Nat) (width : Nat) : Nat :=
  s.roles.length*(6*inputBytes original+5)+7*width+budget width+
    s.roles.length*(Fintype.card K*(inputBytes original+width+budget width)+1)+20
omit [DecidableEq K] [Fintype K] in
/-- Whole checker clearing preserves exactly the original template, scanner and DFS data. -/
theorem clean_withChecker (original : K→List Bool) (bank : List Bool) (depth : Nat)
    (front hist : List Bool) (live : K→List Bool) :
    clean (withChecker (data original bank depth front hist) live)=data original bank depth front hist := by
  funext k;cases k <;> rfl
/-- Actual post-checker inventory is bounded by executed pushes, not by an
assumed workspace/canonicality/retention contract. The result pop only shrinks it. -/
theorem popped_inventory_le (original : K→List Bool) (raw : List Bool) (budget : Nat→Nat)
    (t : Nat) (finish : C.State K L) (ht : t≤ budget raw.length)
    (hr : C.run s.code t (checkerInitial s original raw)=some finish) (base : Stack K→List Bool) :
    inventory (withChecker base (Function.update finish.data s.output []))≤
      Fintype.card K*(inputBytes original+raw.length+budget raw.length) := by
  have hp (k : K) :
      ((withChecker base (Function.update finish.data s.output [])) (checker k)).length≤
        inputBytes original+raw.length+budget raw.length := by
    change (Function.update finish.data s.output [] k).length≤_
    by_cases h:k=s.output
    · subst k
      rw [Function.update_self]
      exact Nat.zero_le _
    · rw [Function.update_of_ne h]
      have hdata:=output_cell_le s original raw t finish hr k
      omega
  change (∑k:K,((withChecker base (Function.update finish.data s.output [])) (checker k)).length)≤_
  calc
    _≤∑_k:K,(inputBytes original+raw.length+budget raw.length):=Finset.sum_le_sum (fun k _=>hp k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- COMPLETE executed leaf: copy every actual template input, reverse the
physical prefix, call the fixed checker, consume its real singleton output,
write each codec bit, drain ALL checker roles, and pop the real caller frame. -/
theorem leaf_returns (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (bank front hist : List Bool) :
    ∃t≤ leafBound s original budget front.length,Returns (program s) t .leaf
      (data original bank 0 front hist)
      (data original bank 0 front ((leafBytes (answer front.reverse)).reverse++hist)) := by
  let nextHist:=(leafBytes (answer front.reverse)).reverse++hist
  obtain ⟨a,ha,h0⟩:=load_call s original bank front hist
  have h1:=copy_prefix s original bank front hist
  have h2:=reverse_prefix s original hraw bank front hist
  obtain ⟨b,hb,finish,hr,hvalue,h3⟩:=checker_call s original answer budget hc bank front hist
  have h4:=verdict_pop s original bank front hist finish.data (answer front.reverse) hvalue
  have h5:=emit_run s (answer front.reverse) (Function.update finish.data s.output []) original bank front hist
  let cleanupData:=withChecker (data original bank 0 front nextHist) (Function.update finish.data s.output [])
  obtain ⟨c,hcTime,hclear⟩:=clear_returns s cleanupData
  have h6:=SemiprimeD1StackProcedureReturns.call (program s) c .leafCleanup (.clear 0) .leafReturn
    cleanupData (clean cleanupData) rfl hclear
  have he:clean cleanupData=data original bank 0 front nextHist:=clean_withChecker original bank 0 front nextHist _
  rw [he] at h6
  have h:=runs_trans (program s) _ _ _ _ _ _ _ _ h0
    (runs_trans (program s) _ _ _ _ _ _ _ _ h1
      (runs_trans (program s) _ _ _ _ _ _ _ _ h2
        (runs_trans (program s) _ _ _ _ _ _ _ _ h3
          (runs_trans (program s) _ _ _ _ _ _ _ _ h4
            (runs_trans (program s) _ _ _ _ _ _ _ _ h5 h6)))))
  refine ⟨_,?_,of_runs (program s) _ .leaf .leafReturn _ _ h rfl⟩
  have hInv:=popped_inventory_le s original front.reverse budget b finish
    (by simpa only [List.length_reverse] using hb) hr (data original bank 0 front nextHist)
  simp only [List.length_reverse] at hInv
  have hlen:(leafBytes (answer front.reverse)).length≤6:=by cases answer front.reverse <;> decide
  unfold leafBound
  change inventory cleanupData≤_ at hInv
  have hm:=Nat.mul_le_mul_left s.roles.length (Nat.add_le_add_right hInv 1)
  omega
omit [DecidableEq K] [Fintype K] in
/-- The physically emitted local0/1 scalar is exactly the frozen tree-codec leaf. -/
theorem leaf_bytes (answer : List Bool→Bool) (raw : List Bool) :
    leafBytes (answer raw)=SemiprimeD1TensorTapeCodec.tape (tree answer raw 0) :=
  SemiprimeD1BooleanTreeStream.leafBytes_original _
end RiemannGaussian.SemiprimeD1StackStaticTableLeaf
