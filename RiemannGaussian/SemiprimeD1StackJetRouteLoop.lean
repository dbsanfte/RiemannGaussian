/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteBase
import RiemannGaussian.SemiprimeD1StackJetRouteRecords
/-! # All-prefix execution of the physical mixed-radix record loop -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteLoop
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls
open SemiprimeD1StackJetRouteStep SemiprimeD1StackJetRouteBase
open SemiprimeD1StackJetRouteRecords (tape)
open SemiprimeD1StackJetRouteFailure (compose)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1StackRouteArithmetic (compatible)
local notation "ctl" => SemiprimeD1StackJetRoute.control

/-- Every radix record is actually read and evaluated. No predicate/trace answer
is supplied; the only answer here specifies the proven output of the fixed code. -/
theorem loop (records : List (ℕ×ℕ)) (i j : ℕ) (result : List Bool) :
    ∃m≤4000*(records.length+1)*((tape records).length+i+j+result.length+1),
      Trace.Runs code m (ctl .recordPeek)
        (bank [] (tape records) (unary i) (unary j) result [] [] [] [] [] [] [] [])
        (ctl .halt) (answer (compatible records i j) result) := by
  induction records generalizing i j with
  | nil =>
    obtain ⟨m,hm,ht⟩ := base i j result
    refine ⟨m,?_,ht⟩
    simp only [List.length_nil,tape,Nat.zero_add,Nat.mul_one]
    omega
  | cons pair records ih =>
    rcases pair with ⟨q,d⟩
    by_cases ha : i/d+j/d<q
    · obtain ⟨m,hm,hs⟩ := compatible_step q d i j ha (tape records) result
      obtain ⟨n,hn,ht⟩ := ih (i%d) (j%d)
      refine ⟨m+n,?_,?_⟩
      · have hri := Nat.mod_le i d
        have hrj := Nat.mod_le j d
        have hbase : (tape records).length+i%d+j%d+result.length+1≤
            (tape ((q,d)::records)).length+i+j+result.length+1 := by
          rw [SemiprimeD1StackJetRouteRecords.tape_cons_length]
          omega
        have hscaled := Nat.mul_le_mul_left (4000*(records.length+1)) hbase
        have hstep : q+d+i+j+1≤(tape ((q,d)::records)).length+i+j+result.length+1 := by
          rw [SemiprimeD1StackJetRouteRecords.tape_cons_length]
          omega
        have hm' := hm.trans (Nat.mul_le_mul_left 2000 hstep)
        simp only [List.length_cons]
        nlinarith
      · simpa only [tape,compatible,ha,decide_true,Bool.true_and] using compose hs ht
    · obtain ⟨m,hm,ht⟩ := incompatible_step q d i j ha (tape records) result
      refine ⟨m,?_,?_⟩
      · have hstep : q+d+i+j+(tape records).length+result.length+1≤
            (tape ((q,d)::records)).length+i+j+result.length+1 := by
          rw [SemiprimeD1StackJetRouteRecords.tape_cons_length]
          omega
        have hm' := hm.trans (Nat.mul_le_mul_left 2000 hstep)
        simp only [List.length_cons]
        nlinarith
      · simpa [tape,compatible,ha,answer] using ht
end RiemannGaussian.SemiprimeD1StackJetRouteLoop
