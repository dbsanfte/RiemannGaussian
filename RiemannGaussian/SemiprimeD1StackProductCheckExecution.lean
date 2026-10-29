/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckCompute

/-! # Whole raw local-product checker without advice
Both actual computed branches close from the same raw assignment and binary
modulus. The guard, grouping, operands, product, residue and verdict are never
initial cells or executing parameters.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckExecution
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckGuard

/-- Specification of the actual final computed verdict, never a code operand. -/
def answer (raw cached : List Bool) : Bool :=
  if accepted raw cached then SemiprimeD1StackProductCheckCompute.verdict raw cached else false
/-- Exact completed payload with original raw word, cache and unread suffix. -/
def done (raw cached : List Bool) : C.State Stack Label :=
  SemiprimeD1StackProductCheckReject.done raw cached (answer raw cached)
/-- Whole actual source allowance includes both proved branch allowances. -/
def timeBound (raw cached : List Bool) : ℕ :=
  SemiprimeD1StackProductCheckReject.rejectBudget raw cached+
    SemiprimeD1StackProductCheckCompute.computeBudget raw cached

/-- The SAME actual program halts for every raw assignment and every cached
binary word, including zero modulus. There are no positivity or guard premises. -/
theorem source_run (raw cached : List Bool) :
    ∃t ≤ timeBound raw cached,C.run program t (initial raw cached)=some (done raw cached) := by
  cases ha:accepted raw cached with
  | false =>
    obtain ⟨t,ht,hr⟩:=SemiprimeD1StackProductCheckReject.source_run raw cached ha
    refine ⟨t,ht.trans (Nat.le_add_right _ _),?_⟩
    simpa only [done,answer,ha,Bool.false_eq_true,ite_false] using hr
  | true =>
    obtain ⟨t,ht,hr⟩:=SemiprimeD1StackProductCheckCompute.source_run raw cached ha
    refine ⟨t,ht.trans (Nat.le_add_left _ _),?_⟩
    simpa only [done,answer,ha,ite_true] using hr

/-- Literal computed verdict, with all parser/operand/vector/count work cleared. -/
theorem output_answer (raw cached : List Bool) : (done raw cached).data output=[answer raw cached] := rfl
/-- Original assignment is retained physically by this same checker. -/
theorem retained_raw (raw cached : List Bool) : (done raw cached).data rawInput=raw := rfl
/-- Original binary modulus is retained physically by this same checker. -/
theorem retained_modulus (raw cached : List Bool) : (done raw cached).data modulus=cached := rfl
/-- Exact unread suffix includes padding and all bytes beyond the three words. -/
theorem retained_suffix (raw cached : List Bool) :
    (done raw cached).data SemiprimeD1StackProductCheckAcquisition.readerRole=raw.drop (3*cached.length) := rfl

end RiemannGaussian.SemiprimeD1StackProductCheckExecution
