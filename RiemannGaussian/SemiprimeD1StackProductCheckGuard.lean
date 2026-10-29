/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckAcquisition

/-! # Executed guard inside the raw local product checker
The complete canonical-vector program reads the actual acquired bytes. Its
computed answer, not an assumed guard, supplies positivity for later arithmetic.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckGuard
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckAcquisition SemiprimeD1StackProcedureTrace

/-- Exact three raw words, used only to specify the actually computed guard. -/
def words (raw cached : List Bool) : List (List Bool) :=
  SemiprimeD1StackWordVectorSpec.blocks cached 3 raw
/-- The guard's computed Boolean, never an initial or code argument. -/
def accepted (raw cached : List Bool) : Bool :=
  SemiprimeD1StackVectorCanonicalExecution.answer cached (words raw cached)
/-- Actual guard-output cell consumed by the enclosing control branch. -/
def guardRole : Stack := guardStack .output
/-- Reached payload after complete actual canonicality checking. -/
def afterGuard (raw cached : List Bool) : Stack→List Bool :=
  Function.update (afterAcquire raw cached) guardRole [accepted raw cached]

/-- Whole actual guard call, including rejected-vector draining, obtains its
answer from the physical vector constructed by this same enclosing program. -/
theorem guard_call (raw cached : List Bool) :
    ∃m ≤ SemiprimeD1StackVectorCanonicalExecution.timeBound (words raw cached) cached,
      Runs program (m+1) .guard (afterAcquire raw cached) .branch (afterGuard raw cached) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackVectorCanonicalExecution.source_run (words raw cached) cached
  refine ⟨m,hm,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program guardStack Label.canonical guardStack_injective
    G.program .start (fun _=>rfl) .guard .branch rfl m
    (SemiprimeD1StackVectorCanonical.initial (SemiprimeD1TensorTapeCodec.vectorBits (words raw cached)) cached)
    (SemiprimeD1StackVectorCanonicalExecution.done (words raw cached) cached)
    (afterAcquire raw cached) (afterGuard raw cached)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      have hg : k≠guardRole := by intro h;subst k;exact hk .output rfl
      simp only [afterGuard,Function.update_of_ne hg]

/-- Closed raw-input acquisition+guard prefix, with no solved predicate/operands. -/
theorem checked_prefix (raw cached : List Bool) :
    ∃t ≤ (3+SemiprimeD1StackWordVectorExecution.timeBound raw cached countWord+1)+
      (SemiprimeD1StackVectorCanonicalExecution.timeBound (words raw cached) cached+1),
      Runs program t .start (input raw cached) .branch (afterGuard raw cached) := by
  obtain ⟨a,ha,h0⟩:=acquired_prefix raw cached
  obtain ⟨b,hb,h1⟩:=guard_call raw cached
  exact ⟨a+(b+1),by omega,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩

/-- Runtime control consumes the ACTUAL computed guard bit; no proof verdict
selects the rejecting or computing branch of the finite program. -/
theorem branch_run (raw cached : List Bool) :
    Runs program 1 .branch (afterGuard raw cached) (if accepted raw cached then .tag 0 else .reject)
      (afterAcquire raw cached) := by
  apply one_base program .branch (if accepted raw cached then .tag 0 else .reject)
    (.pop guardRole .bad .reject (.tag 0)) _ _ rfl
  · cases h:accepted raw cached <;>
      simp [SemiprimeD1StackBytecode.execute,afterGuard,Function.update,SemiprimeD1StackBytecode.choose,h]
  · funext k
    by_cases hk:k=guardRole
    · subst k;rfl
    · change Function.update (afterGuard raw cached) guardRole [] k=afterAcquire raw cached k
      simp only [afterGuard,Function.update_of_ne hk]

/-- A true COMPUTED guard implies positive modulus from the first actual word.
No positivity, canonicality or generated-expression validity oracle is required. -/
theorem accepted_modulus_pos (raw cached : List Bool) (ha : accepted raw cached=true) :
    0<SemiprimeBitArithmetic.bitValue cached := by
  have hall:=(SemiprimeD1StackVectorCanonicalExecution.answer_true cached (words raw cached)).mp ha
  have hword:=hall (SemiprimeD1StackWordBlockExecution.result raw cached) (by
    simp only [words,SemiprimeD1StackWordVectorSpec.blocks,List.mem_cons_self])
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) hword

end RiemannGaussian.SemiprimeD1StackProductCheckGuard
