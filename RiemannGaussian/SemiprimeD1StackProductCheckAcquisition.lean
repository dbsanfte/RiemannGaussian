/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheck

/-! # Actual constant-count and raw-input acquisition inside the product checker
Every three-word operand vector is produced by the enclosing code, not supplied
as an initial list, getter or encoded record. This is a source-prefix theorem;
the full rejecting/computing checker trace remains a separate composition.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckAcquisition
open SemiprimeD1StackProductCheck SemiprimeD1StackProcedureTrace

/-- The three word-count bytes are literal actual program pushes. -/
def countWord : List Bool := [true,true,true]
/-- Actual retained counter cache shared with the whole vector producer. -/
def countRole : Stack := .inl W.countCache
/-- Actual source suffix produced by the whole three-word acquisition. -/
def readerRole : Stack := vectorStack (.inl 0)
/-- Actual encoded acquired vector, later parsed by this same checker. -/
def vectorRole : Stack := vectorStack W.output
/-- Reached payload after literal three-marker construction. -/
def beforeAcquire (raw cached : List Bool) : Stack→List Bool :=
  Function.update (input raw cached) countRole countWord
/-- Reached payload after the complete actual word-vector program. -/
def afterAcquire (raw cached : List Bool) : Stack→List Bool :=
  Function.update
    (Function.update (beforeAcquire raw cached) readerRole (raw.drop (3*cached.length)))
    vectorRole (SemiprimeD1StackWordVectorExecution.result raw cached countWord)

/-- One literal count push, with no natural-number count operand. -/
theorem push_count (pc next : Label) (data : Stack→List Bool)
    (hcode : program pc=.base (.push countRole true next)) :
    Runs program 1 pc data next (Function.update data countRole (true::data countRole)) := by
  apply one_base program pc next (.push countRole true next) _ _ hcode
  · rfl
  · rfl
/-- The actual count starts empty because no count/operand advice was initialized. -/
theorem initial_count (raw cached : List Bool) : input raw cached countRole=[] := rfl
/-- All three count bytes are physically pushed before the real acquisition call. -/
theorem count_run (raw cached : List Bool) :
    Runs program 3 .start (input raw cached) .acquire (beforeAcquire raw cached) := by
  have h0:=push_count .start .push1 (input raw cached) rfl
  have h1:=push_count .push1 .push2 (Function.update (input raw cached) countRole [true]) rfl
  have h2:=push_count .push2 .acquire
    (Function.update (Function.update (input raw cached) countRole [true]) countRole [true,true]) rfl
  change Runs program 1 .start (input raw cached) .push1
    (Function.update (input raw cached) countRole [true]) at h0
  change Runs program 1 .push1 (Function.update (input raw cached) countRole [true]) .push2
    (Function.update (Function.update (input raw cached) countRole [true]) countRole [true,true]) at h1
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  have hd : Function.update (Function.update (Function.update (input raw cached) countRole [true]) countRole [true,true])
      countRole [true,true,true]=beforeAcquire raw cached := by
    funext k
    by_cases hk:k=countRole
    · subst k;simp [Function.update,beforeAcquire,countWord]
    · simp [Function.update,beforeAcquire,hk]
  change Runs program 3 .start (input raw cached) .acquire
    (Function.update (Function.update (Function.update (input raw cached) countRole [true]) countRole [true,true])
      countRole [true,true,true]) at h
  rw [hd] at h
  exact h

/-- The complete actual vector procedure executes INSIDE the product checker
with its real shared binary modulus template. No operand list or getter is given. -/
theorem acquire_call (raw cached : List Bool) :
    ∃m ≤ SemiprimeD1StackWordVectorExecution.timeBound raw cached countWord,
      Runs program (m+1) .acquire (beforeAcquire raw cached) .guard (afterAcquire raw cached) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackWordVectorExecution.source_run raw cached countWord
  refine ⟨m,hm,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program vectorStack Label.vector vectorStack_injective
    W.program (.control .start) (fun _=>rfl) .acquire .guard rfl m
    (SemiprimeD1StackWordVector.initial raw cached countWord)
    (SemiprimeD1StackWordVectorExecution.done raw cached countWord)
    (beforeAcquire raw cached) (afterAcquire raw cached)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k
      rcases k with k|k
      · fin_cases k <;> rfl
      · fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · fin_cases k <;> rfl
      · fin_cases k <;> rfl
    · intro k hk
      have hreader : k≠readerRole := by
        intro h;subst k;exact hk (.inl 0) rfl
      have hvector : k≠vectorRole := by
        intro h;subst k;exact hk W.output rfl
      simp only [afterAcquire,Function.update_of_ne hvector,Function.update_of_ne hreader]

/-- Closed original raw-input prefix reaches its actual computed vector cache. -/
theorem acquired_prefix (raw cached : List Bool) :
    ∃t ≤ 3+SemiprimeD1StackWordVectorExecution.timeBound raw cached countWord+1,
      Runs program t .start (input raw cached) .guard (afterAcquire raw cached) := by
  obtain ⟨m,hm,h1⟩:=acquire_call raw cached
  refine ⟨3+(m+1),by omega,runs_trans program _ _ _ _ _ _ _ _ (count_run raw cached) h1⟩

end RiemannGaussian.SemiprimeD1StackProductCheckAcquisition
