/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckParse

/-! # Actual modular product and comparison inside the raw checker
Only operands parsed by this program feed the real multiply/divide procedure.
Its output is directly the left comparison stack; every input is physically
consumed and every literal count byte is drained before the enclosing halt.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckCompute
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckAcquisition
open SemiprimeD1StackProductCheckParse SemiprimeD1StackProcedureTrace

/-- Real divider residue of the two actually parsed input words. -/
def residue (raw cached : List Bool) : List Bool :=
  SemiprimeD1StackResidueMulExecution.residue (first raw cached) (second raw cached) cached
/-- Reached payload after both complete actual multiplication/division traces. -/
def afterMultiply (raw cached : List Bool) : Stack→List Bool :=
  Function.update (Function.update (Function.update (ready raw cached) (operand 0) []) (operand 1) [])
    (multiplyStack M.output) (residue raw cached)
/-- Specified comparison result; no such Boolean is given to the executing code. -/
def verdict (raw cached : List Bool) : Bool :=
  decide (SemiprimeBitArithmetic.bitValue (residue raw cached)=SemiprimeBitArithmetic.bitValue (third raw cached))
/-- Reached payload after actual numeric comparison and operand cleanup. -/
def afterCompare (raw cached : List Bool) : Stack→List Bool :=
  Function.update (Function.update (Function.update (afterMultiply raw cached) (multiplyStack M.output) [])
    (operand 2) []) output [verdict raw cached]
/-- The real multiplier inclusion is injective into the fixed physical bank. -/
theorem multiplyStack_injective : Function.Injective multiplyStack := by
  intro i j h
  simpa only [multiplyStack,Sum.inr.injEq,Sum.inl.injEq] using h

/-- The complete actual modular multiplier is called on the physically parsed
operands, preserving the same actual binary modulus and unrelated caller cells. -/
theorem multiply_call (raw cached : List Bool) :
    Runs program (SemiprimeD1StackResidueMulExecution.totalTime (first raw cached) (second raw cached) cached+1)
      .multiply (ready raw cached) .compare (afterMultiply raw cached) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program multiplyStack Label.multiplication multiplyStack_injective
    M.program .start (fun _=>rfl) .multiply .compare rfl
    (SemiprimeD1StackResidueMulExecution.totalTime (first raw cached) (second raw cached) cached)
    (SemiprimeD1StackResidueMul.initial (first raw cached) (second raw cached) cached)
    (SemiprimeD1StackResidueMulExecution.done (first raw cached) (second raw cached) cached)
    (ready raw cached) (afterMultiply raw cached)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackResidueMulExecution.source_run (first raw cached) (second raw cached) cached
  · constructor
    · intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
    · intro k hk
      have h0:k≠operand 0 := by intro h;subst k;exact hk multiplyLeft rfl
      have h1:k≠operand 1 := by intro h;subst k;exact hk multiplyRight rfl
      have ho:k≠multiplyStack M.output := by intro h;subst k;exact hk M.output rfl
      simp only [afterMultiply,Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne ho]

/-- The numeric comparison consumes the actual computed residue and actual
third parsed word, including high-zero padding and mismatch tail cleanup. -/
theorem compare_call (raw cached : List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime (residue raw cached) (third raw cached)+1)
      .compare (afterMultiply raw cached) .clearCount (afterCompare raw cached) := by
  apply included_call program equalStack Label.equality equalStack_injective
    E.code .loop (fun _=>rfl) .compare .clearCount rfl
    (SemiprimeD1StackWordEqualExecution.executionTime (residue raw cached) (third raw cached))
    (SemiprimeD1StackWordEqual.state (some .loop) none (residue raw cached) (third raw cached) [])
    (SemiprimeD1StackWordEqual.state none none [] [] [verdict raw cached])
    (afterMultiply raw cached) (afterCompare raw cached)
  · rfl
  · rfl
  · exact SemiprimeD1StackWordEqualExecution.source_run (residue raw cached) (third raw cached) none
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      have hl:k≠multiplyStack M.output := by intro h;subst k;exact hk .left rfl
      have hr:k≠operand 2 := by intro h;subst k;exact hk .right rfl
      have ho:k≠output := by intro h;subst k;exact hk .output rfl
      simp only [afterCompare,Function.update_of_ne hl,Function.update_of_ne hr,Function.update_of_ne ho]

/-- The actual final count drain leaves ONLY the stated retained inputs,
exact unread suffix, modulus cache and computed singleton verdict. -/
theorem cleanup_data (raw cached : List Bool) :
    Function.update (afterCompare raw cached) countRole []=
      SemiprimeD1StackProductCheckReject.finalData raw cached (verdict raw cached) := by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> fin_cases k <;> rfl
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · rcases k with k|k
            · fin_cases k <;> rfl
            · cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> rfl
          · cases k <;> rfl
      · rcases k with k|k
        · cases k <;> rfl
        · fin_cases k <;> rfl

/-- Every literal instruction in the actual computing branch is charged. -/
def computeBudget (raw cached : List Bool) : ℕ :=
  (3+SemiprimeD1StackWordVectorExecution.timeBound raw cached countWord+1)+
    (SemiprimeD1StackVectorCanonicalExecution.timeBound (SemiprimeD1StackProductCheckGuard.words raw cached) cached+1)+
    1+parseTime raw cached+
    (SemiprimeD1StackResidueMulExecution.totalTime (first raw cached) (second raw cached) cached+1)+
    (SemiprimeD1StackWordEqualExecution.executionTime (residue raw cached) (third raw cached)+1)+4+1

/-- Complete actual computing path. The premise identifies the already computed
guard bit; it supplies no operand, canonicality, arithmetic or clock to code. -/
theorem source_run (raw cached : List Bool) (ha : SemiprimeD1StackProductCheckGuard.accepted raw cached=true) :
    ∃t ≤ computeBudget raw cached,C.run program t (initial raw cached)=
      some (SemiprimeD1StackProductCheckReject.done raw cached (verdict raw cached)) := by
  obtain ⟨a,hat,h0⟩:=SemiprimeD1StackProductCheckGuard.checked_prefix raw cached
  have h1:=SemiprimeD1StackProductCheckGuard.branch_run raw cached
  simp only [ha,ite_true] at h1
  have h2:=SemiprimeD1StackProductCheckParse.source_run raw cached
  have h3:=multiply_call raw cached
  have h4:=compare_call raw cached
  have h5:=SemiprimeD1StackProductCheckReject.clear_count (afterCompare raw cached)
  change Runs program 4 .clearCount (afterCompare raw cached) .done
    (Function.update (afterCompare raw cached) countRole []) at h5
  rw [cleanup_data raw cached] at h5
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5
  obtain ⟨finish,hr,ho⟩:=h [] (initial raw cached) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (SemiprimeD1StackProductCheckReject.finalData raw cached (verdict raw cached)) [] finish ho
  refine ⟨(((((a+1)+parseTime raw cached)+
    (SemiprimeD1StackResidueMulExecution.totalTime (first raw cached) (second raw cached) cached+1))+
    (SemiprimeD1StackWordEqualExecution.executionTime (residue raw cached) (third raw cached)+1))+4)+1,?_,?_⟩
  · unfold computeBudget;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl

end RiemannGaussian.SemiprimeD1StackProductCheckCompute
