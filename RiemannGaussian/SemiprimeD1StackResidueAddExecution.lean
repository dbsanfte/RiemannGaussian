/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackResidueAdd

/-! # Literal cached-modulus addition trace
The adder and divider clocks below are their proved actual trace lengths.
Their value-level specifications are never used as executing instructions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackResidueAddExecution
open SemiprimeD1StackResidueAdd SemiprimeD1StackProcedureTrace

/-- Raw binary sum, specifying the actual adder output. -/
def sum (a b : List Bool) : List Bool := (SemiprimeBitArithmetic.addBits a b false).bits
/-- Actual restoring-division residue, including its physical padding. -/
def residue (a b cached : List Bool) : List Bool :=
  (SemiprimeBitDivision.divideLoop (sum a b) cached).remainder
/-- Actual quotient, physically erased before the component returns. -/
def quotient (a b cached : List Bool) : List Bool :=
  (SemiprimeBitDivision.divideLoop (sum a b) cached).quotient
/-- Actual adder instruction count. -/
def addTime (a b : List Bool) : ℕ :=
  3*(max a.length b.length+1)+2*(sum a b).length+2
/-- Reached payload after the real addition call. -/
def afterAdd (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] (sum a b))
    (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- Reached payload after the real cached-divisor copy. -/
def afterCopy (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] (sum a b))
    (D.payload [] cached [] [] [] [] [] [] [] [] []) cached []
/-- Reached payload after BOTH complete arithmetic traces. -/
def afterDivide (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] [])
    (D.payload [] [] [] [] [] [] [] (residue a b cached) (quotient a b cached) [] []) cached []
/-- Exact final cells: only the cached modulus and computed residue remain. -/
def finalData (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] [])
    (D.payload [] [] [] [] [] [] [] (residue a b cached) [] [] []) cached []
/-- Actual halted source state. -/
def done (a b cached : List Bool) : C.State Stack Label := ⟨none,none,none,finalData a b cached,[]⟩
/-- All actual nested instructions, quotient clearing and final halt are paid. -/
def totalTime (a b cached : List Bool) : ℕ :=
  (addTime a b+1)+(5*cached.length+4)+
    (SemiprimeD1StackDividerExecution.executionTime (sum a b) cached+1)+
    ((quotient a b cached).length+1)+1

/-- The actual binary sum is left DIRECTLY in the physical division input. -/
theorem add_call (a b cached : List Bool) :
    Runs program (addTime a b+1) .start (input a b cached)
      .copyModulus (afterAdd a b cached) := by
  apply included_call program Sum.inl Label.addition Sum.inl_injective A.code (.start false)
    (fun _=>rfl) .start .copyModulus rfl (addTime a b)
    (SemiprimeD1StackAdder.state (some (.start false)) none a b [] [])
    (SemiprimeD1StackAdder.state none none [] [] [] (sum a b))
    (input a b cached) (afterAdd a b cached)
  · rfl
  · rfl
  · exact SemiprimeD1StackAdderExecution.source_run a b false
  · constructor
    · intro k; rfl
    · intro k _; rfl
  · constructor
    · intro k; rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl

/-- Physical copy acquires the divider's operand while preserving the modulus cache. -/
theorem modulus_copy (a b cached : List Bool) :
    Runs program (5*cached.length+4) .copyModulus (afterAdd a b cached)
      .divide (afterCopy a b cached) := by
  apply included_call program copyStack Label.copy copyStack_injective
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .copyModulus .divide rfl (5*cached.length+3)
    (SemiprimeD1StackCopy.state 0 none cached [] []) (SemiprimeD1StackCopy.done cached cached)
    (afterAdd a b cached) (afterCopy a b cached)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words cached [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> first | rfl | exact False.elim (hk 1 rfl)
        · rfl

/-- The actual nested divider consumes the actual sum and acquired copy,
preserving the original binary modulus and every unrelated physical cell. -/
theorem divide_call (a b cached : List Bool) :
    Runs program (SemiprimeD1StackDividerExecution.executionTime (sum a b) cached+1)
      .divide (afterCopy a b cached) .clearQuotient (afterDivide a b cached) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program divideStack Label.division divideStack_injective
    D.code (.control .start) (fun _=>rfl) .divide .clearQuotient rfl
    (SemiprimeD1StackDividerExecution.executionTime (sum a b) cached)
    (SemiprimeD1StackDivider.state (some (.control .start)) none none
      (sum a b) cached [] [] [] [] [] [] [] [] [])
    (SemiprimeD1StackDivider.state none none none [] [] [] [] [] [] []
      (residue a b cached) (quotient a b cached) [] [])
    (afterCopy a b cached) (afterDivide a b cached)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackDividerExecution.source_run (sum a b) cached
  · constructor
    · intro k
      rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk (.inr .input) rfl).elim
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> first | rfl | exact False.elim (hk (.inr .divisor) rfl) | exact False.elim (hk (.inr .remainder) rfl) | exact False.elim (hk (.inr .quotient) rfl)
        · rfl

/-- The physical quotient is erased cell by cell, with no silent workspace reset. -/
theorem clear_quotient (a b cached : List Bool) :
    Runs program ((quotient a b cached).length+1) .clearQuotient (afterDivide a b cached)
      .done (finalData a b cached) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearQuotient .done
    (divideStack (.inr .quotient)) rfl (finalData a b cached) (quotient a b cached)
  have hi : Function.update (finalData a b cached) (divideStack (.inr .quotient))
      (quotient a b cached)=afterDivide a b cached := by
    funext k
    rcases k with k|k
    · simp [Function.update,divideStack,finalData,afterDivide,store]
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;>
          simp [Function.update,divideStack,finalData,afterDivide,store,D.payload]
      · cases k <;> simp [Function.update,divideStack,finalData,afterDivide,store]
  have ho : Function.update (finalData a b cached) (divideStack (.inr .quotient)) []=
      finalData a b cached := by
    exact Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- Complete actual fixed-source addition/remainder trace. This total
trace is valid even for an all-zero cache; ring semantics use positive modulus. -/
theorem source_run (a b cached : List Bool) :
    C.run program (totalTime a b cached) (initial a b cached)=some (done a b cached) := by
  have h01:=runs_trans program _ _ _ _ _ _ _ _ (add_call a b cached) (modulus_copy a b cached)
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 (divide_call a b cached)
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 (clear_quotient a b cached)
  obtain ⟨finish,hfinish,hout⟩:=h0123 [] (initial a b cached) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (finalData a b cached) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl

end RiemannGaussian.SemiprimeD1StackResidueAddExecution
