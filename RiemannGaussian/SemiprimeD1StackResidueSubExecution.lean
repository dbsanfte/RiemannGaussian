/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackResidueSub
/-! # Actual cached-modulus subtraction pipeline trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackResidueSubExecution
open SemiprimeD1StackResidueSub SemiprimeD1StackProcedureTrace
/-- Actual binary adder output, used only to specify reached cells. -/
def sum (a cached : List Bool) : List Bool := (SemiprimeBitArithmetic.addBits a cached false).bits
/-- Actual binary subtractor output after its physical borrow header is removed. -/
def difference (a b cached : List Bool) : List Bool :=
  (SemiprimeBitDivision.subBits (sum a cached) b false).result.bits
/-- The actual computed borrow cell, not an input or control oracle. -/
def borrow (a b cached : List Bool) : Bool :=
  (SemiprimeBitDivision.subBits (sum a cached) b false).borrow
/-- Actual restoring-division remainder. -/
def residue (a b cached : List Bool) : List Bool :=
  (SemiprimeBitDivision.divideLoop (difference a b cached) cached).remainder
/-- Actual quotient, erased physically before return. -/
def quotient (a b cached : List Bool) : List Bool :=
  (SemiprimeBitDivision.divideLoop (difference a b cached) cached).quotient
/-- Exact binary-adder instruction count. -/
def addTime (a cached : List Bool) : ℕ :=
  3*(max a.length cached.length+1)+2*(sum a cached).length+2
/-- Exact binary-subtractor instruction count, including actual borrow emission. -/
def subtractTime (a b cached : List Bool) : ℕ :=
  3*(max (sum a cached).length b.length+1)+2*(difference a b cached).length+3
/-- Reached payload after the first actual cache copy. -/
def afterCopyAdder (a b cached : List Bool) : Stack→List Bool :=
  store (A.store a cached [] []) (S.store [] b [] [])
    (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- The actual sum is wired directly into the next subtractor. -/
def afterAdd (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] (sum a cached)) (S.store [] b [] [])
    (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- Real subtraction returns its computed borrow header and difference bytes. -/
def afterSubtract (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] []) (S.store [] [] [] (borrow a b cached::difference a b cached))
    (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- The actual popped header is absent; no silent byte reset is used. -/
def afterDrop (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] []) (S.store [] [] [] (difference a b cached))
    (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- The second real cache copy prepares the divisor without touching the difference. -/
def afterCopyDivision (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] []) (S.store [] [] [] (difference a b cached))
    (D.payload [] cached [] [] [] [] [] [] [] [] []) cached []
/-- Actual complete division result, before physical quotient erasure. -/
def afterDivide (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] []) (S.store [] [] [] [])
    (D.payload [] [] [] [] [] [] [] (residue a b cached) (quotient a b cached) [] []) cached []
/-- Exact clean final cells: only original cached modulus and computed residue. -/
def finalData (a b cached : List Bool) : Stack→List Bool :=
  store (A.store [] [] [] []) (S.store [] [] [] [])
    (D.payload [] [] [] [] [] [] [] (residue a b cached) [] [] []) cached []
/-- Exact actual halt with empty return stack and cleared transient flags. -/
def done (a b cached : List Bool) : C.State Stack Label := ⟨none,none,none,finalData a b cached,[]⟩
/-- Every actual copy/call/arithmetic/header/drain/halt transition is included. -/
def totalTime (a b cached : List Bool) : ℕ :=
  (5*cached.length+4)+(addTime a cached+1)+(subtractTime a b cached+1)+1+
    (5*cached.length+4)+(SemiprimeD1StackDividerExecution.executionTime (difference a b cached) cached+1)+
    ((quotient a b cached).length+1)+1

/-- The actual adder modulus operand is copied from the physically retained cache. -/
theorem copy_adder (a b cached : List Bool) :
    Runs program (5*cached.length+4) .start (input a b cached) .add (afterCopyAdder a b cached) := by
  apply included_call program (copyStack false) Label.copyAdder (copyStack_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .start .add rfl (5*cached.length+3)
    (SemiprimeD1StackCopy.state 0 none cached [] []) (SemiprimeD1StackCopy.done cached cached)
    (input a b cached) (afterCopyAdder a b cached)
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
      · cases k <;> first | rfl | exact (hk 1 rfl).elim
      · rfl

/-- The real binary addition consumes x and its acquired modulus copy. -/
theorem add_call (a b cached : List Bool) :
    Runs program (addTime a cached+1) .add (afterCopyAdder a b cached) .subtract (afterAdd a b cached) := by
  apply included_call program Sum.inl Label.addition Sum.inl_injective A.code (.start false)
    (fun _=>rfl) .add .subtract rfl (addTime a cached)
    (SemiprimeD1StackAdder.state (some (.start false)) none a cached [] [])
    (SemiprimeD1StackAdder.state none none [] [] [] (sum a cached))
    (afterCopyAdder a b cached) (afterAdd a b cached)
  · rfl
  · rfl
  · exact SemiprimeD1StackAdderExecution.source_run a cached false
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl

/-- Actual subtractor input uses the acquired sum directly, not an evaluated answer. -/
theorem subtract_call (a b cached : List Bool) :
    Runs program (subtractTime a b cached+1) .subtract (afterAdd a b cached)
      .dropBorrow (afterSubtract a b cached) := by
  apply included_call program subtractStack Label.subtraction subtractStack_injective S.code (.start false)
    (fun _=>rfl) .subtract .dropBorrow rfl (subtractTime a b cached)
    (SemiprimeD1StackSubtractor.state (some (.start false)) none (sum a cached) b [] [])
    (SemiprimeD1StackSubtractor.state none none [] [] [] (borrow a b cached::difference a b cached))
    (afterAdd a b cached) (afterSubtract a b cached)
  · rfl
  · rfl
  · exact SemiprimeD1StackSubtractorExecution.source_run (sum a cached) b false
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk .left rfl).elim
      · rcases k with k|k
        · cases k <;> first | rfl | exact (hk .right rfl).elim | exact (hk .output rfl).elim
        · rfl

/-- The computed borrow header is physically popped, regardless of its bit value. -/
theorem drop_borrow (a b cached : List Bool) :
    Runs program 1 .dropBorrow (afterSubtract a b cached) .copyDivisor (afterDrop a b cached) := by
  apply one_base program .dropBorrow .copyDivisor
    (.pop (divideStack (.inr .input)) .copyDivisor .copyDivisor .copyDivisor) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.copyDivisor Label.copyDivisor Label.copyDivisor
      (some (borrow a b cached)))=some Label.copyDivisor
    cases borrow a b cached <;> rfl
  · change Function.update (afterSubtract a b cached) (divideStack (.inr .input))
      (difference a b cached)=afterDrop a b cached
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl

/-- The real second cache copy acquires the division operand and retains its source. -/
theorem copy_division (a b cached : List Bool) :
    Runs program (5*cached.length+4) .copyDivisor (afterDrop a b cached)
      .divide (afterCopyDivision a b cached) := by
  apply included_call program (copyStack true) Label.copyDivision (copyStack_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .copyDivisor .divide rfl (5*cached.length+3)
    (SemiprimeD1StackCopy.state 0 none cached [] []) (SemiprimeD1StackCopy.done cached cached)
    (afterDrop a b cached) (afterCopyDivision a b cached)
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
        · rfl
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> first | rfl | exact (hk 1 rfl).elim
          · rfl

/-- Complete real restoring division consumes the actual difference bytes. -/
theorem divide_call (a b cached : List Bool) :
    Runs program (SemiprimeD1StackDividerExecution.executionTime (difference a b cached) cached+1)
      .divide (afterCopyDivision a b cached) .clearQuotient (afterDivide a b cached) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program divideStack Label.division divideStack_injective
    D.code (.control .start) (fun _=>rfl) .divide .clearQuotient rfl
    (SemiprimeD1StackDividerExecution.executionTime (difference a b cached) cached)
    (SemiprimeD1StackDivider.state (some (.control .start)) none none
      (difference a b cached) cached [] [] [] [] [] [] [] [] [])
    (SemiprimeD1StackDivider.state none none none [] [] [] [] [] [] []
      (residue a b cached) (quotient a b cached) [] [])
    (afterCopyDivision a b cached) (afterDivide a b cached)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackDividerExecution.source_run (difference a b cached) cached
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> first | rfl | exact (hk (.inr .input) rfl).elim
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> first | rfl | exact (hk (.inr .divisor) rfl).elim | exact (hk (.inr .remainder) rfl).elim | exact (hk (.inr .quotient) rfl).elim
          · rfl

/-- Actual cell-by-cell quotient erasure; no final workspace reset is assumed. -/
theorem clear_quotient (a b cached : List Bool) :
    Runs program ((quotient a b cached).length+1) .clearQuotient (afterDivide a b cached)
      .done (finalData a b cached) := by
  have h := SemiprimeD1StackPhysicalLoops.drain program .clearQuotient .done
    (divideStack (.inr .quotient)) rfl (finalData a b cached) (quotient a b cached)
  have hi : Function.update (finalData a b cached) (divideStack (.inr .quotient))
      (quotient a b cached)=afterDivide a b cached := by
    funext k
    rcases k with k|k
    · cases k <;> simp [Function.update,divideStack,finalData,afterDivide,store,A.store]
    · rcases k with k|k
      · cases k <;> simp [Function.update,divideStack,finalData,afterDivide,store,A.store]
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;>
            simp [Function.update,divideStack,finalData,afterDivide,store,D.payload]
        · cases k <;> simp [Function.update,divideStack,finalData,afterDivide,store]
  have ho : Function.update (finalData a b cached) (divideStack (.inr .quotient)) []=
      finalData a b cached := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- Total actual clean-halt trace for ALL input bytes, including a zero cache.
Canonical ring semantics are attached separately under original operand guards. -/
theorem source_run (a b cached : List Bool) :
    C.run program (totalTime a b cached) (initial a b cached)=some (done a b cached) := by
  have h1 := runs_trans program _ _ _ _ _ _ _ _ (copy_adder a b cached) (add_call a b cached)
  have h2 := runs_trans program _ _ _ _ _ _ _ _ h1 (subtract_call a b cached)
  have h3 := runs_trans program _ _ _ _ _ _ _ _ h2 (drop_borrow a b cached)
  have h4 := runs_trans program _ _ _ _ _ _ _ _ h3 (copy_division a b cached)
  have h5 := runs_trans program _ _ _ _ _ _ _ _ h4 (divide_call a b cached)
  have h6 := runs_trans program _ _ _ _ _ _ _ _ h5 (clear_quotient a b cached)
  obtain ⟨finish,hfinish,hout⟩ := h6 [] (initial a b cached) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program .done rfl (finalData a b cached) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackResidueSubExecution
