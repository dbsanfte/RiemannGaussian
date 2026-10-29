/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeBinaryFactorExecution
import RiemannGaussian.SemiprimeD1PublicRecoveryBudget

/-! # Exact public report aggregation for the tape-backed binary execution
The prefix budget in internal composition refers to this actual closed program.
No count/backend supplier is a runtime input and no old query clock is reused.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapePublicReport
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic SemiprimeBitDivision
attribute [local irreducible] SemiprimeD1WordTapePublicSearch.search
  SemiprimeD1PhysicalPublicSearch.search SemiprimeD1PublicOperandBits.run
  SemiprimeD1FactorValidationBits.run

/-- Sum the actual retained fields from one cached binary-execution report. -/
def work (input : List Bool) : ℕ :=
  let out:=SemiprimeD1WordTapeBinaryFactorExecution.run input
  out.queryWork+out.arithmeticClock+out.metadataWork

/-- The binary endpoint retains exactly the actually executed search query sum. -/
theorem run_queryWork_eq (input : List Bool) (hN : 0<bitValue input) :
    (SemiprimeD1WordTapeBinaryFactorExecution.run input).queryWork=
      ((SemiprimeD1WordTapePublicSearch.queriedPrefixes (bitValue input) hN).map
        (fun fixed => (SemiprimeD1WordTapePublicCounter.prefixRun (bitValue input) hN fixed).clock)).sum := by
  have hz:=(nonzeroBits_correct input).mpr hN
  have he:=SemiprimeD1WordTapePublicSearch.search_queryWork_eq (bitValue input) hN
  dsimp only [SemiprimeD1WordTapeBinaryFactorExecution.run]
  rw [dite_eq_left hz]
  split <;> exact he

/-- Internal uniform-prefix composition counts every actual repeated acquisition. -/
theorem run_queryWork (input : List Bool) (hN : 0<bitValue input) (C : ℕ)
    (hC : ∀ fixed : List (Fin (wireCount (bitValue input))×Bool),
      fixed.length ≤ wireCount (bitValue input) →
      (SemiprimeD1WordTapePublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ C) :
    (SemiprimeD1WordTapeBinaryFactorExecution.run input).queryWork ≤
      (wireCount (bitValue input)+1)*C := by
  have hz:=(nonzeroBits_correct input).mpr hN
  have hs:=SemiprimeD1WordTapePublicSearch.search_queryWork (bitValue input) hN C hC
  dsimp only [SemiprimeD1WordTapeBinaryFactorExecution.run]
  rw [dite_eq_left hz]
  split <;> exact hs

/-- The final physical factor bytes are preserved literally on every input. -/
theorem run_factors_eq_physical (input : List Bool) :
    (SemiprimeD1WordTapeBinaryFactorExecution.run input).factors=
      (SemiprimeD1BinaryFactorExecution.run input).factors := by
  by_cases hz : (nonzeroBits input).nonzero=true
  · have hN:=(nonzeroBits_correct input).mp hz
    have hv:=congrArg SemiprimeCountRecovery.SearchResult.values
      (SemiprimeD1WordTapePublicSearch.search_result_eq_physical (bitValue input) hN)
    dsimp only [SemiprimeD1WordTapeBinaryFactorExecution.run,SemiprimeD1BinaryFactorExecution.run]
    simp only [dite_eq_left hz]
    rw [hv]
    cases (SemiprimeD1PhysicalPublicSearch.search (bitValue input) hN).result.values <;> rfl
  · simp only [SemiprimeD1WordTapeBinaryFactorExecution.run,SemiprimeD1BinaryFactorExecution.run,dite_eq_right hz]

/-- Only unchanged decoder/validation/control reports agree after exact branch
and metadata refinement. Changed query and recursion reports are excluded. -/
theorem run_local_eq (input : List Bool) :
    (SemiprimeD1WordTapeBinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1WordTapeBinaryFactorExecution.run input).metadataWork=
    (SemiprimeD1BinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1BinaryFactorExecution.run input).metadataWork := by
  by_cases hz : (nonzeroBits input).nonzero=true
  · have hN:=(nonzeroBits_correct input).mp hz
    have hv:=congrArg SemiprimeCountRecovery.SearchResult.values
      (SemiprimeD1WordTapePublicSearch.search_result_eq_physical (bitValue input) hN)
    have hm:=SemiprimeD1WordTapePublicSearch.search_metadata_eq_physical (bitValue input) hN
    dsimp only [SemiprimeD1WordTapeBinaryFactorExecution.run,SemiprimeD1BinaryFactorExecution.run]
    simp only [dite_eq_left hz]
    rw [hv,hm]
    cases (SemiprimeD1PhysicalPublicSearch.search (bitValue input) hN).result.values <;> rfl
  · simp only [SemiprimeD1WordTapeBinaryFactorExecution.run,SemiprimeD1BinaryFactorExecution.run,dite_eq_right hz]

/-- Physical decoding and proper-divisor/cofactor validation have the original
proved polynomial budget because their actual inputs and operations agree. -/
theorem run_local_work (input : List Bool) (hc : SemiprimeSourceCompactBits.Compact input)
    (hN : 0<bitValue input) :
    (SemiprimeD1WordTapeBinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1WordTapeBinaryFactorExecution.run input).metadataWork ≤
        SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)) := by
  rw [run_local_eq]
  exact SemiprimeD1PublicRecoveryBudget.run_local_work input hc hN

/-- Actual new public report from a derived uniform actual-prefix bound. -/
theorem work_le (input : List Bool) (hc : SemiprimeSourceCompactBits.Compact input)
    (hN : 0<bitValue input) (C : ℕ)
    (hC : ∀ fixed : List (Fin (wireCount (bitValue input))×Bool),
      fixed.length ≤ wireCount (bitValue input) →
      (SemiprimeD1WordTapePublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ C) :
    work input ≤ (wireCount (bitValue input)+1)*C+
      SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)) := by
  have hq:=run_queryWork input hN C hC
  have hl:=run_local_work input hc hN
  unfold work
  dsimp only
  omega

/-- Fixed recovery constants precede the complete original-input family. The
remaining premise is internal actual-prefix composition, not a runtime oracle. -/
theorem exists_original_join : ∃ C₀ k : ℕ,∀ input : List Bool,
    SemiprimeSourceCompactBits.Compact input → ∀ hN : 0<bitValue input,∀ C : ℕ,
    (∀ fixed : List (Fin (wireCount (bitValue input))×Bool),
      fixed.length ≤ wireCount (bitValue input) →
      (SemiprimeD1WordTapePublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ C) →
    work input ≤ (wireCount (bitValue input)+1)*C+
      C₀*(SemiprimeMacroParameters.bitLength (bitValue input)+1)^k := by
  obtain ⟨C₀,k,hlocal⟩:=SemiprimeD1PublicRecoveryBudget.exists_original_local_work
  refine ⟨C₀,k,?_⟩
  intro input hc hN C hC
  have hq:=run_queryWork input hN C hC
  have hl:=hlocal input hc hN
  rw [←run_local_eq input] at hl
  unfold work
  dsimp only
  omega

end RiemannGaussian.SemiprimeD1WordTapePublicReport
