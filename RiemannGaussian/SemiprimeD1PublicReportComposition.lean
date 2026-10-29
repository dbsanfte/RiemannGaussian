/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PublicRecoveryBudget

/-! # Exact public contribution split for the actual binary factor execution
This joins the new byte-producing public path to its own actual prefix reports.
An internal uniform-prefix inequality is a proof-composition premise; the later
whole-family theorem must derive it from this counter's acquired recursion.
No such bound or count function is an argument of the executed algorithm.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PublicReportComposition
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic SemiprimeBitDivision
attribute [local irreducible] SemiprimeD1PhysicalPublicSearch.search
  SemiprimeD1PublicOperandBits.run SemiprimeD1FactorValidationBits.run

/-- The exact sum of all retained fields of this binary execution. This is
still a mixed component report, not an asserted primitive-machine clock. -/
def work (input : List Bool) : ℕ :=
  (SemiprimeD1BinaryFactorExecution.run input).queryWork+
    (SemiprimeD1BinaryFactorExecution.run input).arithmeticClock+
    (SemiprimeD1BinaryFactorExecution.run input).metadataWork

/-- Every actual prefix acquisition and recursive report is retained by the
same byte-producing program, on every executed search/validation branch. -/
theorem run_queryWork (input : List Bool) (hN : 0 < bitValue input) (C : ℕ)
    (hC : ∀ fixed : List (Fin (wireCount (bitValue input)) × Bool),
      fixed.length ≤ wireCount (bitValue input) →
      (SemiprimeD1PhysicalPublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ C) :
    (SemiprimeD1BinaryFactorExecution.run input).queryWork ≤
      (wireCount (bitValue input)+1)*C := by
  have hz := (nonzeroBits_correct input).mpr hN
  have hs := SemiprimeD1PhysicalPublicSearch.search_queryWork (bitValue input) hN C hC
  dsimp only [SemiprimeD1BinaryFactorExecution.run]
  rw [dite_eq_left hz]
  split <;> exact hs

/-- Internal original-input full-report join. The sole remaining prefix budget
premise refers to the ACTUAL closed public prefix program, never an oracle. -/
theorem work_le (input : List Bool) (hc : SemiprimeSourceCompactBits.Compact input)
    (hN : 0 < bitValue input) (C : ℕ)
    (hC : ∀ fixed : List (Fin (wireCount (bitValue input)) × Bool),
      fixed.length ≤ wireCount (bitValue input) →
      (SemiprimeD1PhysicalPublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ C) :
    work input ≤ (wireCount (bitValue input)+1)*C+
      SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)) := by
  have hq := run_queryWork input hN C hC
  have hl := SemiprimeD1PublicRecoveryBudget.run_local_work input hc hN
  unfold work
  omega

/-- Fixed polynomial recovery constants precede the complete original-input
family; only the actual uniform prefix-run report remains to be supplied by
the recursive cost theorem. No extra target logarithm is lost in recovery. -/
theorem exists_original_join : ∃ C₀ k : ℕ,∀ input : List Bool,
    SemiprimeSourceCompactBits.Compact input → ∀ hN : 0 < bitValue input,∀ C : ℕ,
    (∀ fixed : List (Fin (wireCount (bitValue input)) × Bool),
      fixed.length ≤ wireCount (bitValue input) →
      (SemiprimeD1PhysicalPublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ C) →
    work input ≤ (wireCount (bitValue input)+1)*C+
      C₀*(SemiprimeMacroParameters.bitLength (bitValue input)+1)^k := by
  obtain ⟨C₀,k,hlocal⟩ := SemiprimeD1PublicRecoveryBudget.exists_original_local_work
  refine ⟨C₀,k,?_⟩
  intro input hc hN C hC
  have hq := run_queryWork input hN C hC
  have hl := hlocal input hc hN
  unfold work
  omega

end RiemannGaussian.SemiprimeD1PublicReportComposition
