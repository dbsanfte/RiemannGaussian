/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryFactorExecution
import RiemannGaussian.SemiprimeD1CanonicalInput
import RiemannGaussian.SemiprimeD1RootStateResources
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Closed original-input polynomial of search and final factor recovery
The actual byte-producing execution retains every query separately. Its OTHER
physical arithmetic and native index/label/control reports have one fixed
polynomial bound in original input length. Native reports are still reports;
this does not assert a complete host/heap/address/tape bit simulation.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PublicRecoveryBudget
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimePublicBudgetDimensions SemiprimeBitArithmetic SemiprimeBitDivision
attribute [local irreducible] SemiprimeD1PhysicalPublicSearch.search
  SemiprimeD1PublicOperandBits.run SemiprimeD1FactorValidationBits.run
  SemiprimeD1PhysicalPublicCounter.prefixCount

/-- Fixed maximum operand width from actual digit and transform dimensions. -/
def operandWidth (n : ℕ) : ℕ := 64*n*(128*n+2)

/-- Fixed physical shift/add polynomial of the actual operand assembly. -/
def operandArithmetic (n : ℕ) : ℕ :=
  20*(64*n+1)^2*(128*n+2)+3*(64*n)+3*(64*n+1)+1

/-- Original typed label/index reports for at most n selected labels. -/
def operandMetadata (n : ℕ) : ℕ :=
  64*n*((64*n+1)*(8*n+9)+3)+10*(n+64*n+64*n+1)^2

/-- Closed actual operand widths and BOTH executed report contributions,
using the original public dimensions rather than supplied decoder resources. -/
theorem operand_bounds (N : ℕ) (hN : 0 < N) (values : List (Fin (wireCount N) × Bool))
    (side : Fin 2) (hv : values.length ≤ wireCount N) :
    (SemiprimeD1PublicOperandBits.run N values side).bits.length ≤ operandWidth (wireCount N) ∧
    (SemiprimeD1PublicOperandBits.run N values side).arithmeticClock ≤ operandArithmetic (wireCount N) ∧
    (SemiprimeD1PublicOperandBits.run N values side).metadataWork ≤ operandMetadata (wireCount N) := by
  have ht := transform_le N hN
  obtain ⟨hd,hr⟩ := digit_radix_le N hN
  have hw := SemiprimeD1PublicOperandBits.run_width N values side
  have ha := SemiprimeD1PublicOperandBits.run_arithmeticClock N values side
  have hm := SemiprimeD1PublicOperandBits.run_metadataWork N values side
  rw [axes_product] at hw ha hm
  refine ⟨hw.trans ?_,ha.trans ?_,hm.trans ?_⟩
  · unfold operandWidth
    calc
      _ ≤ 64*wireCount N*(64*wireCount N+64*wireCount N+2) := by gcongr
      _ = _ := by ring
  · unfold operandArithmetic
    calc
      _ ≤ 20*(64*wireCount N+1)^2*(64*wireCount N+64*wireCount N+2)+
          3*(64*wireCount N)+3*(64*wireCount N+1)+1 := by gcongr
      _ = _ := by ring
  · unfold operandMetadata
    calc
      _ ≤ 64*wireCount N*((64*wireCount N+1)*(2*wireCount N+6*wireCount N+9)+3)+
          10*(wireCount N+64*wireCount N+64*wireCount N+1)^2 := by gcongr
      _ = _ := by ring

/-- Every successful actual search result contains exactly the original number
of labels, even before any semantic correctness premise about its counts. -/
theorem search_values_length (N : ℕ) (hN : 0 < N) (values : List (Fin (wireCount N) × Bool))
    (h : (SemiprimeD1PhysicalPublicSearch.search N hN).result.values=some values) :
    values.length=wireCount N := by
  have hs : (SemiprimeD1PhysicalPublicCounter.search N hN).values=some values :=
    (congrArg SemiprimeCountRecovery.SearchResult.values
      (SemiprimeD1PhysicalPublicSearch.search_spec N hN)).symm.trans h
  unfold SemiprimeD1PhysicalPublicCounter.search SemiprimeCountRecovery.search at hs
  split at hs
  · cases hs
    have hi := SemiprimeCountRecovery.select_indices (SemiprimeD1PhysicalPublicCounter.prefixCount N hN)
      (List.finRange (wireCount N)) []
    simpa only [List.length_map,List.length_finRange] using congrArg List.length hi
  · cases hs

/-- Actual maximum word width for input-versus-operand validation. -/
def validationWidth (n : ℕ) : ℕ := operandWidth n+n+2

/-- All work other than prefix counter runs, keeping native and physical
reports in the SAME explicit polynomial rather than silently omitting either. -/
def localBudget (n : ℕ) : ℕ :=
  3*n+1+operandArithmetic n+100*(validationWidth n+1)^2+7+
    (n+2)*60*(n+1)+operandMetadata n+10*(3*n+1)

/-- Entire actual final recovery/search overhead, uniformly over positive
canonical original binary inputs and every executed search branch. -/
theorem run_local_work (input : List Bool) (hcanonical : SemiprimeSourceCompactBits.Compact input)
    (hN : 0 < bitValue input) :
    (SemiprimeD1BinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1BinaryFactorExecution.run input).metadataWork ≤ localBudget (wireCount (bitValue input)) := by
  let N := bitValue input
  have hz := (nonzeroBits_correct input).mpr hN
  have hlen : input.length ≤ wireCount N :=
    (SemiprimeD1CanonicalInput.compact_length input hcanonical).trans_le (bitLength_le N hN)
  have hi := nonzeroBits_cost input
  have hs := SemiprimeD1PhysicalPublicSearch.search_metadataWork N hN
  dsimp only [SemiprimeD1BinaryFactorExecution.run]
  rw [dite_eq_left hz]
  cases hv : (SemiprimeD1PhysicalPublicSearch.search N hN).result.values with
  | none =>
    dsimp only
    unfold localBudget
    nlinarith
  | some values =>
    dsimp only
    have hlabels := search_values_length N hN values hv
    have ho := operand_bounds N hN values 0 hlabels.le
    have hcheck := SemiprimeD1FactorValidationBits.run_clock input
      (SemiprimeD1PublicOperandBits.run N values 0).bits (validationWidth (wireCount N))
      (by unfold validationWidth;omega) (by unfold validationWidth;omega)
      (by unfold validationWidth;omega)
    unfold localBudget
    rw [hlabels]
    nlinarith

/-- This concrete recovery polynomial is monotone; no arbitrary polynomial is
substituted for the actual executed reports. -/
theorem localBudget_mono {n m : ℕ} (h : n ≤ m) : localBudget n ≤ localBudget m := by
  unfold localBudget validationWidth operandArithmetic operandMetadata operandWidth
  gcongr

/-- Fixed monomial witnesses for the actual original binary length, before all N. -/
theorem original_monomial : ∃ C k : ℕ,∀ ell,
    localBudget (SemiprimeD1PublicPackingReady.scale ell) ≤ C*(ell+1)^k := by
  change SemiprimeReportPolynomialGrowth.Bound
    (fun ell => localBudget (SemiprimeD1PublicPackingReady.scale ell))
  unfold localBudget validationWidth operandArithmetic operandMetadata operandWidth
    SemiprimeD1PublicPackingReady.scale
  boundArithmetic

/-- CLOSED whole-family polynomial contribution of actual search controls,
operand reconstruction, validation and cofactor extraction. Query work remains
separate and fully retained; native host/address lowering is still required. -/
theorem exists_original_local_work : ∃ C k : ℕ,∀ input : List Bool,
    SemiprimeSourceCompactBits.Compact input → 0 < bitValue input →
    (SemiprimeD1BinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1BinaryFactorExecution.run input).metadataWork ≤
        C*(SemiprimeMacroParameters.bitLength (bitValue input)+1)^k := by
  obtain ⟨C,k,hC⟩ := original_monomial
  refine ⟨C,k,?_⟩
  intro input hc hN
  have hm := SemiprimeD1RootStateResources.root_edges_le_scale (bitValue input) hN []
  rw [SemiprimeD1RootStateResources.root_edges] at hm
  have hn : wireCount (bitValue input) ≤
      SemiprimeD1PublicPackingReady.scale (bitLength (bitValue input)) := by omega
  exact (run_local_work input hc hN).trans ((localBudget_mono hn).trans (hC _))

end RiemannGaussian.SemiprimeD1PublicRecoveryBudget
