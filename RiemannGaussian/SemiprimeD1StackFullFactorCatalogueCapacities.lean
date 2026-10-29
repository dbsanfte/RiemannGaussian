/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueHistoryBounds
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordRootBounds
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueBounds
import RiemannGaussian.SemiprimePublicBudgetDimensions
/-! # Actual all-factor input and zero-history row capacities
The fixed polynomial is chosen before N. Its exponential uses the genuine
original scope bound, whose fourth power is cubic in binary input width.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueCapacities
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueRows
open SemiprimeD1StackFullFactorCatalogueLoop SemiprimeD1StackFullFactorCatalogueHistoryBounds
open SemiprimeD1BooleanFactorCatalogueIndices (vertex scopeWords key)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
namespace R
export SemiprimeD1StackAllDescriptorRecordRootBounds
  (baseCapacity capacity arityCapacity raw_capacity scope_bytes occurrences_linear timeBound_zero_history timeBound_original)
end R
/-- One fixed coefficient covers the actual initial bytes, queries and row clocks. -/
def coefficient : Nat :=1263*10^20+10^130*(10^21)^18+10^150
/-- Width polynomial for a zero-history row, with no original vertex advice. -/
def polynomial (n:Nat) : Nat :=coefficient*(n+1)^108
/-- Actual exponential row allowance; the original scope exponent is retained explicitly. -/
def rowAllowance (bits:List Bool) : Nat :=polynomial bits.length*2^(R.arityCapacity bits)
/-- Linear bound for the number of original factors, distinct from E and M. -/
def factorAllowance (n:Nat) : Nat :=12800*n
/-- Every lesser fixed width power is covered by the fixed polynomial. -/
theorem power_le (n k:Nat) (hk:k ≤ 108) :(n+1)^k ≤ (n+1)^108:=
  Nat.pow_le_pow_right (by omega) hk
/-- Every original actual factor count fits the actual linear occurrence budget. -/
theorem factor_count_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    factorCount (bitValue bits) ≤ factorAllowance bits.length:=by
  have hf:=SemiprimePublicBudgetDimensions.factorCount_le (bitValue bits) hN
  have hm:=R.occurrences_linear bits hc hN
  have he:=SemiprimeD1StackOwnerLookupOriginal.Public.occurrences_eq (bitValue bits) hN
  change SemiprimeD1BooleanFactorCatalogueIndicesBounds.occurrences (bitValue bits)=
    2*SemiprimePublicAcquiredExecution.wireCount (bitValue bits) at he
  unfold factorAllowance
  omega
/-- The retained N and actual scope words each fit the polynomial without exponential advice. -/
theorem base_le (n:Nat) :10^20*(n+1)^6 ≤ polynomial n:=by
  have hp:=power_le n 6 (by decide)
  have hc:(10:Nat)^20 ≤ coefficient:=by unfold coefficient;omega
  exact Nat.mul_le_mul hc hp
/-- The frozen copy/filter per-factor polynomial fits the same fixed width polynomial. -/
theorem query_polynomial_le (n:Nat) :10^150*(n+1)^35 ≤ polynomial n:=by
  have hc:(10:Nat)^150 ≤ coefficient:=by unfold coefficient;omega
  exact Nat.mul_le_mul hc (power_le n 35 (by decide))
/-- Every cached raw word fits the base capacity from the actual descriptor source. -/
theorem raw_base (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) (i:Fin 6) :
    (DR.rawFields bits (vertex (bitValue bits) f) i).length ≤ R.baseCapacity bits:=by
  have h:=R.raw_capacity bits hc hN f i
  unfold R.baseCapacity
  omega
/-- The actual scope vector fits that same clean input capacity. -/
theorem scope_base (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) :
    (SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits f.val)).length ≤ R.baseCapacity bits:=by
  have h:=R.scope_bytes bits hc hN f
  have hp:=Nat.pow_le_pow_right (show 1 ≤ bits.length+1 by omega) (by decide:2 ≤ 6)
  unfold R.baseCapacity
  omega
/-- All1263 allocated initial roles, including shadows, fit the real zero-history mass cap. -/
theorem input_mass_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) :rowInputMass bits f ≤ 1263*R.baseCapacity bits:=
  SemiprimeD1StackAllDescriptorRecordUniformBounds.mass_clean_bound _ _ [] [] _
    (raw_base bits hc hN f) (scope_base bits hc hN f) (Nat.zero_le _) (Nat.zero_le _)
/-- The real zero-history trace allowance and initial bytes fit one actual row allowance. -/
theorem row_cap_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) :rowCap bits f ≤ rowAllowance bits:=by
  have hm:=input_mass_le bits hc hN f
  have ht:=R.timeBound_zero_history bits hc hN f
  have hp:=power_le bits.length 6 (by decide)
  have hmass:rowInputMass bits f ≤ (1263*10^20)*(bits.length+1)^108:=by
    unfold R.baseCapacity at hm
    nlinarith only [hm,hp]
  have he:1 ≤ (2:Nat)^(R.arityCapacity bits):=Nat.pow_pos (by decide)
  have hmassExp:=Nat.mul_le_mul_left ((1263*10^20)*(bits.length+1)^108) he
  unfold rowCap rowAllowance polynomial coefficient
  nlinarith only [hmass,hmassExp,ht]
/-- Every physical descriptor field is one of the same five actually acquired raw words. -/
theorem descriptor_field_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) (i:Fin 5) :
    (E.vertex (vertex (bitValue bits) f) i).length ≤ 10^15*(bits.length+1)^6:=by
  fin_cases i
  · exact R.raw_capacity bits hc hN f 1
  · exact R.raw_capacity bits hc hN f 2
  · exact R.raw_capacity bits hc hN f 3
  · exact R.raw_capacity bits hc hN f 4
  · exact R.raw_capacity bits hc hN f 5
/-- Actual parsing, raw-field draining, full binary-scope draining and EOF steps are charged. -/
theorem cleanup_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) :
    9*SemiprimeD1StackFullFactorCatalogueFields.mass (E.vertex (vertex (bitValue bits) f))+
      (SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits f.val)).length+50 ≤ polynomial bits.length:=by
  have hm:SemiprimeD1StackFullFactorCatalogueFields.mass (E.vertex (vertex (bitValue bits) f)) ≤
      5*(10^15*(bits.length+1)^6):=by
    unfold SemiprimeD1StackFullFactorCatalogueFields.mass
    calc
      _ ≤ ∑_i:Fin 5,10^15*(bits.length+1)^6:=Finset.sum_le_sum (fun i _=>descriptor_field_le bits hc hN f i)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hs:=R.scope_bytes bits hc hN f
  have h6:=power_le bits.length 6 (by decide)
  have h2:=power_le bits.length 2 (by decide)
  have h1:1 ≤ (bits.length+1)^108:=Nat.pow_pos (by omega)
  have hcst:(45*10^15+10^10+50:Nat) ≤ coefficient:=by unfold coefficient;omega
  unfold polynomial
  nlinarith only [hm,hs,h6,h2,h1,hcst]
/-- The same prepared physical filter is paid from the frozen source's own polynomial. -/
theorem query_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) :
    SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key f.val)+2 ≤ polynomial bits.length:=
  (SemiprimeD1StackBooleanFactorCatalogueBounds.query_le_cap bits hc hN f).trans
    (query_polynomial_le bits.length)
/-- The unchanged actual N-only pair/catalogue acquisition and copy setup is paid once. -/
theorem setup_le (bits:List Bool) :SemiprimeD1StackFullFactorCatalogueSource.setupBound bits ≤ polynomial bits.length:=
  (SemiprimeD1StackBooleanFactorCatalogueBounds.setup_le_cap bits).trans (query_polynomial_le bits.length)
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueCapacities
