/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsExecution
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsByteCost
import RiemannGaussian.SemiprimeD1StackVertexCatalogueBounds
/-! # Own fixed physical-byte polynomial and original-family scope rate
All source byte caps below come from their SAME actual halted executions.
The old1804 clock pays only that real old call; no native report is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsBounds
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsExecution
open SemiprimeD1StackMarkedRootRecordsEncoding SemiprimeD1StackMarkedRootRecordsAlignment
open SemiprimeD1StackMarkedRootRecordsAcquisition SemiprimeD1StackMarkedRootRecordsLoop
open SemiprimeD1StackMarkedRootRecordsByteCost
open SemiprimeBitArithmetic (bitValue)
namespace RB
export SemiprimeD1StackRootNetworkRecordsBounds (runBound prefixPolynomial)
end RB
/-- Common actual ordered local-arity cap before every original descriptor. -/
def scopeCap (bits : List Bool) : Nat := SemiprimeMacroParameters.scopeBound bits.length
/-- One fixed width polynomial before all original inputs. -/
def widthPolynomial (n : Nat) : Nat := 100*(n+RB.prefixPolynomial n 1+10^13*(n+1)^5+2)
/-- Physical source/input byte cap, acquired by the actual old source and new catalogue. -/
def capacity (bits : List Bool) : Nat := widthPolynomial bits.length*2^(19*scopeCap bits)
/-- Final own whole source cap; exponent58 pays the cubic physical-byte envelope. -/
def runBound (bits : List Bool) : Nat := 10^28*(widthPolynomial bits.length)^3*2^(58*scopeCap bits)
/-- All real retained old-source words are paid by the actual1804 call. -/
theorem retained_length (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (k : R.Stack) : (retained bits hN k).length ≤ bits.length+RB.runBound bits := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackRootNetworkRecordsBounds.source_run_bounded bits hc hN
  have hd := SemiprimeD1StackReturnLink.run_data_bound R.program t bits.length _ _
    (SemiprimeD1StackRootNetworkRecordsResources.initial_length bits) hr
  exact (hd k).trans (Nat.add_le_add_left ht bits.length)
/-- The actual fresh descriptor stream is paid by its full real53-source trace. -/
theorem descriptor_length (bits : List Bool) (hb : bits≠[]) :
    (descriptorBytes bits).length ≤ bits.length+VE.budget bits := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackVertexCatalogueExecution.source_run bits hb
  have hi (k : V.Stack) : ((SemiprimeD1StackVertexCatalogue.initial bits).data k).length ≤ bits.length := by
    change (SemiprimeD1StackVertexCatalogue.input bits k).length ≤ bits.length
    rw [catalogue_input_only]
    by_cases h : k=V.originalInput <;> simp [h]
  have hd := SemiprimeD1StackReturnLink.run_data_bound V.program t bits.length _ _ hi hr
  exact (hd (V.kernelStack (SemiprimeD1StackCartesian4.aux 2))).trans (Nat.add_le_add_left ht bits.length)
/-- Pure capacity arithmetic: actual metadata/catalogue costs are not substituted into control. -/
theorem capacity_lower (bits : List Bool) (hb : bits≠[]) :
    100*(bits.length+RB.runBound bits+VE.budget bits+2) ≤ capacity bits := by
  have hv := SemiprimeD1StackVertexCatalogueBounds.budget_le bits hb
  have he : 1 ≤ (2:Nat)^(19*scopeCap bits) := Nat.one_le_pow _ _ (by decide)
  have hn := Nat.le_mul_of_pos_right bits.length (by positivity : 0 < (2:Nat)^(19*scopeCap bits))
  have hv0 := Nat.le_mul_of_pos_right (10^13*(bits.length+1)^5) (by positivity : 0 < (2:Nat)^(19*scopeCap bits))
  have h2 := Nat.le_mul_of_pos_right 2 (by positivity : 0 < (2:Nat)^(19*scopeCap bits))
  unfold capacity widthPolynomial RB.runBound SemiprimeD1StackRootNetworkRecordsBounds.runBoundPrefix
  change 100*(bits.length+RB.prefixPolynomial bits.length 1*2^(19*scopeCap bits)+VE.budget bits+2) ≤ _
  nlinarith only [hv,hn,hv0,h2]
/-- The actual old owner payload remains paid even after dropping its final FALSE marker. -/
theorem owners_length (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    (owners bits hN).length ≤ bits.length+RB.runBound bits := by
  have h := retained_length bits hc hN (R.ownerStack SemiprimeD1StackOwnerRecords.output)
  change (owners bits hN++[false]).length ≤ _ at h
  simp only [List.length_append,List.length_cons,List.length_nil] at h
  omega
/-- The real paired-loop byte radius is bounded by the actual source-acquired input bytes. -/
theorem resource_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    resource bits (rows bits hN) ≤ capacity bits := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact Nat.lt_irrefl _ hN
  have hf := retained_length bits hc hN (R.factorStack SemiprimeD1StackFullFactorCatalogue.output)
  have hd := descriptor_length bits hb
  have hc0 := capacity_lower bits hb
  have hfe := factor_cache bits hc hN
  have hde := descriptor_cache bits hc hN
  have hf0 : (oldRecords (rows bits hN)).length ≤ bits.length+RB.runBound bits :=
    (congrArg List.length hfe).symm.trans_le hf
  have hd0 : (descriptors (rows bits hN)).length ≤ bits.length+VE.budget bits :=
    (congrArg List.length hde).symm.trans_le hd
  unfold resource
  omega
/-- Every actual unary-port field count is the old original finite factor arity. -/
theorem rows_arity (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∀ row∈rows bits hN,row.scope.length ≤ scopeCap bits := by
  intro row hr
  obtain ⟨f,_,rfl⟩ := List.mem_map.mp hr
  change ((SemiprimeD1BooleanFactorCatalogueIndicesOriginal.numericPorts (bitValue bits) f).map
    (fun p => List.replicate p true)).length ≤ scopeCap bits
  rw [List.length_map,SemiprimeD1BooleanFactorCatalogueIndicesOriginal.numericPorts_length]
  have h := SemiprimePublicAcquiredExecution.indexedArity_le (bitValue bits) f
  exact h.trans_eq (congrArg SemiprimeMacroParameters.scopeBound
    (SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc).symm)
/-- SAME real setup bound is paid by the capacity, including all preserved copies. -/
theorem setupBudget_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    setupBudget (retained bits hN) bits ≤ capacity bits := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact Nat.lt_irrefl _ hN
  have hf := retained_length bits hc hN (R.factorStack SemiprimeD1StackFullFactorCatalogue.output)
  have hd := descriptor_length bits hb
  have hcap := capacity_lower bits hb
  unfold setupBudget
  omega
/-- The actual whole clock is bounded by a fixed cubic of paid bytes per maximal actual scope. -/
theorem timeBound_capacity (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    timeBound bits hN ≤ 10^28*(capacity bits)^3*2^(scopeCap bits) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact Nat.lt_irrefl _ hN
  have hcap := capacity_lower bits hb
  have hR : 2 ≤ capacity bits := by omega
  have hroot := SemiprimeD1StackRootNetworkRecordsBounds.timeBound_le bits hc hN
  have hsetup := setupBudget_le bits hc hN
  have howner := owners_length bits hc hN
  have hsum := sum_rowBudget_le bits (rows bits hN) hb (capacity bits) (scopeCap bits)
    (fun row hr => (radius_le bits (rows bits hN) row hr).trans (resource_le bits hc hN)) (rows_arity bits hc hN)
  have hn : (rows bits hN).length ≤ capacity bits :=
    (rows_count (rows bits hN)).trans (by have h := resource_le bits hc hN;unfold resource at h;omega)
  have hs := Nat.mul_le_mul_right (10^26*(capacity bits)^2*2^(scopeCap bits)) hn
  have hout := payload_length bits (rows bits hN)
  have hP : capacity bits ≤ 10^26*(capacity bits)^3*2^(scopeCap bits) := by
    have he : 1 ≤ (2:Nat)^(scopeCap bits) := Nat.one_le_pow _ _ (by decide)
    have hpow : capacity bits ≤ (capacity bits)^3 := Nat.le_pow (by decide : 0 < (3:Nat))
    nlinarith
  have hpoly : 1 ≤ 10^26*(capacity bits)^3*2^(scopeCap bits) := by omega
  have htimes : capacity bits*(10^26*(capacity bits)^2*2^(scopeCap bits))=
      10^26*(capacity bits)^3*2^(scopeCap bits) := by ring
  rw [htimes] at hs
  unfold timeBound readyBound loopBudget
  rw [show 10^28*(capacity bits)^3*2^(scopeCap bits)=100*(10^26*(capacity bits)^3*2^(scopeCap bits)) by ring]
  omega
/-- Exact exponent join for this source's paid cubic byte envelope. -/
theorem scope_cube (B : Nat) : ((2:Nat)^(19*B))^3*2^B=2^(58*B) := by
  rw [←pow_mul,←pow_add]
  congr 1
  omega
/-- Fixed original-family polynomial times scope exponential for the SAME whole source. -/
theorem timeBound_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    timeBound bits hN ≤ runBound bits := by
  have h := timeBound_capacity bits hc hN
  unfold capacity at h
  rw [mul_pow] at h
  have he : 10^28*((widthPolynomial bits.length)^3*(2^(19*scopeCap bits))^3)*2^(scopeCap bits)=runBound bits := by
    unfold runBound
    rw [Nat.mul_assoc,Nat.mul_assoc,scope_cube]
    ring
  exact h.trans_eq he
/-- Complete actual source with the fixed own scope-rate budget, not an old native report. -/
theorem source_run_bounded (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t ≤ runBound bits,C.run program t (initial bits)=some (done bits hN) := by
  obtain ⟨t,ht,hr⟩ := source_run bits hc hN
  exact ⟨t,ht.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsBounds
