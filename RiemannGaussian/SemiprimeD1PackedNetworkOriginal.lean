/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedNetworkOwners
import RiemannGaussian.SemiprimeD1PackedNetworkFactors
import RiemannGaussian.SemiprimeD1PackedNetworkReindex
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsOriginal
import RiemannGaussian.SemiprimeD1WordTapeRecursiveCounter
import RiemannGaussian.SemiprimeD1PackedMomentRecovery
/-! # The actual acquired marked root has the exact packed factor moment
All natural owner and marked-factor entry premises are discharged. The final
root reduction alone cancels higher moments. The native recursive counter's
semantic equality is included, without transporting its clock to a primitive
machine. Actual whole-counter acquisition/runtime remains a separate join.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkOriginal
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeD1PackedNetworkSemantics
open SemiprimeD1StackMarkedRootRecordsNetwork (network)
open SemiprimeD1PackedMomentPrecision (precision)
open SemiprimeD1RootScalar SemiprimeD1JetInterpretation
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
/-- The FULL natural contraction of the actual named marked network is the original indexed one. -/
theorem contraction (N : ℕ) (hN : 0<N) :
    naturalContraction (network N hN)=SemiprimeD1PackedNetworkReindex.full N hN := by
  rw [SemiprimeD1PackedNetworkOwners.eliminate]
  exact Finset.sum_congr rfl (fun bits _ => SemiprimeD1PackedNetworkFactors.right_consistent N hN bits)
/-- The actual marked leaf's decoded2ell-bit scalar is exactly the packed count and factor sum. -/
theorem leaf_value (N : ℕ) (hN : 0<N) :
    (scalar (interpret ⟨[],precision N⟩
      (SemiprimeD1TensorNetwork.leaf ⟨[],precision N⟩ (network N hN)).words)).val=
        SemiprimeD1PackedMomentSemiprime.packedValue N hN := by
  rw [leaf_scalar,contraction]
  exact SemiprimeD1PackedNetworkReindex.packed_value N hN
/-- The already specified native recursive counter has the SAME useful scalar.
This is semantic equality only; it supplies no finite-machine runtime theorem. -/
theorem counter_value (s fuel depth N : ℕ) (hN : 0<N) :
    (scalar (interpret ⟨[],precision N⟩
      (SemiprimeD1WordTapeRecursiveCounter.run s fuel depth ⟨[],precision N⟩ (network N hN)).words)).val=
        SemiprimeD1PackedMomentSemiprime.packedValue N hN := by
  rw [SemiprimeD1WordTapeRecursiveCounter.run_words_eq_leaf s fuel depth _ _
    (by simp [SemiprimeD1JetAxes.Context.Positive])
    (SemiprimeD1StackMarkedRootRecordsTopology.wellFormed N hN)
    (SemiprimeD1StackMarkedRootRecordsTopology.good N hN)]
  exact leaf_value N hN
/-- Every semiprime's actual marked root scalar has exact count and factor-sum channels. -/
theorem semiprime_readout (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    let hN:=Nat.mul_pos hp.pos hq.pos
    let value:=(scalar (interpret ⟨[],precision (p*q)⟩
      (SemiprimeD1TensorNetwork.leaf ⟨[],precision (p*q)⟩ (network (p*q) hN)).words)).val
    value%2^SemiprimeMacroParameters.bitLength (p*q)=(if p=q then 1 else 2) ∧
      value/2^SemiprimeMacroParameters.bitLength (p*q)=(if p=q then p else p+q) := by
  dsimp only
  rw [leaf_value]
  exact SemiprimeD1PackedMomentSemiprime.readout p q hp hq
/-- Original-binary acquisition emits exactly the network whose scalar identity is proved here.
Only acquisition of those records is timed; the physical contraction caller is still required. -/
theorem source_records (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    ∃ t ≤ SemiprimeD1StackMarkedRootRecordsBounds.runBound bits,
      SemiprimeD1StackCalls.run SemiprimeD1StackMarkedRootRecords.program t
        (SemiprimeD1StackMarkedRootRecords.initial bits)=
          some (SemiprimeD1StackMarkedRootRecordsExecution.done bits hN) ∧
      (SemiprimeD1StackMarkedRootRecordsExecution.done bits hN).data
        (SemiprimeD1StackMarkedRootRecords.aux .output)=SemiprimeD1StackVertexProduct.records
          (SemiprimeD1TensorNetwork.vertices (network (SemiprimeBitArithmetic.bitValue bits) hN)) ∧
      (naturalContraction (network (SemiprimeBitArithmetic.bitValue bits) hN) :
        ZMod (2^precision (SemiprimeBitArithmetic.bitValue bits))).val=
          SemiprimeD1PackedMomentSemiprime.packedValue (SemiprimeBitArithmetic.bitValue bits) hN := by
  obtain ⟨t,ht,hr,ho⟩:=SemiprimeD1StackMarkedRootRecordsOriginal.source_original bits hc hN
  refine ⟨t,ht,hr,ho,?_⟩
  rw [contraction]
  exact SemiprimeD1PackedNetworkReindex.packed_value _ hN
end RiemannGaussian.SemiprimeD1PackedNetworkOriginal
