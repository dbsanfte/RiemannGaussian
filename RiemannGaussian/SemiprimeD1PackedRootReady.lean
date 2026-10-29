/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedRootFactoryInputs
/-! # One original-input execution supplies the actual marked-root caller boundary
All structural caches, actual NEW record words, matching tensor context and
independently acquired rational width come from the SAME fixed N-only machine.
This is its caller boundary, not a physical contraction or a supplied scalar.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedRootReady
open SemiprimeBitArithmetic (bitValue)
namespace P
export SemiprimeD1StackPackedRootInput (Stack program initial output width rationalWidth originalInput)
export SemiprimeD1StackPackedRootInputEncoding (done)
export SemiprimeD1StackPackedRootInputBounds (runBound)
end P
/-- Exact reached-word specification only; no proof field or semantic getter inhabits runtime control. -/
structure Ready (bits : List Bool) (hN : 0<bitValue bits) : Prop where
  /-- ALL154 literal structural cache words have the actual marked-network meaning. -/
  source : ∀k : SemiprimeD1StackSourceSelectionAcquire.Stack,
    (P.done bits hN).data (SemiprimeD1PackedRootCaches.sourceStack k)=
      SemiprimeD1StackSourceSelectionAcquireEncoding.result
        (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
        (SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits) k
  /-- Every original chronological placement, including repeated occurrences, is available. -/
  placements : (P.done bits hN).data SemiprimeD1PackedRootCaches.placements=
    SemiprimeD1TensorTapeCodec.vectorBits
      ((SemiprimeD1PackedNetworkTopology.inventory
        (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
        (SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits)).1.map
          SemiprimeD1StackPacketInventoryEncoding.placementBytes)
  /-- The actual observed packet bytes retain first-discovery order. -/
  packets : (P.done bits hN).data SemiprimeD1PackedRootCaches.packets=
    SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1PackedNetworkTopology.inventory
        (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
        (SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits)).2
  /-- Table readers must consume this actually acquired NEW record operand. -/
  records : (P.done bits hN).data P.output=SemiprimeD1StackVertexProduct.records
    (SemiprimeD1TensorNetwork.vertices
      (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN))
  /-- The same N physically supplies its matching empty-axis2ell context. -/
  context : SemiprimeD1StackPackedRootInputOriginal.acquiredContext bits hN=
    ⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩
  /-- The actual TRUE tensor width corresponds to the NEW precision. -/
  tensorWidth : (P.done bits hN).data P.width=
    List.replicate (SemiprimeD1PackedMomentPrecision.precision (bitValue bits)) true
  /-- The rational FALSE template is acquired from a/M, independently of tensor precision. -/
  rationalWidth : (P.done bits hN).data P.rationalWidth=List.replicate
    (SemiprimeD1RecoveryNodeBits.width (SemiprimeD1StackRecoveryWidthOriginal.originalA bits)
      (SemiprimeD1StackRecoveryWidthOriginal.originalM bits)) false
  /-- Original N is physically retained at the exact same halt. -/
  number : (P.done bits hN).data P.originalInput=bits
/-- Every caller requirement is internally discharged for every canonical positive original N. -/
theorem ready_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) : Ready bits hN :=
  ⟨SemiprimeD1PackedRootCaches.source_original bits hN,
    SemiprimeD1PackedRootCaches.placements_original bits hN,
    SemiprimeD1PackedRootCaches.packets_original bits hN,
    SemiprimeD1StackPackedRootInputOriginal.output_original bits hc hN,
    SemiprimeD1StackPackedRootInputOriginal.context_original bits hc hN,
    SemiprimeD1StackPackedRootInputOriginal.width_original bits hc hN,
    SemiprimeD1StackPackedRootInputOriginal.rational_width_original bits hN,
    SemiprimeD1StackPackedRootInputOriginal.retained_N bits hN⟩
/-- SAME actual N-only source and its OWN physical clock supply the complete useful root boundary. -/
theorem source_ready (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    ∃t ≤ P.runBound bits,SemiprimeD1StackCalls.run P.program t (P.initial bits)=
      some (P.done bits hN) ∧ Ready bits hN := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackPackedRootInputBounds.source_run_bounded bits hc hN
  exact ⟨t,ht,hr,ready_original bits hc hN⟩
/-- Fixed constants precede the WHOLE original input family; structural reinterpretation adds no call. -/
theorem uniform_source_ready : ∃A d : ℕ,∀(bits : List Bool)
    (_hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits),
    ∃t ≤ A*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^d*
      2^(114000*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run P.program t (P.initial bits)=some (P.done bits hN) ∧ Ready bits hN := by
  obtain ⟨a,d,ha⟩ := SemiprimeD1StackPackedRootInputOriginal.uniform_original
  refine ⟨a,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr,_,_⟩ := ha bits hc hN
  exact ⟨t,ht,hr,ready_original bits hc hN⟩
end RiemannGaussian.SemiprimeD1PackedRootReady
