/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
/-! # Actual closed source calls in the marked original-record caller
Each trace below invokes a particular frozen source theorem. Tape-view
relations describe physical aliasing only; neither traces nor budgets are
machine operands or unspecified suppliers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCalls
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
namespace RE
export SemiprimeD1StackRootNetworkRecordsExecution (done timeBound)
end RE
namespace VE
export SemiprimeD1StackVertexCatalogueExecution (done budget)
end VE
namespace TE
export SemiprimeD1StackMarkedPublicInputTableExecution (done runBound)
end TE
/-- The literal front door really executes the complete original-N1804 source. -/
theorem root_call (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < SemiprimeBitArithmetic.bitValue bits) (before after : Stack → List Bool)
    (hin : Link.DataRel root before (R.initial bits).data before)
    (hout : Link.DataRel root before (RE.done bits hN [] []).data after) :
    ∃ t ≤ RE.timeBound bits hN [] []+2,
      Runs program t (ctl .start) before (ctl .ready) after := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackRootNetworkRecordsExecution.source_run bits hc hN
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program root rootLabel Sum.inl_injective
    R.program (.inl .start) (fun _ => rfl) (ctl .start) (ctl .ready) rfl t
    (R.initial bits) (RE.done bits hN [] []) before after rfl rfl rfl rfl hr hin hout
/-- The fresh descriptor tape is acquired by the actual fixed53-role catalogue. -/
theorem catalogue_call (bits : List Bool) (hb : bits≠[]) (before after : Stack → List Bool)
    (hin : Link.DataRel catalogue before (SemiprimeD1StackVertexCatalogue.initial bits).data before)
    (hout : Link.DataRel catalogue before (VE.done bits).data after) :
    ∃ t ≤ VE.budget bits+1,
      Runs program t (ctl .catalogue) before (ctl .copyDescriptors) after := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackVertexCatalogueExecution.source_run bits hb
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program catalogue catalogueLabel
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj h)) V.program (.inl .main) (fun _ => rfl)
    (ctl .catalogue) (ctl .copyDescriptors) rfl t
    (SemiprimeD1StackVertexCatalogue.initial bits) (VE.done bits) before after rfl rfl rfl rfl hr hin hout
/-- Literal unary port fields are valid scope records: only their COUNT is used.
The source pays parsing all physical payload bytes, regardless of their values. -/
theorem table_call (bits indexWord : List Bool) (sideBit : Bool) (words : List (List Bool))
    (hb : bits≠[]) (before after : Stack → List Bool)
    (hin : Link.DataRel tableStack before
      (SemiprimeD1StackMarkedPublicInputTable.initial bits indexWord sideBit
        (SemiprimeD1TensorTapeCodec.vectorBits words)).data before)
    (hout : Link.DataRel tableStack before (TE.done bits indexWord sideBit words).data after) :
    ∃ t ≤ TE.runBound bits indexWord sideBit words+1,
      Runs program t (ctl .inputTable) before (ctl .log) after := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackMarkedPublicInputTableExecution.source_run bits indexWord sideBit words hb
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program tableStack tableLabel table_injective
    T.program .start (fun _ => rfl) (ctl .inputTable) (ctl .log) rfl t
    (SemiprimeD1StackMarkedPublicInputTable.initial bits indexWord sideBit
      (SemiprimeD1TensorTapeCodec.vectorBits words)) (TE.done bits indexWord sideBit words)
    before after rfl rfl rfl rfl hr hin hout
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCalls
