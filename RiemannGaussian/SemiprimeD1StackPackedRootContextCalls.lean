/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootContextPrimitives
/-! # Both actual whole-source calls, with original operands and real returns -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootContextCalls
open SemiprimeD1StackPackedRootContext SemiprimeD1StackPackedRootContextEncoding
open SemiprimeD1StackPackedRootContextPrimitives SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
local notation "ctl" => (Sum.inl : Control→Label)
/-- Real N-only metadata source call, with ALL13 actual outputs retained. -/
theorem metadata_call (bits : List Bool) :
    ∃t ≤ SemiprimeD1StackPackedRootMetadataExecution.polynomial bits+1,
      Runs program t (ctl .start) (input bits) (ctl .copyPrecision) (ready bits).data := by
  obtain ⟨t,ht,h⟩ := SemiprimeD1StackPackedRootMetadataExecution.source_run_bounded bits
  have hi : Link.DataRel metadata (input bits) (M.initial bits).data (input bits) :=
    ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel metadata (input bits) (M.done bits).data (ready bits).data := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
  exact ⟨t+1,by omega,SemiprimeD1StackProcedureCallsTrace.included_call program metadata metadataLabel metadata_injective
    M.program (.local .start) (fun _ => rfl) (ctl .start) (ctl .copyPrecision) rfl t (M.initial bits) (M.done bits)
    (input bits) (ready bits).data rfl rfl rfl rfl h hi ho⟩
/-- Real context source computes rank one and materializes the precision VALUE;
the entire metadata bank is foreign and retained, not re-acquired or projected. -/
theorem context_call (m : M.Stack→List Bool) (p : List Bool) :
    ∃t ≤ SemiprimeD1StackJetContextCorrectness.budget [] p+1,
      Runs program t (ctl .acquireContext) (data m (J.initial [false] p).data) (ctl .done)
        (data m (SemiprimeD1StackJetContextCorrectness.finalData [] p)) := by
  obtain ⟨t,ht,h⟩ := SemiprimeD1StackJetContextCorrectness.source_run [] (by simp) p
  let source := J.initial [false] p
  let out : C.State J.Stack J.Label := ⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData [] p,[]⟩
  let before := data m source.data
  let after := data m out.data
  have hi : Link.DataRel context before source.data before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel context before out.data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · exact False.elim (hk k rfl)
  exact ⟨t+1,by omega,SemiprimeD1StackProcedureCallsTrace.included_call program context contextLabel context_injective
    J.program .start (fun _ => rfl) (ctl .acquireContext) (ctl .done) rfl t source out before after
    rfl rfl rfl rfl h hi ho⟩
/-- Empty-axis context acquisition is linear in the ACTUAL binary word width
and precision VALUE; no logarithmic proxy erases the materialized markers. -/
theorem context_budget (bits : List Bool) :
    SemiprimeD1StackJetContextCorrectness.budget [] (M.precisionWord bits.length) ≤ 47*bits.length+222 := by
  have h := SemiprimeD1StackJetContextBounds.budget_le [] (by simp) (M.precisionWord bits.length)
  have hlen := SemiprimeD1StackPackedRootMetadataEncoding.precision_length bits.length
  have hval := SemiprimeD1StackPackedRootMetadataEncoding.precision_value bits.length
  simp only [List.map_nil,SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,List.length_nil,List.prod_nil,
    Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_one] at h
  rw [hval] at h
  omega
end RiemannGaussian.SemiprimeD1StackPackedRootContextCalls
