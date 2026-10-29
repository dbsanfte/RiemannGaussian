/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquirePrimitives
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireBounds
/-! # Three real complete sources with all other2114-role banks retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireCalls
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
/-- One actual source call pays its own whole clock and retains both other complete banks. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) :
    ∃t ≤ SemiprimeD1StackRootNetworkRowsBounds.runBound bits+1,Runs program t (ctl .root)
      (data (R.initial bits).data parameters acquisition) (ctl (.copy .rows)) (data (SemiprimeD1StackRootNetworkRowsExecution.done bits hN [] []).data parameters acquisition) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootNetworkRowsBounds.source_run_bounded bits hc hN
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root
    (fun _ _ h=>Sum.inl.inj h) R.program (.inl .start) (fun _=>rfl) (ctl .root) (ctl (.copy .rows)) rfl t
    (R.initial bits) (SemiprimeD1StackRootNetworkRowsExecution.done bits hN [] []) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- One actual source call pays its own whole clock and retains both other complete banks. -/
theorem parameters_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) (root:R.Stack→List Bool) (acquisition:Q.Stack→List Bool) :
    ∃t ≤ 10^51*(bits.length+1)^10+1,Runs program t (ctl .parameters)
      (data root (P.initial bits).data acquisition) (ctl .root) (data root (SemiprimeD1StackRootParametersExecution.done bits).data acquisition) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootParametersBounds.source_run_polynomial bits hc hN
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program parameterStack Label.parameters
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj h)) P.program (.inl .start) (fun _=>rfl) (ctl .parameters) (ctl .root) rfl t
    (P.initial bits) (SemiprimeD1StackRootParametersExecution.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- One actual source call pays its own whole clock and retains both other complete banks. -/
theorem acquisition_call (net:SemiprimeD1TensorNetwork.Network) (a:Nat) (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) :
    ∃t ≤ SemiprimeD1StackSourceSelectionAcquireBounds.polynomial net a+1,Runs program t (ctl .acquire)
      (data root parameters (SemiprimeD1StackSourceSelectionAcquireEncoding.source net a).data) (ctl .done) (data root parameters (SemiprimeD1StackSourceSelectionAcquireEncoding.done net a).data) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceSelectionAcquireBounds.source_run_bounded net a
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program acquisitionStack Label.acquire
    (fun _ _ h=>Sum.inr.inj (Sum.inr.inj h)) Q.program (.local .start) (fun _=>rfl) (ctl .acquire) (ctl .done) rfl t
    (SemiprimeD1StackSourceSelectionAcquireEncoding.source net a) (SemiprimeD1StackSourceSelectionAcquireEncoding.done net a) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · exact (hk k rfl).elim
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireCalls
