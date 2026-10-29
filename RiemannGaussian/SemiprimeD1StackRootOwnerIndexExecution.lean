/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexComponents
/-! # Whole original-N root-record and owner-index source execution
Both actual sources, their real calls and the final halt share one whole clock.
The acquired original record/count words are shared physically. No extra N/count
scan, table getter, graph/owner function or precomputed catalogue is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndexExecution
open SemiprimeD1StackRootOwnerIndex SemiprimeD1StackRootOwnerIndexComponents
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl :Control→Label)
/-- Genuine clean halt retains both complete source banks and both unused input shadows. -/
def done (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :C.State Stack Label :=
  ⟨none,none,none,result bits hN fixed tail,[]⟩
/-- Whole actual clock includes N-only root prefix seed, both real calls and the final halt. -/
def timeBound (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :Nat :=
  SemiprimeD1StackRootNetworkRecordsExecution.timeBound bits hN fixed tail+
    E.timeBound (rootowners bits hN fixed) (rootSuffix bits hN fixed)+4
/-- The actual binary-N-only record source executes inside this one enclosing original-input program. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ SemiprimeD1StackRootNetworkRecordsExecution.timeBound bits hN [] []+1,
      Runs program (q+1) (ctl .start) (input bits) (ctl .index) (data (R.done bits hN [] []).data (fun _=>[])) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootNetworkRecordsExecution.source_run bits hc hN
  exact ⟨q,hq,root_lift (.inl .start) .start rfl (R.initial bits) (R.done bits hN [] []) q rfl rfl rfl rfl hr⟩
/-- The same literal program also acquires the entire caller-prefix root before acquiring its index. -/
theorem root_prefix_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q ≤ SemiprimeD1StackRootNetworkRecordsExecution.timeBound bits hN fixed tail,
      Runs program (q+1) (ctl .prescribed)
        (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail)).data
        (ctl .index) (data (R.done bits hN fixed tail).data (fun _=>[])) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootNetworkRecordsExecution.source_run_prefix bits hc hN fixed tail
  exact ⟨q,hq,root_lift (.inl .main) .prescribed rfl
    (R.initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail))
    (R.done bits hN fixed tail) q rfl rfl rfl rfl hr⟩
/-- Entire actual prescribed-prefix trace retains the actual root bank while acquiring its complete owner index. -/
theorem source_prefix_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q,q+1 ≤ timeBound bits hN fixed tail ∧ Runs program q (ctl .prescribed)
      (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail)).data
      (ctl .done) (result bits hN fixed tail) :=by
  obtain ⟨a,ha,h0⟩:=root_prefix_call bits hc hN fixed tail
  obtain ⟨b,hb,h1⟩:=index_call bits hc hN fixed tail
  refine ⟨(a+1)+(b+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold timeBound
  omega
/-- Entire actual N-only trace includes the real root seed, both real source calls and output acquisition. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q,q+1 ≤ timeBound bits hN [] [] ∧ Runs program q (ctl .start) (input bits)
      (ctl .done) (result bits hN [] []) :=by
  obtain ⟨a,ha,h0⟩:=root_call bits hc hN
  obtain ⟨b,hb,h1⟩:=index_call bits hc hN [] []
  refine ⟨(a+1)+(b+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold timeBound
  omega
/-- Complete actual original-binary-N program executes its true final halt, with no count/index advice. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ timeBound bits hN [] [],SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) :=by
  obtain ⟨q,hq,hr⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN [] []) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Same actual source/halt covers every physically prescribed original prefix and retained tail. -/
theorem source_run_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q ≤ timeBound bits hN fixed tail,SemiprimeD1StackCalls.run program q
      (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail))=
        some (done bits hN fixed tail) :=by
  obtain ⟨q,hq,hr⟩:=source_prefix_trace bits hc hN fixed tail
  obtain ⟨finish,hf,hAt⟩:=hr []
    (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN fixed tail) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Every one of the real1804 root source words survives literally at the completed index boundary. -/
theorem root_retained (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) (k:R.Stack) :
    (done bits hN fixed tail).data (rootStack k)=(R.done bits hN fixed tail).data k :=rfl
/-- Both unused allocated source-input shadows remain physically EMPTY. -/
theorem shadows_empty (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data (.inr .vertices)=[] ∧ (done bits hN fixed tail).data (.inr .leftCount)=[] :=⟨rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackRootOwnerIndexExecution
