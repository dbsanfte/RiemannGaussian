/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesComponents
/-! # Whole original-binary-N to ordered compact occurrence-key source execution
The real records/index source runs once. Its actual index cache then enters
the same occurrence source program. Both real calls and the final halt share one clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesExecution
open SemiprimeD1StackRootSourceOccurrences SemiprimeD1StackRootSourceOccurrencesComponents
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl :Control→Label)
/-- Exact clean halt of the same whole original-N program, retaining every1852source word. -/
def done (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :C.State Stack Label :=
  ⟨none,none,none,result bits hN fixed tail,[]⟩
/-- Own whole source clock pays the actual original records/index source, actual occurrence source, both calls and halt. -/
def timeBound (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :Nat :=
  SemiprimeD1StackRootNetworkRowsExecution.timeBound bits hN fixed tail+
    E.timeBound (rootn bits hN fixed) (rootrows bits hN fixed)+3
/-- The actual N-only row/index acquisition runs inside the one whole caller. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q≤SemiprimeD1StackRootNetworkRowsExecution.timeBound bits hN [] [],
      Runs program (q+1) (ctl .start) (input bits) (ctl .occurrences) (data (R.done bits hN [] []).data (fun _=>[])) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootNetworkRowsExecution.source_run bits hc hN
  exact ⟨q,hq,root_lift (.inl .start) .start rfl (R.initial bits) (R.done bits hN [] []) q rfl rfl rfl rfl hr⟩
/-- The actual caller-prefix row/index acquisition enters the same occurrence source call. -/
theorem root_prefix_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q≤SemiprimeD1StackRootNetworkRowsExecution.timeBound bits hN fixed tail,
      Runs program (q+1) (ctl .prescribed)
        (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail)).data
        (ctl .occurrences) (data (R.done bits hN fixed tail).data (fun _=>[])) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootNetworkRowsExecution.source_run_prefix bits hc hN fixed tail
  exact ⟨q,hq,root_lift (.inl .prescribed) .prescribed rfl
    (R.initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail))
    (R.done bits hN fixed tail) q rfl rfl rfl rfl hr⟩
/-- One actual prescribed-prefix trace includes real source acquisition and exact occurrence-key construction. -/
theorem source_prefix_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q,q+1≤timeBound bits hN fixed tail ∧ Runs program q (ctl .prescribed)
      (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail)).data
      (ctl .done) (result bits hN fixed tail) :=by
  obtain ⟨a,ha,h0⟩:=root_prefix_call bits hc hN fixed tail
  obtain ⟨b,hb,h1⟩:=occurrence_call bits hc hN fixed tail
  refine ⟨(a+1)+(b+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold timeBound
  omega
/-- One actual N-only trace includes all acquisition and every row/tally output byte. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q,q+1≤timeBound bits hN [] [] ∧ Runs program q (ctl .start) (input bits)
      (ctl .done) (result bits hN [] []) :=by
  obtain ⟨a,ha,h0⟩:=root_call bits hc hN
  obtain ⟨b,hb,h1⟩:=occurrence_call bits hc hN [] []
  refine ⟨(a+1)+(b+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold timeBound
  omega
/-- Complete actual original-N source and its real final halt. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q≤timeBound bits hN [] [],SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) :=by
  obtain ⟨q,hq,hr⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN [] []) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- The same actual source covers every physical prescription, including repeated/conflicting entries and retained tails. -/
theorem source_run_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q≤timeBound bits hN fixed tail,SemiprimeD1StackCalls.run program q
      (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail))=
        some (done bits hN fixed tail) :=by
  obtain ⟨q,hq,hr⟩:=source_prefix_trace bits hc hN fixed tail
  obtain ⟨finish,hf,hAt⟩:=hr []
    (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN fixed tail) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Every actual1852original source/index word survives literally at the row boundary. -/
theorem root_retained (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) (k:R.Stack) :
    (done bits hN fixed tail).data (rootStack k)=(R.done bits hN fixed tail).data k :=rfl
end RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesExecution
