/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueAcquisition
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueFinish
/-! # Whole actual metadata-to-feasible-tuples source, in native order
The actual computed weight catalogue, not an advised tape, is passed to the
same finite enumerator. Only packet/tile counts and precision are prepared.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueExecution
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCataloguePrimitives SemiprimeD1StackWeightedModeCatalogueOrders
open SemiprimeD1StackWeightedModeCatalogueAcquisition SemiprimeD1StackWeightedModeCatalogueFinish
open SemiprimeD1StackWeightedModeView (unary vector history)
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl :Control→Label)
/-- Exact final acquired words, retaining product metadata and complete mode labels. -/
def result (p t width:Nat):Words:=
  {ready p t width with enumData:=SemiprimeD1StackWeightedModeExecution.result (weights p t width) width}
/-- Actual stopped source state, with no real return frames left. -/
def done (p t width:Nat):C.State Stack Label:=⟨none,none,none,store (result p t width),[]⟩
/-- The actual nested enumerator receives precisely the physically acquired catalogue. -/
theorem enumerate_call (p t width:Nat):
    ∃time ≤SemiprimeD1StackWeightedModeBounds.runBound (weights p t width) width+1,
      Runs program time (ctl .enumerate) (store (ready p t width)) (ctl .done) (store (result p t width)):=by
  have hw:∀w∈weights p t width,0 < w:=SemiprimeD1ModeCatalog.weights_positive _ _
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackWeightedModeBounds.source_run_bounded (weights p t width) hw width
  refine ⟨time+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program weighted weightedLabel weighted_injective
    W.program (.inl .start) (fun _=>rfl) (ctl .enumerate) (ctl .done) rfl time
    (W.initial (vector (weights p t width)) (unary width))
    (SemiprimeD1StackWeightedModeExecution.done (weights p t width) width) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
/-- Own initial multiplication/copy and complete order/slot-loop allowance. -/
def acquisitionBudget (p t width:Nat):Nat:=
  5*p+5*(p*(2*t+3)+1)+5*width+17+
    1000*((width-1)+1)*(p*t+1)*((width-1)+p*t+2)
/-- Both actual reverse-log byte lengths are charged before the actual DFS call. -/
def timeBound (p t width:Nat):Nat:=acquisitionBudget p t width+
  2*(history (orderWeights (p*t) 0 (width-1)) []).length+
  2*(history (orderLabels (p*t) 0 (width-1)) []).length+8+
  SemiprimeD1StackWeightedModeBounds.runBound (weights p t width) width+2
/-- The same actual initial source, multiplication and catalogue scan reach the literal reverse logs. -/
theorem acquisition_trace (p t width:Nat):
    ∃time ≤acquisitionBudget p t width,Runs program time (ctl .start)
      (input (unary p) (unary t) (unary width)) (ctl .catalogueSeed)
      (store (scanning p t width 0 (width-1) 0 0
        (history (orderWeights (p*t) 0 (width-1)) []) (history (orderLabels (p*t) 0 (width-1)) []))):=by
  obtain ⟨u,hu,h0⟩:=setup_run p t width
  obtain ⟨v,hv,h1⟩:=orders_run p t width (width-1) 0 [] []
  simp only [Nat.zero_add] at hv h1
  refine ⟨u+v,?_,join h0 h1⟩
  unfold acquisitionBudget
  omega
/-- Complete real source trace: compute slots, catalogue, labels, feasible tuples and final output. -/
theorem source_trace (p t width:Nat):
    ∃time,time+1 ≤timeBound p t width ∧ Runs program time (ctl .start)
      (input (unary p) (unary t) (unary width)) (ctl .done) (store (result p t width)):=by
  obtain ⟨u,hu,h0⟩:=acquisition_trace p t width
  have h1:=finish_run p t width
  obtain ⟨v,hv,h2⟩:=enumerate_call p t width
  have h:=join h0 (join h1 h2)
  refine ⟨u+((2*(history (orderWeights (p*t) 0 (width-1)) []).length+
    2*(history (orderLabels (p*t) 0 (width-1)) []).length+8)+v),?_,h⟩
  unfold timeBound
  omega
/-- The final halt is physically executed; no prepared catalogue or feasible tuple is an input. -/
theorem source_run (p t width:Nat):
    ∃time ≤timeBound p t width,C.run program time (initial (unary p) (unary t) (unary width))=
      some (done p t width):=by
  obtain ⟨time,ht,hr⟩:=source_trace p t width
  obtain ⟨finish,hf,ha⟩:=hr [] (initial (unary p) (unary t) (unary width)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (store (result p t width)) [] finish ha
  refine ⟨time+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Exact original feasible-mode tuple order for the physically computed packet/tile slots. -/
theorem output_original (p t width:Nat):
    (done p t width).data (weighted .output)=SemiprimeD1TensorTapeCodec.vectorBits
      ((SemiprimeD1WeightedTuples.tuples (SemiprimeD1ModeCatalog.weights (p*t) (width-1)) (width-1)).map vector):=by
  exact SemiprimeD1StackWeightedModeExecution.output_exact (weights p t width) width
/-- The actual generated label catalogue is retained at the stopped source. -/
theorem labels_original (p t width:Nat):(done p t width).data (aux .labels)=labels p t width:=rfl
/-- Both actual original counts and the actual computed product remain available. -/
theorem product_retained (p t width:Nat) (k:M.Stack):
    (done p t width).data (multiply k)=M.data (unary p) (unary t) [] [] [] [] (unary (p*t)) k:=rfl
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueExecution
