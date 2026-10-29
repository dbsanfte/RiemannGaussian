/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueLoop
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesBounds
/-! # Closed actual binary-N-only acquisition of all original Boolean factor rows
The scope domain, descriptor order, per-row data and unary factor counter follow
from the same physically acquired original source. No data/clock supplier remains.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueExecution
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueView
open SemiprimeD1StackBooleanFactorCatalogueSource SemiprimeD1StackBooleanFactorCatalogueLoop
open SemiprimeD1BooleanFactorCatalogueIndices (key scopeWords indices descriptorTape)
open SemiprimeD1BooleanFactorCatalogueIndicesBounds (occurrences)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
/-- Original physical factor list length, not an executing count input. -/
theorem indices_length (N : Nat) : (indices N).length=factorCount N := by
  simp only [SemiprimeD1BooleanFactorCatalogueIndices.indices,List.length_finRange]
/-- The actual first descriptor has factor counter0, and every successor is consecutive. -/
theorem indices_sequence (N : Nat) : (indices N).map Fin.val=List.range' 0 (indices N).length := by
  rw [SemiprimeD1BooleanFactorCatalogueIndices.indices_values,List.range_eq_range',indices_length]
/-- The original source graph always has a real carry-initial factor. -/
theorem indices_ne_nil (N : Nat) : indices N≠[] := by
  intro h
  have hl:=congrArg List.length h
  rw [indices_length,List.length_nil] at hl
  have hp:=SemiprimeD1BooleanFactorCatalogueIndices.factorCount_pos N
  omega
/-- SAME actually acquired catalogue supplies the loop's exact original queue. -/
theorem ready_loop (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ready bits=loopData bits 0 (indices (bitValue bits)) [] [false] := by
  unfold ready loopData catalogue
  rw [←SemiprimeD1BooleanFactorCatalogueIndices.descriptor_source bits hc hN,Function.update_eq_self]
  rfl
/-- Actual output byte specification, acquired by the real repeated logger and final reversal. -/
def outputTape (bits : List Bool) : List Bool :=
  (afterRows bits 0 (indices (bitValue bits)) []).reverse++[false]
/-- Retained source state has exactly one physically pushed key marker per original descriptor. -/
def finalSource (bits : List Bool) : F.Stack→List Bool :=
  SemiprimeD1StackFactorScopeFibre.afterSource bits (key (indices (bitValue bits)).length)
/-- Every source/cache role is retained; all descriptors and private work are physically consumed. -/
def done (bits : List Bool) : C.State Stack Label :=
  SemiprimeD1StackBooleanFactorCatalogueFinish.done (finalSource bits) (catalogue bits []) (outputTape bits)
/-- Complete own allowance: actual setup, actual descriptor/filter loop,
one actual full-history reversal, all calls/returns and the literal halt. -/
def timeBound (bits : List Bool) : Nat :=
  setupBound bits+loopBudget bits (occurrences (bitValue bits)) 0 (indices (bitValue bits))+
    2*(afterRows bits 0 (indices (bitValue bits)) []).length+4
/-- The entire fixed218-role program starts with original binary N ONLY and
acquires all original Boolean factor rows in their actual source order. -/
theorem source_run (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ timeBound bits,C.run program t (initial bits)=some (done bits) := by
  have hb:bits≠[]:=by intro he;rw [he] at hN;exact Nat.lt_irrefl _ hN
  obtain ⟨s,hs,h0⟩:=setup_run bits hb
  rw [ready_loop bits hc hN] at h0
  obtain ⟨u,hu,h1⟩:=rows_run bits hN (occurrences (bitValue bits))
    (SemiprimeD1BooleanFactorCatalogueIndicesBounds.scope_word_length_le bits hc hN)
    (SemiprimeD1BooleanFactorCatalogueIndicesBounds.scope_word_value_le bits hc hN)
    0 (indices (bitValue bits)) (indices_sequence (bitValue bits)) (indices_ne_nil (bitValue bits)) [] [false]
  rw [Nat.zero_add] at h1
  have h2:=SemiprimeD1StackBooleanFactorCatalogueFinish.reverse_call (finalSource bits) (catalogue bits [])
    (afterRows bits 0 (indices (bitValue bits)) []) [false]
  have h:=h0.trans (h1.trans h2)
  obtain ⟨finish,hr,ho⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨s+(u+(2*(afterRows bits 0 (indices (bitValue bits)) []).length+3))+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases ho with ⟨hp,hd,hf⟩
    change C.step program finish=some (done bits)
    simp only [C.step,SemiprimeD1StackCalls.step,hp,Option.map_some,program,C.execute,hd,hf,
      done,SemiprimeD1StackBooleanFactorCatalogueFinish.done,outputTape]
/-- Genuine original-binary machine certificate, with no prepared source/query/table advice. -/
noncomputable def machineCatalogue (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (timeBound bits) := by
  rw [SemiprimeD1StackBooleanFactorCatalogueFinish.initial_configuration]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.local .main) program
  have h:=source_run bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All possible successfully reached prefixes stop by the actual proved full halt. -/
theorem prefix_fuel_le (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr:C.run program fuel (initial bits)=some finish) :
    fuel ≤ timeBound bits := by
  obtain ⟨t,ht,he⟩:=source_run bits hc hN
  have hf:fuel ≤ t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every one of218 Boolean data roles and every actual return cell is counted. -/
theorem prefix_cells (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr:C.run program fuel (initial bits)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length ≤ 219*(bits.length+timeBound bits) := by
  have hi (k : Stack) : ((initial bits).data k).length ≤ bits.length:=by
    change (input bits k).length ≤ bits.length
    rw [SemiprimeD1StackBooleanFactorCatalogueFinish.input_eq]
    split <;> simp
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ finish hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(finish.data k).length) ≤ 218*(bits.length+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel finish hr
  omega
/-- Identical complete inventory at every actual compiled original-N prefix. -/
theorem machine_prefix_cells (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 219*(bits.length+timeBound bits) := by
  rw [SemiprimeD1StackBooleanFactorCatalogueFinish.initial_configuration] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (.local .main) program fuel (initial bits)
  have hh:=he.trans hr
  cases hrun:C.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have hc':SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel finish hrun
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueExecution
