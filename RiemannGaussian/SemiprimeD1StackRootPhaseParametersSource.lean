/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersCalls
/-! # Original-N root/grid acquisition and paid construction of all five phase inputs -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersSource
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackRootPhaseParametersCalls
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- Complete physical input view with no acquired phase result/cache. -/
def withInputs (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t p:List Bool) : Stack→List Bool :=
  data root (P.input a u edges t p) work
/-- The five-input source with all inputs empty is the literal empty private bank. -/
theorem zero_input : P.input 0 0 0 [] []=(fun _=>[]) :=by
  funext k
  rw [SemiprimeD1StackRootPhaseParametersInventory.input_only]
  simp only [List.replicate_zero,ite_self]
/-- One actual physical exponent word write changes only that original input. -/
theorem update_exponent (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t p:List Bool) (next:Nat) :
    Function.update (withInputs root work a u edges t p) phaseExponent (List.replicate next true)=withInputs root work next u edges t p :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual physical levels word write changes only that original input. -/
theorem update_levels (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t p:List Bool) (next:Nat) :
    Function.update (withInputs root work a u edges t p) phaseLevels (List.replicate next true)=withInputs root work a next edges t p :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual physical edges word write changes only that original input. -/
theorem update_edges (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t p:List Bool) (next:Nat) :
    Function.update (withInputs root work a u edges t p) phaseEdges (List.replicate next true)=withInputs root work a u next t p :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual physical index word write changes only that original input. -/
theorem update_index (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t p:List Bool) (next:List Bool) :
    Function.update (withInputs root work a u edges t p) phaseIndex (next)=withInputs root work a u edges next p :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual physical precision word write changes only that original input. -/
theorem update_precision (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t p:List Bool) (next:List Bool) :
    Function.update (withInputs root work a u edges t p) phasePrecision (next)=withInputs root work a u edges t next :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- Four real paid operand copies and TWO literal binary pushes establish
exactly the five original phase inputs, with no expected result/cache supplier. -/
theorem setup_run (root:G.Stack→List Bool) (work:Aux→List Bool) (a u edges:Nat) (t:List Bool)
    (ha:root G.exponent=List.replicate a true)
    (hu:root (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.levels))=List.replicate u true)
    (hm:root (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.edges))=List.replicate edges true)
    (ht:work .index=t) (hs:work .copyScratch=[]) :
    Runs program (5*(a+u+edges+t.length)+18) (.copySite 1) (data root (fun _=>[]) work)
      .phaseCall (withInputs root work a u edges t [false,true]) :=by
  have h0:=copy_call 1 (withInputs root work 0 0 0 [] []) rfl hs
  change Runs program (5*(root G.exponent).length+4) (.copySite 1) (withInputs root work 0 0 0 [] [])
    (.copySite 2) (Function.update (withInputs root work 0 0 0 [] []) phaseExponent (root G.exponent)) at h0
  rw [ha,List.length_replicate,update_exponent] at h0
  have h1:=copy_call 2 (withInputs root work a 0 0 [] []) rfl hs
  change Runs program (5*(root _).length+4) (.copySite 2) (withInputs root work a 0 0 [] [])
    (.copySite 3) (Function.update (withInputs root work a 0 0 [] []) phaseLevels (root _)) at h1
  rw [hu,List.length_replicate,update_levels] at h1
  have h2:=copy_call 3 (withInputs root work a u 0 [] []) rfl hs
  change Runs program (5*(root _).length+4) (.copySite 3) (withInputs root work a u 0 [] [])
    (.copySite 4) (Function.update (withInputs root work a u 0 [] []) phaseEdges (root _)) at h2
  rw [hm,List.length_replicate,update_edges] at h2
  have h3:=copy_call 4 (withInputs root work a u edges [] []) rfl hs
  change Runs program (5*(work .index).length+4) (.copySite 4) (withInputs root work a u edges [] [])
    .pHigh (Function.update (withInputs root work a u edges [] []) phaseIndex (work .index)) at h3
  rw [ht,update_index] at h3
  have h4:Runs program 1 .pHigh (withInputs root work a u edges t []) .pLow
      (withInputs root work a u edges t [true]):=by
    apply one_base program _ _ (.push phasePrecision true .pLow) _ _ rfl
    · rfl
    · exact update_precision root work a u edges t [] [true]
  have h5:Runs program 1 .pLow (withInputs root work a u edges t [true]) .phaseCall
      (withInputs root work a u edges t [false,true]):=by
    apply one_base program _ _ (.push phasePrecision false .phaseCall) _ _ rfl
    · rfl
    · exact update_precision root work a u edges t [true] [false,true]
  have hh:=compose (compose (compose (compose (compose h0 h1) h2) h3) h4) h5
  have hz:withInputs root work 0 0 0 [] []=data root (fun _=>[]) work:=by rw [withInputs,zero_input]
  rw [hz] at hh
  convert hh using 1
  omega
/-- One real whole original-N grid call acquires all126 retained words exactly once. -/
theorem grid_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤SemiprimeD1StackRootPhaseGridExecution.runBound bits,
      Runs program (t+1) .start (input bits) (.copySite 0) (afterGrid bits) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootPhaseGridExecution.source_run bits hc hN
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program gridStack Label.grid grid_injective
    G.program (.inl .start) (fun _=>rfl) .start (.copySite 0) rfl t (G.initial bits)
    (SemiprimeD1StackRootPhaseGridEncoding.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersSource
