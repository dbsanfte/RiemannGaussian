/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersLoop
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersFinish
/-! # One original-N trace acquires the grid and caches every actual complete phase bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersExecution
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackRootPhaseParametersSource
open SemiprimeD1StackRootPhaseParametersView SemiprimeD1StackRootPhaseParametersLoop
open SemiprimeD1StackRootPhaseParametersFinish SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- Active vectors have their actual false sentinel; inactive grid bytes are empty. -/
def terminal (bits:List Bool) : List Bool :=if SemiprimeD1StackRootPhaseGridEncoding.active bits then [false] else []
/-- No external row count, phase operand, result, mode or clock enters this complete budget. -/
def runBound (bits:List Bool) : Nat :=
  SemiprimeD1StackRootPhaseGridExecution.runBound bits+
  5*(SemiprimeD1StackRootPhaseGridEncoding.result bits G.output).length+
  sweepBound (SemiprimeD1StackRootPhaseGridEncoding.result bits) (exponentValue bits) (levelsValue bits)
    (edgeValue bits) (phases bits) [] (terminal bits)+
  2*(stream (references (phases bits).length)).length+10
/-- Exactly one physically read vector sentinel or empty inactive source. -/
theorem terminal_cases (bits:List Bool) : terminal bits=[] ∨ terminal bits=[false] :=by
  unfold terminal
  split
  · exact Or.inr rfl
  · exact Or.inl rfl
/-- The physically acquired original root/grid output supplies the complete loop tape. -/
theorem acquired_grid (bits:List Bool) :
    SemiprimeD1StackRootPhaseGridEncoding.result bits G.output=rowTape (phases bits) (terminal bits) :=by
  by_cases ha:SemiprimeD1StackRootPhaseGridEncoding.active bits=true
  · simp only [phases,terminal,ha,ite_true]
    rw [rowTape_vector]
    change (if SemiprimeD1StackRootPhaseGridEncoding.active bits then _ else [])=_
    rw [ha]
    rfl
  · have hf:SemiprimeD1StackRootPhaseGridEncoding.active bits=false:=Bool.eq_false_iff.mpr ha
    simp only [phases,terminal,hf,rowTape]
    change (if SemiprimeD1StackRootPhaseGridEncoding.active bits then _ else [])=[]
    rw [hf]
    rfl
/-- The current parent exponent is the actual retained tally, not successor metadata. -/
theorem acquired_exponent (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    SemiprimeD1StackRootPhaseGridEncoding.result bits G.exponent=List.replicate (exponentValue bits) true :=
  SemiprimeD1StackRootPhaseGridEncoding.acquired_exponent bits hc
/-- The current parent u tally is physically acquired from N by the retained source. -/
theorem acquired_levels (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    SemiprimeD1StackRootPhaseGridEncoding.result bits
      (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.levels))=
      List.replicate (levelsValue bits) true :=
  (SemiprimeD1StackRootRecursiveControlOriginal.source_preserved bits SemiprimeD1StackRootParameters.levels).trans
    (SemiprimeD1StackRootParametersOriginal.levels_original bits hc)
/-- The actual shared occurrence count M is retained without a second graph scan. -/
theorem acquired_edges (bits:List Bool) :
    SemiprimeD1StackRootPhaseGridEncoding.result bits
      (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.edges))=
      List.replicate (edgeValue bits) true :=
  (SemiprimeD1StackRootRecursiveControlOriginal.source_preserved bits SemiprimeD1StackRootParameters.edges).trans
    (SemiprimeD1StackRootRecursiveControlEncoding.acquired_edges bits)
/-- The complete acquired grid is copied to its consuming reader ONCE and retained. -/
theorem grid_copy (root:G.Stack→List Bool) :
    Runs program (5*(root G.output).length+4) (.copySite 0) (loop root [] [] 0 [])
      .header (loop root (root G.output) [] 0 []) :=by
  have h:=copy_call 0 (loop root [] [] 0 []) rfl rfl
  change Runs program (5*(root G.output).length+4) (.copySite 0) (loop root [] [] 0 []) .header
    (Function.update (view root (fun _=>[]) [] [] [] [] [] [] [] []) (aux .reader) (root G.output)) at h
  rw [update_reader] at h
  exact h
/-- All sixty-two new roles are empty after the one whole acquired-grid call. -/
theorem afterGrid_loop (bits:List Bool) :
    afterGrid bits=loop (SemiprimeD1StackRootPhaseGridEncoding.result bits) [] [] 0 [] :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- WHOLE original-N-only source trace, including every actual phase call and
both accepted/rejected complete stopped banks, with one final physical reversal. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t,t+1≤runBound bits ∧ Runs program t .start (input bits) .done (result bits) :=by
  let root:=SemiprimeD1StackRootPhaseGridEncoding.result bits
  let cached:=records (exponentValue bits) (levelsValue bits) (edgeValue bits) (phases bits)
  obtain ⟨g,hg,h0⟩:=grid_call bits hc hN
  rw [afterGrid_loop] at h0
  have h1:=grid_copy root
  have hout:root G.output=rowTape (phases bits) (terminal bits):=acquired_grid bits
  rw [hout] at h1
  obtain ⟨r,hr,h2⟩:=rows_run root (exponentValue bits) (levelsValue bits) (edgeValue bits)
    (phases bits) [] (terminal bits) (terminal_cases bits) (acquired_exponent bits hc)
    (acquired_levels bits hc) (acquired_edges bits)
  have h3:=finish_run root cached
  change Runs program r .header (loop root (rowTape (phases bits) (terminal bits)) [] 0 [])
    .finishSeed (loop root [] (SemiprimeD1StackHeapAllocate.heapBytes cached) cached.length
      (stream (references cached.length)).reverse) at h2
  have hh:=compose (compose (compose h0 h1) h2) h3
  refine ⟨_,?_,hh⟩
  have hl:cached.length=(phases bits).length:=by simp only [cached,records,List.length_map]
  change (g+1)+(5*(rowTape (phases bits) (terminal bits)).length+4)+r+(2*(stream (references cached.length)).length+4)+1≤runBound bits
  rw [hl]
  unfold runBound
  rw [acquired_grid]
  dsimp only [root] at hr
  omega
/-- Complete same-program halt from ORIGINAL binary N alone, with every private
phase word cleared and every source/grid cell retained exactly. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) :=by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hs⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result bits) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersExecution
