/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCataloguePrimitives
/-! # Original-N source calls of the complete physical port producer -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueSource
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueComponents
open SemiprimeD1StackPortCataloguePrimitives
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- Exact data after the real original vertex catalogue, all new work initially empty. -/
def afterVertex (bits:List Bool) : Stack→List Bool :=
  Sum.elim (SemiprimeD1StackEdgeCatalogueExecution.afterCat bits) (fun _=>[])
/-- Actual physically copied source descriptors before the shared edge parser executes. -/
def copied (bits:List Bool) : Stack→List Bool :=
  Function.update (afterVertex bits) (aux .reader) (afterVertex bits vertexReader)
/-- Actual data after original edge generation, preserving the private descriptor copy. -/
def afterEdges (bits:List Bool) : Stack→List Bool :=
  Sum.elim (SemiprimeD1StackEdgeCatalogueExecution.result bits)
    (Function.update (fun _=>[]) Aux.reader (afterVertex bits vertexReader))
/-- Actual nonempty binary-input guard; input N is never converted to unary. -/
theorem input_guard (bits:List Bool) (hb:bits≠[]) :
    Runs program 1 (.local .main) (input bits) (.local .callVertex) (input bits) := by
  apply one_base program _ _ (.peek originalInput (.local .halt) (.local .callVertex) (.local .callVertex)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (Label.local .halt) (.local .callVertex)
      (.local .callVertex) bits.head?)=some (.local .callVertex)
    cases bits with
    | nil => exact False.elim (hb rfl)
    | cons b bs => cases b <;> rfl
  · rfl
/-- The whole vertex source executes ONCE from original binary N, not from a prepared graph. -/
theorem vertex_call (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ 10000000000000*(bits.length+1)^5+1,
      Runs program time (.local .callVertex) (input bits) (.local .copyVertex) (afterVertex bits) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackVertexCatalogueBounds.source_run_polynomial bits hb
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program vertexStack Label.vertex vertexStack_injective
    V.program (.inl .main) (fun _=>rfl) (.local .callVertex) (.local .copyVertex) rfl m
    (SemiprimeD1StackVertexCatalogue.initial bits) (SemiprimeD1StackVertexCatalogueExecution.done bits)
    (input bits) (afterVertex bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with (k|k)|k
      · exact False.elim (hk k rfl)
      · rcases k with k|k <;> rfl
      · rfl
/-- The private source copy is paid before its original is consumed by edge acquisition. -/
theorem copy_vertex (bits:List Bool) :
    Runs program (5*(afterVertex bits vertexReader).length+4) (.local .copyVertex)
      (afterVertex bits) (.local .callEdges) (copied bits) := by
  have h:=copy_call (afterVertex bits) rfl
  simpa only [show afterVertex bits (aux .reader)=[] from rfl,List.append_nil,copied] using h
/-- Shared original edge stage executes without rerunning metadata or the vertex catalogue. -/
theorem edge_source (bits:List Bool) :
    ∃ time ≤ 56*(SemiprimeD1EdgeCatalogueEncoding.tape
      (SemiprimeD1StackEdgeCatalogueExecution.records bits) []).length+5,
      C.run E.program time
        (⟨some (.inl .parse),none,none,SemiprimeD1StackEdgeCatalogueExecution.afterCat bits,[]⟩:C.State E.Stack E.Label)=
          some (SemiprimeD1StackEdgeCatalogueExecution.done bits) := by
  obtain ⟨m,hm,h⟩:=SemiprimeD1StackEdgeCatalogueExecution.ready_original bits
  obtain ⟨finish,hr,hout⟩:=h []
    (⟨some (.inl .parse),none,none,SemiprimeD1StackEdgeCatalogueExecution.afterCat bits,[]⟩:C.State E.Stack E.Label)
    ⟨rfl,rfl,rfl⟩
  refine ⟨m+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step E.program finish=some (SemiprimeD1StackEdgeCatalogueExecution.done bits)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,E.program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,
    SemiprimeD1StackEdgeCatalogueExecution.done]
/-- The actual parser call retains the original descriptor copy and all foreign counters. -/
theorem edges_call (bits:List Bool) :
    ∃ time ≤ 56*(SemiprimeD1EdgeCatalogueEncoding.tape
      (SemiprimeD1StackEdgeCatalogueExecution.records bits) []).length+6,
      Runs program time (.local .callEdges) (copied bits) (.local .parse) (afterEdges bits) := by
  obtain ⟨m,hm,hr⟩:=edge_source bits
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program edgeStack Label.edges edgeStack_injective
    E.program (.inl .parse) (fun _=>rfl) (.local .callEdges) (.local .parse) rfl m
    (⟨some (.inl .parse),none,none,SemiprimeD1StackEdgeCatalogueExecution.afterCat bits,[]⟩:C.State E.Stack E.Label)
    (SemiprimeD1StackEdgeCatalogueExecution.done bits) (copied bits) (afterEdges bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;simp [copied,afterVertex,edgeStack,aux,Function.update]
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPortCatalogueSource
