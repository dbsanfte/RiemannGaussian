/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueSource
import RiemannGaussian.SemiprimeD1StackPortCatalogueTransduction
/-! # Whole original binary-input port catalogue, without a graph/count/arity supplier -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueExecution
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueSource
open SemiprimeD1StackPortCatalogueView SemiprimeD1StackPortCatalogueArity
open SemiprimeD1StackPortCatalogueTransduction
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (tape vertex)
open SemiprimeMacroParameters
open SemiprimeD1StackVertexCatalogueCaches (digitCountValue)
open SemiprimeD1StackUnaryDivmod (unary)
/-- All actual original factors in the exact acquired descriptor order. -/
def vertices (bits:List Bool) := (SemiprimeMacroFiniteEnumerations.subdividedVertices
  (firstAxis bits.length) (secondAxis bits.length) (digitCountValue bits)).values
/-- Retained source base after its original descriptor tape was consumed by edge acquisition. -/
def sourceBase (bits:List Bool) : V.Stack→List Bool :=
  fun k=>SemiprimeD1StackEdgeCatalogueExecution.result bits (E.catStack k)
/-- Complete actual edge bytes are retained for subsequent physical endpoint routing. -/
def edges (bits:List Bool) : List Bool :=
  SemiprimeD1StackEdgeCatalogueExecution.result bits (E.aux .output)
/-- Actual final word data, with physically acquired factor and occurrence tallies. -/
def result (bits:List Bool) : Stack→List Bool :=
  finalData (sourceBase bits) (edges bits) (output (vertices bits) 0 0 [])
    (vertices bits).length (count (vertices bits))
/-- Exact stopped source state. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Whole actual resource expression before original-input polynomial substitution. -/
def budget (bits:List Bool) : ℕ :=
  10000000000000*(bits.length+1)^5+
  61*(tape (SemiprimeD1StackEdgeCatalogueExecution.records bits) []).length+
  scanTime (vertices bits) 0 0+2*(output (vertices bits) 0 0 []).length+17
/-- Exact shared readonly counter format, derived from the original executed source. -/
theorem source_metadata (bits:List Bool) : Metadata (firstAxis bits.length) (secondAxis bits.length)
    (digitCountValue bits) (sourceBase bits) := by
  have hf:=SemiprimeD1StackVertexCatalogueCaches.base_format bits
  constructor
  · have h:=hf .radiusSucc
    change SemiprimeD1StackVertexCatalogueCaches.base bits (V.cacheStack 4)=unary (firstAxis bits.length*secondAxis bits.length+1) at h ⊢
    exact h
  · constructor
    · exact hf .firstAxis
    · constructor
      · exact hf .secondAxis
      · exact hf .digits
/-- All physical copied descriptors and work/cache fields at the actual transducer entry. -/
theorem afterEdges_clean (bits:List Bool) :
    afterEdges bits=clean (sourceBase bits) (tape ((vertices bits).map vertex) [])
      (fun _=>[]) [] [] (edges bits) [] [] [] := by
  funext k
  rcases k with (k|k|k)|k
  · rfl
  · rfl
  · cases k <;> rfl
  · cases k with
    | reader =>
      change SemiprimeD1VertexCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length)
        (digitCountValue bits) []=tape ((vertices bits).map vertex) []
      exact (SemiprimeD1EdgeCatalogueEncoding.original_input _ _ _ []).symm
    | _ => rfl
/-- Ready local stage after the actual shared source calls; original N is the sole source parameter. -/
theorem ready_original (bits:List Bool) :
    ∃ time ≤ scanTime (vertices bits) 0 0+2*(output (vertices bits) 0 0 []).length+4,
      Runs program time (.local .parse) (afterEdges bits) (.local .halt) (result bits) := by
  rw [afterEdges_clean]
  exact ready (vertices bits) (sourceBase bits) (source_metadata bits) (edges bits)
/-- Exact copied source length is the literal original descriptor tape length. -/
theorem copied_length (bits:List Bool) : (afterVertex bits vertexReader).length=
    (tape (SemiprimeD1StackEdgeCatalogueExecution.records bits) []).length := by
  change (SemiprimeD1VertexCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length)
    (digitCountValue bits) []).length=_
  rw [←SemiprimeD1EdgeCatalogueEncoding.original_input]
  rfl
/-- The closed fixed program begins with binary N alone and physically acquires the complete port catalogue. -/
theorem source_run (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ budget bits,C.run program time (initial bits)=some (done bits) := by
  have h0:=input_guard bits hb
  obtain ⟨a,ha,h1⟩:=vertex_call bits hb
  have h2:=copy_vertex bits
  obtain ⟨b,hb',h3⟩:=edges_call bits
  obtain ⟨d,hd,h4⟩:=ready_original bits
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  obtain ⟨finish,hr,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨1+(a+(5*(afterVertex bits vertexReader).length+4+(b+d)))+1,?_,?_⟩
  · rw [copied_length]
    unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases hout with ⟨hpc,hdata,hframes⟩
    change C.step program finish=some (done bits)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]
/-- Actual output is the exact factor-major original port specification, not a supplied graph answer. -/
theorem original_ports (bits:List Bool) : result bits (aux .output)=
    SemiprimeD1PortCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length)
      (digitCountValue bits) [] := by
  change output (vertices bits) 0 0 []=_
  rw [output_original]
  rfl
/-- The runtime tally counts original occurrences, never original wire IDs or serialized bytes. -/
theorem occurrence_tally (bits:List Bool) : result bits (aux .occurrenceOrdinal)=unary
    (SemiprimeMacroFiniteEnumerations.incidences (firstAxis bits.length) (secondAxis bits.length)
      (digitCountValue bits)).values.length := by
  change unary (count (vertices bits))=_
  congr 1
  exact SemiprimeD1PortCatalogueEncoding.original_count _ _ _
/-- Exact input representation: the one fixed machine starts from original binary N only. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial originalInput (.local .main) bits:=by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with (k|k)|k
    · simp [E.input,SemiprimeD1StackEdgeCatalogueExecution.cat_input,originalInput,vertexStack,edgeStack,E.catStack]
    · simp [E.input,originalInput,vertexStack,edgeStack,E.catStack]
    · simp [originalInput,vertexStack,edgeStack]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct originalInput (aux .output) (.local .main) program bits).symm
end RiemannGaussian.SemiprimeD1StackPortCatalogueExecution
