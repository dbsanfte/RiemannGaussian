/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueTransduction

/-! # Whole original binary-input half-edge catalogue acquisition -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueExecution
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackEdgeCatalogueView SemiprimeD1StackEdgeCatalogueTransduction
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record tape output vertex)
open SemiprimeD1StackVertexCatalogueCaches (digitCountValue)
open SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Mathematical descriptor sequence of the actual acquired old catalogue. -/
def records (bits:List Bool) : List Record :=
  (SemiprimeMacroFiniteEnumerations.subdividedVertices (firstAxis bits.length) (secondAxis bits.length)
    (digitCountValue bits)).values.map vertex
/-- Exact global source store after the real included catalogue procedure. -/
def afterCat (bits:List Bool) : Stack→List Bool :=
  Sum.elim (SemiprimeD1StackVertexCatalogueExecution.result bits) (fun _=>[])
/-- Final actual data retain source metadata and contain the physically emitted edge tape. -/
def result (bits:List Bool) : Stack→List Bool :=
  finalData (SemiprimeD1StackVertexCatalogueExecution.result bits) (output (records bits) [])
/-- Actual halted complete producer state. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Whole actual clock before substituting the acquired source-tape byte bound. -/
def budget (bits:List Bool) : ℕ :=
  10000000000000*(bits.length+1)^5+56*(tape (records bits) []).length+6

/-- The original source initial-data fact follows from its actual machine encoding. -/
theorem cat_input (bits:List Bool) (k:Cat.Stack) :
    SemiprimeD1StackVertexCatalogue.input bits k=(if k=Cat.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct Cat.originalInput
    (Cat.kernelStack (SemiprimeD1StackCartesian4.aux 2)) (Sum.inl SemiprimeD1StackVertexCatalogue.Control.main:Cat.Label)
    Cat.program bits
  have he:=hi.trans (SemiprimeD1StackVertexCatalogueExecution.initial_eq bits)
  have hd:=congrArg (fun cfg:SemiprimeD1StackVertexCatalogue.machine.Cfg=>cfg.stk (some k)) he
  change (if k=Cat.originalInput then bits else [])=SemiprimeD1StackVertexCatalogue.input bits k at hd
  exact hd.symm
/-- This whole fixed machine starts from binary N alone. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial (catStack Cat.originalInput) (.inl .main) bits:=by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k
    · simp [cat_input,catStack]
    · simp [catStack]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct (catStack Cat.originalInput) (aux .output) (.inl .main) program bits).symm
/-- The actual source procedure executes once, retaining all its original metadata. -/
theorem cat_call (bits:List Bool) (hb:bits≠[]) :
    ∃m≤10000000000000*(bits.length+1)^5+1,Runs program m (.inl .main) (input bits) (.inl .parse) (afterCat bits) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackVertexCatalogueBounds.source_run_polynomial bits hb
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program catStack catLabel catStack_injective
    Cat.program (.inl .main) (fun _=>rfl) (.inl .main) (.inl .parse) rfl m
    (SemiprimeD1StackVertexCatalogue.initial bits) (SemiprimeD1StackVertexCatalogueExecution.done bits)
    (input bits) (afterCat bits)
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
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl
/-- The transducer input is the ACTUAL acquired catalogue, not a supplied descriptor list. -/
theorem afterCat_clean (bits:List Bool) :
    afterCat bits=clean (SemiprimeD1StackVertexCatalogueExecution.result bits) (tape (records bits) []) (fun _=>[]) [] [] := by
  funext k
  rcases k with k|k|k
  · by_cases hk:k=sourceReader
    · subst k
      change SemiprimeD1VertexCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length)
        (digitCountValue bits) []=tape (records bits) []
      exact (SemiprimeD1EdgeCatalogueEncoding.original_input _ _ _ []).symm
    · simp only [afterCat,Sum.elim_inl,clean,store,ite_eq_right hk]
  · rfl
  · cases k <;> rfl
/-- Reusable real stage after shared catalogue acquisition; original N is its sole source parameter. -/
theorem ready_original (bits:List Bool) :
    ∃m≤56*(tape (records bits) []).length+4,Runs program m (.inl .parse) (afterCat bits) (.inl .halt) (result bits) := by
  rw [afterCat_clean]
  exact ready _ _
/-- WHOLE closed original-input runtime, including source, all parsing/dispatch, final reversal and halt. -/
theorem source_run (bits:List Bool) (hb:bits≠[]) :
    ∃m≤budget bits,C.run program m (initial bits)=some (done bits) := by
  obtain ⟨a,ha,h0⟩:=cat_call bits hb
  obtain ⟨b,hb,h1⟩:=ready_original bits
  have h:=h0.trans h1
  obtain ⟨finish,hr,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨a+b+1,?_,?_⟩
  · unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases hout with ⟨hpc,hdata,hframes⟩
    change C.step program finish=some (done bits)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]
/-- The final edge bytes equal the complete ORIGINAL enumeration, in its exact order. -/
theorem original_edges (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    result bits (aux .output)=(SemiprimePublicAcquiredExecution.edgeEnumeration (bitValue bits)).values.foldr
      SemiprimeD1EdgeCatalogueEncoding.edge [] := by
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  have hb:bits≠[]:=by intro h;subst bits;simp [bitValue] at hN
  change output (records bits) []=_
  unfold records
  rw [SemiprimeD1EdgeCatalogueEncoding.original_output,
    SemiprimeD1StackVertexCatalogueTags.digitCount_raw bits hb,hw]
  rfl
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueExecution
