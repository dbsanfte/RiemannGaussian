/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueFields
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueSource
/-! # Actual complete eighteen-tag source from physically parsed descriptor fields -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueRows
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
namespace DR
export SemiprimeD1StackAllDescriptorRecordOriginal (rawFields originalCode raw_canonical raw_transform_bound)
end DR
namespace DS
export SemiprimeD1StackAllDescriptorRecordSpec (done nextHistory timeBound)
end DS
namespace E
export SemiprimeD1EdgeCatalogueEncoding (vertex)
end E
/-- Actual raw fields agree exactly with the full descriptor source's original six-word notation. -/
theorem raw_original (bits:List Bool) (v:SemiprimePublicAcquiredExecution.PublicVertex (SemiprimeBitArithmetic.bitValue bits)) :
    raw bits (E.vertex v)=DR.rawFields bits v:=rfl
/-- Every original descriptor invokes the REAL full source, with physical N/scope aliases
and no type, mode, table, factor ordinal or checker answer supplied to control. -/
theorem descriptor_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits)
    (vertex:SemiprimePublicAcquiredExecution.PublicVertex (SemiprimeBitArithmetic.bitValue bits))
    (fibre:F.Stack→List Bool) (catalogue:V.Stack→List Bool) (hist out:List Bool)
    (words:List (List Bool)) (hn:fibre F.originalInput=bits)
    (hb:fibre F.output=SemiprimeD1TensorTapeCodec.vectorBits words) :
    ∃t≤DS.timeBound (DR.originalCode vertex) (DR.rawFields bits vertex) words hist out,
      Runs program (t+1) (.local .row) (data fibre catalogue (E.vertex vertex) hist out)
        (.local (.clearField 0))
        (data fibre catalogue (E.vertex vertex)
          (DS.nextHistory (DR.originalCode vertex) (DR.rawFields bits vertex) words hist out) out):=by
  obtain ⟨htag,h2,h3,h4⟩:=DR.raw_canonical bits vertex
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackAllDescriptorRecordExecution.source_run
    (DR.originalCode vertex) (DR.rawFields bits vertex) htag h2 h3 h4 (DR.raw_transform_bound bits vertex) hc hN words hist out
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program descriptorStack Label.descriptor descriptor_injective
    D.program (.inl .start) (fun _=>rfl) (.local .row) (.local (.clearField 0)) rfl t
    (SemiprimeD1StackAllDescriptorRecord.initial (DR.rawFields bits vertex)
      (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)
    (DS.done (DR.originalCode vertex) (DR.rawFields bits vertex) words hist out)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      have h:=data_descriptor fibre catalogue (E.vertex vertex) hist out [] k
      rw [hn,hb,raw_original] at h
      exact h
    · intro k _;rfl
  · constructor
    · intro k
      have h:=data_descriptor fibre catalogue (E.vertex vertex)
        (DS.nextHistory (DR.originalCode vertex) (DR.rawFields bits vertex) words hist out) out [] k
      rw [hn,hb,raw_original] at h
      exact h
    · intro k hk
      rcases k with k|k|k|k
      · rfl
      · rfl
      · by_cases h0:k=D.source 0
        · subst k;rfl
        · by_cases hb:k=D.scopeBank
          · subst k;rfl
          · have he:descriptorStack k=.inr (.inr (.inl k)):=by simp only [descriptorStack,h0,hb,ite_false]
            exact (hk k he).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueRows
