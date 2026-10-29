/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogue

/-! # Literal source/metadata/arity inclusions of the actual port producer -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueComponents
open SemiprimeD1StackPortCatalogue
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackUnaryDivmod (unary)

/-- The original edge-source data embed literally. -/
theorem edgeStack_injective : Function.Injective edgeStack := Sum.inl_injective
/-- Shared vertex data are included without aliasing any original role. -/
theorem vertexStack_injective : Function.Injective vertexStack := by
  intro a b h
  simpa only [vertexStack,edgeStack,E.catStack,Sum.inl.injEq] using h
/-- All fifteen actual arity operands/work roles remain distinct. -/
theorem arityStack_injective : Function.Injective arityStack := by decide
/-- Arity output is private work, separate from every actual readonly input. -/
theorem aritySource_remaining (key:A.Source) : aritySource key≠aux .remaining := by cases key <;> decide
/-- Actual original tape/source/destination copy operands are distinct. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- Physical field input/cache/scratch/valid are disjoint. -/
theorem fieldStack_injective (part:Fin 5) : Function.Injective (fieldStack part) := by
  intro a b h
  rcases a with a|a <;> rcases b with b|b
  · cases a <;> cases b <;> simp_all [fieldStack,aux,oldAux,cache,edgeStack,E.cache,E.aux]
  · cases a <;> cases b <;> simp_all [fieldStack,aux,oldAux,cache,edgeStack,E.cache,E.aux]
  · cases a;cases b <;> simp_all [fieldStack,aux,oldAux,cache,edgeStack,E.cache,E.aux]
  · cases a;cases b;rfl
/-- No actual field source is the frame buffer. -/
theorem frameSource_buffer (part:Fin 8) : frameSource part≠oldAux .frameBuffer := by fin_cases part <;> decide
/-- No actual field source is temporary frame scratch. -/
theorem frameSource_scratch (part:Fin 8) : frameSource part≠oldAux .frameScratch := by fin_cases part <;> decide
/-- Every field framing call has three distinct physical operands. -/
theorem frameStack_injective (part:Fin 8) : Function.Injective (frameStack part) := by
  have h0:=frameSource_buffer part
  have h1:=frameSource_scratch part
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [frameStack,oldAux,edgeStack,E.aux]
/-- Both actual reversals use distinct source/destination words. -/
theorem reverseStack_injective (finish:Bool) : Function.Injective (reverseStack finish) := by cases finish <;> decide

/-- Actual arity input data are just the physically parsed fields and acquired metadata. -/
theorem arity_input {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits) (store:Stack→List Bool)
    (hh:∀key,store (aritySource key)=SemiprimeD1StackVertexArityOriginal.originalHeader v key)
    (hw:∀key,store (arityAux key)=[]) :
    LinkB.DataRel arityStack store
      (SemiprimeD1StackVertexArityView.store (SemiprimeD1StackVertexArityOriginal.originalHeader v) [] [] [] [] [] []) store := by
  constructor
  · intro k
    cases k with
    | inl key => exact hh key
    | inr key =>
      change store (arityAux key)=_
      rw [hw key]
      cases key <;> rfl
  · intro k _;rfl
/-- Returning actual arity changes only the private remaining-port counter. -/
theorem arity_output {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits) (store:Stack→List Bool)
    (hh:∀key,store (aritySource key)=SemiprimeD1StackVertexArityOriginal.originalHeader v key)
    (hw:∀key,store (arityAux key)=[]) :
    LinkB.DataRel arityStack store (SemiprimeD1StackVertexArityOriginal.done v).data
      (Function.update store (aux .remaining) (unary (SemiprimeMacroGraph.subdividedArity v))) := by
  constructor
  · intro k
    cases k with
    | inl key =>
      rw [show arityStack (.inl key)=aritySource key from rfl,
        Function.update_of_ne (aritySource_remaining key),hh key]
      rfl
    | inr key =>
      by_cases hk:key=SemiprimeD1StackVertexArity.Aux.arity
      · subst key
        change Function.update store (aux .remaining) (unary (SemiprimeMacroGraph.subdividedArity v)) (aux .remaining)=_
        rw [Function.update_self]
        rfl
      · have hn:arityAux key≠aux .remaining:=by
          intro he
          have hc:arityStack (.inr key)=arityStack (.inr SemiprimeD1StackVertexArity.Aux.arity):=he
          exact hk (Sum.inr.inj (arityStack_injective hc))
        rw [show arityStack (.inr key)=arityAux key from rfl,Function.update_of_ne hn,hw key]
        cases key <;> first | contradiction | rfl
  · intro k hk
    have hn:k≠aux .remaining:=by intro he;exact hk (.inr SemiprimeD1StackVertexArity.Aux.arity) he.symm
    exact Function.update_of_ne hn _ _
/-- Original arity is acquired by REAL copied-counter/product/comparison calls.
There is no desired arity, truth verdict, Fits or time supplier premise. -/
theorem arity_call {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits) (store:Stack→List Bool)
    (hh:∀key,store (aritySource key)=SemiprimeD1StackVertexArityOriginal.originalHeader v key)
    (hw:∀key,store (arityAux key)=[]) :
    ∃time≤SemiprimeD1StackVertexArityRecipes.recipeBudget
      (SemiprimeD1StackVertexArityOriginal.indexValue v) (r*t+1) r t digits+109,
      Runs program time (.local .arity) store (.local .loop)
        (Function.update store (aux .remaining) (unary (SemiprimeMacroGraph.subdividedArity v))) := by
  obtain ⟨time,ht,he⟩:=SemiprimeD1StackVertexArityOriginal.source_run v
  refine ⟨time+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program arityStack Label.arity arityStack_injective
    A.program (.inl .main) (fun _=>rfl) (.local .arity) (.local .loop) rfl time
    (⟨some (.inl .main),none,none,
      SemiprimeD1StackVertexArityView.store (SemiprimeD1StackVertexArityOriginal.originalHeader v) [] [] [] [] [] [],[]⟩:C.State A.Stack A.Label)
    (SemiprimeD1StackVertexArityOriginal.done v)
    store (Function.update store (aux .remaining) (unary (SemiprimeMacroGraph.subdividedArity v)))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact he
  · exact arity_input v store hh hw
  · exact arity_output v store hh hw
end RiemannGaussian.SemiprimeD1StackPortCatalogueComponents
