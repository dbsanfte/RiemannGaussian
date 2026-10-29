/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeBounds
import RiemannGaussian.SemiprimeD1StackEdgeCount
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeOriginal
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipeClassify SemiprimeD1StackPortOwnerRecipeExecution
open SemiprimeD1StackPortOwnerRecipeBounds
open SemiprimeD1StackUnaryDivmod (unary)
/-- Literal original Edge13 field order: half, tag, and four scalar coordinates. -/
def fieldInput : Fin 6→Input := ![.half,.tag,.a,.b,.c,.d]
/-- Original parsed descriptor words are exactly their actually acquired unary counters. -/
theorem bit_unary {r t digits:ℕ} (s:SemiprimeMacroGraph.BitSignal r t digits) (part:Fin 5) :
    unary ((SemiprimeD1EdgeCatalogueEncoding.bit s part).length)=SemiprimeD1EdgeCatalogueEncoding.bit s part := by
  rcases s with ⟨w,b⟩|flag
  · cases w <;> fin_cases part <;>
      simp [SemiprimeD1EdgeCatalogueEncoding.bit,SemiprimeD1EdgeCatalogueEncoding.fields,unary]
  · cases flag <;> fin_cases part <;>
      simp [SemiprimeD1EdgeCatalogueEncoding.bit,SemiprimeD1EdgeCatalogueEncoding.fields,unary]
/-- Evaluator entry bytes agree with the actual already-parsed original edge record,
including its empty half word. No independently encoded native key is supplied. -/
theorem original_field {r t digits:ℕ} (edge:SemiprimeMacroGraph.Edge r t digits) (part:Fin 6) :
    words (original edge) (fieldInput part)=SemiprimeD1StackEdgeCount.edgeFields edge part := by
  fin_cases part
  · cases hh:edge.2 <;> simp [fieldInput,words,original,SemiprimeD1StackEdgeCount.edgeFields,
      SemiprimeD1EdgeCatalogueEncoding.sideWord,hh]
  · exact bit_unary edge.1 0
  · exact bit_unary edge.1 1
  · exact bit_unary edge.1 2
  · exact bit_unary edge.1 3
  · exact bit_unary edge.1 4
/-- Complete actual original-record arithmetic endpoint compiler, with fixed polynomial clock. -/
theorem original_source_polynomial {r t digits:ℕ} (hd:0<digits)
    (edge:SemiprimeMacroGraph.Edge r t digits) :
    ∃time≤200000*(SemiprimeD1StackPortOwnerRecipeNumeric.volume (original edge)+1)^4,
      C.run program time (initial (words (original edge)))=some (done (original edge) (originalTag edge)) :=
  source_run_polynomial (original edge) (originalTag edge) (original_tag edge) hd
/-- The physically emitted original key is compact because its own true sentinel was pushed. -/
theorem original_compact {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (edge:SemiprimeMacroGraph.Edge r t digits) :
    SemiprimeSourceCompactBits.Compact ((done (original edge) (originalTag edge)).data (aux .output)) := by
  rw [output_original hd hc edge]
  exact SemiprimeD1PortOwnerKeys.key_compact _
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeOriginal
