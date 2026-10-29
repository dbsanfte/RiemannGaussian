/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueView
/-! # Actual parsed-descriptor arity acquisition inside the original port producer -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueArity
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueComponents
open SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Only the actual retained source counters, shared by every vertex. -/
def Metadata (r t digits:ℕ) (base:V.Stack→List Bool) : Prop :=
  base (V.cacheStack 4)=unary (r*t+1) ∧
  base (V.rootStack (SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 0)))=unary r ∧
  base (V.rootStack (SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 1)))=unary t ∧
  base (V.countStack SemiprimeD1StackDigitCount.Stack.count)=unary digits
/-- Original descriptor words and retained counters supply every real arity operand. -/
theorem header {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits)
    (base:V.Stack→List Bool) (hm:Metadata r t digits base)
    (tape raw slot edges factor occurrence:List Bool) :
    ∀key,clean base tape (SemiprimeD1EdgeCatalogueEncoding.vertex v)
      raw slot edges factor occurrence [] (aritySource key)=
      SemiprimeD1StackVertexArityOriginal.originalHeader v key := by
  intro key
  rcases hm with ⟨hR,hr,ht,hd⟩
  cases key with
  | tag => rfl
  | index => rfl
  | radiusSucc => exact hR
  | firstAxis => exact hr
  | secondAxis => exact ht
  | digits => exact hd
/-- Each actual original vertex computes its arity; the edge cache and all ordinals survive. -/
theorem arity_run {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits)
    (base:V.Stack→List Bool) (hm:Metadata r t digits base)
    (tape raw slot edges factor occurrence:List Bool) :
    ∃time≤SemiprimeD1StackVertexArityRecipes.recipeBudget
      (SemiprimeD1StackVertexArityOriginal.indexValue v) (r*t+1) r t digits+109,
      Runs program time (.local .arity)
        (clean base tape (SemiprimeD1EdgeCatalogueEncoding.vertex v) raw slot edges factor occurrence [])
        (.local .loop)
        (clean base tape (SemiprimeD1EdgeCatalogueEncoding.vertex v) raw slot edges factor occurrence
          (unary (SemiprimeMacroGraph.subdividedArity v))) := by
  have hw:∀key,clean base tape (SemiprimeD1EdgeCatalogueEncoding.vertex v)
      raw slot edges factor occurrence [] (arityAux key)=[]:=by intro key;cases key <;> rfl
  obtain ⟨time,ht,he⟩:=arity_call v _ (header v base hm tape raw slot edges factor occurrence) hw
  rw [clean_remaining] at he
  exact ⟨time,ht,he⟩
end RiemannGaussian.SemiprimeD1StackPortCatalogueArity
