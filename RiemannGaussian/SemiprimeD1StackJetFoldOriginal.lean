/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldBounds
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshOriginal
import RiemannGaussian.SemiprimeD1WordTapeRecursivePhase
/-! # Exact original phase order and actual child-context cache compatibility
The physical source receives actual prepared child words. Native continuation
functions occur only in the equivalence statement below; they are not executed
by the fold source. The ready bridge uses the NEW child context/precision cache,
and makes no equality assumption between old and new precision caches.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldOriginal
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldProjection
open SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldSpec SemiprimeD1StackJetFoldContext
open SemiprimeD1StackJetFoldExecution
open SemiprimeD1JetAxes (Context)
/-- Every actual ready-cache role is exactly the original context supplier's reached physical word. -/
theorem ready_context (axes:List Nat) (precision children:List Bool) (k:X.Stack):
    (ready axes precision children).data (contextStack k)=SemiprimeD1StackJetContextCorrectness.finalData axes precision k:=by
  change data (bank (acquiredHeader axes precision children) [] [] [] [] [] [] [] [] []) (contextStack k)=_
  rw [data_context]
  fin_cases k <;> rfl
/-- The complete actual15-role NEW child cache retained by Fresh85 matches the SAME-program fold ready entry. -/
theorem fresh_child_cache (a u edges:Nat) (t p:List Bool) (axes:List Nat)
    (hg:SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t=true) (children:List Bool) (k:X.Stack):
    SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t p axes
      (SemiprimeD1StackPhaseChildContextFresh.contextStack (SemiprimeD1StackPhaseChildContext.childStack k))=
      (ready (SemiprimeD1StackPhaseChildContextPrimitives.count a u edges t::axes)
        (SemiprimeD1StackPhaseChildContextPrimitives.precision a u edges t p) children).data (contextStack k):=by
  rw [ready_context,SemiprimeD1StackPhaseChildContextFreshOriginal.context_retained]
  exact (SemiprimeD1StackPhaseChildContextOriginal.acquired_caches a u edges t p axes hg).2 k
/-- Literal64-child-group native word order, without recoding any binary child coefficient. -/
theorem product_sixtyfour (ctx:Context) (children:Fin 64→SemiprimeD1JetAffineCoefficient.JetRun):
    productWords ctx ((List.finRange 64).map (fun g=>(children g).words))=
      (SemiprimeD1RecursiveCounter.product ctx ((List.finRange 64).map children)).words:=by
  simpa only [List.map_map,Function.comp_def] using product_native ctx ((List.finRange 64).map children)
/-- All original mode rows use the same exact64-group order followed by the same literal right sum. -/
theorem output_sixtyfour (axes:List Nat) (precision:List Bool)
    (modes:List (Fin 64→SemiprimeD1JetAffineCoefficient.JetRun)):
    (done axes precision (modes.map (fun row=>(List.finRange 64).map (fun g=>(row g).words)))).data output=
      jetTape (SemiprimeD1JetAffineCoefficient.sumRuns (context axes precision)
        (modes.map (fun row=>SemiprimeD1RecursiveCounter.product (context axes precision)
          ((List.finRange 64).map row)))).words:=by
  have h:=output_native axes precision (modes.map (fun row=>(List.finRange 64).map row))
  simpa only [List.map_map,Function.comp_def] using h
/-- Pure word-level composition of exact mode products with the unchanged native sum order. -/
theorem sum_terms_native {T:Type} (ctx:Context) (xs:List T) (children:T→Group)
    (term:T→SemiprimeD1JetAffineCoefficient.JetRun)
    (hw:∀x∈xs,productWords ctx (children x)=(term x).words):
    sumWords ctx (xs.map children)=(SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map term)).words:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    have hx:=hw x (by simp)
    have ht:=ih (fun y hy=>hw y (by simp [hy]))
    simp only [List.map_cons,sumWords,SemiprimeD1JetAffineCoefficient.sumRuns,hx,ht]
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire SemiprimeD1RecursiveCounter.product
  SemiprimeD1JetAffineCoefficient.sumRuns productWords sumWords
/-- Exact original phase term identity; these named child words describe the prepared input, not a solver opcode. -/
theorem phaseTerm_words (next:Context→SemiprimeD1TensorNetwork.Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (parent:SemiprimeD1RecursiveCallTree.Call) (a u:Nat)
    (t:Fin (SemiprimeD1WireKernelOriginal.size a)) (i:Fin a) (beta:List Nat):
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount parent.net.rows.length 64
      a u i.val parent.ctx.precision (SemiprimeD1TensorNetwork.arity parent.net.rows) (SemiprimeD1TensorNetwork.owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (SemiprimeD1TensorNetwork.edgeCount parent.net) u*(u-i.val)
    let fresh:=SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
    let current:Context:=⟨q::parent.ctx.axes,source.precision⟩
    productWords current ((List.finRange 64).map (fun g=>
      (next current (SemiprimeD1ChildWordNetwork.fromSource parent.net source i g parent.ctx [q]
        source.precision fresh t beta).network).words))=
      (SemiprimeD1WordTapeRecursivePhase.phaseTerm next parent a u t i beta).words:=by
  dsimp only
  unfold SemiprimeD1WordTapeRecursivePhase.phaseTerm
  rw [←product_native]
  simp only [List.map_map,Function.comp_def]
/-- Exact original active-phase total identity for the physical prepared child words, preserving every mode/group order. -/
theorem phaseTotal_words (next:Context→SemiprimeD1TensorNetwork.Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (parent:SemiprimeD1RecursiveCallTree.Call) (a u:Nat)
    (t:Fin (SemiprimeD1WireKernelOriginal.size a)) (i:Fin a):
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount parent.net.rows.length 64
      a u i.val parent.ctx.precision (SemiprimeD1TensorNetwork.arity parent.net.rows) (SemiprimeD1TensorNetwork.owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (SemiprimeD1TensorNetwork.edgeCount parent.net) u*(u-i.val)
    let fresh:=SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
    let current:Context:=⟨q::parent.ctx.axes,source.precision⟩
    sumWords current (source.modes.values.map (fun beta=>(List.finRange 64).map (fun g=>
      (next current (SemiprimeD1ChildWordNetwork.fromSource parent.net source i g parent.ctx [q]
        source.precision fresh t beta).network).words)))=
      (SemiprimeD1WordTapeRecursivePhase.phaseTotal next parent a u t i).words:=by
  dsimp only
  unfold SemiprimeD1WordTapeRecursivePhase.phaseTotal
  apply sum_terms_native
  intro beta _
  exact phaseTerm_words next parent a u t i beta
end RiemannGaussian.SemiprimeD1StackJetFoldOriginal
