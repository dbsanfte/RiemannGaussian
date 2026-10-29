/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeAcquisition
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeClassify
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeOutput
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeExecution
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipeAcquisition SemiprimeD1StackPortOwnerRecipeClassify
open SemiprimeD1StackPortOwnerRecipeDecision SemiprimeD1StackPortOwnerRecipeEmit
open SemiprimeD1StackProcedureTrace (Runs runs_trans halt_run)
/-- Chronological sum of actual literal-tag, arithmetic, tag scan, decision and framing work. -/
def budget (p:Counters) (tag:Tag) : ℕ :=
  (406+remainingBudget p 41 0)+(p.tag+1)+4+(6*mass p (selected p tag)+31)+1
/-- Exact actual halted store: acquired operands/caches retained, compact endpoint key physically emitted. -/
def done (p:Counters) (tag:Tag) : C.State Stack Label :=
  ⟨none,none,none,SemiprimeD1StackPortOwnerRecipeEmit.store p (selected p tag) 6,[]⟩
/-- ALL eight original constructor branches execute the SAME fixed finite source.
Input consists only of acquired unary metadata/edge fields and the actual half marker. -/
theorem source_run (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) (hd:0<p.digits) :
    ∃time≤budget p tag,C.run program time (initial (words p))=some (done p tag) := by
  obtain ⟨a,ha,hacq⟩:=acquisition_run p
  have hclass:=classify_run p tag ht
  obtain ⟨d,hdTime,hdecision⟩:=decision_run p tag hd
  have hemit:=emit_run p (selected p tag)
  have h:=runs_trans program _ _ _ _ _ _ _ _ hacq (runs_trans program _ _ _ _ _ _ _ _ hclass
    (runs_trans program _ _ _ _ _ _ _ _ hdecision hemit))
  obtain ⟨finish,hr,hout⟩:=h [] (initial (words p)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .halt) rfl (done p tag).data [] finish hout
  refine ⟨(a+((p.tag+1)+(d+(6*mass p (selected p tag)+31))))+1,?_,?_⟩
  · unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hh]
    rfl
/-- Physically emitted compact bytes are exactly the literal arithmetic endpoint recipe. -/
theorem output_expected (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) :
    (done p tag).data (aux .output)=expected p := by
  change suffix p (selected p tag) 6=expected p
  exact SemiprimeD1StackPortOwnerRecipeOutput.output_expected p tag ht
/-- Exact full original forward arithmetic endpoint, not a supplied key/permutation premise. -/
theorem output_original {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (edge:SemiprimeMacroGraph.Edge r t digits) :
    (done (original edge) (originalTag edge)).data (aux .output)=
      SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc edge false) := by
  rw [output_expected _ _ (original_tag edge)]
  exact expected_original hd hc edge
/-- Whole actual compiler execution on EVERY actual original edge record and acquired dimensions. -/
theorem original_source_run {r t digits:ℕ} (hd:0<digits) (edge:SemiprimeMacroGraph.Edge r t digits) :
    ∃time≤budget (original edge) (originalTag edge),C.run program time (initial (words (original edge)))=
      some (done (original edge) (originalTag edge)) :=
  source_run (original edge) (originalTag edge) (original_tag edge) hd
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeExecution
