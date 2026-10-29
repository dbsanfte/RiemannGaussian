/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
/-! # Actual original-index fitting, independent of coefficient width -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridNode
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
/-- Exact two physical writes of the included fit: consumes actual input and acquires actual fixed-width output. -/
def fitted (w:Words) (word cached:List Bool) :Words:=
  {w with auxiliary:=Function.update w.auxiliary .moveScratch [],registers:=Function.update w.registers (.node,false) (SemiprimeD1StackWordFitExecution.result word cached)}
/-- The included real WordFit consumes overlong raw padding, preserves the physical cache, and clears its actual work. -/
theorem fit_call (w:Words) (word cached:List Bool)
    (hi:∀k,bank w (fitStack k)=SemiprimeD1StackWordFit.store word cached [] [] [] k) :
    Runs program (SemiprimeD1StackWordFitExecution.totalTime word cached+1) (.local .fitNode)
      (bank w) (.local .nodeSign) (bank (fitted w word cached)):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program fitStack Label.fit fit_injective F.program
    .start (fun _=>rfl) (.local .fitNode) (.local .nodeSign) rfl _
    (SemiprimeD1StackWordFit.initial word cached) (SemiprimeD1StackWordFitExecution.done word cached)
    _ _ rfl rfl rfl rfl (SemiprimeD1StackWordFitExecution.source_run word cached)
  · exact ⟨hi,fun _ _=>rfl⟩
  · constructor
    · intro k;fin_cases k
      · rfl
      · exact hi 1
      · exact hi 2
      · exact hi 3
      · rfl
    · intro k hk
      have hm:k≠aux .moveScratch:=by intro he;exact (hk 0 he.symm).elim
      have hn:k≠reg .node false:=by intro he;exact (hk 4 he.symm).elim
      have he:bank (fitted w word cached)=Function.update (Function.update (bank w) (aux .moveScratch) [])
          (reg .node false) (SemiprimeD1StackWordFitExecution.result word cached):=by
        rw [update_auxiliary,update_registers _ (.node,false)]
        rfl
      rw [he,Function.update_of_ne hn,Function.update_of_ne hm]
/-- Fitting the acquired binary index gives EXACT legacy a+2 digits, with no supplied digit word. -/
theorem fit_index (a q:Nat) (word:List Bool) (hv:SemiprimeBitArithmetic.bitValue word=q) (hq:q<2^(a+1)) :
    SemiprimeD1StackWordFitExecution.result word (List.replicate (a+2) false)=
      (SemiprimeD1RecoveryGridBits.index a q).word.numerator.magnitude:=by
  have hb:q<2^(a+2):=by
    have hp:2^(a+2)=2^(a+1)*2:=by rw [show a+2=(a+1)+1 by omega,pow_succ]
    rw [hp]
    omega
  change SemiprimeD1StackWordFitExecution.result word (List.replicate (a+2) false)=
    (SemiprimeEncodedRowSelection.digits (a+2) q).bits
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · rw [SemiprimeD1StackWordFitExecution.result_length,List.length_replicate,SemiprimeEncodedRowSelection.digits_length]
  · change SemiprimeBitArithmetic.bitValue (SemiprimeBitDivision.fitBits word (List.replicate (a+2) false)).bits=_
    rw [SemiprimeBitDivision.fitBits_value (by simpa only [List.length_replicate,hv] using hb),hv,
      SemiprimeEncodedRowSelection.digits_value _ _ hb]
/-- Own exact paid prefix clock, including original binary copy, both index literals and the real fit call. -/
def runBound (word cached:List Bool) :Nat:=5*word.length+4+SemiprimeD1StackWordFitExecution.totalTime word cached+1+2
/-- Honest physical index cache acquisition keeps binary t and the separate coefficient-width template intact. -/
theorem node_run (w:Words) (word cached:List Bool)
    (ht:w.auxiliary .originalT=word) (hw:w.auxiliary .indexTemplate=cached)
    (hmove:w.auxiliary .moveScratch=[]) (hscan:w.auxiliary .scan=[])
    (horder:w.auxiliary .orderTodo=[]) (hs:w.auxiliary .copyScratch=[])
    (hn:w.registers (.node,false)=[]) (hd:w.registers (.node,true)=[]) :
    Runs program (runBound word cached) (.local .node) (bank w) (.local .originalT)
      (bank {w with registers:=Function.update (Function.update w.registers (.node,false) (false::SemiprimeD1StackWordFitExecution.result word cached)) (.node,true) [true]}):=by
  let copied:Words:={w with auxiliary:=Function.update w.auxiliary .moveScratch word}
  have h0:=PTrace.copy_call .node (.local .node) (.local .fitNode) rfl (bank w) word [] ht hmove hs
  change Runs program _ _ _ _ (Function.update (bank w) (aux .moveScratch) (word++[])) at h0
  rw [List.append_nil,update_auxiliary] at h0
  have hi:∀k,bank copied (fitStack k)=SemiprimeD1StackWordFit.store word cached [] [] [] k:=by
    intro k;fin_cases k
    · rfl
    · exact hw
    · exact horder
    · exact hscan
    · exact hn
  have h1:=fit_call copied word cached hi
  have he:fitted copied word cached={w with registers:=Function.update w.registers (.node,false) (SemiprimeD1StackWordFitExecution.result word cached)}:=by
    dsimp only [fitted,copied]
    rw [Function.update_idem]
    congr 1
    exact Function.update_eq_self_iff.mpr hmove.symm
  rw [he] at h1
  let out:Words:={w with registers:=Function.update w.registers (.node,false) (SemiprimeD1StackWordFitExecution.result word cached)}
  have h2:=PTrace.push_run (.local .nodeSign) (.local .nodeDen) (reg .node false) false (bank out) rfl
  change Runs program 1 _ _ _ (Function.update (bank out) (reg .node false)
    (false::SemiprimeD1StackWordFitExecution.result word cached)) at h2
  rw [update_registers _ (.node,false)] at h2
  have h3:=PTrace.push_run (.local .nodeDen) (.local .originalT) (reg .node true) true
    (bank {out with registers:=Function.update out.registers (.node,false) (false::SemiprimeD1StackWordFitExecution.result word cached)}) rfl
  have hd1:({out with registers:=Function.update out.registers (.node,false) (false::SemiprimeD1StackWordFitExecution.result word cached)}:Words).registers (.node,true)=[]:=hd
  change Runs program 1 _ _ _ (Function.update _ (reg .node true) (true::_)) at h3
  change Runs program 1 _ _ _ (Function.update _ (reg .node true)
    (true::({out with registers:=Function.update out.registers (.node,false) (false::SemiprimeD1StackWordFitExecution.result word cached)}:Words).registers (.node,true))) at h3
  rw [hd1,update_registers _ (.node,true)] at h3
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  dsimp only [out] at h
  rw [Function.update_idem] at h
  simpa only [runBound,show 5*word.length+4+(SemiprimeD1StackWordFitExecution.totalTime word cached+1)+1+1=
    5*word.length+4+SemiprimeD1StackWordFitExecution.totalTime word cached+1+2 by omega] using h
end RiemannGaussian.SemiprimeD1StackRecoveryGridNode
