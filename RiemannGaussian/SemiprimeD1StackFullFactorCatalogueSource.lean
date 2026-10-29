/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueView
import RiemannGaussian.SemiprimeD1StackFactorScopeFibreBounds
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual original-N setup of the retained-source full factor sweep -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueSource
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueView
open SemiprimeD1StackProcedureFragments (Runs included_call one_base)
namespace FS
export SemiprimeD1StackFactorScopeFibre (result)
end FS
namespace VS
export SemiprimeD1StackVertexCatalogue (input initial)
export SemiprimeD1StackVertexCatalogueExecution (result done)
end VS
/-- Actual source retains original binary N, without normalization or re-encoding. -/
theorem retained_N (bits : List Bool) : FS.result bits [] F.originalInput=bits := by rfl
/-- The actual catalogue initializer loads binary N in exactly its single input role. -/
theorem catalogue_input (bits : List Bool) (k : V.Stack) :
    VS.input bits k=(if k=V.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct V.originalInput catalogueOutput (.inl .main) V.program bits
  have he:=hi.trans (SemiprimeD1StackVertexCatalogueExecution.initial_eq bits)
  have hd:=congrArg (fun cfg:SemiprimeD1StackVertexCatalogue.machine.Cfg=>cfg.stk (some k)) he
  exact hd.symm
/-- Genuine physical data after the complete source and its first actual factor query. -/
def afterSource (bits : List Bool) : Stack→List Bool :=
  data (FS.result bits []) (fun _=>[]) (fun _=>[]) [] []
/-- Genuine physical data after the real preserving binary-N copy. -/
def afterCopy (bits : List Bool) : Stack→List Bool :=
  data (FS.result bits []) (VS.input bits) (fun _=>[]) [] []
/-- Genuine physical data after all original descriptors are actually acquired. -/
def afterCatalogue (bits : List Bool) : Stack→List Bool :=
  data (FS.result bits []) (VS.result bits) (fun _=>[]) [] []
/-- The loop-ready data include the one physically pushed final false terminator. -/
def ready (bits : List Bool) : Stack→List Bool :=
  data (FS.result bits []) (VS.result bits) (fun _=>[]) [] [false]
/-- One real included call executes the source once and computes the first actual scope. -/
theorem source_call (bits : List Bool) (hb:bits≠[]) :
    ∃t ≤ SemiprimeD1StackFactorScopeFibreBounds.runBound bits [],
      Runs program (t+1) (.local .main) (input bits) (.local .copyN) (afterSource bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackFactorScopeFibreExecution.source_run bits [] hb
  refine ⟨t,ht.trans (SemiprimeD1StackFactorScopeFibreBounds.timeBound_le bits [] hb),?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program sourceStack Label.source Sum.inl_injective
    F.program .main (fun _=>rfl) (.local .main) (.local .copyN) rfl t
    (F.initial bits []) (SemiprimeD1StackFactorScopeFibre.done bits [])
    (input bits) (afterSource bits) rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>unfold afterSource;rw [empty_outer];rfl
/-- Original binary N is copied physically; no second N value is preloaded. -/
theorem copy_N (bits : List Bool) :
    Runs program (5*bits.length+4) (.local .copyN) (afterSource bits) (.local .catalogue) (afterCopy bits) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.local .copyN) (.local .catalogue) rfl (5*bits.length+3)
    (SemiprimeD1StackCopy.state 0 none bits [] []) (SemiprimeD1StackCopy.done bits bits)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words bits [] none
  · constructor
    · intro k
      fin_cases k
      · exact retained_N bits
      · rfl
      · rfl
    · intro k _;rfl
  · constructor
    · intro k
      fin_cases k
      · exact retained_N bits
      · change VS.input bits V.originalInput=bits
        rw [catalogue_input,ite_eq_left rfl]
      · rfl
    · intro k hk
      rcases k with k|k|k|k
      · rfl
      · have hn:k≠V.originalInput:=by intro h;subst k;exact hk 1 rfl
        change VS.input bits k=[]
        rw [catalogue_input,ite_eq_right hn]
      · rfl
      · rfl
/-- The actual complete53-role original catalogue source runs after the paid N copy. -/
theorem catalogue_call (bits : List Bool) (hb:bits≠[]) :
    ∃t ≤ 10000000000000*(bits.length+1)^5,
      Runs program (t+1) (.local .catalogue) (afterCopy bits) (.local .seed) (afterCatalogue bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackVertexCatalogueBounds.source_run_polynomial bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program catalogueStack Label.catalogue
    (by intro a b h;exact Sum.inl_injective (Sum.inr_injective h)) V.program (.inl .main)
    (fun _=>rfl) (.local .catalogue) (.local .seed) rfl t (VS.initial bits) (VS.done bits)
    (afterCopy bits) (afterCatalogue bits) rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k
      · rfl
      · exact (hk k rfl).elim
      · rfl
      · rfl
/-- The record terminator is one actual allocated false bit on the physical output. -/
theorem seed_run (bits : List Bool) :
    Runs program 1 (.local .seed) (afterCatalogue bits) (.local .loop) (ready bits) := by
  apply one_base program (.local .seed) (.local .loop) (.push output false (.local .loop)) _ _ rfl
  · rfl
  · exact update_output _ _ _ _ _ _ _
/-- Own setup clock includes the source/filter, N copy, catalogue and false push. -/
def setupBound (bits : List Bool) : Nat :=
  SemiprimeD1StackFactorScopeFibreBounds.runBound bits []+10000000000000*(bits.length+1)^5+5*bits.length+7
/-- Complete original-N setup trace, before the separately required descriptor loop. -/
theorem setup_run (bits : List Bool) (hb:bits≠[]) :
    ∃t ≤ setupBound bits,Runs program t (.local .main) (input bits) (.local .loop) (ready bits) := by
  obtain ⟨s,hs,h0⟩:=source_call bits hb
  have h1:=copy_N bits
  obtain ⟨c,hc,h2⟩:=catalogue_call bits hb
  have h3:=seed_run bits
  refine ⟨(s+1)+((5*bits.length+4)+((c+1)+1)),?_,h0.trans (h1.trans (h2.trans h3))⟩
  unfold setupBound
  omega
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueSource
