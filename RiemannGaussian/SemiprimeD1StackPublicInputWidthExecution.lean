/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputWidth

/-! # Whole original-input active-digit bound trace
Actual public acquisition runs ONCE, followed by the complete bound program
on directly shared acquired caches. No normalized counter or solved bound is
an endpoint assumption; the only other input is the actual index tape.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicInputWidthExecution
open SemiprimeD1StackPublicInputWidth SemiprimeD1StackProcedureTrace
/-- Specification of the actual completed public preprocessing cells. -/
def context (bits : List Bool) : P.Stack→List Bool := SemiprimeD1BinaryPublicAcquisitionComponents.result bits
/-- Child cache is obtained from the ACTUALLY shared physical cells. -/
def cache (bits index : List Bool) : W.Cache := ⟨context bits widthKey,context bits radixKey,index⟩
/-- Physical reached payload after complete public acquisition once. -/
def ready (bits index : List Bool) : Stack→List Bool := Sum.elim (context bits) (privateInput index)
/-- Physical completed cells; no hidden width/radix copies occupy private shadows. -/
def result (bits index : List Bool) : Stack→List Bool :=
  Sum.elim (context bits) (fun k=>if k=.indexCache then index else if k=.output then
    SemiprimeD1StackInputWidthExecution.bound (cache bits index) else [])
/-- Exact whole original-input source halt. -/
def done (bits index : List Bool) : C.State Stack Label := ⟨none,none,none,result bits index,[]⟩
/-- Both actual complete calls, their real returns and the enclosing halt. -/
def timeBound (bits index : List Bool) : ℕ :=
  SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+
    SemiprimeD1StackInputWidthBounds.runBound (cache bits index)+3

/-- The ORIGINAL binary N preprocessing is executed inside this SAME program. -/
theorem acquire_call (bits index : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits,
      Runs program (t+1) .start (input bits index) .bound (ready bits index) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.preprocess Sum.inl_injective
    P.program (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) (fun _=>rfl) .start .bound rfl t
    (P.initial bits) (⟨none,none,none,context bits,[]⟩:C.State P.Stack P.Label)
    (input bits index) (ready bits index)
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
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl

/-- The actual acquired bit-count and radix are shared directly with the
complete physical offset/minimum/bound procedure. No cache format is assumed. -/
theorem bound_call (bits index : List Bool) :
    ∃t≤SemiprimeD1StackInputWidthBounds.runBound (cache bits index),
      Runs program (t+1) .bound (ready bits index) .done (result bits index) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackInputWidthBounds.source_run_bounded (cache bits index)
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program widthStack Label.acquisition width_injective
    W.program .start (fun _=>rfl) .bound .done rfl t
    (W.initial (cache bits index)) (SemiprimeD1StackInputWidthExecution.done (cache bits index))
    (ready bits index) (result bits index)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (hk .output rfl).elim

/-- COMPLETE actual original-input bound construction, with no width, target,
digit count, active/inactive verdict, product, bound word or elapsed advice. -/
theorem source_run (bits index : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits index,C.run program t (initial bits index)=some (done bits index) := by
  obtain ⟨a,ha,h0⟩:=acquire_call bits index hb
  obtain ⟨b,hbTime,h1⟩:=bound_call bits index
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hr,ho⟩:=h [] (initial bits index) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (result bits index) [] finish ho
  refine ⟨(a+1)+(b+1)+1,by unfold timeBound;omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
  rfl
/-- Actual singleton-high bound word is the physical designated output. -/
theorem output_bound (bits index : List Bool) :
    (done bits index).data output=SemiprimeD1StackInputWidthExecution.bound (cache bits index) := rfl
/-- Every actual original public cache survives this entire computation. -/
theorem retained_public (bits index : List Bool) (k : P.Stack) : (done bits index).data (.inl k)=context bits k := rfl
/-- The actual original index bytes, including arbitrary marker bits, survive. -/
theorem retained_index (bits index : List Bool) : (done bits index).data (.inr .indexCache)=index := rfl
end RiemannGaussian.SemiprimeD1StackPublicInputWidthExecution
