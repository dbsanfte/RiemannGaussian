/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafComponents
/-! # Whole N-only and acquired-cache entries of the SAME literal leaf source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafExecution
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackRootScaleLeafComponents SemiprimeD1StackProcedureTrace
/-- Exact complete final data and empty internal real return stack. -/
def done (bits : List Bool) : C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- Whole source cubic includes the one actual old metadata acquisition call. -/
def runBound (bits : List Bool) : Nat :=10000000000000*(bits.length+1)^3
/-- Ready entry performs only scaling, exact square root and actual leaf division. -/
theorem ready_run (bits : List Bool) :
    ∃t≤readyBound bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) :=by
  obtain ⟨t,ht,hr⟩:=ready_trace bits
  obtain ⟨finish,hf,hAt⟩:=hr [] (ready bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result bits) [] finish hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- One real call executes the frozen original-N source, not a template/cache supplier. -/
theorem root_call (bits : List Bool) :
    ∃t≤SemiprimeD1StackRootScheduleExecution.runBound bits+1,
      Runs program t .start (input bits) .ready (base bits) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootScheduleExecution.source_run bits
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root root_injective
    R.program .start (fun _=>rfl) .start .ready rfl t (R.initial bits)
    (SemiprimeD1StackRootScheduleExecution.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- WHOLE original-input pipeline pays all old metadata/scaling/root/division
instructions on ONE fixed finite program with N as its sole initial input. -/
theorem source_trace (bits : List Bool) :
    ∃t,t+1≤runBound bits ∧ Runs program t .start (input bits) .done (result bits) :=by
  obtain ⟨a,ha,h0⟩:=root_call bits
  obtain ⟨b,hb,h1⟩:=ready_trace bits
  refine ⟨a+b,?_,join h0 h1⟩
  unfold runBound readyBound SemiprimeD1StackRootScheduleExecution.runBound at *
  have hp:1≤(bits.length+1)^3:=by
    have h:0<(bits.length+1)^3:=by positivity
    omega
  omega
/-- Actual complete halt from the sole original binary input word. -/
theorem source_run (bits : List Bool) :
    ∃t≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) :=by
  obtain ⟨t,ht,hr⟩:=source_trace bits
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result bits) [] finish hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- True one-input initialization contains no acquired metadata or answer words. -/
theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) :=by
  have hs:SemiprimeD1StackCalls.initial (rootStack (R.boot .input)) Label.start bits=initial bits:=by
    apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:C.State Stack Label))
    funext j
    rcases j with j|j
    · rcases j with j|j
      · cases j <;> rfl
      · rcases j with j|j <;> rfl
    · rcases j with j|j <;> rfl
  exact (SemiprimeD1StackCalls.initial_correct (rootStack (R.boot .input)) (aux .leaf) Label.start program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Genuine fixed finite machine from ORIGINAL N, with its complete own polynomial. -/
noncomputable def acquireInTime (bits : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits) :=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (rootStack (R.boot .input)) (aux .leaf) .start program
  let h:=source_run bits
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- The SAME finite machine can continue directly from the actual acquired15-role
cache; this certificate contains NO second metadata/bootstrap acquisition. -/
noncomputable def readyInTime (bits : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (ready bits))
      (some (SemiprimeD1StackCalls.configuration (done bits))) (readyBound bits) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (rootStack (R.boot .input)) (aux .leaf) .start program
  let h:=ready_run bits
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackRootScaleLeafExecution
