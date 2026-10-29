/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackValidationLink

/-! # Exact nested-procedure caller composition
This joins complete proved nested-call traces to actual larger callers. Every
internal call/return is preserved, not abstracted as a component evaluator.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
open SemiprimeD1StackProcedureTrace

/-- A literal real call executes the included nested-call component trace,
then physically returns, preserving every outer frame and auxiliary cell. -/
theorem included_call {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (program : G→C.Instruction K G) (stack : A→K) (label : L→G)
    (hinj : Function.Injective stack) (component : L→C.Instruction A L) (entry : L)
    (hcode : ∀l,program (label l)=SemiprimeD1StackValidationLink.instruction stack label (component l))
    (pc next : G) (hcall : program pc=.call (label entry) next)
    (time : ℕ) (source out : C.State A L) (data result : K→List Bool)
    (hentry : source.pc=some entry) (hstart : source.frames=[])
    (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : C.run component time source=some out)
    (hin : SemiprimeD1StackMultiplierLink.DataRel stack data source.data data)
    (hout : SemiprimeD1StackMultiplierLink.DataRel stack data out.data result) :
    Runs program (time+1) pc data next result := by
  intro frames target h
  rcases h with ⟨hpc,hdata,houter⟩
  let mid:=C.execute (.call (label entry) next) target
  have hm : C.run program 1 target=some mid := by
    change C.step program target=some mid
    simp only [C.step,SemiprimeD1StackCalls.step,hpc,Option.map_some,hcall,mid]
  have hrel : SemiprimeD1StackValidationLink.Rel stack label data next frames source mid := by
    constructor
    · change SemiprimeD1StackMultiplierLink.DataRel stack data source.data target.data
      rw [hdata]
      exact hin
    · simp only [SemiprimeD1StackValidationLink.PcRel,hentry,hstart,List.map_nil,List.nil_append,
        mid,C.execute,houter,and_self]
  obtain ⟨finish,hfinish,hrel⟩:=SemiprimeD1StackValidationLink.run_rel stack label hinj
    program component hcode data next frames time source out mid hrel hr hframes
  have hd : finish.data=result:=SemiprimeD1StackMultiplierLink.data_unique stack data
    out.data finish.data result hrel.1 hout
  have hp : finish.pc=some next ∧ finish.frames=frames := by
    simpa only [SemiprimeD1StackValidationLink.PcRel,hstop] using hrel.2
  refine ⟨finish,?_,hp.1,hd,hp.2⟩
  rw [show time+1=1+time by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hfinish]

end RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
