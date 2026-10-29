/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Real inclusion of a stopped helper fragment and its actual return
This is a proof theorem for THIS source's concrete reused finite helper program,
not an evaluator/callback or instruction operand. Both real call and real return
are executed and charged while arbitrary foreign tapes and returns are retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsIncluded
open SemiprimeD1StackProcedureTrace
/-- A literal included fragment ending before a real ret is a complete called trace after paying both call/ret steps. -/
theorem called_fragment {A K L G:Type} [DecidableEq A] [DecidableEq K]
    (program:G→C.Instruction K G) (stack:A→K) (label:L→G) (hinj:Function.Injective stack)
    (component:L→C.Instruction A L) (entry stopped:L)
    (hcode:∀l,program (label l)=SemiprimeD1StackValidationLink.instruction stack label (component l))
    (pc next:G) (hcall:program pc=.call (label entry) next)
    (time:Nat) (before after:A→List Bool) (data result:K→List Bool)
    (hret:component stopped=.ret) (hr:Runs component time entry before stopped after)
    (hin:SemiprimeD1StackMultiplierLink.DataRel stack data before data)
    (hout:SemiprimeD1StackMultiplierLink.DataRel stack data after result):
    Runs program (time+2) pc data next result:=by
  let source:C.State A L:=⟨some entry,none,none,before,[]⟩
  obtain ⟨finish,hfinish,hAt⟩:=hr [] source ⟨rfl,rfl,rfl⟩
  let out:C.State A L:=⟨none,none,none,after,[]⟩
  have hlast:C.run component 1 finish=some out:=by
    change C.step component finish=some out
    simp only [C.step,SemiprimeD1StackCalls.step,hAt.1,Option.map_some,hret,C.execute,hAt.2.1,hAt.2.2]
    rfl
  have hwhole:C.run component (time+1) source=some out:=by
    rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact hlast
  have h:=SemiprimeD1StackProcedureCallsTrace.included_call program stack label hinj component entry hcode pc next hcall
    (time+1) source out data result rfl rfl rfl rfl hwhole hin hout
  simpa only [Nat.add_assoc,show 1+1=2 from rfl] using h
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsIncluded
