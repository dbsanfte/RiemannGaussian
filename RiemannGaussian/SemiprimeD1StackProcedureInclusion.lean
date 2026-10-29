/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1StackProcedureTrace
/-! # Actual trace inclusion for nested fixed procedures -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackProcedureInclusion
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace V
export SemiprimeD1StackValidationLink (instruction Rel PcRel run_rel)
end V
namespace M
export SemiprimeD1StackMultiplierLink (DataRel data_unique)
end M
open SemiprimeD1StackProcedureTrace (At Runs)
/-- The literal included component may itself make real calls. Its successful
balanced execution supplies the return invariant, not a reset or cost oracle. -/
theorem included_call {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (program : G→C.Instruction K G) (stack : A→K) (label : L→G)
    (hinj : Function.Injective stack) (component : L→C.Instruction A L) (entry : L)
    (hcode : ∀l,program (label l)=V.instruction stack label (component l))
    (pc next : G) (hcall : program pc=.call (label entry) next)
    (time : ℕ) (source out : C.State A L) (data result : K→List Bool)
    (hentry : source.pc=some entry) (hsource : source.frames=[])
    (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : C.run component time source=some out)
    (hin : M.DataRel stack data source.data data)
    (hout : M.DataRel stack data out.data result) :
    Runs program (time+1) pc data next result := by
  intro frames target h
  rcases h with ⟨hpc,hdata,houter⟩
  let mid := C.execute (.call (label entry) next) target
  have hm : C.run program 1 target=some mid := by
    change C.step program target=some mid
    simp only [C.step,SemiprimeD1StackCalls.step,hpc,Option.map_some,hcall,mid]
  have hrel : V.Rel stack label data next frames source mid := by
    constructor
    · change M.DataRel stack data source.data target.data
      rw [hdata]
      exact hin
    · simp only [SemiprimeD1StackValidationLink.PcRel,hentry,hsource,List.map_nil,
        List.nil_append,mid,C.execute,houter,and_self]
  obtain ⟨finish,hfinish,hrel⟩ := V.run_rel stack label hinj program component hcode
    data next frames time source out mid hrel hr hframes
  have he : finish.data=result := M.data_unique stack data out.data finish.data result hrel.1 hout
  have hp : finish.pc=some next ∧ finish.frames=frames := by
    simpa only [SemiprimeD1StackValidationLink.PcRel,hstop] using hrel.2
  refine ⟨finish,?_,hp.1,he,hp.2⟩
  rw [show time+1=1+time by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hfinish]
end RiemannGaussian.SemiprimeD1StackProcedureInclusion
