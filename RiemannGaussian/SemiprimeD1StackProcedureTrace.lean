/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierLink

/-! # Actual procedure-trace composition
All premises below are exact traces of literal component instructions. No
component is supplied as an opaque evaluator, result oracle or cost report.
The finite enclosing program physically executes its call and return frames.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProcedureTrace
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel Rel)
end Link

/-- Exact program position, physical store and outer return frames. -/
def At {K L : Type} (pc : L) (data : K→List Bool) (frames : List L) (state : C.State K L) : Prop :=
  state.pc=some pc ∧ state.data=data ∧ state.frames=frames

/-- Literal trace effect for every actual caller's frames and transient flags. -/
def Runs {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (time : ℕ) (pc : L) (data : K→List Bool) (next : L) (result : K→List Bool) : Prop :=
  ∀frames target,At pc data frames target→
    ∃finish,C.run program time target=some finish ∧ At next result frames finish

/-- The empty executed trace leaves the exact caller state in place. -/
theorem runs_refl {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc : L) (data : K→List Bool) : Runs program 0 pc data pc data := by
  intro frames target h
  exact ⟨target,rfl,h⟩

/-- Actual component traces concatenate at their exact intermediate physical store. -/
theorem runs_trans {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (m n : ℕ) (pc mid next : L) (data middle result : K→List Bool)
    (hm : Runs program m pc data mid middle) (hn : Runs program n mid middle next result) :
    Runs program (m+n) pc data next result := by
  intro frames target h
  obtain ⟨between,hbetween,hmid⟩ := hm frames target h
  obtain ⟨finish,hfinish,hout⟩ := hn frames between hmid
  refine ⟨finish,?_,hout⟩
  rw [SemiprimeD1StackReturnLink.run_add,hbetween,Option.bind_some,hfinish]

/-- A real call plus a proved included component execution preserves all other
payload and the entire caller's outer return stack. -/
theorem included_call {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (program : G→C.Instruction K G) (stack : A→K) (label : L→G)
    (hinj : Function.Injective stack) (component : L→B.Instruction A L) (entry : L)
    (hcode : ∀l,program (label l)=Link.instruction stack label (component l))
    (pc next : G) (hcall : program pc=.call (label entry) next)
    (time : ℕ) (source out : B.State A L) (data result : K→List Bool)
    (hentry : source.pc=some entry) (hstop : out.pc=none)
    (hr : B.run component time source=some out)
    (hin : Link.DataRel stack data source.store data)
    (hout : Link.DataRel stack data out.store result) :
    Runs program (time+1) pc data next result := by
  intro frames target h
  rcases h with ⟨hpc,hdata,hframes⟩
  let mid := C.execute (.call (label entry) next) target
  have hm : C.run program 1 target=some mid := by
    change C.step program target=some mid
    simp only [C.step,SemiprimeD1StackCalls.step,hpc,Option.map_some,hcall,mid]
  have hrel : Link.Rel stack label data next frames source mid := by
    constructor
    · change Link.DataRel stack data source.store target.data
      rw [hdata]
      exact hin
    · simp only [SemiprimeD1StackMultiplierLink.PcRel,hentry,mid,C.execute,hframes,and_self]
  obtain ⟨finish,hfinish,hrel⟩ := SemiprimeD1StackMultiplierLink.run_rel stack label hinj
    program component hcode data next frames time source out mid hrel hr
  have he : finish.data=result :=
    SemiprimeD1StackMultiplierLink.data_unique stack data out.store finish.data result hrel.1 hout
  have hp : finish.pc=some next ∧ finish.frames=frames := by
    simpa only [SemiprimeD1StackMultiplierLink.PcRel,hstop] using hrel.2
  refine ⟨finish,?_,hp.1,he,hp.2⟩
  rw [show time+1=1+time by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hfinish]

/-- One actual local instruction, with its Boolean-stack effects evaluated
literally. Its validity is independent of old transient read/return flags. -/
theorem one_base {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc next : L) (op : B.Instruction K L) (data result : K→List Bool)
    (hcode : program pc=.base op)
    (hp : (B.execute op ⟨some pc,none,data⟩).pc=some next)
    (hd : (B.execute op ⟨some pc,none,data⟩).store=result) :
    Runs program 1 pc data next result := by
  intro frames target h
  rcases h with ⟨hpc,hdata,hframes⟩
  refine ⟨C.execute (.base op) target,?_,?_,?_,?_⟩
  · change C.step program target=some (C.execute (.base op) target)
    simp only [C.step,SemiprimeD1StackCalls.step,hpc,Option.map_some,hcode]
  · cases op <;> simpa only [C.execute,B.execute,hdata] using hp
  · cases op <;> simpa only [C.execute,B.execute,hdata] using hd
  · cases op <;> exact hframes

/-- A final literal halt clears flags and retains only the actually reached
data and return stacks; no reset of live workspace is silently performed. -/
theorem halt_run {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc : L) (hcode : program pc=.base .halt) (data : K→List Bool) (frames : List L)
    (target : C.State K L) (h : At pc data frames target) :
    C.run program 1 target=some (⟨none,none,none,data,frames⟩:C.State K L) := by
  rcases h with ⟨hpc,hdata,hframes⟩
  change C.step program target=some _
  simp only [C.step,SemiprimeD1StackCalls.step,hpc,Option.map_some,hcode,C.execute,hdata,hframes]

end RiemannGaussian.SemiprimeD1StackProcedureTrace
