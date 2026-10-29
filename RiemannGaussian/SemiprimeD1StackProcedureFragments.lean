/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierLink

/-! # Actual fixed-program procedure fragments
These lemmas compose literal executed instructions and real included calls.
They introduce no runtime function opcode or report-to-time assumption. Every
application must instantiate one fixed finite program before its input.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProcedureFragments
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end Link

/-- Exact program counter/data/return payload, ignoring only finite transient flags. -/
def At {K G:Type} (pc:G) (data:K→List Bool) (frames:List G) (state:C.State K G) : Prop :=
  state.pc=some pc ∧ state.data=data ∧ state.frames=frames

/-- Actual successful fragment of ONE literal program, preserving all outer frames. -/
def Runs {K G:Type} [DecidableEq K] (program:G→C.Instruction K G)
    (time:ℕ) (pc:G) (data:K→List Bool) (next:G) (out:K→List Bool) : Prop :=
  ∀frames state,At pc data frames state→
    ∃finish,C.run program time state=some finish ∧ At next out frames finish

/-- Actual fragments compose by the source transition iterator. -/
theorem Runs.trans {K G:Type} [DecidableEq K] {program:G→C.Instruction K G}
    {m n:ℕ} {pc mid next:G} {data work out:K→List Bool}
    (h:Runs program m pc data mid work) (g:Runs program n mid work next out) :
    Runs program (m+n) pc data next out := by
  intro frames state hs
  obtain ⟨temp,ht,hs⟩:=h frames state hs
  obtain ⟨finish,hf,hout⟩:=g frames temp hs
  refine ⟨finish,?_,hout⟩
  rw [SemiprimeD1StackReturnLink.run_add,ht,Option.bind_some,hf]

/-- Empty actual fragment. -/
theorem Runs.refl {K G:Type} [DecidableEq K] (program:G→C.Instruction K G) (pc:G) (data:K→List Bool) :
    Runs program 0 pc data pc data := by
  intro frames state h
  exact ⟨state,rfl,h⟩

/-- Real call push, literal included execution and actual return pop, with exact auxiliary data. -/
theorem included_call {A L K G:Type} [DecidableEq A] [DecidableEq K]
    (program:G→C.Instruction K G) (stack:A→K) (label:L→G) (hinj:Function.Injective stack)
    (component:L→B.Instruction A L) (entry:L)
    (hcode:∀l,program (label l)=Link.instruction stack label (component l))
    (pc next:G) (hcall:program pc=.call (label entry) next)
    (time:ℕ) (source out:B.State A L) (data result:K→List Bool)
    (hentry:source.pc=some entry) (hstop:out.pc=none)
    (hr:B.run component time source=some out)
    (hin:Link.DataRel stack data source.store data)
    (hout:Link.DataRel stack data out.store result) : Runs program (time+1) pc data next result := by
  intro frames target h
  rcases h with ⟨hpc,hdata,hframes⟩
  let mid:=C.execute (.call (label entry) next) target
  have hm:C.run program 1 target=some mid:=by
    change C.step program target=some mid
    simp [C.step,SemiprimeD1StackCalls.step,hpc,hcall,mid]
  have hrel:Link.Rel stack label data next frames source mid:=by
    constructor
    · change Link.DataRel stack data source.store target.data
      rw [hdata]
      exact hin
    · simp [SemiprimeD1StackMultiplierLink.PcRel,hentry,mid,C.execute,hframes]
  obtain ⟨finish,hfinish,hrel⟩:=Link.run_rel stack label hinj program component hcode
    data next frames time source out mid hrel hr
  have he:finish.data=result:=Link.data_unique stack data out.store finish.data result hrel.1 hout
  have hp:finish.pc=some next ∧ finish.frames=frames:=by
    simpa only [SemiprimeD1StackMultiplierLink.PcRel,hstop] using hrel.2
  refine ⟨finish,?_,hp.1,he,hp.2⟩
  rw [show time+1=1+time by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hfinish]

/-- One actual local literal instruction, checked by its executed payload effect. -/
theorem one_base {K G:Type} [DecidableEq K] (program:G→C.Instruction K G)
    (pc next:G) (op:B.Instruction K G) (data out:K→List Bool)
    (hcode:program pc=.base op)
    (hp:(B.execute op ⟨some pc,none,data⟩).pc=some next)
    (hd:(B.execute op ⟨some pc,none,data⟩).store=out) : Runs program 1 pc data next out := by
  intro frames state h
  rcases h with ⟨hpc,hdata,hframes⟩
  refine ⟨C.execute (.base op) state,?_,?_,?_,?_⟩
  · change C.step program state=some (C.execute (.base op) state)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,hcode]
  · cases op <;> simpa only [C.execute,B.execute,hdata] using hp
  · cases op <;> simpa only [C.execute,B.execute,hdata] using hd
  · cases op <;> exact hframes
end RiemannGaussian.SemiprimeD1StackProcedureFragments
