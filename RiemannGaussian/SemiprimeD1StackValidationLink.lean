/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierLink

/-! # Literal inclusion of procedures that themselves make real calls
Nested return frames are physically mapped and the outer continuation is
appended. A successful source trace ending with empty frames supplies the
balanced-halt fact; no assumed trace/cost oracle is needed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackValidationLink
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
open SemiprimeD1StackMultiplierLink (DataRel data_update)

/-- Fixed stack/label inclusion, preserving nested real calls and real returns. -/
def instruction {A K L G : Type} (stack : A → K) (label : L → G) :
    C.Instruction A L → C.Instruction K G
  | .base op => SemiprimeD1StackMultiplierLink.instruction stack label op
  | .call callee next => .call (label callee) (label next)
  | .ret => .ret

/-- The source's own frames are mapped above the actual caller continuation. -/
def PcRel {A K L G : Type} (label : L → G) (returnTo : G) (outer : List G)
    (source : C.State A L) (target : C.State K G) : Prop :=
  match source.pc with
  | none => target.pc=some returnTo ∧ target.frames=outer
  | some pc => target.pc=some (label pc) ∧ target.frames=source.frames.map label++returnTo::outer

/-- Exact data and real nested continuation correspondence; transient flags are finite. -/
def Rel {A K L G : Type} (stack : A → K) (label : L → G) (aux : K → List Bool)
    (returnTo : G) (outer : List G) (source : C.State A L) (target : C.State K G) : Prop :=
  DataRel stack aux source.data target.data ∧ PcRel label returnTo outer source target

/-- One included operation preserves actual payload and nested frame correspondence. -/
theorem instruction_rel {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (stack : A → K) (label : L → G) (hinj : Function.Injective stack)
    (aux : K → List Bool) (returnTo : G) (outer : List G)
    (op : C.Instruction A L) (source : C.State A L) (target : C.State K G) (pc : L)
    (hp : source.pc=some pc) (hh : op=.base .halt → source.frames=[])
    (h : Rel stack label aux returnTo outer source target) :
    Rel stack label aux returnTo outer (C.execute op source) (C.execute (instruction stack label op) target) := by
  rcases h with ⟨hd,hpc⟩
  have ht : target.pc=some (label pc) ∧ target.frames=source.frames.map label++returnTo::outer := by
    simpa only [PcRel,hp] using hpc
  cases op with
  | base op =>
    cases op with
    | push j bit next =>
      constructor
      · simpa only [instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j] using
          data_update stack hinj aux source.data target.data hd j (bit::source.data j)
      · simp only [PcRel,instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,ht.2,and_self]
    | pop j empty low high =>
      constructor
      · simpa only [instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j] using
          data_update stack hinj aux source.data target.data hd j (source.data j).tail
      · simp only [PcRel,instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j,
          SemiprimeD1StackMultiplierLink.choose_map,ht.2,and_self]
    | peek j empty low high =>
      constructor
      · exact hd
      · simp only [PcRel,instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j,
          SemiprimeD1StackMultiplierLink.choose_map,ht.2,and_self]
    | jump next =>
      constructor
      · exact hd
      · simp only [PcRel,instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,ht.2,and_self]
    | halt =>
      have hf:=hh rfl
      constructor
      · simpa only [instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,ht.2,hf,List.map_nil,List.nil_append] using hd
      · simp only [PcRel,instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,ht.2,hf,
          List.map_nil,List.nil_append,and_self]
  | call callee next =>
    constructor
    · exact hd
    · simp only [PcRel,instruction,C.execute,ht.2,List.map_cons,List.cons_append,and_self]
  | ret =>
    cases hf:source.frames with
    | nil =>
      constructor
      · simpa only [instruction,C.execute,ht.2,hf,List.map_nil,List.nil_append] using hd
      · simp only [PcRel,instruction,C.execute,ht.2,hf,List.map_nil,List.nil_append,and_self]
    | cons next frames =>
      constructor
      · simpa only [instruction,C.execute,ht.2,hf,List.map_cons,List.cons_append] using hd
      · simp only [PcRel,instruction,C.execute,ht.2,hf,List.map_cons,List.cons_append,and_self]

/-- A halted source cannot silently execute more instructions. -/
theorem halted_run {A L : Type} [DecidableEq A] (program : L → C.Instruction A L)
    (fuel : ℕ) (source out : C.State A L) (hp : source.pc=none)
    (hr : C.run program fuel source=some out) : source=out := by
  cases fuel with
  | zero => exact Option.some.inj hr
  | succ fuel =>
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackReturnLink.run_add] at hr
    have hh : C.run program 1 source=none := by simp [C.run,C.step,hp]
    rw [hh,Option.bind_none] at hr
    cases hr

/-- Every successful balanced source trace is literally executed in its real caller. -/
theorem run_rel {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (stack : A → K) (label : L → G) (hinj : Function.Injective stack)
    (program : G → C.Instruction K G) (component : L → C.Instruction A L)
    (hcode : ∀pc,program (label pc)=instruction stack label (component pc))
    (aux : K → List Bool) (returnTo : G) (outer : List G)
    (fuel : ℕ) (source out : C.State A L) (target : C.State K G)
    (h : Rel stack label aux returnTo outer source target)
    (hr : C.run component fuel source=some out) (hout : out.frames=[]) :
    ∃finish,C.run program fuel target=some finish ∧ Rel stack label aux returnTo outer out finish := by
  induction fuel generalizing source target with
  | zero => change some source=some out at hr; cases hr; exact ⟨target,rfl,h⟩
  | succ fuel ih =>
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackReturnLink.run_add] at hr
    change (C.step component source).bind (C.run component fuel)=some out at hr
    cases hp:source.pc with
    | none => simp [C.step,hp] at hr
    | some pc =>
      have hs : C.step component source=some (C.execute (component pc) source) := by simp [C.step,hp]
      rw [hs,Option.bind_some] at hr
      have hh : component pc=.base .halt → source.frames=[] := by
        intro hop
        have he:=halted_run component fuel (C.execute (component pc) source) out (by simp [hop,C.execute]) hr
        have hf:=congrArg (fun st : C.State A L => st.frames) he
        simpa only [hop,C.execute] using hf.trans hout
      have htpc : target.pc=some (label pc) := by
        have ht:=h.2
        rw [PcRel,hp] at ht
        exact ht.1
      have ht : C.step program target=some (C.execute (instruction stack label (component pc)) target) := by
        simp [C.step,htpc,hcode]
      obtain ⟨finish,hfinish,hrel⟩:=ih (C.execute (component pc) source)
        (C.execute (instruction stack label (component pc)) target)
        (instruction_rel stack label hinj aux returnTo outer _ source target pc hp hh h) hr
      refine ⟨finish,?_,hrel⟩
      rw [show fuel+1=1+fuel by omega,SemiprimeD1StackReturnLink.run_add]
      change (C.step program target).bind (C.run program fuel)=some finish
      rw [ht,Option.bind_some,hfinish]

end RiemannGaussian.SemiprimeD1StackValidationLink
