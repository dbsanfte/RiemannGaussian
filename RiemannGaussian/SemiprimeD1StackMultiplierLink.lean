/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackReturnLink

/-! # Literal procedure inclusion for the fixed multiplier
A source component's actual halt becomes a real return-frame pop. Both stack
and label maps are fixed finite program data, and all unmapped payload is kept.
The final multiplier instantiates this with the proved Copy and Adder traces.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1StackMultiplierLink
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run choose)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Literal stack/label substitution, with component halt replaced by real return. -/
def instruction {A K L G : Type} (stack : A → K) (label : L → G) :
    B.Instruction A L → C.Instruction K G
  | .push k bit next => .base (.push (stack k) bit (label next))
  | .pop k empty low high => .base (.pop (stack k) (label empty) (label low) (label high))
  | .peek k empty low high => .base (.peek (stack k) (label empty) (label low) (label high))
  | .jump next => .base (.jump (label next))
  | .halt => .ret

/-- Exact mapped component cells and every untouched auxiliary cell. -/
def DataRel {A K : Type} (stack : A → K) (aux : K → List Bool)
    (source : A → List Bool) (target : K → List Bool) : Prop :=
  (∀i,target (stack i)=source i) ∧ (∀k,(∀i,stack i≠k) → target k=aux k)

/-- Reading a prepared component projection requires no supplied operand. -/
theorem data_initial {A K : Type} (stack : A → K) (input : K → List Bool) :
    DataRel stack input (fun i => input (stack i)) input := ⟨fun _ => rfl,fun _ _ => rfl⟩

/-- One literal component write touches only its actual included stack. -/
theorem data_update {A K : Type} [DecidableEq A] [DecidableEq K]
    (stack : A → K) (hinj : Function.Injective stack) (aux : K → List Bool)
    (source : A → List Bool) (target : K → List Bool) (hd : DataRel stack aux source target)
    (j : A) (bits : List Bool) :
    DataRel stack aux (Function.update source j bits) (Function.update target (stack j) bits) := by
  constructor
  · intro i
    by_cases h : i=j
    · subst i
      simp only [Function.update_self]
    · have hs : stack i≠stack j := fun he => h (hinj he)
      simpa only [Function.update_of_ne h,Function.update_of_ne hs] using hd.1 i
  · intro k hk
    have hs : k≠stack j := (hk j).symm
    simpa only [Function.update_of_ne hs] using hd.2 k hk

/-- The same mapped result and preserved auxiliary data determine the whole store. -/
theorem data_unique {A K : Type} (stack : A → K) (aux : K → List Bool)
    (source : A → List Bool) (left right : K → List Bool)
    (hl : DataRel stack aux source left) (hr : DataRel stack aux source right) : left=right := by
  classical
  funext k
  by_cases hk : ∃i,stack i=k
  · obtain ⟨i,rfl⟩:=hk
    exact (hl.1 i).trans (hr.1 i).symm
  · have hnone : ∀i,stack i≠k := by intro i hi;exact hk ⟨i,hi⟩
    exact (hl.2 k hnone).trans (hr.2 k hnone).symm

/-- Finite EOF/Boolean dispatch commutes with literal label inclusion. -/
theorem choose_map {L G : Type} (label : L → G) (empty low high : L) (bit : Option Bool) :
    B.choose (label empty) (label low) (label high) bit=label (B.choose empty low high bit) := by
  cases bit with
  | none => rfl
  | some bit => cases bit <;> rfl

/-- Exact active/returned program counters and actual return stack. -/
def PcRel {A K L G : Type} (label : L → G) (returnTo : G) (frames : List G)
    (source : B.State A L) (target : C.State K G) : Prop :=
  match source.pc with
  | none => target.pc=some returnTo ∧ target.frames=frames
  | some pc => target.pc=some (label pc) ∧ target.frames=returnTo::frames

/-- A component inclusion retains data, real continuation and all outer frames.
Read flags are finite transient control and are deliberately unconstrained. -/
def Rel {A K L G : Type} (stack : A → K) (label : L → G) (aux : K → List Bool)
    (returnTo : G) (frames : List G) (source : B.State A L) (target : C.State K G) : Prop :=
  DataRel stack aux source.store target.data ∧ PcRel label returnTo frames source target

/-- Every actual included instruction preserves its source/return correspondence. -/
theorem instruction_rel {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (stack : A → K) (label : L → G) (hinj : Function.Injective stack)
    (aux : K → List Bool) (returnTo : G) (frames : List G)
    (op : B.Instruction A L) (source : B.State A L) (target : C.State K G) (pc : L)
    (hp : source.pc=some pc) (h : Rel stack label aux returnTo frames source target) :
    Rel stack label aux returnTo frames (B.execute op source) (C.execute (instruction stack label op) target) := by
  rcases h with ⟨hd,hpc⟩
  have ht : target.pc=some (label pc) ∧ target.frames=returnTo::frames := by
    simpa only [PcRel,hp] using hpc
  cases op with
  | push j bit next =>
    constructor
    · simpa only [instruction,B.execute,C.execute,hd.1 j] using
        data_update stack hinj aux source.store target.data hd j (bit::source.store j)
    · simp only [PcRel,instruction,B.execute,C.execute,ht.2,and_self]
  | pop j empty low high =>
    constructor
    · simpa only [instruction,B.execute,C.execute,hd.1 j] using
        data_update stack hinj aux source.store target.data hd j (source.store j).tail
    · simp only [PcRel,instruction,B.execute,C.execute,hd.1 j,choose_map,ht.2,and_self]
  | peek j empty low high =>
    constructor
    · exact hd
    · simp only [PcRel,instruction,B.execute,C.execute,hd.1 j,choose_map,ht.2,and_self]
  | jump next =>
    constructor
    · exact hd
    · simp only [PcRel,instruction,B.execute,C.execute,ht.2,and_self]
  | halt =>
    constructor
    · simpa only [instruction,B.execute,C.execute,ht.2] using hd
    · simp only [PcRel,instruction,B.execute,C.execute,ht.2,and_self]

/-- Successful component traces execute in the actual enclosing call program. -/
theorem run_rel {A K L G : Type} [DecidableEq A] [DecidableEq K]
    (stack : A → K) (label : L → G) (hinj : Function.Injective stack)
    (program : G → C.Instruction K G) (component : L → B.Instruction A L)
    (hcode : ∀l,program (label l)=instruction stack label (component l))
    (aux : K → List Bool) (returnTo : G) (frames : List G)
    (fuel : ℕ) (s out : B.State A L) (t : C.State K G)
    (h : Rel stack label aux returnTo frames s t)
    (hr : B.run component fuel s=some out) :
    ∃finish,C.run program fuel t=some finish ∧ Rel stack label aux returnTo frames out finish := by
  induction fuel generalizing s t with
  | zero => change some s=some out at hr; cases hr; exact ⟨t,rfl,h⟩
  | succ fuel ih =>
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackCopy.run_add] at hr
    change (B.step component s).bind (B.run component fuel)=some out at hr
    cases hp:s.pc with
    | none => simp [B.step,SemiprimeD1StackBytecode.step,hp] at hr
    | some pc =>
      have hs : B.step component s=some (B.execute (component pc) s) := by
        simp [B.step,SemiprimeD1StackBytecode.step,hp]
      rw [hs,Option.bind_some] at hr
      have htpc : t.pc=some (label pc) := by
        have hh:=h.2
        rw [PcRel,hp] at hh
        exact hh.1
      have ht : C.step program t=some (C.execute (instruction stack label (component pc)) t) := by
        simp [C.step,SemiprimeD1StackCalls.step,htpc,hcode]
      obtain ⟨finish,hfinish,hrel⟩:=ih (B.execute (component pc) s)
        (C.execute (instruction stack label (component pc)) t)
        (instruction_rel stack label hinj aux returnTo frames _ s t pc hp h) hr
      refine ⟨finish,?_,hrel⟩
      rw [show fuel+1=1+fuel by omega,SemiprimeD1StackReturnLink.run_add]
      change (C.step program t).bind (C.run program fuel)=some finish
      rw [ht,Option.bind_some,hfinish]

end RiemannGaussian.SemiprimeD1StackMultiplierLink
