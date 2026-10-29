/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAssignmentLoop

/-! # Literal body and increment calls inside the enumeration loop -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackAssignmentLoopExecution
open SemiprimeD1StackAssignmentLoop
local notation "ctl" => SemiprimeD1StackAssignmentLoop.control
namespace M
export SemiprimeD1StackMultiplierLink (Rel DataRel PcRel instruction run_rel data_initial)
end M
namespace B
export SemiprimeD1StackBytecode (State run)
end B

/-- A physical write changes precisely one literal data stack. -/
@[simp] theorem update_data (word scratch next history output xs : List Bool) (k : Stack) :
    Function.update (data word scratch next history output) k xs=
      data (if k=.word then xs else word) (if k=.scratch then xs else scratch)
        (if k=.next then xs else next) (if k=.history then xs else history)
        (if k=.output then xs else output) := by
  funext j
  cases k <;> cases j <;> simp [data]

/-- A real call pushes its literal continuation before executing included code. -/
theorem component_call {K L : Type} [DecidableEq K]
    (stack : K → Stack) (label : L → Label) (hinj : Function.Injective stack)
    (component : L → SemiprimeD1StackBytecode.Instruction K L)
    (hcode : ∀l,code (label l)=M.instruction stack label (component l))
    (start resumeTo : Control) (entry : L)
    (hstart : code (ctl start)=(.call (label entry) (ctl resumeTo)))
    (input : Stack → List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) (m : ℕ) (result : B.State K L)
    (hr : B.run component m ⟨some entry,none,fun k => input (stack k)⟩=some result) :
    ∃resultState,C.run code (m+1) ⟨some (ctl start),flag,returned,input,frames⟩=some resultState ∧
      M.Rel stack label input (ctl resumeTo) frames result resultState := by
  let entered : C.State Stack Label := ⟨some (label entry),none,none,input,ctl resumeTo::frames⟩
  have hs : C.run code 1 ⟨some (ctl start),flag,returned,input,frames⟩=some entered := by
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
      SemiprimeD1StackCalls.execute,hstart,entered]
  have hrel : M.Rel stack label input (ctl resumeTo) frames
      ⟨some entry,none,fun k => input (stack k)⟩ entered :=
    ⟨M.data_initial stack input,rfl,rfl⟩
  obtain ⟨resultState,hf,hd⟩ := M.run_rel stack label hinj code component hcode input
    (ctl resumeTo) frames m _ result entered hrel hr
  refine ⟨resultState,?_,hd⟩
  rw [show m+1=1+m by omega,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,hf]

/-- Reconstruct only finite flags around a proved literal data/PC/frame result. -/
theorem state_eq (c : C.State Stack Label) (pc : Label)
    (word scratch next history output : List Bool) (frames : List Label)
    (hp : c.pc=some pc) (hd : c.data=data word scratch next history output) (hf : c.frames=frames) :
    c=state pc c.flag c.returned word scratch next history output frames := by
  rcases c with ⟨l,flag,returned,store,fs⟩
  dsimp at hp hd hf
  cases hp
  cases hd
  cases hf
  rfl

/-- Actual included body logs one assignment and returns with the argument restored. -/
theorem body_call (word history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    ∃m≤6*(2*word.length+3)+1,∃f r,C.run code m
      (state (ctl .bodyCall) flag returned word [] [] history output frames)=
      some (state (ctl .incCall) f r word [] []
        ((true::SemiprimeSourceHistogramKeyBits.frame word []).reverse++history) output frames) := by
  obtain ⟨m,hm,hbody⟩ := SemiprimeD1StackAssignmentBody.body_run word history
  have hprojection : (fun k => data word [] [] history output (bodyStack k))=
      SemiprimeD1StackAssignmentBody.contents word [] history := by
    funext k
    cases k <;> rfl
  rw [←hprojection] at hbody
  obtain ⟨resultState,hr,hrel⟩ := component_call bodyStack body bodyStack_injective A.code body_code
    .bodyCall .incCall A.entry rfl (data word [] [] history output) flag returned frames m _ hbody
  have hd : resultState.data=data word [] []
      ((true::SemiprimeSourceHistogramKeyBits.frame word []).reverse++history) output := by
    funext k
    cases k with
    | word => exact hrel.1.1 .word
    | scratch => exact hrel.1.1 .scratch
    | next => exact hrel.1.2 .next (by intro k; cases k <;> simp [bodyStack])
    | history => exact hrel.1.1 .history
    | output => exact hrel.1.2 .output (by intro k; cases k <;> simp [bodyStack])
  have hp : resultState.pc=some (ctl .incCall) ∧ resultState.frames=frames := hrel.2
  refine ⟨m+1,by omega,resultState.flag,resultState.returned,?_⟩
  exact hr.trans (congrArg some (state_eq resultState _ _ _ _ _ _ _ hp.1 hd hp.2))

/-- Actual included incrementer returns physical overflow/wrapped bytes, not an answer. -/
theorem increment_call (word history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    ∃m≤5*(2*word.length+3)+1,∃f r,C.run code m
      (state (ctl .incCall) flag returned word [] [] history output frames)=
      some (state (ctl .afterInc) f r [] []
        (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)
        history output frames) := by
  obtain ⟨m,hm,hinc⟩ := SemiprimeD1StackIncrementBytecode.increment_run word []
  have hprojection : (fun k => data word [] [] history output (incStack k))=
      SemiprimeD1TensorTapeFieldMachine.contents word [] [] := by
    funext k
    cases k <;> rfl
  rw [←hprojection] at hinc
  obtain ⟨resultState,hr,hrel⟩ := component_call incStack increment incStack_injective I.code increment_code
    .incCall .afterInc I.entry rfl (data word [] [] history output) flag returned frames m _ hinc
  have hd : resultState.data=data [] []
      (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word) history output := by
    funext k
    cases k with
    | word => exact hrel.1.1 .input
    | scratch => exact hrel.1.1 .scratch
    | next => simpa [incStack,data,SemiprimeD1TensorTapeFieldMachine.contents] using hrel.1.1 .output
    | history => exact hrel.1.2 .history (by intro k; cases k <;> simp [incStack])
    | output => exact hrel.1.2 .output (by intro k; cases k <;> simp [incStack])
  have hp : resultState.pc=some (ctl .afterInc) ∧ resultState.frames=frames := hrel.2
  refine ⟨m+1,by omega,resultState.flag,resultState.returned,?_⟩
  exact hr.trans (congrArg some (state_eq resultState _ _ _ _ _ _ _ hp.1 hd hp.2))

/-- Actual interpreter paths compose with every transition retained. -/
theorem run_trans {m n : ℕ} {a b c : C.State Stack Label}
    (h : C.run code m a=some b) (g : C.run code n b=some c) :
    C.run code (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,h,Option.bind_some,g]

/-- Physically move the wrapped word out of the incrementer result stack. -/
theorem move_drain (xs rev history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    C.run code (2*xs.length+1) (state (ctl .moveDrain) flag returned [] rev xs history output frames)=
      some (state (ctl .restore) none returned [] (xs.reverse++rev) [] history output frames) := by
  induction xs generalizing rev flag with
  | nil =>
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
      SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data]
  | cons b bs ih =>
    have hs : C.run code 2 (state (ctl .moveDrain) flag returned [] rev (b::bs) history output frames)=
        some (state (ctl .moveDrain) (some b) returned [] (b::rev) bs history output frames) := by
      cases b <;> simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
        SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data,
        Function.iterate_succ_apply]
    rw [show 2*(b::bs).length+1=2+(2*bs.length+1) by simp; omega,
      SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::rev) (some b)

/-- Restore every wrapped digit to the next actual body call. -/
theorem move_restore (xs word history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    C.run code (2*xs.length+1) (state (ctl .restore) flag returned word xs [] history output frames)=
      some (state (ctl .bodyCall) none returned (xs.reverse++word) [] [] history output frames) := by
  induction xs generalizing word flag with
  | nil =>
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
      SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data]
  | cons b bs ih =>
    have hs : C.run code 2 (state (ctl .restore) flag returned word (b::bs) [] history output frames)=
        some (state (ctl .restore) (some b) returned (b::word) bs [] history output frames) := by
      cases b <;> simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
        SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data,
        Function.iterate_succ_apply]
    rw [show 2*(b::bs).length+1=2+(2*bs.length+1) by simp; omega,
      SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::word) (some b)

/-- Real final log reversal, including the final halt and return-frame preservation. -/
theorem reverse_history (xs output next : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    C.run code (2*xs.length+2) (state (ctl .reverse) flag returned [] [] next xs output frames)=
      some ⟨none,none,none,data [] [] next [] (xs.reverse++output),frames⟩ := by
  induction xs generalizing flag output with
  | nil =>
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
      SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data,Function.iterate_succ_apply]
  | cons b bs ih =>
    have hs : C.run code 2 (state (ctl .reverse) flag returned [] [] next (b::bs) output frames)=
        some (state (ctl .reverse) (some b) returned [] [] next bs (b::output) frames) := by
      cases b <;> simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
        SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data,
        Function.iterate_succ_apply]
    rw [show 2*(b::bs).length+2=2+(2*bs.length+2) by simp; omega,
      SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)


/-- The final wrapped word is physically cleared after overflow. -/
theorem clear_next (xs history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    C.run code (xs.length+1) (state (ctl .clearNext) flag returned [] [] xs history output frames)=
      some (state (ctl .finish) none returned [] [] [] history output frames) := by
  induction xs generalizing flag with
  | nil =>
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,SemiprimeD1StackCalls.execute,
      SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data]
  | cons b bs ih =>
    have hs : C.run code 1 (state (ctl .clearNext) flag returned [] [] (b::bs) history output frames)=
        some (state (ctl .clearNext) (some b) returned [] [] bs history output frames) := by
      cases b <;> simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,
        SemiprimeD1StackCalls.execute,SemiprimeD1StackBytecode.choose,code,state,
        SemiprimeD1StackAssignmentLoop.control,data]
    convert run_trans hs (ih (some b)) using 1
    simp
    all_goals (congr 1; omega)

/-- A false physical overflow bit returns the wrapped word to the next body call. -/
theorem continue_run (xs history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    C.run code (4*xs.length+3)
      (state (ctl .afterInc) flag returned [] [] (false::xs) history output frames)=
      some (state (ctl .bodyCall) none returned xs [] [] history output frames) := by
  have hs : C.run code 1 (state (ctl .afterInc) flag returned [] [] (false::xs) history output frames)=
      some (state (ctl .moveDrain) (some false) returned [] [] xs history output frames) := by
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,SemiprimeD1StackCalls.execute,
      SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data]
  have hd := move_drain xs [] history output (some false) returned frames
  have hr := move_restore (xs.reverse++[]) [] history output none returned frames
  have h := run_trans hs (run_trans hd hr)
  convert h using 1 <;> simp
  all_goals (congr 1; omega)

/-- True physical overflow clears leftovers and emits the entire framed log. -/
theorem finish_run (xs history output : List Bool) (flag : Option Bool) (returned : Option Label)
    (frames : List Label) :
    C.run code (xs.length+2*history.length+7)
      (state (ctl .afterInc) flag returned [] [] (true::xs) history output frames)=
      some ⟨none,none,none,data [] [] [] [] (history.reverse++false::output),frames⟩ := by
  have hs : C.run code 1 (state (ctl .afterInc) flag returned [] [] (true::xs) history output frames)=
      some (state (ctl .clearNext) (some true) returned [] [] xs history output frames) := by
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,SemiprimeD1StackCalls.execute,
      SemiprimeD1StackBytecode.choose,code,state,SemiprimeD1StackAssignmentLoop.control,data]
  have hc := clear_next xs history output (some true) returned frames
  have hf : C.run code 1 (state (ctl .finish) none returned [] [] [] history output frames)=
      some (state (ctl .reverse) none returned [] [] [] (false::history) output frames) := by
    simp [SemiprimeD1StackCalls.run,SemiprimeD1StackCalls.step,SemiprimeD1StackCalls.execute,
      code,state,SemiprimeD1StackAssignmentLoop.control,data]
  have hr := reverse_history (false::history) output [] none returned frames
  have h := run_trans hs (run_trans hc (run_trans hf hr))
  convert h using 1 <;> simp [List.reverse_cons,List.append_assoc]
  all_goals (congr 1; omega)

end RiemannGaussian.SemiprimeD1StackAssignmentLoopExecution
