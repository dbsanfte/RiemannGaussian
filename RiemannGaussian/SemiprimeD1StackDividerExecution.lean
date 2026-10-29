/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDivider

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackDividerExecution
open SemiprimeD1StackDivider
namespace C
export SemiprimeD1StackCalls (State execute step run)
end C

/-- Composition of actual transitions of the fixed division program. -/
theorem run_append (m n : ℕ) (a b c : C.State Stack Label)
    (hm : C.run code m a=some b) (hn : C.run code n b=some c) :
    C.run code (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hn]

/-- Two actual literal transitions. -/
theorem two_steps (a b c : C.State Stack Label)
    (h₁ : C.step code a=some b) (h₂ : C.step code b=some c) : C.run code 2 a=some c := by
  change (C.step code a).bind (C.step code)=some c
  rw [h₁,Option.bind_some,h₂]

/-- Three actual literal transitions. -/
theorem three_steps (a b c d : C.State Stack Label)
    (h₁ : C.step code a=some b) (h₂ : C.step code b=some c) (h₃ : C.step code c=some d) :
    C.run code 3 a=some d := by
  change ((C.step code a).bind (C.step code)).bind (C.step code)=some d
  rw [h₁,Option.bind_some,h₂,Option.bind_some,h₃]

/-- Exact literal write to the xs stack. -/
theorem payload_xs (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .input) bits=payload bits ys ds left right scratch diff rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_xs (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .input)=xs := rfl

/-- Exact literal write to the ys stack. -/
theorem payload_ys (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .divisor) bits=payload xs bits ds left right scratch diff rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_ys (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .divisor)=ys := rfl

/-- Exact literal write to the ds stack. -/
theorem payload_ds (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .digits) bits=payload xs ys bits left right scratch diff rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_ds (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .digits)=ds := rfl

/-- Exact literal write to the left stack. -/
theorem payload_left (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inl .left) bits=payload xs ys ds bits right scratch diff rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_left (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inl .left)=left := rfl

/-- Exact literal write to the right stack. -/
theorem payload_right (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inl .right) bits=payload xs ys ds left bits scratch diff rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_right (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inl .right)=right := rfl

/-- Exact literal write to the scratch stack. -/
theorem payload_scratch (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inl .scratch) bits=payload xs ys ds left right bits diff rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_scratch (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inl .scratch)=scratch := rfl

/-- Exact literal write to the diff stack. -/
theorem payload_diff (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inl .output) bits=payload xs ys ds left right scratch bits rem quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_diff (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inl .output)=diff := rfl

/-- Exact literal write to the rem stack. -/
theorem payload_rem (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .remainder) bits=payload xs ys ds left right scratch diff bits quo cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_rem (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .remainder)=rem := rfl

/-- Exact literal write to the quo stack. -/
theorem payload_quo (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .quotient) bits=payload xs ys ds left right scratch diff rem bits cp tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_quo (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .quotient)=quo := rfl

/-- Exact literal write to the cp stack. -/
theorem payload_cp (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .copyScratch) bits=payload xs ys ds left right scratch diff rem quo bits tmp := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_cp (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .copyScratch)=cp := rfl

/-- Exact literal write to the tmp stack. -/
theorem payload_tmp (xs ys ds left right scratch diff rem quo cp tmp bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp) (.inr .template) bits=payload xs ys ds left right scratch diff rem quo cp bits := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_tmp (xs ys ds left right scratch diff rem quo cp tmp : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp (.inr .template)=tmp := rfl

/-- Literal reversal/movement loop with every pop and push paid. -/
theorem reverse_run (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*xs.length+1) (state (some (.control .start)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .initialize)) none rt ([]) ys (xs.reverse++ds) left right scratch diff rem quo cp tmp) := by
  induction xs generalizing ds flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_xs]
  | cons b xs ih =>
    have hs : C.run code 2 (state (some (.control .start)) flag rt (b::xs) ys ds left right scratch diff rem quo cp tmp)=
        some (state (some (.control .start)) (some b) rt (xs) ys (b::ds) left right scratch diff rem quo cp tmp) := by
      apply two_steps (b:=state (some (.control (.reversePush b))) (some b) rt (xs) ys ds left right scratch diff rem quo cp tmp)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_xs]
      · simp [C.step,C.execute,state,code,payload_ds]
    have hh:=run_append 2 (2*xs.length+1) _ _ _ hs (ih (b::ds) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal reversal/movement loop with every pop and push paid. -/
theorem diff_move (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*diff.length+1) (state (some (.control .diffToScratch)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .scratchToR)) none rt xs ys ds left right (diff.reverse++scratch) ([]) rem quo cp tmp) := by
  induction diff generalizing scratch flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_diff]
  | cons b diff ih =>
    have hs : C.run code 2 (state (some (.control .diffToScratch)) flag rt xs ys ds left right scratch (b::diff) rem quo cp tmp)=
        some (state (some (.control .diffToScratch)) (some b) rt xs ys ds left right (b::scratch) (diff) rem quo cp tmp) := by
      apply two_steps (b:=state (some (.control (.diffPush b))) (some b) rt xs ys ds left right scratch (diff) rem quo cp tmp)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_diff]
      · simp [C.step,C.execute,state,code,payload_scratch]
    have hh:=run_append 2 (2*diff.length+1) _ _ _ hs (ih (b::scratch) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal reversal/movement loop with every pop and push paid. -/
theorem rem_move (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*scratch.length+1) (state (some (.control .scratchToR)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .initialize)) none rt xs ys ds left right ([]) diff (scratch.reverse++rem) quo cp tmp) := by
  induction scratch generalizing rem flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_scratch]
  | cons b scratch ih =>
    have hs : C.run code 2 (state (some (.control .scratchToR)) flag rt xs ys ds left right (b::scratch) diff rem quo cp tmp)=
        some (state (some (.control .scratchToR)) (some b) rt xs ys ds left right (scratch) diff (b::rem) quo cp tmp) := by
      apply two_steps (b:=state (some (.control (.remPush b))) (some b) rt xs ys ds left right (scratch) diff rem quo cp tmp)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_scratch]
      · simp [C.step,C.execute,state,code,payload_rem]
    have hh:=run_append 2 (2*scratch.length+1) _ _ _ hs (ih (b::rem) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal reversal/movement loop with every pop and push paid. -/
theorem restore_move (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*scratch.length+1) (state (some (.control .fitRestore)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .loop)) none rt xs ys ds left right ([]) diff (scratch.reverse++rem) quo cp tmp) := by
  induction scratch generalizing rem flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_scratch]
  | cons b scratch ih =>
    have hs : C.run code 2 (state (some (.control .fitRestore)) flag rt xs ys ds left right (b::scratch) diff rem quo cp tmp)=
        some (state (some (.control .fitRestore)) (some b) rt xs ys ds left right (scratch) diff (b::rem) quo cp tmp) := by
      apply two_steps (b:=state (some (.control (.restorePush b))) (some b) rt xs ys ds left right (scratch) diff rem quo cp tmp)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_scratch]
      · simp [C.step,C.execute,state,code,payload_rem]
    have hh:=run_append 2 (2*scratch.length+1) _ _ _ hs (ih (b::rem) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal clearing loop, one actual pop per discarded cell. -/
theorem discard_rem (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (rem.length+1) (state (some (.control .discardR)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .diffToScratch)) none rt xs ys ds left right scratch diff ([]) quo cp tmp) := by
  induction rem generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_rem]
  | cons b rem ih =>
    have hs : C.run code 1 (state (some (.control .discardR)) flag rt xs ys ds left right scratch diff (b::rem) quo cp tmp)=
        some (state (some (.control .discardR)) (some b) rt xs ys ds left right scratch diff (rem) quo cp tmp) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_rem]
    have hh:=run_append 1 (rem.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal clearing loop, one actual pop per discarded cell. -/
theorem discard_diff (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (diff.length+1) (state (some (.control .discardDiff)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .initialize)) none rt xs ys ds left right scratch ([]) rem quo cp tmp) := by
  induction diff generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_diff]
  | cons b diff ih =>
    have hs : C.run code 1 (state (some (.control .discardDiff)) flag rt xs ys ds left right scratch (b::diff) rem quo cp tmp)=
        some (state (some (.control .discardDiff)) (some b) rt xs ys ds left right scratch (diff) rem quo cp tmp) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_diff]
    have hh:=run_append 1 (diff.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal clearing loop, one actual pop per discarded cell. -/
theorem discard_fit (xs ys ds left right scratch diff rem quo cp tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (rem.length+1) (state (some (.control .fitDiscard)) flag rt xs ys ds left right scratch diff rem quo cp tmp)=
    some (state (some (.control .fitRestore)) none rt xs ys ds left right scratch diff ([]) quo cp tmp) := by
  induction rem generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_rem]
  | cons b rem ih =>
    have hs : C.run code 1 (state (some (.control .fitDiscard)) flag rt xs ys ds left right scratch diff (b::rem) quo cp tmp)=
        some (state (some (.control .fitDiscard)) (some b) rt xs ys ds left right scratch diff (rem) quo cp tmp) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_rem]
    have hh:=run_append 1 (rem.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual remainder copy call, including continuation push and real return pop. -/
theorem copy_rem (xs ys ds right scratch diff rem quo tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (1+(5*rem.length+3))
      (state (some (.control .callCopyR)) flag rt xs ys ds [] right scratch diff rem quo [] tmp)=
    some (state (some (.control .callCopyD)) ff rr xs ys ds rem right scratch diff rem quo [] tmp) := by
  let original:=payload xs ys ds [] right scratch diff rem quo [] tmp
  let entered : C.State Stack Label :=
    ⟨some (.copy .remainder 0),none,none,original,[.control .callCopyD]⟩
  have hstart : C.run code 1 (state (some (.control .callCopyR)) flag rt xs ys ds [] right scratch diff rem quo [] tmp)=some entered := rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel (copyStack .remainder) (Label.copy .remainder) original
      (.control .callCopyD) [] (SemiprimeD1StackCopy.state 0 none rem [] []) entered := by
    constructor
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel (copyStack .remainder)
    (Label.copy .remainder) (copyStack_injective .remainder) code SemiprimeD1StackCopy.code
    (fun _=>rfl) original (.control .callCopyD) [] _ _ _ entered hrel
    (SemiprimeD1StackCopy.copy_words rem [] none)
  have desired : SemiprimeD1StackMultiplierLink.DataRel (copyStack .remainder) original
      (SemiprimeD1StackCopy.done rem (rem++[])).store (payload xs ys ds rem right scratch diff rem quo [] tmp) := by
    simp only [List.append_nil]
    constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact False.elim (hk 1 (by rfl))
      · cases k <;> rfl
  have hd:=SemiprimeD1StackMultiplierLink.data_unique (copyStack .remainder) original _ _ _ hr.1 desired
  have hp : finish.pc=some (.control .callCopyD) ∧ finish.frames=[] := hr.2
  have heq : finish=state (some (.control .callCopyD)) finish.flag finish.returned xs ys ds rem right scratch diff rem quo [] tmp := by
    cases finish
    simp_all [state]
  refine ⟨finish.flag,finish.returned,?_⟩
  exact run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))

/-- Actual divisor copy call, including continuation push and real return pop. -/
theorem copy_divisor (xs ys ds left scratch diff rem quo tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (1+(5*ys.length+3))
      (state (some (.control .callCopyD)) flag rt xs ys ds left [] scratch diff rem quo [] tmp)=
    some (state (some (.control .callSub)) ff rr xs ys ds left ys scratch diff rem quo [] tmp) := by
  let original:=payload xs ys ds left [] scratch diff rem quo [] tmp
  let entered : C.State Stack Label :=
    ⟨some (.copy .divisor 0),none,none,original,[.control .callSub]⟩
  have hstart : C.run code 1 (state (some (.control .callCopyD)) flag rt xs ys ds left [] scratch diff rem quo [] tmp)=some entered := rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel (copyStack .divisor) (Label.copy .divisor) original
      (.control .callSub) [] (SemiprimeD1StackCopy.state 0 none ys [] []) entered := by
    constructor
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel (copyStack .divisor)
    (Label.copy .divisor) (copyStack_injective .divisor) code SemiprimeD1StackCopy.code
    (fun _=>rfl) original (.control .callSub) [] _ _ _ entered hrel
    (SemiprimeD1StackCopy.copy_words ys [] none)
  have desired : SemiprimeD1StackMultiplierLink.DataRel (copyStack .divisor) original
      (SemiprimeD1StackCopy.done ys (ys++[])).store (payload xs ys ds left ys scratch diff rem quo [] tmp) := by
    simp only [List.append_nil]
    constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact False.elim (hk 1 (by rfl))
      · cases k <;> rfl
  have hd:=SemiprimeD1StackMultiplierLink.data_unique (copyStack .divisor) original _ _ _ hr.1 desired
  have hp : finish.pc=some (.control .callSub) ∧ finish.frames=[] := hr.2
  have heq : finish=state (some (.control .callSub)) finish.flag finish.returned xs ys ds left ys scratch diff rem quo [] tmp := by
    cases finish
    simp_all [state]
  refine ⟨finish.flag,finish.returned,?_⟩
  exact run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))

/-- Actual template copy call, including continuation push and real return pop. -/
theorem copy_template (xs ys ds left right scratch diff rem quo : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (1+(5*ys.length+3))
      (state (some (.control .initialize)) flag rt xs ys ds left right scratch diff rem quo [] [])=
    some (state (some (.control .fitTemplate)) ff rr xs ys ds left right scratch diff rem quo [] ys) := by
  let original:=payload xs ys ds left right scratch diff rem quo [] []
  let entered : C.State Stack Label :=
    ⟨some (.copy .template 0),none,none,original,[.control .fitTemplate]⟩
  have hstart : C.run code 1 (state (some (.control .initialize)) flag rt xs ys ds left right scratch diff rem quo [] [])=some entered := rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel (copyStack .template) (Label.copy .template) original
      (.control .fitTemplate) [] (SemiprimeD1StackCopy.state 0 none ys [] []) entered := by
    constructor
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel (copyStack .template)
    (Label.copy .template) (copyStack_injective .template) code SemiprimeD1StackCopy.code
    (fun _=>rfl) original (.control .fitTemplate) [] _ _ _ entered hrel
    (SemiprimeD1StackCopy.copy_words ys [] none)
  have desired : SemiprimeD1StackMultiplierLink.DataRel (copyStack .template) original
      (SemiprimeD1StackCopy.done ys (ys++[])).store (payload xs ys ds left right scratch diff rem quo [] ys) := by
    simp only [List.append_nil]
    constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact False.elim (hk 1 (by rfl))
  have hd:=SemiprimeD1StackMultiplierLink.data_unique (copyStack .template) original _ _ _ hr.1 desired
  have hp : finish.pc=some (.control .fitTemplate) ∧ finish.frames=[] := hr.2
  have heq : finish=state (some (.control .fitTemplate)) finish.flag finish.returned xs ys ds left right scratch diff rem quo [] ys := by
    cases finish
    simp_all [state]
  refine ⟨finish.flag,finish.returned,?_⟩
  exact run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))

/-- The linked subtractor produces its actual borrow bit followed by difference bytes. -/
theorem subtract_call (xs ys ds left right rem quo tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code
      (1+(3*(max left.length right.length+1)+2*(SemiprimeBitDivision.subBits left right false).result.bits.length+3))
      (state (some (.control .callSub)) flag rt xs ys ds left right [] [] rem quo [] tmp)=
    some (state (some (.control .borrowRead)) ff rr xs ys ds [] [] []
      ((SemiprimeBitDivision.subBits left right false).borrow::
        (SemiprimeBitDivision.subBits left right false).result.bits) rem quo [] tmp) := by
  let original:=payload xs ys ds left right [] [] rem quo [] tmp
  let entered : C.State Stack Label :=
    ⟨some (.subtractor (.start false)),none,none,original,[.control .borrowRead]⟩
  have hstart : C.run code 1
      (state (some (.control .callSub)) flag rt xs ys ds left right [] [] rem quo [] tmp)=some entered := rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel Sum.inl Label.subtractor original
      (.control .borrowRead) [] (SemiprimeD1StackSubtractor.state (some (.start false)) none left right [] []) entered := by
    constructor
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk; rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel Sum.inl Label.subtractor Sum.inl_injective
    code SemiprimeD1StackSubtractor.code (fun _=>rfl) original (.control .borrowRead) []
    _ _ _ entered hrel (SemiprimeD1StackSubtractorExecution.source_run left right false)
  have desired : SemiprimeD1StackMultiplierLink.DataRel Sum.inl original
      (SemiprimeD1StackSubtractor.state none none [] [] []
        ((SemiprimeBitDivision.subBits left right false).borrow::
          (SemiprimeBitDivision.subBits left right false).result.bits)).store
      (payload xs ys ds [] [] [] ((SemiprimeBitDivision.subBits left right false).borrow::
        (SemiprimeBitDivision.subBits left right false).result.bits) rem quo [] tmp) := by
    constructor
    · intro k; cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · cases k <;> rfl
  have hd:=SemiprimeD1StackMultiplierLink.data_unique Sum.inl original _ _ _ hr.1 desired
  have hp : finish.pc=some (.control .borrowRead) ∧ finish.frames=[] := hr.2
  have heq : finish=state (some (.control .borrowRead)) finish.flag finish.returned xs ys ds [] [] []
      ((SemiprimeBitDivision.subBits left right false).borrow::
        (SemiprimeBitDivision.subBits left right false).result.bits) rem quo [] tmp := by
    cases finish
    simp_all [state]
  refine ⟨finish.flag,finish.returned,?_⟩
  exact run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))

/-- One physical fitting round reads one template cell and one data cell. -/
theorem fit_three (ys ds rem quo scratch tmp : List Bool) (b : Bool)
    (flag : Option Bool) (rt : Option Label) :
    C.run code 3
      (state (some (.control .fitTemplate)) flag rt [] ys ds [] [] scratch [] rem quo [] (b::tmp))=
    some (state (some (.control .fitTemplate)) rem.head? rt [] ys ds [] []
      (rem.head?.getD false::scratch) [] rem.tail quo [] tmp) := by
  apply three_steps
    (b:=state (some (.control .fitRead)) (some b) rt [] ys ds [] [] scratch [] rem quo [] tmp)
    (c:=state (some (.control (.fitPush (rem.head?.getD false)))) rem.head? rt
      [] ys ds [] [] scratch [] rem.tail quo [] tmp)
  · cases b <;> simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_tmp]
  · cases rem with
    | nil => simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_rem]
    | cons d rem => cases d <;> simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_rem]
  · simp [C.step,C.execute,state,code,payload_scratch]

/-- Actual fit traversal, preserving all returned low bits and physical zero padding. -/
theorem fit_scan (ys ds rem quo scratch tmp : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (3*tmp.length+1)
      (state (some (.control .fitTemplate)) flag rt [] ys ds [] [] scratch [] rem quo [] tmp)=
    some (state (some (.control .fitDiscard)) none rt [] ys ds [] []
      ((SemiprimeBitDivision.fitBits rem tmp).bits.reverse++scratch) []
      (rem.drop tmp.length) quo [] []) := by
  induction tmp generalizing rem scratch flag with
  | nil => simp [C.run,C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_tmp,SemiprimeBitDivision.fitBits]
  | cons b tmp ih =>
    have hs:=fit_three ys ds rem quo scratch tmp b flag rt
    have hi:=ih rem.tail (rem.head?.getD false::scratch) rem.head?
    have hh:=run_append 3 (3*tmp.length+1) _ _ _ hs hi
    cases rem <;> simpa only [SemiprimeBitDivision.fitBits,List.head?_nil,List.head?_cons,
      Option.getD_none,Option.getD_some,List.tail_nil,List.tail_cons,List.drop_nil,List.drop_succ_cons,
      List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Exact fitted traversal cost, with discarded high bits explicitly counted. -/
def fitClock (rem ys : List Bool) : ℕ :=
  (3*ys.length+1)+((rem.drop ys.length).length+1)+(2*ys.length+1)

/-- Fitting executes the low-bit scan, high-bit clearing, and physical reversal. -/
theorem fit_run (ys ds rem quo : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (fitClock rem ys)
      (state (some (.control .fitTemplate)) flag rt [] ys ds [] [] [] [] rem quo [] ys)=
    some (state (some (.control .loop)) none rt [] ys ds [] [] [] []
      (SemiprimeBitDivision.fitBits rem ys).bits quo [] []) := by
  have h1:=fit_scan ys ds rem quo [] ys flag rt
  simp only [List.append_nil] at h1
  have h2:=discard_fit [] ys ds [] [] (SemiprimeBitDivision.fitBits rem ys).bits.reverse []
    (rem.drop ys.length) quo [] [] none rt
  have h3:=restore_move [] ys ds [] [] (SemiprimeBitDivision.fitBits rem ys).bits.reverse [] [] quo [] [] none rt
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h3
  rw [(SemiprimeBitDivision.fitBits_counts rem ys).1] at h3
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3

/-- Template acquisition and fitting are both actual paid executions. -/
def initializeClock (ys rem : List Bool) : ℕ := 1+(5*ys.length+3)+fitClock rem ys

/-- The initialization subroutine is also used after every restoring decision. -/
theorem initialize_run (ys ds rem quo : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (initializeClock ys rem)
      (state (some (.control .initialize)) flag rt [] ys ds [] [] [] [] rem quo [] [])=
    some (state (some (.control .loop)) ff rr [] ys ds [] [] [] []
      (SemiprimeBitDivision.fitBits rem ys).bits quo [] []) := by
  obtain ⟨ff,rr,h1⟩:=copy_template [] ys ds [] [] [] [] rem quo flag rt
  exact ⟨none,rr,run_append _ _ _ _ _ h1 (fit_run ys ds rem quo ff rr)⟩

/-- Exact actual branch cost after the subtractor's borrow-prefix output. -/
def restoreClock (ys expanded diff : List Bool) (borrow : Bool) : ℕ :=
  2+(if borrow then diff.length+1+initializeClock ys expanded
    else (expanded.length+1)+(2*diff.length+1)+(2*diff.length+1)+initializeClock ys diff)

/-- Actual restoration uses the physically produced borrow bit, not a comparison oracle. -/
theorem restore_run (ys ds expanded diff quo : List Bool) (borrow : Bool)
    (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (restoreClock ys expanded diff borrow)
      (state (some (.control .borrowRead)) flag rt [] ys ds [] [] [] (borrow::diff) expanded quo [] [])=
    some (state (some (.control .loop)) ff rr [] ys ds [] [] [] []
      (SemiprimeBitDivision.fitBits (if borrow then expanded else diff) ys).bits ((!borrow)::quo) [] []) := by
  cases borrow with
  | false =>
    have h0 : C.run code 2
        (state (some (.control .borrowRead)) flag rt [] ys ds [] [] [] (false::diff) expanded quo [] [])=
        some (state (some (.control .discardR)) (some false) rt [] ys ds [] [] [] diff expanded (true::quo) [] []) := by
      apply two_steps (b:=state (some (.control (.quotientPush false))) (some false) rt
        [] ys ds [] [] [] diff expanded quo [] [])
      · simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_diff]
      · simp [C.step,C.execute,state,code,payload_quo]
    have h1:=discard_rem [] ys ds [] [] [] diff expanded (true::quo) [] [] (some false) rt
    have h2:=diff_move [] ys ds [] [] [] diff [] (true::quo) [] [] none rt
    simp only [List.append_nil] at h2
    have h3:=rem_move [] ys ds [] [] diff.reverse [] [] (true::quo) [] [] none rt
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h3
    obtain ⟨ff,rr,h4⟩:=initialize_run ys ds diff (true::quo) none rt
    have hh:=run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h0 h1) h2) h3
    refine ⟨ff,rr,?_⟩
    simpa only [restoreClock,Bool.false_eq_true,ite_false,Bool.not_false,Nat.add_assoc] using
      run_append _ _ _ _ _ hh h4
  | true =>
    have h0 : C.run code 2
        (state (some (.control .borrowRead)) flag rt [] ys ds [] [] [] (true::diff) expanded quo [] [])=
        some (state (some (.control .discardDiff)) (some true) rt [] ys ds [] [] [] diff expanded (false::quo) [] []) := by
      apply two_steps (b:=state (some (.control (.quotientPush true))) (some true) rt
        [] ys ds [] [] [] diff expanded quo [] [])
      · simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_diff]
      · simp [C.step,C.execute,state,code,payload_quo]
    have h1:=discard_diff [] ys ds [] [] [] diff expanded (false::quo) [] [] (some true) rt
    obtain ⟨ff,rr,h2⟩:=initialize_run ys ds expanded (false::quo) none rt
    refine ⟨ff,rr,?_⟩
    simpa only [restoreClock,ite_true,Bool.not_true,Nat.add_assoc] using
      run_append _ _ _ _ _ (run_append _ _ _ _ _ h0 h1) h2

/-- Proof-side raw restoring result of one digit, with no native quotient operation. -/
def digitNext (ys rem : List Bool) (bit : Bool) : Bool × List Bool :=
  let difference:=SemiprimeBitDivision.subBits (bit::rem) ys false
  (!difference.borrow,(SemiprimeBitDivision.fitBits
    (if difference.borrow then bit::rem else difference.result.bits) ys).bits)

/-- Exact actual digit cost, including all three copy calls, subtract and fit. -/
def digitClock (ys rem : List Bool) (bit : Bool) : ℕ :=
  let expanded:=bit::rem
  let difference:=SemiprimeBitDivision.subBits expanded ys false
  2+(1+(5*expanded.length+3))+(1+(5*ys.length+3))+
    (1+(3*(max expanded.length ys.length+1)+2*difference.result.bits.length+3))+
    restoreClock ys expanded difference.result.bits difference.borrow

/-- One complete restoring round, using actual linked procedure executions. -/
theorem digit_run (ys ds rem quo : List Bool) (bit : Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (digitClock ys rem bit)
      (state (some (.control .loop)) flag rt [] ys (bit::ds) [] [] [] [] rem quo [] [])=
    some (state (some (.control .loop)) ff rr [] ys ds [] [] [] []
      (digitNext ys rem bit).2 ((digitNext ys rem bit).1::quo) [] []) := by
  have h0 : C.run code 2
      (state (some (.control .loop)) flag rt [] ys (bit::ds) [] [] [] [] rem quo [] [])=
      some (state (some (.control .callCopyR)) (some bit) rt [] ys ds [] [] [] [] (bit::rem) quo [] []) := by
    apply two_steps (b:=state (some (.control (.expand bit))) (some bit) rt [] ys ds [] [] [] [] rem quo [] [])
    · cases bit <;> simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ds]
    · simp [C.step,C.execute,state,code,payload_rem]
  obtain ⟨f1,r1,h1⟩:=copy_rem [] ys ds [] [] [] (bit::rem) quo [] (some bit) rt
  obtain ⟨f2,r2,h2⟩:=copy_divisor [] ys ds (bit::rem) [] [] (bit::rem) quo [] f1 r1
  obtain ⟨f3,r3,h3⟩:=subtract_call [] ys ds (bit::rem) ys (bit::rem) quo [] f2 r2
  obtain ⟨ff,rr,h4⟩:=restore_run ys ds (bit::rem)
    (SemiprimeBitDivision.subBits (bit::rem) ys false).result.bits quo
    (SemiprimeBitDivision.subBits (bit::rem) ys false).borrow f3 r3
  refine ⟨ff,rr,?_⟩
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h0 h1) h2) h3) h4

/-- Proof-side invariant for the physical quotient/remainder pair. -/
def digitPair (ys : List Bool) (qr : List Bool × List Bool) (bit : Bool) : List Bool × List Bool :=
  let next:=digitNext ys qr.2 bit
  (next.1::qr.1,next.2)

/-- MSB-first restoring is byte-for-byte the frozen recursive division routine. -/
theorem fold_original (xs ys : List Bool) :
    xs.reverse.foldl (digitPair ys) ([],(SemiprimeBitDivision.fitBits [] ys).bits)=
      ((SemiprimeBitDivision.divideLoop xs ys).quotient,(SemiprimeBitDivision.divideLoop xs ys).remainder) := by
  induction xs with
  | nil => rfl
  | cons bit xs ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    dsimp only [digitPair,digitNext]
    rw [SemiprimeBitDivision.divideLoop]
    cases hb:(SemiprimeBitDivision.subBits (bit::(SemiprimeBitDivision.divideLoop xs ys).remainder) ys false).borrow <;>
      simp

/-- Final divisor cleanup is a literal linear sequence of pops and halt. -/
theorem cleanup_run (ys rem quo : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (ys.length+2)
      (state (some (.control .cleanup)) flag rt [] ys [] [] [] [] [] rem quo [] [])=
    some (state none none none [] [] [] [] [] [] [] rem quo [] []) := by
  induction ys generalizing flag with
  | nil =>
    apply two_steps (b:=state (some (.control .done)) none rt [] [] [] [] [] [] [] rem quo [] [])
    · simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ys]
    · rfl
  | cons b ys ih =>
    have hs : C.run code 1
        (state (some (.control .cleanup)) flag rt [] (b::ys) [] [] [] [] [] rem quo [] [])=
        some (state (some (.control .cleanup)) (some b) rt [] ys [] [] [] [] [] rem quo [] []) := by
      cases b <;> simp [C.run,C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ys]
    have hh:=run_append 1 (ys.length+2) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- The exact actual round count, including final cleanup, used only in proofs. -/
def loopClock (ys : List Bool) : List Bool → List Bool → ℕ
  | [],_ => ys.length+3
  | bit::ds,rem => digitClock ys rem bit+loopClock ys ds (digitNext ys rem bit).2

/-- The complete actual round loop, with both declared outputs retained. -/
theorem loop_run (ys ds rem quo : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (loopClock ys ds rem)
      (state (some (.control .loop)) flag rt [] ys ds [] [] [] [] rem quo [] [])=
    some (state none none none [] [] [] [] [] [] []
      (ds.foldl (digitPair ys) (quo,rem)).2 (ds.foldl (digitPair ys) (quo,rem)).1 [] []) := by
  induction ds generalizing rem quo flag rt with
  | nil =>
    have hs : C.run code 1
        (state (some (.control .loop)) flag rt [] ys [] [] [] [] [] rem quo [] [])=
        some (state (some (.control .cleanup)) none rt [] ys [] [] [] [] [] rem quo [] []) := by
      simp [C.run,C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ds]
    simpa only [loopClock,List.foldl_nil,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      run_append 1 (ys.length+2) _ _ _ hs (cleanup_run ys rem quo none rt)
  | cons bit ds ih =>
    obtain ⟨ff,rr,hs⟩:=digit_run ys ds rem quo bit flag rt
    exact run_append _ _ _ _ _ hs (ih (digitNext ys rem bit).2 ((digitNext ys rem bit).1::quo) ff rr)

/-- Exact trace length for the prepared-input entry point. -/
def executionTime (xs ys : List Bool) : ℕ :=
  2*xs.length+1+initializeClock ys []+
    loopClock ys xs.reverse (SemiprimeBitDivision.fitBits [] ys).bits

/-- Closed actual execution matches both original raw division output words. -/
theorem source_run (xs ys : List Bool) :
    C.run code (executionTime xs ys)
      (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] [])=
    some (state none none none [] [] [] [] [] [] []
      (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] []) := by
  have h1:=reverse_run xs ys [] [] [] [] [] [] [] [] [] none none
  simp only [List.append_nil] at h1
  obtain ⟨ff,rr,h2⟩:=initialize_run ys xs.reverse [] [] none none
  have h3:=loop_run ys xs.reverse (SemiprimeBitDivision.fitBits [] ys).bits [] ff rr
  rw [fold_original] at h3
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3

/-- Physical fitting always restores the exact divisor width. -/
theorem digitNext_width (ys rem : List Bool) (bit : Bool) :
    (digitNext ys rem bit).2.length=ys.length :=
  (SemiprimeBitDivision.fitBits_counts _ ys).1

/-- Actual fitting cost includes every discarded high cell. -/
theorem initializeClock_le (ys rem : List Bool) :
    initializeClock ys rem ≤ 10*ys.length+rem.length+7 := by
  simp only [initializeClock,fitClock,List.length_drop]
  omega

/-- One restoring digit costs linearly in the actual fixed divisor width. -/
theorem digitClock_le (ys rem : List Bool) (bit : Bool) (hw : rem.length=ys.length) :
    digitClock ys rem bit ≤ 100*(ys.length+2) := by
  let expanded:=bit::rem
  let diff:=(SemiprimeBitDivision.subBits expanded ys false).result.bits
  have he : expanded.length=ys.length+1 := by simp [expanded,hw]
  have hd : diff.length=ys.length+1 := by
    simpa only [diff,he,Nat.max_eq_left (Nat.le_succ _)] using
      (SemiprimeBitDivision.subBits_counts expanded ys false).2.2.2.2
  have h1:=initializeClock_le ys expanded
  have h2:=initializeClock_le ys diff
  change 2+(1+(5*expanded.length+3))+(1+(5*ys.length+3))+
    (1+(3*(max expanded.length ys.length+1)+2*diff.length+3))+
    restoreClock ys expanded diff (SemiprimeBitDivision.subBits expanded ys false).borrow ≤ _
  unfold restoreClock
  split <;> omega

/-- The actual round loop has a quadratic bit-length bound, without quotient-value dependence. -/
theorem loopClock_le (ys ds rem : List Bool) (hw : rem.length=ys.length) :
    loopClock ys ds rem ≤ 100*ds.length*(ys.length+2)+ys.length+3 := by
  induction ds generalizing rem with
  | nil => simp [loopClock]
  | cons bit ds ih =>
    have hd:=digitClock_le ys rem bit hw
    have ht:=ih (digitNext ys rem bit).2 (digitNext_width ys rem bit)
    simp only [loopClock,List.length_cons]
    nlinarith

/-- Explicit fixed quadratic bit-length budget for the complete actual program. -/
def timeBound (n m : ℕ) : ℕ := 2*n+1+(10*m+7)+(100*n*(m+2)+m+3)

/-- No supplied subroutine-time promise occurs in the complete time bound. -/
theorem source_time (xs ys : List Bool) : executionTime xs ys ≤ timeBound xs.length ys.length := by
  have h1:=initializeClock_le ys []
  have h2:=loopClock_le ys xs.reverse (SemiprimeBitDivision.fitBits [] ys).bits
    (SemiprimeBitDivision.fitBits_counts [] ys).1
  simp only [List.length_nil,List.length_reverse] at *
  unfold executionTime timeBound
  omega

/-- Actual source-transition certificate with a derived quadratic budget. -/
def sourceDivide (xs ys : List Bool) :
    StateTransition.EvalsToInTime (C.step code)
      (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] [])
      (some (state none none none [] [] [] [] [] [] []
        (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] []))
      (timeBound xs.length ys.length) :=
  ⟨⟨_,source_run xs ys⟩,source_time xs ys⟩

/-- Actual fixed FinTM2 division. Both declared outputs are physical Boolean stacks;
every other stack, return frame and finite flag is cleared. -/
def machineDivide (xs ys : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] []))
      (some (SemiprimeD1StackCalls.configuration
        (state none none none [] [] [] [] [] [] []
          (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] [])))
      (timeBound xs.length ys.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label)
    (Sum.inr Aux.input) (Sum.inr Aux.quotient) (Label.control Control.start) code _ _ _ (sourceDivide xs ys)

/-- Positive divisors give the exact total frozen quotient/remainder byte interface. -/
theorem divideBits_outputs (xs ys : List Bool) (hD : 0<SemiprimeBitArithmetic.bitValue ys) :
    (SemiprimeBitDivision.divideBits xs ys).quotient=(SemiprimeBitDivision.divideLoop xs ys).quotient ∧
    (SemiprimeBitDivision.divideBits xs ys).remainder=(SemiprimeBitDivision.divideLoop xs ys).remainder := by
  have hb:=(SemiprimeBitDivision.nonzeroBits_correct ys).mpr hD
  simp [SemiprimeBitDivision.divideBits,hb]

/-- Actual positive-divisor certificate, refined to the routine used by normalization. -/
def machineDividePositive (xs ys : List Bool) (hD : 0<SemiprimeBitArithmetic.bitValue ys) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] []))
      (some (SemiprimeD1StackCalls.configuration
        (state none none none [] [] [] [] [] [] []
          (SemiprimeBitDivision.divideBits xs ys).remainder (SemiprimeBitDivision.divideBits xs ys).quotient [] [])))
      (timeBound xs.length ys.length) := by
  rw [(divideBits_outputs xs ys hD).1,(divideBits_outputs xs ys hD).2]
  exact machineDivide xs ys

/-- The produced raw outputs have the desired natural quotient and remainder under the same guard. -/
theorem output_values (xs ys : List Bool) (hD : 0<SemiprimeBitArithmetic.bitValue ys) :
    SemiprimeBitArithmetic.bitValue (SemiprimeBitDivision.divideLoop xs ys).quotient=
      SemiprimeBitArithmetic.bitValue xs/SemiprimeBitArithmetic.bitValue ys ∧
    SemiprimeBitArithmetic.bitValue (SemiprimeBitDivision.divideLoop xs ys).remainder=
      SemiprimeBitArithmetic.bitValue xs%SemiprimeBitArithmetic.bitValue ys := by
  have h:=SemiprimeBitDivision.divideBits_correct xs ys
  rw [(divideBits_outputs xs ys hD).1,(divideBits_outputs xs ys hD).2] at h
  exact h

/-- Every actual source prefix bounds all eleven Boolean stacks and its return stack. -/
theorem prefix_cells (xs ys : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 12*(xs.length+ys.length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound code fuel (xs.length+ys.length)
    _ out (by
      intro k
      rcases k with k|k
      · cases k <;> simp [state,payload]
      · cases k <;> simp [state,payload]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound code fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 11*(xs.length+ys.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(xs.length+ys.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 11*(xs.length+ys.length+fuel) := by
        have ha : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        have hb : Fintype.card Aux=7 := by decide
        simp [Stack,ha,hb]
  omega

/-- Successful prefixes cannot continue past this program's actual halt. -/
theorem prefix_fuel_le (xs ys : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] [])=some out) :
    fuel ≤ executionTime xs ys := by
  by_contra hn
  have he : fuel=executionTime xs ys+(1+(fuel-(executionTime xs ys+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run code 1 (state none none none [] [] [] [] [] [] []
      (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] [])=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- A source-prefix polynomial space bound with no supplied fuel limit. -/
theorem prefix_polynomial_cells (xs ys : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      12*(xs.length+ys.length+timeBound xs.length ys.length) := by
  have hf:=(prefix_fuel_le xs ys fuel out hr).trans (source_time xs ys)
  exact (prefix_cells xs ys fuel out hr).trans (by omega)

/-- Every actual compiled-machine prefix satisfies the same input-polynomial space bound. -/
theorem machine_prefix_polynomial_cells (xs ys : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      12*(xs.length+ys.length+timeBound xs.length ys.length) := by
  let start:=state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] []
  have he:=SemiprimeD1StackCalls.run_correct (.inr .input) (.inr .quotient) (.control .start) code fuel start
  change (C.run code fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run code fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_polynomial_cells xs ys fuel out hc

/-- An explicit fixed quadratic monomial also dominates the transition bound. -/
theorem timeBound_le_square (n m : ℕ) : timeBound n m ≤ 1000*(n+m+2)^2 := by
  unfold timeBound
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (m*m),Nat.zero_le (n*m)]

end RiemannGaussian.SemiprimeD1StackDividerExecution
