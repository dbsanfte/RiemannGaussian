/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplier

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackMultiplierExecution
open SemiprimeD1StackMultiplier
namespace C
export SemiprimeD1StackCalls (State execute step run)
end C

/-- Source trace composition for this literal enclosing program. -/
theorem run_append (m n : ℕ) (a b c : C.State Stack Label)
    (hm : C.run code m a=some b) (hn : C.run code n b=some c) :
    C.run code (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hn]

/-- Two actual transitions, never a subroutine-cost assumption. -/
theorem two_steps (a b c : C.State Stack Label)
    (h₁ : C.step code a=some b) (h₂ : C.step code b=some c) : C.run code 2 a=some c := by
  change (C.step code a).bind (C.step code)=some c
  rw [h₁,Option.bind_some,h₂]

/-- Exact literal write to the xs payload stack. -/
theorem payload_xs (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) input bits=payload bits ys ds left acc scratch out cp cs := by
  change Function.update (payload xs ys ds left acc scratch out cp cs) (.inr (.inr false)) bits=payload bits ys ds left acc scratch out cp cs
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_xs (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs input=xs := rfl

/-- Exact literal write to the ys payload stack. -/
theorem payload_ys (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) factor bits=payload xs bits ds left acc scratch out cp cs := by
  change Function.update (payload xs ys ds left acc scratch out cp cs) (.inr (.inl 0)) bits=payload xs bits ds left acc scratch out cp cs
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_ys (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs factor=ys := rfl

/-- Exact literal write to the ds payload stack. -/
theorem payload_ds (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) digits bits=payload xs ys bits left acc scratch out cp cs := by
  change Function.update (payload xs ys ds left acc scratch out cp cs) (.inr (.inr true)) bits=payload xs ys bits left acc scratch out cp cs
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_ds (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs digits=ds := rfl

/-- Exact literal write to the left payload stack. -/
theorem payload_left (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) (.inl .left) bits=payload xs ys ds bits acc scratch out cp cs := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_left (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs (.inl .left)=left := rfl

/-- Exact literal write to the acc payload stack. -/
theorem payload_acc (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) (.inl .right) bits=payload xs ys ds left bits scratch out cp cs := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_acc (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs (.inl .right)=acc := rfl

/-- Exact literal write to the scratch payload stack. -/
theorem payload_scratch (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) (.inl .scratch) bits=payload xs ys ds left acc bits out cp cs := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_scratch (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs (.inl .scratch)=scratch := rfl

/-- Exact literal write to the out payload stack. -/
theorem payload_out (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) (.inl .output) bits=payload xs ys ds left acc scratch bits cp cs := by
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_out (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs (.inl .output)=out := rfl

/-- Exact literal write to the cp payload stack. -/
theorem payload_cp (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) copied bits=payload xs ys ds left acc scratch out bits cs := by
  change Function.update (payload xs ys ds left acc scratch out cp cs) (.inr (.inl 1)) bits=payload xs ys ds left acc scratch out bits cs
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_cp (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs copied=cp := rfl

/-- Exact literal write to the cs payload stack. -/
theorem payload_cs (xs ys ds left acc scratch out cp cs bits : List Bool) :
    Function.update (payload xs ys ds left acc scratch out cp cs) copyScratch bits=payload xs ys ds left acc scratch out cp bits := by
  change Function.update (payload xs ys ds left acc scratch out cp cs) (.inr (.inl 2)) bits=payload xs ys ds left acc scratch out cp bits
  funext k
  rcases k with k|k
  · cases k <;> simp [payload,Function.update]
  · rcases k with k|k
    · fin_cases k <;> simp [payload,Function.update]
    · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_cs (xs ys ds left acc scratch out cp cs : List Bool) :
    payload xs ys ds left acc scratch out cp cs copyScratch=cs := rfl

/-- Actual pop/push traversal; every source cell is moved once. -/
theorem reverse_run (xs ys ds left acc scratch out cp cs : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*xs.length+1)
      (state (some (.control .start)) flag rt xs ys ds left acc scratch out cp cs)=
    some (state (some (.control .loop)) none rt ([]) ys (xs.reverse++ds) left acc scratch out cp cs) := by
  induction xs generalizing ds flag with
  | nil =>
    simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,
      state,code,payload_xs]
  | cons b xs ih =>
    have hs : C.run code 2
        (state (some (.control .start)) flag rt (b::xs) ys ds left acc scratch out cp cs)=
        some (state (some (.control .start)) (some b) rt (xs) ys (b::ds) left acc scratch out cp cs) := by
      apply two_steps (b:=state (some (.control (.reversePush b))) (some b) rt (xs) ys ds left acc scratch out cp cs)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_xs]
      · simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_ds]
    have hh:=run_append 2 (2*xs.length+1) _ _ _ hs (ih (b::ds) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual pop/push traversal; every source cell is moved once. -/
theorem copy_move (xs ys ds left acc scratch out cp cs : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*cp.length+1)
      (state (some (.control .copyToScratch)) flag rt xs ys ds left acc scratch out cp cs)=
    some (state (some (.control .scratchToLeft)) none rt xs ys ds left acc (cp.reverse++scratch) out ([]) cs) := by
  induction cp generalizing scratch flag with
  | nil =>
    simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,
      state,code,payload_cp]
  | cons b cp ih =>
    have hs : C.run code 2
        (state (some (.control .copyToScratch)) flag rt xs ys ds left acc scratch out (b::cp) cs)=
        some (state (some (.control .copyToScratch)) (some b) rt xs ys ds left acc (b::scratch) out (cp) cs) := by
      apply two_steps (b:=state (some (.control (.copyPush b))) (some b) rt xs ys ds left acc scratch out (cp) cs)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_cp]
      · simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_scratch]
    have hh:=run_append 2 (2*cp.length+1) _ _ _ hs (ih (b::scratch) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual pop/push traversal; every source cell is moved once. -/
theorem left_move (xs ys ds left acc scratch out cp cs : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*scratch.length+1)
      (state (some (.control .scratchToLeft)) flag rt xs ys ds left acc scratch out cp cs)=
    some (state (some (.control .callAdder)) none rt xs ys ds (scratch.reverse++left) acc ([]) out cp cs) := by
  induction scratch generalizing left flag with
  | nil =>
    simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,
      state,code,payload_scratch]
  | cons b scratch ih =>
    have hs : C.run code 2
        (state (some (.control .scratchToLeft)) flag rt xs ys ds left acc (b::scratch) out cp cs)=
        some (state (some (.control .scratchToLeft)) (some b) rt xs ys ds (b::left) acc (scratch) out cp cs) := by
      apply two_steps (b:=state (some (.control (.leftPush b))) (some b) rt xs ys ds left acc (scratch) out cp cs)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_scratch]
      · simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_left]
    have hh:=run_append 2 (2*scratch.length+1) _ _ _ hs (ih (b::left) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual pop/push traversal; every source cell is moved once. -/
theorem sum_move (xs ys ds left acc scratch out cp cs : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*out.length+1)
      (state (some (.control .sumToScratch)) flag rt xs ys ds left acc scratch out cp cs)=
    some (state (some (.control .scratchToAcc)) none rt xs ys ds left acc (out.reverse++scratch) ([]) cp cs) := by
  induction out generalizing scratch flag with
  | nil =>
    simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,
      state,code,payload_out]
  | cons b out ih =>
    have hs : C.run code 2
        (state (some (.control .sumToScratch)) flag rt xs ys ds left acc scratch (b::out) cp cs)=
        some (state (some (.control .sumToScratch)) (some b) rt xs ys ds left acc (b::scratch) (out) cp cs) := by
      apply two_steps (b:=state (some (.control (.sumPush b))) (some b) rt xs ys ds left acc scratch (out) cp cs)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_out]
      · simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_scratch]
    have hh:=run_append 2 (2*out.length+1) _ _ _ hs (ih (b::scratch) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual pop/push traversal; every source cell is moved once. -/
theorem acc_move (xs ys ds left acc scratch out cp cs : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (2*scratch.length+1)
      (state (some (.control .scratchToAcc)) flag rt xs ys ds left acc scratch out cp cs)=
    some (state (some (.control .loop)) none rt xs ys ds left (scratch.reverse++acc) ([]) out cp cs) := by
  induction scratch generalizing acc flag with
  | nil =>
    simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,
      state,code,payload_scratch]
  | cons b scratch ih =>
    have hs : C.run code 2
        (state (some (.control .scratchToAcc)) flag rt xs ys ds left acc (b::scratch) out cp cs)=
        some (state (some (.control .scratchToAcc)) (some b) rt xs ys ds left (b::acc) (scratch) out cp cs) := by
      apply two_steps (b:=state (some (.control (.accPush b))) (some b) rt xs ys ds left acc (scratch) out cp cs)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_scratch]
      · simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,
          state,code,payload_acc]
    have hh:=run_append 2 (2*scratch.length+1) _ _ _ hs (ih (b::acc) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,
      List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh


/-- The actual copy call executes its frozen trace and pops its real continuation. -/
theorem copy_call (xs ys ds left acc scratch out : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (1+(5*ys.length+3))
      (state (some (.control .callCopy)) flag rt xs ys ds left acc scratch out [] [])=
    some (state (some (.control .copyToScratch)) ff rr xs ys ds left acc scratch out ys []) := by
  let original:=payload xs ys ds left acc scratch out [] []
  let entered : C.State Stack Label :=
    ⟨some (.copy 0),none,none,original,[.control .copyToScratch]⟩
  have hstart : C.run code 1
      (state (some (.control .callCopy)) flag rt xs ys ds left acc scratch out [] [])=some entered := rfl
  have hi : Function.Injective copyStack := by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)
  have hrel : SemiprimeD1StackMultiplierLink.Rel copyStack Label.copy original
      (.control .copyToScratch) [] (SemiprimeD1StackCopy.state 0 none ys [] []) entered := by
    constructor
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel copyStack Label.copy hi
    code SemiprimeD1StackCopy.code (fun _=>rfl) original (.control .copyToScratch) []
    (5*ys.length+3) _ _ entered hrel (SemiprimeD1StackCopy.copy_words ys [] none)
  have desired : SemiprimeD1StackMultiplierLink.DataRel copyStack original
      (SemiprimeD1StackCopy.done ys (ys++[])).store
      (payload xs ys ds left acc scratch out ys []) := by
    constructor
    · intro k; fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,payload]
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · cases k <;> rfl
  have hd:=SemiprimeD1StackMultiplierLink.data_unique copyStack original _ _ _ hr.1 desired
  have hp : finish.pc=some (.control .copyToScratch) ∧ finish.frames=[] := hr.2
  have heq : finish=state (some (.control .copyToScratch)) finish.flag finish.returned
      xs ys ds left acc scratch out ys [] := by
    cases finish
    simp_all [state]
  refine ⟨finish.flag,finish.returned,?_⟩
  exact run_append 1 (5*ys.length+3) _ _ _ hstart (hfinish.trans (congrArg some heq))

/-- The actual adder call executes its frozen trace and pops its real continuation. -/
theorem adder_call (xs ys ds left acc cp cs : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code
      (1+(3*(max left.length acc.length+1)+2*(SemiprimeBitArithmetic.addBits left acc false).bits.length+2))
      (state (some (.control .callAdder)) flag rt xs ys ds left acc [] [] cp cs)=
    some (state (some (.control .sumToScratch)) ff rr xs ys ds [] [] []
      (SemiprimeBitArithmetic.addBits left acc false).bits cp cs) := by
  let original:=payload xs ys ds left acc [] [] cp cs
  let entered : C.State Stack Label :=
    ⟨some (.adder (.start false)),none,none,original,[.control .sumToScratch]⟩
  have hstart : C.run code 1
      (state (some (.control .callAdder)) flag rt xs ys ds left acc [] [] cp cs)=some entered := rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel Sum.inl Label.adder original
      (.control .sumToScratch) [] (SemiprimeD1StackAdder.state (some (.start false)) none left acc [] []) entered := by
    constructor
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk; rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel Sum.inl Label.adder Sum.inl_injective
    code SemiprimeD1StackAdder.code (fun _=>rfl) original (.control .sumToScratch) []
    _ _ _ entered hrel (SemiprimeD1StackAdderExecution.source_run left acc false)
  have desired : SemiprimeD1StackMultiplierLink.DataRel Sum.inl original
      (SemiprimeD1StackAdder.state none none [] [] [] (SemiprimeBitArithmetic.addBits left acc false).bits).store
      (payload xs ys ds [] [] [] (SemiprimeBitArithmetic.addBits left acc false).bits cp cs) := by
    constructor
    · intro k; cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rcases k with k|k <;> rfl
  have hd:=SemiprimeD1StackMultiplierLink.data_unique Sum.inl original _ _ _ hr.1 desired
  have hp : finish.pc=some (.control .sumToScratch) ∧ finish.frames=[] := hr.2
  have heq : finish=state (some (.control .sumToScratch)) finish.flag finish.returned
      xs ys ds [] [] [] (SemiprimeBitArithmetic.addBits left acc false).bits cp cs := by
    cases finish
    simp_all [state]
  refine ⟨finish.flag,finish.returned,?_⟩
  exact run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))

/-- Literal transition count of one multiplier digit, including both real calls. -/
def digitClock (ys acc : List Bool) (bit : Bool) : ℕ :=
  if bit then
    2+(1+(5*ys.length+3))+(2*ys.length+1)+(2*ys.length+1)+
      (1+(3*(max ys.length (false::acc).length+1)+
        2*(SemiprimeBitArithmetic.addBits ys (false::acc) false).bits.length+2))+
      (2*(SemiprimeBitArithmetic.addBits ys (false::acc) false).bits.length+1)+
      (2*(SemiprimeBitArithmetic.addBits ys (false::acc) false).bits.length+1)
  else 2

/-- One actual digit iteration restores both call workspaces and retains the factor. -/
theorem digit_run (ys ds acc : List Bool) (bit : Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (digitClock ys acc bit)
      (state (some (.control .loop)) flag rt [] ys (bit::ds) [] acc [] [] [] [])=
    some (state (some (.control .loop)) ff rr [] ys ds [] (digitStep ys acc bit) [] [] [] []) := by
  cases bit with
  | false =>
    refine ⟨some false,rt,?_⟩
    apply two_steps (b:=state (some (.control .shiftFalse)) (some false) rt [] ys ds [] acc [] [] [] [])
    · simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ds]
    · simp [C.step,C.execute,state,code,digitStep,payload_acc]
  | true =>
    have h0 : C.run code 2
        (state (some (.control .loop)) flag rt [] ys (true::ds) [] acc [] [] [] [])=
        some (state (some (.control .callCopy)) (some true) rt [] ys ds [] (false::acc) [] [] [] []) := by
      apply two_steps (b:=state (some (.control .shiftTrue)) (some true) rt [] ys ds [] acc [] [] [] [])
      · simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ds]
      · simp [C.step,C.execute,state,code,payload_acc]
    obtain ⟨f1,r1,h1⟩:=copy_call [] ys ds [] (false::acc) [] [] (some true) rt
    have h2:=copy_move [] ys ds [] (false::acc) [] [] ys [] f1 r1
    simp only [List.append_nil] at h2
    have h3:=left_move [] ys ds [] (false::acc) ys.reverse [] [] [] none r1
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h3
    obtain ⟨f4,r4,h4⟩:=adder_call [] ys ds ys (false::acc) [] [] none r1
    let result:=(SemiprimeBitArithmetic.addBits ys (false::acc) false).bits
    have h5:=sum_move [] ys ds [] [] [] result [] [] f4 r4
    simp only [List.append_nil] at h5
    have h6:=acc_move [] ys ds [] [] result.reverse [] [] [] none r4
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h6
    have h01:=run_append _ _ _ _ _ h0 h1
    have h02:=run_append _ _ _ _ _ h01 h2
    have h03:=run_append _ _ _ _ _ h02 h3
    have h04:=run_append _ _ _ _ _ h03 h4
    have h05:=run_append _ _ _ _ _ h04 h5
    have h06:=run_append _ _ _ _ _ h05 h6
    refine ⟨none,r4,?_⟩
    simpa only [digitClock,ite_true,digitStep] using h06

/-- Persistent-factor cleanup consists of actual pops and the final halt. -/
theorem cleanup_run (ys acc : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (ys.length+2)
      (state (some (.control .cleanup)) flag rt [] ys [] [] acc [] [] [] [])=
    some (state none none none [] [] [] [] acc [] [] [] []) := by
  induction ys generalizing flag with
  | nil =>
    apply two_steps (b:=state (some (.control .done)) none rt [] [] [] [] acc [] [] [] [])
    · simp [C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ys]
    · rfl
  | cons b ys ih =>
    have hs : C.run code 1
        (state (some (.control .cleanup)) flag rt [] (b::ys) [] [] acc [] [] [] [])=
        some (state (some (.control .cleanup)) (some b) rt [] ys [] [] acc [] [] [] []) := by
      cases b <;> simp [C.run,C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ys]
    have hh:=run_append 1 (ys.length+2) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Exact loop trace length, defined only in the proof from the actual digit traces. -/
def loopClock (ys : List Bool) : List Bool → List Bool → ℕ
  | [],_ => ys.length+3
  | bit::ds,acc => digitClock ys acc bit+loopClock ys ds (digitStep ys acc bit)

/-- The closed loop executes every physical digit, then clears all workspace. -/
theorem loop_run (ys ds acc : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (loopClock ys ds acc)
      (state (some (.control .loop)) flag rt [] ys ds [] acc [] [] [] [])=
    some (state none none none [] [] [] [] (ds.foldl (digitStep ys) acc) [] [] [] []) := by
  induction ds generalizing acc flag rt with
  | nil =>
    have hs : C.run code 1
        (state (some (.control .loop)) flag rt [] ys [] [] acc [] [] [] [])=
        some (state (some (.control .cleanup)) none rt [] ys [] [] acc [] [] [] []) := by
      simp [C.run,C.step,C.execute,state,code,SemiprimeD1StackBytecode.choose,payload_ds]
    simpa only [loopClock,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,List.foldl_nil] using
      run_append 1 (ys.length+2) _ _ _ hs (cleanup_run ys acc none rt)
  | cons bit ds ih =>
    obtain ⟨ff,rr,hs⟩:=digit_run ys ds acc bit flag rt
    exact run_append _ _ _ _ _ hs (ih (digitStep ys acc bit) ff rr)

/-- Actual closed multiplication trace: only the result stack remains nonempty. -/
theorem source_run (xs ys : List Bool) :
    C.run code (2*xs.length+1+loopClock ys xs.reverse [])
      (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])=
    some (state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] []) := by
  have hr:=reverse_run xs ys [] [] [] [] [] [] [] none none
  simp only [List.append_nil] at hr
  have hl:=loop_run ys xs.reverse [] none none
  rw [fold_digits] at hl
  exact run_append _ _ _ _ _ hr hl

/-- Each real digit iteration has a linear bound in the current operand sizes. -/
theorem digitClock_le (ys acc : List Bool) (bit : Bool) :
    digitClock ys acc bit ≤ 100*(acc.length+ys.length+3) := by
  cases bit with
  | false => simp only [digitClock,Bool.false_eq_true,ite_false]; omega
  | true =>
    have hh:=(SemiprimeBitArithmetic.addBits_counts ys (false::acc) false).2.2.2.2
    simp only [digitClock,ite_true,List.length_cons] at *
    omega

/-- Uniform loop cost from the proved actual padding-growth invariant. -/
theorem loopClock_le (ys ds acc : List Bool) (cap : ℕ)
    (hc : acc.length+ds.length*(ys.length+2) ≤ cap) :
    loopClock ys ds acc ≤ 100*(ds.length+1)*(cap+ys.length+3) := by
  induction ds generalizing acc with
  | nil => simp only [loopClock,List.length_nil,Nat.zero_add,Nat.mul_one]; omega
  | cons bit ds ih =>
    have hg:=digitStep_length ys acc bit
    have hnext : (digitStep ys acc bit).length+ds.length*(ys.length+2) ≤ cap := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hc
      omega
    have ht:=ih (digitStep ys acc bit) hnext
    have hd:=digitClock_le ys acc bit
    have ha : acc.length ≤ cap := by omega
    simp only [loopClock,List.length_cons]
    nlinarith

/-- A concrete cubic polynomial bound; no subroutine-time hypothesis occurs. -/
def timeBound (n m : ℕ) : ℕ :=
  2*n+1+100*(n+1)*(n*(m+2)+m+3)

/-- The exact proved trace fits the fixed cubic time budget. -/
theorem source_time (xs ys : List Bool) :
    2*xs.length+1+loopClock ys xs.reverse [] ≤ timeBound xs.length ys.length := by
  have h:=loopClock_le ys xs.reverse [] (xs.length*(ys.length+2)) (by simp)
  simpa only [List.length_reverse,timeBound] using Nat.add_le_add_left h (2*xs.length+1)

/-- Source transition certificate for the actual closed program. -/
def sourceMultiply (xs ys : List Bool) :
    StateTransition.EvalsToInTime (C.step code)
      (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])
      (some (state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] []))
      (timeBound xs.length ys.length) :=
  ⟨⟨_,source_run xs ys⟩,source_time xs ys⟩

/-- All actual workspaces and the return stack are empty at the final machine state. -/
theorem finish_eq_final (bits : List Bool) :
    state none none none [] [] [] [] bits [] [] [] []=
      (SemiprimeD1StackCalls.final (.inl .right) bits : C.State Stack Label) := by
  change (⟨none,none,none,payload [] [] [] [] bits [] [] [] [],[]⟩:C.State Stack Label)=
    ⟨none,none,none,(fun k=>if k=Sum.inl SemiprimeD1StackAdder.Stack.right then bits else []),[]⟩
  congr 1
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · fin_cases k <;> rfl
    · cases k <;> rfl

/-- The concrete halted source configuration is the standard output configuration. -/
theorem finish_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration
      (state none none none [] [] [] [] bits [] [] [] [])=Turing.haltList machine bits := by
  rw [finish_eq_final]
  exact SemiprimeD1StackCalls.final_correct input (.inl .right) (.control .start) code bits

/-- Actual fixed finite-stack-machine multiplication, including physical calls/returns. -/
def machineMultiply (xs ys : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] []))
      (some (Turing.haltList machine (SemiprimeBitArithmetic.mulBits xs ys).bits))
      (timeBound xs.length ys.length) := by
  have h:=SemiprimeD1StackCalls.evalsCorrect input (.inl .right) (.control .start) code
    (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])
    (state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] [])
    (timeBound xs.length ys.length) (sourceMultiply xs ys)
  change StateTransition.EvalsToInTime machine.step
    (SemiprimeD1StackCalls.configuration
      (state (some (.control .start)) none none xs ys [] [] [] [] [] [] []))
    (some (SemiprimeD1StackCalls.configuration
      (state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] [])))
    (timeBound xs.length ys.length) at h
  exact Eq.mp (congrArg (fun finish : machine.Cfg =>
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] []))
      (some finish) (timeBound xs.length ys.length))
    (finish_configuration (SemiprimeBitArithmetic.mulBits xs ys).bits)) h

/-- Every actual source prefix bounds all nine Boolean stacks and real return frames. -/
theorem prefix_cells (xs ys : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 10*(xs.length+ys.length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound code fuel (xs.length+ys.length)
    _ out (by
      intro k
      rcases k with k|k
      · cases k <;> simp [state,payload]
      · rcases k with k|k
        · fin_cases k <;> simp [state,payload]
        · cases k <;> simp [state,payload]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound code fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 9*(xs.length+ys.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(xs.length+ys.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 9*(xs.length+ys.length+fuel) := by
        have hc : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        simp [Stack,hc]
  omega

/-- The same all-prefix space bound holds for the actual compiled machine. -/
theorem machine_prefix_cells (xs ys : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      10*(xs.length+ys.length+fuel) := by
  let start:=state (some (.control .start)) none none xs ys [] [] [] [] [] [] []
  have he:=SemiprimeD1StackCalls.run_correct input (.inl .right) (.control .start) code fuel start
  change (C.run code fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run code fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells xs ys fuel out hc

/-- A successful prefix cannot extend past the actual proved halt transition. -/
theorem prefix_fuel_le (xs ys : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])=some out) :
    fuel ≤ 2*xs.length+1+loopClock ys xs.reverse [] := by
  by_contra hn
  have he : fuel=(2*xs.length+1+loopClock ys xs.reverse [])+
      (1+(fuel-(2*xs.length+1+loopClock ys xs.reverse []+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run code 1
      (state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] [])=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- All successful source prefixes have a fixed cubic space bound in the input. -/
theorem prefix_polynomial_cells (xs ys : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      10*(xs.length+ys.length+timeBound xs.length ys.length) := by
  have hf:=(prefix_fuel_le xs ys fuel out hr).trans (source_time xs ys)
  exact (prefix_cells xs ys fuel out hr).trans (by omega)

/-- Every actual machine prefix, with no fuel premise, satisfies that cubic space bound. -/
theorem machine_prefix_polynomial_cells (xs ys : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      10*(xs.length+ys.length+timeBound xs.length ys.length) := by
  let start:=state (some (.control .start)) none none xs ys [] [] [] [] [] [] []
  have he:=SemiprimeD1StackCalls.run_correct input (.inl .right) (.control .start) code fuel start
  change (C.run code fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run code fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_polynomial_cells xs ys fuel out hc

/-- The explicit budget is bounded by one fixed monomial. -/
theorem timeBound_le_cube (n m : ℕ) : timeBound n m ≤ 1000*(n+m+2)^3 := by
  let u:=n+m+2
  have hn : n+1≤u := by omega
  have hm : m+2≤u := by omega
  have hu : 2≤u := by omega
  have hsmall : 2*n+1≤u*u*u := by nlinarith
  have hin : n*(m+2)+m+3≤3*u*u := by nlinarith
  have hprod : 100*(n+1)*(n*(m+2)+m+3)≤100*u*(3*u*u) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 100 hn) hin
  dsimp only [timeBound]
  change 2*n+1+100*(n+1)*(n*(m+2)+m+3)≤1000*u^3
  nlinarith [Nat.zero_le (u*u*u)]

end RiemannGaussian.SemiprimeD1StackMultiplierExecution
