/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCalls
import RiemannGaussian.SemiprimeD1StackRename
import RiemannGaussian.SemiprimeD1StackHeapAllocate

/-! # Actual procedure-return linking of literal stack programs
A fixed main pushes its literal continuation, enters the included program,
and returns through an actual return-stack pop. A component halt is replaced
by return, never by a free semantic submachine operation.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackReturnLink
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Literal component instruction; component halt becomes actual return. -/
def instruction {K L:Type} : B.Instruction K L→C.Instruction K (L⊕Bool)
  | .halt => .ret
  | .push k bit next => .base (.push k bit (.inl next))
  | .pop k empty low high => .base (.pop k (.inl empty) (.inl low) (.inl high))
  | .peek k empty low high => .base (.peek k (.inl empty) (.inl low) (.inl high))
  | .jump next => .base (.jump (.inl next))

/-- One fixed linked code with two static caller labels. -/
def code {K L:Type} (entry:L) (component:L→B.Instruction K L) :
    L⊕Bool→C.Instruction K (L⊕Bool)
  | .inl label => instruction (component label)
  | .inr false => .call (.inl entry) (.inr true)
  | .inr true => .base .halt

/-- Ignore finite read flags but preserve exact data, labels and actual return stack. -/
def Rel {K L:Type} (s:B.State K L) (t:C.State K (L⊕Bool)) : Prop :=
  t.data=s.store ∧ match s.pc with
    | none => t.pc=some (.inr true) ∧ t.frames=[]
    | some label => t.pc=some (.inl label) ∧ t.frames=[.inr true]

/-- The actual linked instruction preserves the exact payload/return correspondence. -/
theorem instruction_rel {K L:Type} [DecidableEq K] (op:B.Instruction K L)
    (s:B.State K L) (t:C.State K (L⊕Bool)) (label:L)
    (hp:s.pc=some label) (h:Rel s t) :
    Rel (B.execute op s) (C.execute (instruction op) t) := by
  rcases h with ⟨hd,ht⟩
  simp only [hp] at ht
  rcases ht with ⟨ht,hf⟩
  cases op <;> simp [Rel,instruction,B.execute,C.execute,hd,hf,
    SemiprimeD1StackRename.choose_inl]

/-- Actual source and linked program run composition. -/
theorem run_add {K L:Type} [DecidableEq K] (program:L→C.Instruction K L)
    (m n:ℕ) (s:C.State K L) :
    C.run program (m+n) s=(C.run program m s).bind (C.run program n) := by
  unfold C.run
  rw [Nat.add_comm m n,Function.iterate_add_apply]
  generalize (fun state=>state.bind (C.step program))^[m] (some s)=o
  cases o with
  | some s => rfl
  | none => exact Function.iterate_fixed rfl n

/-- Every successful component trace executes as literal linked instructions. -/
theorem run_rel {K L:Type} [DecidableEq K] (entry:L) (component:L→B.Instruction K L)
    (fuel:ℕ) (s out:B.State K L) (t:C.State K (L⊕Bool))
    (h:Rel s t) (hr:B.run component fuel s=some out) :
    ∃finish,C.run (code entry component) fuel t=some finish ∧ Rel out finish := by
  induction fuel generalizing s t with
  | zero => change some s=some out at hr;cases hr;exact ⟨t,rfl,h⟩
  | succ fuel ih =>
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackCopy.run_add] at hr
    change (B.step component s).bind (B.run component fuel)=some out at hr
    cases hp:s.pc with
    | none => simp [B.step,SemiprimeD1StackBytecode.step,hp] at hr
    | some label =>
      have hs:B.step component s=some (B.execute (component label) s):=by
        simp [B.step,SemiprimeD1StackBytecode.step,hp]
      rw [hs,Option.bind_some] at hr
      have htpc:t.pc=some (.inl label):=by
        have hh:=h.2
        rw [hp] at hh
        exact hh.1
      have ht:C.step (code entry component) t=some (C.execute (instruction (component label)) t):=by
        simp [C.step,SemiprimeD1StackCalls.step,htpc,code]
      obtain ⟨finish,hfinish,hrel⟩:=ih (B.execute (component label) s)
        (C.execute (instruction (component label)) t) (instruction_rel _ _ _ label hp h) hr
      refine ⟨finish,?_,hrel⟩
      rw [show fuel+1=1+fuel by omega,run_add]
      change (C.step (code entry component) t).bind (C.run (code entry component) fuel)=some finish
      rw [ht,Option.bind_some,hfinish]

/-- Actual caller state; no preloaded return frame is assumed. -/
def initial {K L:Type} (store:K→List Bool) : C.State K (L⊕Bool) :=
  ⟨some (.inr false),none,none,store,[]⟩

/-- Actual caller halt with all return frames consumed. -/
def final {K L:Type} (store:K→List Bool) : C.State K (L⊕Bool) :=
  ⟨none,none,none,store,[]⟩

/-- Call push, included execution, real return pop and caller halt are all executed. -/
theorem linked_run {K L:Type} [DecidableEq K] (entry:L) (component:L→B.Instruction K L)
    (time:ℕ) (input output:K→List Bool)
    (h:B.run component time ⟨some entry,none,input⟩=some ⟨none,none,output⟩) :
    C.run (code entry component) (time+2) (initial input)=some (final output) := by
  have hstart:C.run (code entry component) 1 (initial input)=
      some (⟨some (.inl entry),none,none,input,[.inr true]⟩:C.State K (L⊕Bool)):=rfl
  have hrel:Rel (⟨some entry,none,input⟩:B.State K L)
      (⟨some (.inl entry),none,none,input,[.inr true]⟩:C.State K (L⊕Bool)):=⟨rfl,rfl,rfl⟩
  obtain ⟨finish,hfinish,hrel⟩:=run_rel entry component time _ _ _ hrel h
  have hdata:finish.data=output:=hrel.1
  have hpc:finish.pc=some (.inr true):=hrel.2.1
  have hframes:finish.frames=[]:=hrel.2.2
  have hend:C.run (code entry component) 1 finish=some (final output):=by
    simp [C.run,SemiprimeD1StackCalls.run,C.step,SemiprimeD1StackCalls.step,
      C.execute,SemiprimeD1StackCalls.execute,code,hpc,final,hdata,hframes]
  rw [show time+2=1+(time+1) by omega,run_add,hstart,Option.bind_some,run_add,hfinish,Option.bind_some,hend]

/-- Genuine larger finite-machine certificate with both linking transitions paid. -/
def linkedInTime {K L:Type} [DecidableEq K] [Fintype K] [Fintype L]
    (entry:L) (component:L→B.Instruction K L) (inputStack outputStack:K)
    (time:ℕ) (input output:K→List Bool)
    (h:B.run component time ⟨some entry,none,input⟩=some ⟨none,none,output⟩) :
    StateTransition.EvalsToInTime
      (SemiprimeD1StackCalls.machine inputStack outputStack (.inr false) (code entry component)).step
      (SemiprimeD1StackCalls.configuration (initial input))
      (some (SemiprimeD1StackCalls.configuration (final output))) (time+2) := by
  apply SemiprimeD1StackCalls.evalsCorrect inputStack outputStack (.inr false) (code entry component)
  exact ⟨⟨time+2,linked_run entry component time input output h⟩,le_refl _⟩
/-- Each actual linked instruction increases each data stack by at most one cell. -/
theorem execute_data_bound {K L:Type} [DecidableEq K] (op:C.Instruction K L)
    (s:C.State K L) (cap:ℕ) (h:∀k,(s.data k).length ≤ cap) :
    ∀k,((C.execute op s).data k).length ≤ cap+1 := by
  cases op with
  | base op =>
    have hb:=SemiprimeD1StackCopy.execute_bound op (⟨none,s.flag,s.data⟩:B.State K L) cap h
    cases op <;> exact hb
  | call callee continuation => exact fun k=>(h k).trans (Nat.le_succ cap)
  | ret =>
    cases hf:s.frames <;> intro k <;> simpa [C.execute,SemiprimeD1StackCalls.execute,hf] using (h k).trans (Nat.le_succ cap)

/-- Actual call/return prefixes bound Boolean payload, independently of debug reports. -/
theorem run_data_bound {K L:Type} [DecidableEq K] (program:L→C.Instruction K L)
    (fuel cap:ℕ) (s out:C.State K L) (h:∀k,(s.data k).length ≤ cap)
    (hr:C.run program fuel s=some out) : ∀k,(out.data k).length ≤ cap+fuel := by
  induction fuel generalizing s out cap with
  | zero => change some s=some out at hr;cases hr;exact h
  | succ fuel ih =>
    rw [show fuel+1=1+fuel by omega,run_add] at hr
    change (C.step program s).bind (C.run program fuel)=some out at hr
    cases hp:s.pc with
    | none => simp [C.step,SemiprimeD1StackCalls.step,hp] at hr
    | some label =>
      have he:C.step program s=some (C.execute (program label) s):=by simp [C.step,SemiprimeD1StackCalls.step,hp]
      rw [he,Option.bind_some] at hr
      have hb:=ih (cap+1) (C.execute (program label) s) out (execute_data_bound _ _ _ h) hr
      simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using hb

/-- Concrete fixed caller and actual allocator, with no input-dependent code labels. -/
def allocatorMachine : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine (0:Fin 6) 4 (.inr false)
    (code (0:Fin 22) SemiprimeD1StackHeapAllocate.code)

/-- Concrete allocator call executes its own return push/pop and final caller halt. -/
def allocateInTime (record heap counter:List Bool) :
    StateTransition.EvalsToInTime allocatorMachine.step
      (SemiprimeD1StackCalls.configuration
        (initial (L:=Fin 22) (SemiprimeD1StackHeapAllocate.payload record heap [] counter [] [])))
      (some (SemiprimeD1StackCalls.configuration
        (final (L:=Fin 22) (SemiprimeD1StackHeapAllocate.payload record
          (SemiprimeSourceHistogramKeyBits.frame record heap) [] (true::counter) counter []))))
      (5*counter.length+6*record.length+9) := by
  have h:=linkedInTime (0:Fin 22) SemiprimeD1StackHeapAllocate.code (0:Fin 6) 4
    (5*counter.length+6*record.length+7)
    (SemiprimeD1StackHeapAllocate.payload record heap [] counter [] [])
    (SemiprimeD1StackHeapAllocate.payload record (SemiprimeSourceHistogramKeyBits.frame record heap)
      [] (true::counter) counter [])
    (SemiprimeD1StackHeapAllocate.allocate_run record heap counter none)
  exact h

/-- Concrete linked allocator source prefixes include every Boolean and return-frame cell. -/
theorem allocator_prefix_cells (record heap counter:List Bool) (fuel:ℕ)
    (out:C.State (Fin 6) (Fin 22⊕Bool))
    (hr:C.run (code (0:Fin 22) SemiprimeD1StackHeapAllocate.code) fuel
      (initial (SemiprimeD1StackHeapAllocate.payload record heap [] counter [] []))=some out) :
    (out.data 0).length+(out.data 1).length+(out.data 2).length+
      (out.data 3).length+(out.data 4).length+(out.data 5).length+out.frames.length ≤
      7*(record.length+heap.length+counter.length+fuel) := by
  have h:=run_data_bound (code (0:Fin 22) SemiprimeD1StackHeapAllocate.code) fuel
    (record.length+heap.length+counter.length) _ out (by
      intro k
      fin_cases k <;> simp [initial,SemiprimeD1StackHeapAllocate.payload] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound _ fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have h0:=h 0
  have h1:=h 1
  have h2:=h 2
  have h3:=h 3
  have h4:=h 4
  have h5:=h 5
  omega
/-- The complete linked allocator has a proved bound at every actual target-machine prefix. -/
theorem allocator_machine_prefix_cells (record heap counter:List Bool) (fuel:ℕ)
    (cfg:allocatorMachine.Cfg)
    (hr:(fun cfg=>cfg.bind allocatorMachine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (L:=Fin 22) (SemiprimeD1StackHeapAllocate.payload record heap [] counter [] []))))=some cfg) :
    (cfg.stk (some (0:Fin 6))).length+(cfg.stk (some (1:Fin 6))).length+
      (cfg.stk (some (2:Fin 6))).length+(cfg.stk (some (3:Fin 6))).length+
      (cfg.stk (some (4:Fin 6))).length+(cfg.stk (some (5:Fin 6))).length+(cfg.stk none).length ≤
      7*(record.length+heap.length+counter.length+fuel) := by
  let start:C.State (Fin 6) (Fin 22⊕Bool):=
    initial (SemiprimeD1StackHeapAllocate.payload record heap [] counter [] [])
  let program:=code (0:Fin 22) SemiprimeD1StackHeapAllocate.code
  have he:=SemiprimeD1StackCalls.run_correct (0:Fin 6) 4 (.inr false) program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun cfg=>cfg.bind allocatorMachine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run program fuel start with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    exact allocator_prefix_cells record heap counter fuel out hc
end RiemannGaussian.SemiprimeD1StackReturnLink
