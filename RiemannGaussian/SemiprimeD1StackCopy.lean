/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBytecode

/-! # Fixed finite Boolean-stack copying
The input is moved through a real scratch stack, restored, and copied to the
output by literal pop/push instructions. All labels and stacks are fixed before
input. Native lengths occur in the proof of time, never in machine control.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCopy
open SemiprimeD1StackBytecode

/-- Fixed nine-label program, with input zero, output one, and scratch two. -/
def code (label:Fin 9) : Instruction (Fin 3) (Fin 9) :=
  if label=0 then .pop 0 3 1 2
  else if label=1 then .push 2 false 0
  else if label=2 then .push 2 true 0
  else if label=3 then .pop 2 6 4 5
  else if label=4 then .push 0 false 7
  else if label=5 then .push 0 true 8
  else if label=7 then .push 1 false 3
  else if label=8 then .push 1 true 3
  else .halt

/-- Three actual Boolean payloads; no native list is stored in finite control. -/
def payload (input output scratch:List Bool) : Fin 3→List Bool :=
  fun k=>if k=0 then input else if k=1 then output else scratch

/-- Concrete state at a fixed program label. -/
def state (label:Fin 9) (flag:Option Bool) (input output scratch:List Bool) :
    State (Fin 3) (Fin 9) := ⟨some label,flag,payload input output scratch⟩

/-- Concrete halted state with an empty scratch stack. -/
def done (input output:List Bool) : State (Fin 3) (Fin 9) :=
  ⟨none,none,payload input output []⟩

/-- Actual sequential composition of source transitions. -/
theorem run_add {K L:Type} [DecidableEq K] (program:L→Instruction K L)
    (m n:ℕ) (s:State K L) :
    run program (m+n) s=(run program m s).bind (run program n) := by
  unfold run
  rw [Nat.add_comm m n,Function.iterate_add_apply]
  generalize (fun state=>state.bind (step program))^[m] (some s)=o
  cases o with
  | some s => rfl
  | none => exact Function.iterate_fixed rfl n

/-- Two executed instructions move one input bit onto scratch. -/
theorem move_bit (b:Bool) (xs ys zs:List Bool) (flag:Option Bool) :
    run code 2 (state 0 flag (b::xs) ys zs)=
      some (state 0 (some b) xs ys (b::zs)) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- Three executed instructions restore one scratch bit and copy it to output. -/
theorem copy_bit (b:Bool) (xs ys zs:List Bool) (flag:Option Bool) :
    run code 3 (state 3 flag xs ys (b::zs))=
      some (state 3 (some b) (b::xs) (b::ys) zs) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- Actual first loop, including its empty-input branch, reverses into scratch. -/
theorem move_run (xs ys zs:List Bool) (flag:Option Bool) :
    run code (2*xs.length+1) (state 0 flag xs ys zs)=
      some (state 3 none [] ys (xs.reverse++zs)) := by
  induction xs generalizing zs flag with
  | nil => simp [run,step,execute,code,state,payload,choose]
  | cons b xs ih =>
    rw [show 2*(b::xs).length+1=2+(2*xs.length+1) by simp; omega,run_add,move_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Actual second loop restores/copies the whole scratch word and halts cleanly. -/
theorem copy_run (zs xs ys:List Bool) (flag:Option Bool) :
    run code (3*zs.length+2) (state 3 flag xs ys zs)=
      some (done (zs.reverse++xs) (zs.reverse++ys)) := by
  induction zs generalizing xs ys flag with
  | nil => simp [run,Function.iterate_succ_apply,step,execute,code,state,done,payload,
      choose]
  | cons b zs ih =>
    rw [show 3*(b::zs).length+2=3+(3*zs.length+2) by simp; omega,run_add,copy_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Complete acquired copy: input restored, output prepended, scratch empty. -/
theorem copy_words (xs ys:List Bool) (flag:Option Bool) :
    run code (5*xs.length+3) (state 0 flag xs ys [])=some (done xs (xs++ys)) := by
  rw [show 5*xs.length+3=(2*xs.length+1)+(3*xs.reverse.length+2) by simp; omega,run_add,move_run]
  simp only [List.append_nil,Option.bind_some]
  rw [copy_run,List.reverse_reverse,List.append_nil]

/-- One fixed genuine finite machine, independent of all input payloads. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine 0 1 0 code

/-- Actual finite-machine copying certificate, including both real loops. -/
def copyInTime (xs ys:List Bool) (flag:Option Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (state 0 flag xs ys []))
      (some (configuration (done xs (xs++ys)))) (5*xs.length+3) := by
  apply evalsCorrect 0 1 0 code
  exact ⟨⟨5*xs.length+3,copy_words xs ys flag⟩,le_refl _⟩
/-- Every literal instruction increases any stack length by at most one. -/
theorem execute_bound {K L:Type} [DecidableEq K] (instruction:Instruction K L)
    (s:State K L) (C:ℕ) (h:∀k,(s.store k).length ≤ C) :
    ∀k,((execute instruction s).store k).length ≤ C+1 := by
  cases instruction with
  | push target bit next =>
    intro k
    by_cases hk:k=target
    · subst k; simpa [execute] using Nat.succ_le_succ (h target)
    · simpa [execute,Function.update,hk] using (h k).trans (Nat.le_succ C)
  | pop target empty low high =>
    intro k
    by_cases hk:k=target
    · subst k
      simpa [execute] using (by simp only [List.length_tail]; exact Nat.sub_le _ _: (s.store target).tail.length ≤ (s.store target).length).trans ((h target).trans (Nat.le_succ C))
    · simpa [execute,Function.update,hk] using (h k).trans (Nat.le_succ C)
  | peek target empty low high => exact fun k=>(h k).trans (Nat.le_succ C)
  | jump next => exact fun k=>(h k).trans (Nat.le_succ C)
  | halt => exact fun k=>(h k).trans (Nat.le_succ C)

/-- Every actual reached prefix has bounded payload on every stack. -/
theorem run_bound {K L:Type} [DecidableEq K] (program:L→Instruction K L)
    (fuel C:ℕ) (s out:State K L) (h:∀k,(s.store k).length ≤ C)
    (hr:run program fuel s=some out) : ∀k,(out.store k).length ≤ C+fuel := by
  induction fuel generalizing s out C with
  | zero => change some s=some out at hr;cases hr;exact h
  | succ fuel ih =>
    rw [show fuel+1=1+fuel by omega,run_add] at hr
    change (step program s).bind (run program fuel)=some out at hr
    cases hp:s.pc with
    | none => simp [step,hp] at hr
    | some label =>
      have he:step program s=some (execute (program label) s):=by simp [step,hp]
      rw [he,Option.bind_some] at hr
      have hb:=ih (C+1) (execute (program label) s) out (execute_bound _ _ _ h) hr
      simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using hb

/-- Actual copy prefixes have a linear bound on all three physical stack payloads. -/
theorem copy_prefix_bound (xs ys:List Bool) (flag:Option Bool) (fuel:ℕ)
    (out:State (Fin 3) (Fin 9)) (hr:run code fuel (state 0 flag xs ys [])=some out) :
    ∀k,(out.store k).length ≤ xs.length+ys.length+fuel := by
  apply run_bound code fuel (xs.length+ys.length) _ out ?_ hr
  intro k
  fin_cases k <;> simp [state,payload]
/-- Total actual copy-stack cells at every reached source prefix. -/
theorem copy_prefix_cells (xs ys:List Bool) (flag:Option Bool) (fuel:ℕ)
    (out:State (Fin 3) (Fin 9)) (hr:run code fuel (state 0 flag xs ys [])=some out) :
    (out.store 0).length+(out.store 1).length+(out.store 2).length ≤
      3*(xs.length+ys.length+fuel) := by
  have h:=copy_prefix_bound xs ys flag fuel out hr
  have h0:=h 0
  have h1:=h 1
  have h2:=h 2
  omega

/-- The reached-cell bound applies to actual finite-machine prefixes, not only source runs. -/
theorem machine_prefix_cells (xs ys:List Bool) (flag:Option Bool) (fuel:ℕ)
    (cfg:Turing.TM2.Cfg (fun _:Fin 3=>Bool) (Fin 9) (Option Bool))
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (configuration (state 0 flag xs ys [])))=some cfg) :
    (cfg.stk 0).length+(cfg.stk 1).length+(cfg.stk 2).length ≤
      3*(xs.length+ys.length+fuel) := by
  have he:=run_correct 0 1 0 code fuel (state 0 flag xs ys [])
  change (run code fuel (state 0 flag xs ys [])).map configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (configuration (state 0 flag xs ys []))) at he
  cases hc:run code fuel (state 0 flag xs ys []) with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    exact copy_prefix_cells xs ys flag fuel out hc
end RiemannGaussian.SemiprimeD1StackCopy
