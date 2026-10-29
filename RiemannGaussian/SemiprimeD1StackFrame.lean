/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeSourceHistogramKeyBits

/-! # Fixed finite Boolean-stack record framing
The input is moved through a real scratch stack, restored, and framed onto the
output by literal pop/push instructions, including continuation tags and delimiter. All labels and stacks are fixed before
input. Native lengths occur in the proof of time, never in machine control.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFrame
open SemiprimeD1StackBytecode
open SemiprimeD1StackCopy (run_add)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Fixed eleven-label program, with input zero, output one, and scratch two. -/
def code (label:Fin 11) : Instruction (Fin 3) (Fin 11) :=
  if label=0 then .pop 0 3 1 2
  else if label=1 then .push 2 false 0
  else if label=2 then .push 2 true 0
  else if label=3 then .push 1 false 4
  else if label=4 then .pop 2 10 5 6
  else if label=5 then .push 0 false 7
  else if label=6 then .push 0 true 8
  else if label=7 then .push 1 false 9
  else if label=8 then .push 1 true 9
  else if label=9 then .push 1 true 4
  else .halt

/-- Three actual Boolean payloads; no native list is stored in finite control. -/
def payload (input output scratch:List Bool) : Fin 3→List Bool :=
  fun k=>if k=0 then input else if k=1 then output else scratch

/-- Concrete state at a fixed program label. -/
def state (label:Fin 11) (flag:Option Bool) (input output scratch:List Bool) :
    State (Fin 3) (Fin 11) := ⟨some label,flag,payload input output scratch⟩

/-- Concrete halted state with an empty scratch stack. -/
def done (input output:List Bool) : State (Fin 3) (Fin 11) :=
  ⟨none,none,payload input output []⟩

/-- Two executed instructions move one input bit onto scratch. -/
theorem move_bit (b:Bool) (xs ys zs:List Bool) (flag:Option Bool) :
    run code 2 (state 0 flag (b::xs) ys zs)=
      some (state 0 (some b) xs ys (b::zs)) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- Four executed instructions restore one scratch bit and frame it onto output. -/
theorem frame_bit (b:Bool) (xs ys zs:List Bool) (flag:Option Bool) :
    run code 4 (state 4 flag xs ys (b::zs))=
      some (state 4 (some b) (b::xs) (true::b::ys) zs) := by
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

/-- The second loop prepends framed bits to an already acquired tail. -/
theorem frame_run (zs xs ys:List Bool) (flag:Option Bool) :
    run code (4*zs.length+2) (state 4 flag xs ys zs)=
      some (done (zs.reverse++xs) (zs.reverse.foldr (fun b rest=>true::b::rest) ys)) := by
  induction zs generalizing xs ys flag with
  | nil => simp [run,Function.iterate_succ_apply,step,execute,code,state,done,payload,choose,Function.update]
  | cons b zs ih =>
    rw [show 4*(b::zs).length+2=4+(4*zs.length+2) by simp; omega,run_add,frame_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append,List.foldr_append,List.foldr_cons,List.foldr_nil]

/-- Framing uses one false delimiter after the last data bit. -/
theorem frame_fold (xs ys:List Bool) :
    xs.foldr (fun b rest=>true::b::rest) (false::ys)=frame xs ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [List.foldr_cons,frame] using congrArg (fun rest=>true::b::rest) ih

/-- Actual framed record acquisition preserves input and empties scratch. -/
theorem frame_words (xs ys:List Bool) (flag:Option Bool) :
    run code (6*xs.length+4) (state 0 flag xs ys [])=some (done xs (frame xs ys)) := by
  rw [show 6*xs.length+4=(2*xs.length+1)+(1+(4*xs.reverse.length+2)) by simp; omega,run_add,move_run]
  simp only [List.append_nil,Option.bind_some]
  rw [run_add]
  have hs:run code 1 (state 3 none [] ys xs.reverse)=some (state 4 none [] (false::ys) xs.reverse):=by
    simp [run,step,execute,code,state,payload]
    funext k
    fin_cases k <;> rfl
  rw [hs,Option.bind_some,frame_run,List.reverse_reverse,List.append_nil,frame_fold]

/-- A single fixed finite framing machine, before all inputs. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine 0 1 0 code

/-- Genuine finite-machine record construction, with all pushes and delimiter paid. -/
def frameInTime (xs ys:List Bool) (flag:Option Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (state 0 flag xs ys []))
      (some (configuration (done xs (frame xs ys)))) (6*xs.length+4) := by
  apply evalsCorrect 0 1 0 code
  exact ⟨⟨6*xs.length+4,frame_words xs ys flag⟩,le_refl _⟩
/-- Every reached framing prefix has bounded actual payload on each stack. -/
theorem frame_prefix_bound (xs ys:List Bool) (flag:Option Bool) (fuel:ℕ)
    (out:State (Fin 3) (Fin 11)) (hr:run code fuel (state 0 flag xs ys [])=some out) :
    ∀k,(out.store k).length ≤ xs.length+ys.length+fuel := by
  apply SemiprimeD1StackCopy.run_bound code fuel (xs.length+ys.length) _ out ?_ hr
  intro k
  fin_cases k <;> simp [state,payload]

/-- Actual finite-machine framing prefixes have only linear total stack payload. -/
theorem machine_prefix_cells (xs ys:List Bool) (flag:Option Bool) (fuel:ℕ)
    (cfg:Turing.TM2.Cfg (fun _:Fin 3=>Bool) (Fin 11) (Option Bool))
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
    have h:=frame_prefix_bound xs ys flag fuel out hc
    have h0:=h 0
    have h1:=h 1
    have h2:=h 2
    change (out.store 0).length+(out.store 1).length+(out.store 2).length ≤ _
    omega
end RiemannGaussian.SemiprimeD1StackFrame
