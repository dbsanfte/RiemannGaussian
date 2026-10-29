/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControlPaths
import RiemannGaussian.SemiprimeD1TensorTapeVectorMachine

/-! # Literal assignment-enumeration body
The body physically copies one complete framed assignment to the reverse log
and restores the assignment. It is a fixed included procedure, not a body evaluator.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackAssignmentBody
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeSourceHistogramKeyBits (frame)

/-- Assignment, restoration scratch and chronological reverse log. -/
inductive Stack | word | scratch | history deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.word,.scratch,.history}
  complete := by intro k; cases k <;> simp
/-- Fixed physical copy phases. -/
inductive PC | start | drain | restore deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.start,.drain,.restore}
  complete := by intro k; cases k <;> simp
/-- Every data symbol is Boolean. -/
abbrev Alphabet (_ : Stack) := Bool

/-- Literal fixed body instructions, including all framing and restoration. -/
def program : PC → Stmt Alphabet PC (Option Bool)
  | .start => .push .history (fun _ => true) (.goto (fun _ => .drain))
  | .drain => .pop .word (fun _ b => b)
      (.branch Option.isSome
        (.push .scratch (fun b => b.getD false)
          (.push .history (fun _ => true)
            (.push .history (fun b => b.getD false) (.goto (fun _ => .drain)))))
        (.push .history (fun _ => false) (.goto (fun _ => .restore))))
  | .restore => .pop .scratch (fun _ b => b)
      (.branch Option.isSome
        (.push .word (fun b => b.getD false) (.goto (fun _ => .restore))) .halt)

/-- Literal physical stack bank. -/
def contents (word scratch history : List Bool) : (k : Stack) → List (Alphabet k)
  | .word => word
  | .scratch => scratch
  | .history => history

/-- Concrete source configuration. -/
def cfg (pc : Option PC) (flag : Option Bool) (word scratch history : List Bool) :
    Cfg Alphabet PC (Option Bool) := ⟨pc,flag,contents word scratch history⟩

/-- Exact actual source transitions. -/
inductive Executes : ℕ → Cfg Alphabet PC (Option Bool) → Cfg Alphabet PC (Option Bool) → Prop
  | refl (c) : Executes 0 c c
  | next {n c d e} : TM2.step program c=some d → Executes n d e → Executes (n+1) c e

/-- Literal one-stack update. -/
@[simp] theorem update_contents (word scratch history xs : List Bool) (k : Stack) :
    Function.update (contents word scratch history) k xs=
      contents (if k=.word then xs else word) (if k=.scratch then xs else scratch)
        (if k=.history then xs else history) := by
  funext j
  cases k <;> cases j <;> simp [contents]

/-- Concatenation of actual paths. -/
theorem Executes.trans {n m : ℕ} {a b c : Cfg Alphabet PC (Option Bool)}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- Actual iterate equation for the literal body. -/
theorem Executes.iterates {n : ℕ} {a b : Cfg Alphabet PC (Option Bool)} (h : Executes n a b) :
    ((fun x : Option (Cfg Alphabet PC (Option Bool)) => x.bind (TM2.step program))^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- Drain every assignment bit and write its actual reverse framed bytes. -/
theorem drain_exec (flag : Option Bool) (word scratch history : List Bool) :
    Executes (word.length+1) (cfg (some .drain) flag word scratch history)
      (cfg (some .restore) none [] (word.reverse++scratch) ((frame word []).reverse++history)) := by
  induction word generalizing flag scratch history with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [program,cfg,contents,frame,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .drain) flag (b::bs) scratch history)=
        some (cfg (some .drain) (some b) bs (b::scratch) (b::true::history)) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [frame,List.reverse_cons,List.append_assoc] using
      Executes.next hs (ih (some b) (b::scratch) (b::true::history))

/-- Restore the original assignment physically and consume every scratch cell. -/
theorem restore_exec (flag : Option Bool) (word scratch history : List Bool) :
    Executes (scratch.length+1) (cfg (some .restore) flag word scratch history)
      (cfg none none (scratch.reverse++word) [] history) := by
  induction scratch generalizing flag word with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .restore) flag word (b::bs) history)=
        some (cfg (some .restore) (some b) (b::word) bs history) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs (ih (some b) (b::word))

/-- Full actual body call logs exactly one vector entry while preserving its argument. -/
theorem body_exec (word history : List Bool) :
    Executes (2*word.length+3) (cfg (some .start) none word [] history)
      (cfg none none word [] ((true::frame word []).reverse++history)) := by
  have hs : TM2.step program (cfg (some .start) none word [] history)=
      some (cfg (some .drain) none word [] (true::history)) := by
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  have hd := drain_exec none word [] (true::history)
  have hr := restore_exec none [] (word.reverse++[]) ((frame word []).reverse++true::history)
  have h := Executes.next hs (hd.trans hr)
  simp only [List.append_nil,List.length_reverse,List.reverse_reverse] at h
  convert h using 1 <;> simp [List.reverse_cons,List.append_assoc]
  all_goals omega

/-- Actual fixed bytecode label bank, with all finite register states specialized. -/
abbrev Label := SemiprimeD1StackFiniteControl.Label program
/-- Computable literal body instruction table. -/
def code := SemiprimeD1StackFiniteControl.code program
/-- Fixed entry into this actual included body. -/
def entry : Label := SemiprimeD1StackFiniteControl.entry program .start none

/-- Actual source syntactic cost is at most six elementary instructions. -/
theorem program_depth (pc : PC) : SemiprimeD1StackFiniteControl.depth (program pc)≤6 := by
  cases pc <;> decide

/-- Exact generated body execution; no body result/count/clock is supplied. -/
theorem body_run (word history : List Bool) :
    ∃m≤6*(2*word.length+3),SemiprimeD1StackBytecode.run code m
      ⟨some entry,none,contents word [] history⟩=
      some ⟨none,none,contents word [] ((true::frame word []).reverse++history)⟩ :=
  SemiprimeD1StackFiniteControlPaths.halted_run program 6 program_depth .start none none
    _ _ (2*word.length+3) (body_exec word history).iterates

end RiemannGaussian.SemiprimeD1StackAssignmentBody
