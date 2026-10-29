/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeVectorMachine
import RiemannGaussian.SemiprimeD1TensorTapeLookup

/-! # Fixed Boolean-stack tree lookup
The task stack stores seek/skip bits. Forks push exactly two tasks. Every skipped
subtree is scanned physically; only the selected literal vector is copied.
All lengths and tree depths below are proof indices, not control registers.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeTreeMachine
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Fixed physical Boolean stacks. -/
inductive Stack | input | tasks | path | scratch | output deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.input,.tasks,.path,.scratch,.output}
  complete := by intro x; cases x <;> simp

/-- Eight finite labels for all tree depths. -/
inductive PC | start | task | node | marker | tag | data | resume | reverse
  deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.start,.task,.node,.marker,.tag,.data,.resume,.reverse}
  complete := by intro x; cases x <;> simp

/-- Popped bit and seek flag are the only finite registers. -/
abbrev Registers := Option Bool×Bool
/-- Every stack has a two-symbol alphabet. -/
abbrev Alphabet (_ : Stack) := Bool
/-- Conditional single-byte copy, preserving the seek flag. -/
def copyThen (next : Registers → PC) : Stmt Alphabet PC Registers :=
  .branch (fun v => v.2)
    (.push .scratch (fun v => v.1.getD false) (.goto next)) (.goto next)

/-- Add two physical subtree tasks and reset only finite flags. -/
def forkTasks (lo hi : Registers → Bool) : Stmt Alphabet PC Registers :=
  .push .tasks hi (.push .tasks lo
    (.load (fun _ => (none,false)) (.goto (fun _ => .task))))

/-- Actual fixed instruction table, with no tree/word/Nat oracle operation. -/
def program : PC → Stmt Alphabet PC Registers
  | .start => .push .tasks (fun _ => true) (.goto (fun _ => .task))
  | .task => .pop .tasks (fun _ b => (b,b.getD false))
      (.branch (fun v => v.1.isSome) (.goto (fun _ => .node)) (.goto (fun _ => .reverse)))
  | .node => .pop .input (fun v b => (b,v.2))
      (.branch (fun v => v.1==some true)
        (.branch (fun v => v.2)
          (.pop .path (fun v b => (b,v.2))
            (forkTasks (fun v => !(v.1.getD false)) (fun v => v.1.getD false)))
          (forkTasks (fun _ => false) (fun _ => false)))
        (.goto (fun _ => .marker)))
  | .marker => .pop .input (fun v b => (b,v.2))
      (copyThen (fun v => if v.1==some true then .tag else .resume))
  | .tag => .pop .input (fun v b => (b,v.2))
      (copyThen (fun v => if v.1==some true then .data else .marker))
  | .data => .pop .input (fun v b => (b,v.2)) (copyThen (fun _ => .tag))
  | .resume => .load (fun _ => (none,false)) (.goto (fun _ => .task))
  | .reverse => .pop .scratch (fun v b => (b,v.2))
      (.branch (fun v => v.1.isSome)
        (.push .output (fun v => v.1.getD false) (.goto (fun _ => .reverse))) .halt)

/-- The genuine finite-alphabet machine. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := PC
  main := .start
  σ := Registers
  initialState := (none,false)
  m := program

/-- Explicit literal stack contents. -/
def contents (input tasks path scratch output : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .tasks => tasks
  | .path => path
  | .scratch => scratch
  | .output => output

/-- Concrete fixed-control configurations. -/
def cfg (pc : Option PC) (v : Registers) (input tasks path scratch output : List Bool) :
    TM2.Cfg Alphabet PC Registers := ⟨pc,v,contents input tasks path scratch output⟩

/-- Actual primitive transition. -/
def step := TM2.step program

/-- Updating a stack changes exactly its literal data. -/
@[simp] theorem update_contents (input tasks path scratch output xs : List Bool) (k : Stack) :
    Function.update (contents input tasks path scratch output) k xs =
      contents (if k = .input then xs else input) (if k = .tasks then xs else tasks)
        (if k = .path then xs else path) (if k = .scratch then xs else scratch)
        (if k = .output then xs else output) := by
  funext j
  cases k <;> cases j <;> simp [contents]

/-- Exact paths, indexed only in the proof. -/
inductive Executes : ℕ → TM2.Cfg Alphabet PC Registers → TM2.Cfg Alphabet PC Registers → Prop
  | refl (c) : Executes 0 c c
  | next {n c d e} : step c=some d → Executes n d e → Executes (n+1) c e

/-- Concatenate actual transition sequences. -/
theorem Executes.trans {n m : ℕ} {a b c : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- Exact paths refine Mathlib's actual iterate semantics. -/
theorem Executes.iterates {n : ℕ} {a b : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) :
    ((fun x : Option (TM2.Cfg Alphabet PC Registers) => x.bind step)^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- A literal transition-time certificate. -/
def Executes.inTime {n : ℕ} {a b : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) : StateTransition.EvalsToInTime step a (some b) n :=
  ⟨⟨n,h.iterates⟩,le_rfl⟩

/-- Physically reverse the selected vector, leaving all other stacks intact. -/
theorem reverse_exec (v : Registers) (xs tasks path rev out : List Bool) :
    Executes (rev.length+1) (cfg (some .reverse) v xs tasks path rev out)
      (cfg none (none,v.2) xs tasks path [] (rev.reverse++out)) := by
  induction rev generalizing v out with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1TensorTapeTreeMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have ht := ih (some b,v.2) (b::out)
    have hs : step (cfg (some .reverse) v xs tasks path (b::bs) out)=
        some (cfg (some .reverse) (some b,v.2) xs tasks path bs (b::out)) := by
      simp [SemiprimeD1TensorTapeTreeMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs ht

/-- Raw field scan, with no nested-word control payload. -/
theorem field_exec (w tail tasks path rev out : List Bool) (mode : Bool) (last : Option Bool) :
    Executes (2*w.length+1)
      (cfg (some .tag) (last,mode) (frame w tail) tasks path rev out)
      (cfg (some .marker) (some false,mode) tail tasks path
        (if mode then (frame w []).reverse++rev else rev) out) := by
  induction w generalizing rev last with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    cases mode <;> simp [SemiprimeD1TensorTapeTreeMachine.step,program,copyThen,
      cfg,contents,frame,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have htag : step (cfg (some .tag) (last,mode) (frame (b::bs) tail) tasks path rev out)=
        some (cfg (some .data) (some true,mode) (b::frame bs tail) tasks path
          (if mode then true::rev else rev) out) := by
      cases mode <;> simp [SemiprimeD1TensorTapeTreeMachine.step,program,copyThen,
        cfg,contents,frame,TM2.step,TM2.stepAux]
    have hdata : step (cfg (some .data) (some true,mode) (b::frame bs tail) tasks path
        (if mode then true::rev else rev) out)=
        some (cfg (some .tag) (some b,mode) (frame bs tail) tasks path
          (if mode then b::true::rev else rev) out) := by
      cases mode <;> simp [SemiprimeD1TensorTapeTreeMachine.step,program,copyThen,
        cfg,contents,TM2.step,TM2.stepAux]
    have ht := Executes.next htag (Executes.next hdata (ih _ (some b)))
    convert ht using 1
    cases mode <;> simp [frame,List.reverse_cons,List.append_assoc]

/-- Raw vector scan; all unselected bytes are physically consumed. -/
theorem vector_scan (ws : List (List Bool)) (tail tasks path rev out : List Bool)
    (mode : Bool) (last : Option Bool) :
    Executes (vectorBits ws).length
      (cfg (some .marker) (last,mode) (vectorBits ws++tail) tasks path rev out)
      (cfg (some .resume) (some false,mode) tail tasks path
        (if mode then (vectorBits ws).reverse++rev else rev) out) := by
  induction ws generalizing rev last with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    cases mode <;> simp [SemiprimeD1TensorTapeTreeMachine.step,program,copyThen,
      cfg,contents,vectorBits,TM2.step,TM2.stepAux]
  | cons w ws ih =>
    have hs : step (cfg (some .marker) (last,mode) (vectorBits (w::ws)++tail) tasks path rev out)=
        some (cfg (some .tag) (some true,mode) (frame w (vectorBits ws++tail)) tasks path
          (if mode then true::rev else rev) out) := by
      cases mode <;> simp [SemiprimeD1TensorTapeTreeMachine.step,program,copyThen,
        cfg,contents,vectorBits,SemiprimeD1TensorTapeVectorMachine.frame_append,TM2.step,TM2.stepAux]
    have hf := field_exec w (vectorBits ws++tail) tasks path (if mode then true::rev else rev) out mode (some true)
    have hi := ih (if mode then (frame w []).reverse++(if mode then true::rev else rev)
      else (if mode then true::rev else rev)) (some false)
    have ht := Executes.next hs (hf.trans hi)
    have hframe : frame w (vectorBits ws)=frame w []++vectorBits ws := by
      simpa using SemiprimeD1TensorTapeVectorMachine.frame_append w [] (vectorBits ws)
    convert ht using 1 <;> cases mode <;>
      simp [vectorBits,SemiprimeSourceHistogramKeyBits.frame_length,hframe,
        List.reverse_append,List.reverse_cons,List.append_assoc]

end RiemannGaussian.SemiprimeD1TensorTapeTreeMachine
