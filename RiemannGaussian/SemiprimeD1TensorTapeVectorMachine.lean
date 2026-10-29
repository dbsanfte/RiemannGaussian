/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldMachine

/-! # Physical raw vector-frame scan
A fixed four-label Boolean-stack machine scans every vector tag, field tag and
literal bit. Its finite copy flag selects copying or skipping. Nested words are
never decoded into control registers. This is a subroutine, not a whole-counter
machine refinement.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeVectorMachine
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeD1TensorTapeFieldMachine (Stack Alphabet Registers contents config)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Four fixed labels, independent of vector or word lengths. -/
inductive PC | marker | tag | data | reverse deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.marker,.tag,.data,.reverse}
  complete := by intro x; cases x <;> simp

/-- Finite optional-copy instruction; the flag is preserved. -/
def copyThen (next : Registers → PC) : Stmt Alphabet PC Registers :=
  .branch (fun v => v.2)
    (.push .scratch (fun v => v.1.getD false) (.goto next)) (.goto next)

/-- Literal instruction table; all data remain on Boolean stacks. -/
def program : PC → Stmt Alphabet PC Registers
  | .marker => .pop .input (fun v b => (b,v.2))
      (copyThen (fun v => if v.1==some true then .tag else .reverse))
  | .tag => .pop .input (fun v b => (b,v.2))
      (copyThen (fun v => if v.1==some true then .data else .marker))
  | .data => .pop .input (fun v b => (b,v.2)) (copyThen (fun _ => .tag))
  | .reverse => .pop .scratch (fun v b => (b,v.2))
      (.branch (fun v => v.1.isSome)
        (.push .output (fun v => v.1.getD false) (.goto (fun _ => .reverse))) .halt)

/-- Actual finite-alphabet TM2, with only six finite register settings. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := PC
  main := .marker
  σ := Registers
  initialState := (none,true)
  m := program

/-- Literal configurations for this fixed program. -/
def cfg (pc : Option PC) (v : Registers) (input scratch output : List Bool) :
    TM2.Cfg Alphabet PC Registers := ⟨pc,v,contents input scratch output⟩

/-- Its actual Mathlib primitive-step semantics. -/
def step := TM2.step program

/-- Exact finite paths; the length is proof data, never a machine register. -/
inductive Executes : ℕ → TM2.Cfg Alphabet PC Registers → TM2.Cfg Alphabet PC Registers → Prop
  | refl (c) : Executes 0 c c
  | next {n c d e} : step c=some d → Executes n d e → Executes (n+1) c e

/-- Concatenate literal machine executions. -/
theorem Executes.trans {n m : ℕ} {a b c : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- Exact paths give the actual iterated transition equation. -/
theorem Executes.iterates {n : ℕ} {a b : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) :
    ((fun x : Option (TM2.Cfg Alphabet PC Registers) => x.bind step)^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- Genuine transition-time certificate, rather than an annotated work field. -/
def Executes.inTime {n : ℕ} {a b : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) : StateTransition.EvalsToInTime step a (some b) n :=
  ⟨⟨n,h.iterates⟩,le_rfl⟩

/-- Reverse copying physically pops and pushes every selected byte. -/
theorem reverse_exec (v : Registers) (xs rev out : List Bool) :
    Executes (rev.length+1) (cfg (some .reverse) v xs rev out)
      (cfg none (none,v.2) xs [] (rev.reverse++out)) := by
  induction rev generalizing v out with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1TensorTapeVectorMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have ht := ih (some b,v.2) (b::out)
    have hs : step (cfg (some .reverse) v xs (b::bs) out)=
        some (cfg (some .reverse) (some b,v.2) xs bs (b::out)) := by
      simp [SemiprimeD1TensorTapeVectorMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs ht

/-- Scan a whole framed field, retaining the exact reverse raw bytes if enabled. -/
theorem field_exec (w tail rev out : List Bool) (mode : Bool) (last : Option Bool) :
    Executes (2*w.length+1)
      (cfg (some .tag) (last,mode) (frame w tail) rev out)
      (cfg (some .marker) (some false,mode) tail
        (if mode then (frame w []).reverse++rev else rev) out) := by
  induction w generalizing rev last with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    cases mode <;> simp [SemiprimeD1TensorTapeVectorMachine.step,program,copyThen,
      cfg,contents,frame,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have htag : step (cfg (some .tag) (last,mode) (frame (b::bs) tail) rev out)=
        some (cfg (some .data) (some true,mode) (b::frame bs tail)
          (if mode then true::rev else rev) out) := by
      cases mode <;> simp [SemiprimeD1TensorTapeVectorMachine.step,program,copyThen,
        cfg,contents,frame,TM2.step,TM2.stepAux]
    have hdata : step (cfg (some .data) (some true,mode) (b::frame bs tail)
        (if mode then true::rev else rev) out)=
        some (cfg (some .tag) (some b,mode) (frame bs tail)
          (if mode then b::true::rev else rev) out) := by
      cases mode <;> simp [SemiprimeD1TensorTapeVectorMachine.step,program,copyThen,
        cfg,contents,TM2.step,TM2.stepAux]
    have ht := Executes.next htag (Executes.next hdata (ih _ (some b)))
    convert ht using 1
    cases mode <;> simp [frame,List.reverse_cons,List.append_assoc]

/-- Framing preserves the literal unconsumed suffix. -/
theorem frame_append (w xs ys : List Bool) : frame w (xs++ys)=frame w xs++ys := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp only [frame,ih,List.cons_append]

/-- Scan all vector bytes, keeping only raw framed bytes on the copy stack. -/
theorem vector_scan (ws : List (List Bool)) (tail rev out : List Bool)
    (mode : Bool) (last : Option Bool) :
    Executes (vectorBits ws).length
      (cfg (some .marker) (last,mode) (vectorBits ws++tail) rev out)
      (cfg (some .reverse) (some false,mode) tail
        (if mode then (vectorBits ws).reverse++rev else rev) out) := by
  induction ws generalizing rev last with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    cases mode <;> simp [SemiprimeD1TensorTapeVectorMachine.step,program,copyThen,
      cfg,contents,vectorBits,TM2.step,TM2.stepAux]
  | cons w ws ih =>
    have hs : step (cfg (some .marker) (last,mode) (vectorBits (w::ws)++tail) rev out)=
        some (cfg (some .tag) (some true,mode) (frame w (vectorBits ws++tail))
          (if mode then true::rev else rev) out) := by
      cases mode <;> simp [SemiprimeD1TensorTapeVectorMachine.step,program,copyThen,
        cfg,contents,vectorBits,frame_append,TM2.step,TM2.stepAux]
    have hf := field_exec w (vectorBits ws++tail) (if mode then true::rev else rev) out mode (some true)
    have hi := ih (if mode then (frame w []).reverse++(if mode then true::rev else rev)
      else (if mode then true::rev else rev)) (some false)
    have ht := Executes.next hs (hf.trans hi)
    have hframe : frame w (vectorBits ws)=frame w []++vectorBits ws := by
      simpa using frame_append w [] (vectorBits ws)
    convert ht using 1 <;> cases mode <;>
      simp [vectorBits,SemiprimeSourceHistogramKeyBits.frame_length,hframe,
        List.reverse_append,List.reverse_cons,List.append_assoc]

/-- Copy or skip the entire actual vector; the input suffix is exact. -/
theorem vector_exec (ws : List (List Bool)) (tail out : List Bool) (mode : Bool) :
    Executes ((vectorBits ws).length+(if mode then (vectorBits ws).length else 0)+1)
      (cfg (some .marker) (none,mode) (vectorBits ws++tail) [] out)
      (cfg none (none,mode) tail [] (if mode then vectorBits ws++out else out)) := by
  have h := (vector_scan ws tail [] out mode none).trans
    (reverse_exec (some false,mode) tail (if mode then (vectorBits ws).reverse++[] else []) out)
  cases mode <;> simpa [List.reverse_reverse,Nat.add_assoc] using h

/-- Actual primitive transition bound for copying a well-formed vector frame. -/
def copyInTime (ws : List (List Bool)) (tail : List Bool) :
    StateTransition.EvalsToInTime step
      (cfg (some .marker) (none,true) (vectorBits ws++tail) [] [])
      (some (cfg none (none,true) tail [] (vectorBits ws))) (2*(vectorBits ws).length+1) := by
  have h := vector_exec ws tail [] true
  simpa [two_mul] using h.inTime

/-- Actual primitive transition bound for physically skipping every vector byte. -/
def skipInTime (ws : List (List Bool)) (tail : List Bool) :
    StateTransition.EvalsToInTime step
      (cfg (some .marker) (none,false) (vectorBits ws++tail) [] [])
      (some (cfg none (none,false) tail [] [])) ((vectorBits ws).length+1) := by
  simpa using (vector_exec ws tail [] false).inTime

end RiemannGaussian.SemiprimeD1TensorTapeVectorMachine
