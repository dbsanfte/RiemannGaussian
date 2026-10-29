/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBytecode

/-! # Computable finite-register elimination
A source statement's finite register is specialized into fixed code labels.
Every unbounded source stack stays a Boolean stack. Syntactic locations are
finite recursive sum types, not native numeric addresses or data registers.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackFiniteControl
open Turing Turing.TM2
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run choose)
end B

/-- Recursive finite instruction locations inside one fixed source statement. -/
def Locations {K L S : Type} : Stmt (fun _ : K => Bool) L S → Type
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => Unit ⊕ Locations q
  | .branch _ q r => Unit ⊕ (Locations q ⊕ Locations r)
  | .goto _ | .halt => Unit

/-- Constructive finite location catalogue, without arbitrary choice. -/
@[instance_reducible] def locationsFintype {K L S : Type} (q : Stmt (fun _ : K => Bool) L S) : Fintype (Locations q) :=
  match q with
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q =>
    letI := locationsFintype q
    inferInstanceAs (Fintype (Unit ⊕ Locations q))
  | .branch _ q r =>
    letI := locationsFintype q
    letI := locationsFintype r
    inferInstanceAs (Fintype (Unit ⊕ (Locations q ⊕ Locations r)))
  | .goto _ | .halt => inferInstanceAs (Fintype Unit)

instance {K L S : Type} (q : Stmt (fun _ : K => Bool) L S) : Fintype (Locations q) :=
  locationsFintype q

/-- Root location of each fixed statement. -/
def root {K L S : Type} : (q : Stmt (fun _ : K => Bool) L S) → Locations q
  | .push _ _ _ | .peek _ _ _ | .pop _ _ _ | .load _ _ | .branch _ _ _ => .inl ()
  | .goto _ | .halt => ()

/-- Compile a statement location; finite computations specialize literal operands. -/
def compileLocal {K L S G : Type} (jump : L → S → G) :
    (q : Stmt (fun _ : K => Bool) L S) → (S → Locations q → G) → S → Locations q → B.Instruction K G
  | .push k f q,enter,v,.inl _ => .push k (f v) (enter v (.inr (root q)))
  | .push _ _ q,enter,v,.inr pos => compileLocal jump q (fun v p => enter v (.inr p)) v pos
  | .peek k f q,enter,v,.inl _ => .peek k
      (enter (f v none) (.inr (root q)))
      (enter (f v (some false)) (.inr (root q)))
      (enter (f v (some true)) (.inr (root q)))
  | .peek _ _ q,enter,v,.inr pos => compileLocal jump q (fun v p => enter v (.inr p)) v pos
  | .pop k f q,enter,v,.inl _ => .pop k
      (enter (f v none) (.inr (root q)))
      (enter (f v (some false)) (.inr (root q)))
      (enter (f v (some true)) (.inr (root q)))
  | .pop _ _ q,enter,v,.inr pos => compileLocal jump q (fun v p => enter v (.inr p)) v pos
  | .load f q,enter,v,.inl _ => .jump (enter (f v) (.inr (root q)))
  | .load _ q,enter,v,.inr pos => compileLocal jump q (fun v p => enter v (.inr p)) v pos
  | .branch f q r,enter,v,.inl _ =>
      .jump (if f v then enter v (.inr (.inl (root q))) else enter v (.inr (.inr (root r))))
  | .branch _ q _,enter,v,.inr (.inl pos) =>
      compileLocal jump q (fun v p => enter v (.inr (.inl p))) v pos
  | .branch _ _ r,enter,v,.inr (.inr pos) =>
      compileLocal jump r (fun v p => enter v (.inr (.inr p))) v pos
  | .goto f,_,v,() => .jump (jump (f v) v)
  | .halt,_,_,() => .halt

/-- Finite compiled labels: original label, finite register setting and syntax node. -/
def Label {K L S : Type} (program : L → Stmt (fun _ : K => Bool) L S) :=
  (l : L) × (S × Locations (program l))

instance {K L S : Type} [Fintype L] [Fintype S]
    (program : L → Stmt (fun _ : K => Bool) L S) : Fintype (Label program) :=
  inferInstanceAs (Fintype ((l : L) × (S × Locations (program l))))

/-- Exact literal label at a statement entry. -/
def entry {K L S : Type} (program : L → Stmt (fun _ : K => Bool) L S)
    (l : L) (v : S) : Label program := ⟨l,v,root (program l)⟩

/-- Actual executable fixed bytecode; no source register remains in target state. -/
def code {K L S : Type} (program : L → Stmt (fun _ : K => Bool) L S) :
    Label program → B.Instruction K (Label program)
  | ⟨l,v,pos⟩ => compileLocal (entry program) (program l) (fun v p => ⟨l,v,p⟩) v pos

/-- Actual compiled finite machine, all stacks still Boolean. -/
def machine {K L S : Type} [DecidableEq K] [Fintype K] [Fintype L] [Fintype S]
    (program : L → Stmt (fun _ : K => Bool) L S) (input output : K) (main : L) (initial : S) :
    Turing.FinTM2 := SemiprimeD1StackBytecode.machine input output (entry program main initial) (code program)

/-- Static elementary instruction depth used to bound lowering overhead. -/
def depth {K L S : Type} : Stmt (fun _ : K => Bool) L S → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => 1+depth q
  | .branch _ q r => 1+max (depth q) (depth r)
  | .goto _ | .halt => 1

end RiemannGaussian.SemiprimeD1StackFiniteControl
