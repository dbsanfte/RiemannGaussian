/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControlPaths

/-! # Physical unary quotient/remainder
The divisor is physically copied/restored for every block. Input and divisor
values are numbers of Boolean counter cells, never native control registers.
An explicit zero-divisor branch produces quotient zero and remainder input.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnaryDivmod
open Turing Turing.TM2 Turing.TM2.Stmt

/-- Six fixed Boolean counter/work/result stacks. -/
inductive Stack | input | divisor | copied | scratch | quotient | remainder
  deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.input,.divisor,.copied,.scratch,.quotient,.remainder}
  complete := by intro k; cases k <;> simp

/-- Fixed finite control phases; no numeric state is present. -/
inductive PC | entry | reload | restore | start | count | complete | clearRemainder | clearCopy | zeroCopy
  deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.entry,.reload,.restore,.start,.count,.complete,.clearRemainder,.clearCopy,.zeroCopy}
  complete := by intro k; cases k <;> simp

/-- Every data symbol is a single Boolean. -/
abbrev Alphabet (_ : Stack) := Bool
/-- Mathematical byte layout of a unary counter; not an executable value oracle. -/
def unary (n : ℕ) : List Bool := List.replicate n true

/-- Actual fixed physical divider, including divisor reloads and all cleanup. -/
def program : PC → Stmt Alphabet PC (Option Bool)
  | .entry => .peek .divisor (fun _ b => b)
      (.branch Option.isNone (.goto (fun _ => .zeroCopy)) (.goto (fun _ => .reload)))
  | .reload => .pop .divisor (fun _ b => b)
      (.branch Option.isSome
        (.push .scratch (fun b => b.getD false)
          (.push .copied (fun _ => true) (.goto (fun _ => .reload))))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ b => b)
      (.branch Option.isSome
        (.push .divisor (fun b => b.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .start)))
  | .start => .pop .input (fun _ b => b)
      (.branch Option.isSome
        (.push .remainder (fun _ => true) (.goto (fun _ => .count)))
        (.goto (fun _ => .clearCopy)))
  | .count => .pop .copied (fun _ b => b)
      (.peek .copied (fun _ b => b)
        (.branch Option.isNone (.goto (fun _ => .complete)) (.goto (fun _ => .start))))
  | .complete => .push .quotient (fun _ => true) (.goto (fun _ => .clearRemainder))
  | .clearRemainder => .pop .remainder (fun _ b => b)
      (.branch Option.isSome (.goto (fun _ => .clearRemainder)) (.goto (fun _ => .reload)))
  | .clearCopy => .pop .copied (fun _ b => b)
      (.branch Option.isSome (.goto (fun _ => .clearCopy)) .halt)
  | .zeroCopy => .pop .input (fun _ b => b)
      (.branch Option.isSome
        (.push .remainder (fun _ => true) (.goto (fun _ => .zeroCopy))) .halt)

/-- Actual literal data-bank representation. -/
def contents (input divisor copied scratch quotient remainder : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .divisor => divisor
  | .copied => copied
  | .scratch => scratch
  | .quotient => quotient
  | .remainder => remainder

/-- Concrete configurations with only finite optional-bit control. -/
def cfg (pc : Option PC) (flag : Option Bool)
    (input divisor copied scratch quotient remainder : List Bool) : Cfg Alphabet PC (Option Bool) :=
  ⟨pc,flag,contents input divisor copied scratch quotient remainder⟩

/-- Every physical data write touches exactly one stack. -/
@[simp] theorem update_contents (input divisor copied scratch quotient remainder xs : List Bool)
    (k : Stack) : Function.update (contents input divisor copied scratch quotient remainder) k xs=
      contents (if k=.input then xs else input) (if k=.divisor then xs else divisor)
        (if k=.copied then xs else copied) (if k=.scratch then xs else scratch)
        (if k=.quotient then xs else quotient) (if k=.remainder then xs else remainder) := by
  funext j
  cases k <;> cases j <;> simp [contents]

/-- Exact primitive source paths, with proof-only step indices. -/
abbrev Executes := SemiprimeD1StackFiniteControlPaths.SourcePath program

/-- Literal executions concatenate with all primitive transitions retained. -/
theorem exec_trans {n m : ℕ} {a b c : Cfg Alphabet PC (Option Bool)}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      SemiprimeD1StackFiniteControlPaths.SourcePath.next hs (ih g)

/-- Exact source paths imply the actual TM2 iterate equation. -/
theorem exec_iterates {n : ℕ} {a b : Cfg Alphabet PC (Option Bool)} (h : Executes n a b) :
    ((fun x : Option (Cfg Alphabet PC (Option Bool)) => x.bind (TM2.step program))^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- Unary framing arithmetic is proof-only literal list concatenation. -/
theorem unary_add (m n : ℕ) : unary (m+n)=unary m++unary n :=
  List.replicate_add m n true

/-- One physical unary token is represented by one true cell. -/
@[simp] theorem unary_succ (n : ℕ) : unary (n+1)=true::unary n := by
  simp [unary,List.replicate_succ]

/-- Identical unary tokens commute past a unary prefix, preserving its tail. -/
theorem unary_bump (n : ℕ) (tail : List Bool) : unary n++true::tail=true::(unary n++tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [unary_succ,List.cons_append,ih]

/-- The first reload pass really reads/copies every divisor cell. -/
theorem reload_drain (flag : Option Bool) (input divisor copied scratch quotient remainder : List Bool) :
    Executes (divisor.length+1) (cfg (some .reload) flag input divisor copied scratch quotient remainder)
      (cfg (some .restore) none input [] (unary divisor.length++copied)
        (divisor.reverse++scratch) quotient remainder) := by
  induction divisor generalizing copied scratch flag with
  | nil =>
    apply SemiprimeD1StackFiniteControlPaths.SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,unary,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .reload) flag input (b::bs) copied scratch quotient remainder)=
        some (cfg (some .reload) (some b) input bs (true::copied) (b::scratch) quotient remainder) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    have h := SemiprimeD1StackFiniteControlPaths.SourcePath.next hs
      (ih (some b) (true::copied) (b::scratch))
    simpa [unary_bump,List.reverse_cons,List.append_assoc] using h

/-- The second reload pass physically restores every original divisor bit. -/
theorem reload_restore (flag : Option Bool) (input divisor copied scratch quotient remainder : List Bool) :
    Executes (scratch.length+1) (cfg (some .restore) flag input divisor copied scratch quotient remainder)
      (cfg (some .start) none input (scratch.reverse++divisor) copied [] quotient remainder) := by
  induction scratch generalizing divisor flag with
  | nil =>
    apply SemiprimeD1StackFiniteControlPaths.SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .restore) flag input divisor copied (b::bs) quotient remainder)=
        some (cfg (some .restore) (some b) input (b::divisor) copied bs quotient remainder) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using
      SemiprimeD1StackFiniteControlPaths.SourcePath.next hs (ih (some b) (b::divisor))

/-- Whole actual divisor copy/restore, not a supplied radix counter. -/
theorem reload_exec (flag : Option Bool) (input divisor quotient remainder : List Bool) :
    Executes (2*divisor.length+2) (cfg (some .reload) flag input divisor [] [] quotient remainder)
      (cfg (some .start) none input divisor (unary divisor.length) [] quotient remainder) := by
  have h := exec_trans (reload_drain flag input divisor [] [] quotient remainder)
    (reload_restore none input [] (unary divisor.length++[]) (divisor.reverse++[]) quotient remainder)
  simp only [List.append_nil,List.length_reverse,List.reverse_reverse] at h
  convert h using 1
  omega

/-- Cleanup of the physically copied divisor includes every unconsumed token. -/
theorem clear_copy (flag : Option Bool) (divisor copied quotient remainder : List Bool) :
    Executes (copied.length+1) (cfg (some .clearCopy) flag [] divisor copied [] quotient remainder)
      (cfg none none [] divisor [] [] quotient remainder) := by
  induction copied generalizing flag with
  | nil =>
    apply SemiprimeD1StackFiniteControlPaths.SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    apply SemiprimeD1StackFiniteControlPaths.SourcePath.next ?_ (ih (some b))
    simp [program,cfg,contents,TM2.step,TM2.stepAux]

/-- Clearing a completed remainder block is an actual physical loop. -/
theorem clear_remainder (flag : Option Bool) (input divisor quotient remainder : List Bool) :
    Executes (remainder.length+1) (cfg (some .clearRemainder) flag input divisor [] [] quotient remainder)
      (cfg (some .reload) none input divisor [] [] quotient []) := by
  induction remainder generalizing flag with
  | nil =>
    apply SemiprimeD1StackFiniteControlPaths.SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    apply SemiprimeD1StackFiniteControlPaths.SourcePath.next ?_ (ih (some b))
    simp [program,cfg,contents,TM2.step,TM2.stepAux]

end RiemannGaussian.SemiprimeD1StackUnaryDivmod
