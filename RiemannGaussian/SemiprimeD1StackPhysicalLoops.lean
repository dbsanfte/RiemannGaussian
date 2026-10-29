/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackUnaryDivmod
/-! # Literal finite-program drain loops for acquired physical counters -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackPhysicalLoops
namespace C
export SemiprimeD1StackCalls (Instruction)
end C
namespace B
export SemiprimeD1StackBytecode (execute choose)
end B
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
/-- A literal pop loop visits and erases every cell. The only code premise is
an equality of fixed instruction tables, not a payload, clock or memory oracle. -/
theorem drain {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc next : L) (k : K) (hcode : program pc=.base (.pop k next pc pc))
    (bank : K→List Bool) (word : List Bool) :
    Runs program (word.length+1) pc (Function.update bank k word)
      next (Function.update bank k []) := by
  induction word with
  | nil =>
    apply one_base program pc next (.pop k next pc pc) _ _ hcode
    · simp [B.execute,B.choose]
    · simp [B.execute]
  | cons b bs ih =>
    have hs : Runs program 1 pc (Function.update bank k (b::bs))
        pc (Function.update bank k bs) := by
      apply one_base program pc pc (.pop k next pc pc) _ _ hcode
      · cases b <;> simp [B.execute,B.choose]
      · simp [B.execute]
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      runs_trans program 1 (bs.length+1) pc pc next _ _ _ hs ih
/-- A literal unary transfer loop pays every source read and destination push. -/
theorem move_unary {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc push next : L) (source dest : K) (hne : dest≠source)
    (hpop : program pc=.base (.pop source next push push))
    (hpush : program push=.base (.push dest true pc))
    (bank : K→List Bool) (n : ℕ) (tail : List Bool) :
    Runs program (2*n+1) pc
      (Function.update (Function.update bank dest tail) source (List.replicate n true))
      next (Function.update (Function.update bank dest (List.replicate n true++tail)) source []) := by
  induction n generalizing tail with
  | zero =>
    apply one_base program pc next (.pop source next push push) _ _ hpop
    · simp [B.execute,B.choose]
    · simp [B.execute]
  | succ n ih =>
    let input := Function.update (Function.update bank dest tail) source (List.replicate (n+1) true)
    let middle := Function.update (Function.update bank dest tail) source (List.replicate n true)
    let moved := Function.update (Function.update bank dest (true::tail)) source (List.replicate n true)
    have hs : Runs program 1 pc input push middle := by
      apply one_base program pc push (.pop source next push push) _ _ hpop
      · simp [input,B.execute,B.choose,List.replicate_succ]
      · simp [input,middle,B.execute,List.replicate_succ]
    have ht : Runs program 1 push middle pc moved := by
      apply one_base program push pc (.push dest true pc) _ _ hpush
      · rfl
      · dsimp [middle,moved]
        funext k
        by_cases hks : k=source
        · subst k; simp [B.execute,hne,Ne.symm hne]
        · by_cases hkd : k=dest
          · subst k; simp [B.execute,hne]
          · simp [B.execute,hks,hkd]
    have hh:=runs_trans program 1 (1+(2*n+1)) pc push next _ _ _ hs
      (runs_trans program 1 (2*n+1) push pc next _ _ _ ht (ih (true::tail)))
    rw [show 1+(1+(2*n+1))=2*(n+1)+1 by omega] at hh
    have hb : List.replicate n true++true::tail=true::(List.replicate n true++tail) :=
      SemiprimeD1StackUnaryDivmod.unary_bump n tail
    simpa only [input,List.replicate_succ,hb,List.cons_append] using hh

/-- A literal empty-stack test is one actual transition. -/
theorem peek_empty {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc empty low high : L) (k : K)
    (hcode : program pc=.base (.peek k empty low high)) (bank : K→List Bool) (hk : bank k=[]) :
    Runs program 1 pc bank empty bank := by
  apply one_base program pc empty (.peek k empty low high) _ _ hcode
  · simp [B.execute,B.choose,hk]
  · rfl

/-- Either literal Boolean head takes the same declared nonempty branch. -/
theorem peek_nonempty {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc empty next : L) (k : K)
    (hcode : program pc=.base (.peek k empty next next)) (bank : K→List Bool)
    (head : Bool) (tail : List Bool) (hk : bank k=head::tail) :
    Runs program 1 pc bank next bank := by
  apply one_base program pc next (.peek k empty next next) _ _ hcode
  · cases head <;> simp [B.execute,B.choose,hk]
  · rfl

end RiemannGaussian.SemiprimeD1StackPhysicalLoops
