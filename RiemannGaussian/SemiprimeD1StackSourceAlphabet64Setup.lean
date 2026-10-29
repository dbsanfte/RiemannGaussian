/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Primitives
/-! # Paid unary-width traversal writes actual counter bits and binary cached powers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Setup
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackProcedureTrace
/-- Proof-side cumulative effect of actual false pushes on one physical word. -/
def zeros (bank:Stack→List Bool) (k:Stack) (n:Nat) :Stack→List Bool :=
  Function.update bank k (List.replicate n false++bank k)
/-- A zero-length literal push sequence leaves the actual bank unchanged. -/
theorem zeros_zero (bank:Stack→List Bool) (k:Stack) :zeros bank k 0=bank :=by
  change Function.update bank k (bank k)=bank
  exact Function.update_eq_self _ _
/-- Literal fixed lanes never push more than24 bits per actual source marker. -/
theorem fillLength_le (first:Bool) (part:Fill) :fillLength first part ≤ 24 :=by
  cases first <;> cases part <;> decide
/-- Actual finite push-control loop includes its genuine last jump. -/
theorem pushes_run (first:Bool) (part:Fill) (i:Fin 25) (bank:Stack→List Bool) (hi:i.val ≤ fillLength first part) :
    Runs program (fillLength first part-i.val+1) (.pushes first part i) bank (afterFill first part)
      (zeros bank (fillStack part) (fillLength first part-i.val)) :=by
  suffices ∀n:Nat,∀i:Fin 25,∀bank:Stack→List Bool,i.val+n=fillLength first part→
      Runs program (n+1) (.pushes first part i) bank (afterFill first part) (zeros bank (fillStack part) n) by
    exact this _ i bank (by omega)
  intro n
  induction n with
  | zero=>
    intro i bank he
    have hi:¬i.val<fillLength first part:=by omega
    rw [zeros_zero]
    apply one_base program _ _ (.jump (afterFill first part)) _ _ (by simp only [program,dite_eq_right hi])
    · rfl
    · rfl
  | succ n ih=>
    intro i bank he
    have hi:i.val<fillLength first part:=by omega
    let j:Fin 25:=⟨i.val+1,by have hl:=fillLength_le first part;omega⟩
    let next:=Function.update bank (fillStack part) (false::bank (fillStack part))
    have h0:Runs program 1 (.pushes first part i) bank (.pushes first part j) next:=by
      apply one_base program _ _ (.push (fillStack part) false (.pushes first part j)) _ _
        (by simp only [program,dite_eq_left hi];rfl)
      · rfl
      · rfl
    have h1:=ih j next (by dsimp only [j];omega)
    have heq:zeros next (fillStack part) n=zeros bank (fillStack part) (n+1):=by
      unfold zeros
      dsimp only [next]
      rw [Function.update_same,Function.update_idem,List.replicate_succ',List.append_assoc]
      rfl
    rw [heq] at h1
    have h:=compose h0 h1
    simpa only [show 1+(n+1)=n+1+1 by omega] using h
/-- Whole fixed five-lane push block performs only actual false pushes before the next marker pop. -/
def block (bank:Stack→List Bool) (first:Bool) :Stack→List Bool :=
  zeros (zeros (zeros (zeros (zeros bank (enumStack .word) 6) (aux .square) 12)
    (aux .cube) 18) (aux .fourth) 24) (aux .head) (if first then 18 else 24)
/-- Exact five-lane time includes every physical bit write and five real finite jumps. -/
theorem block_run (bank:Stack→List Bool) (first:Bool) :
    Runs program (6+12+18+24+(if first then 18 else 24)+5) (.pushes first .word 0) bank (.fill false) (block bank first) :=by
  have h0:=pushes_run first .word 0 bank (Nat.zero_le _)
  have h1:=pushes_run first .square 0 (zeros bank (enumStack .word) 6) (Nat.zero_le _)
  have h2:=pushes_run first .cube 0 (zeros (zeros bank (enumStack .word) 6) (aux .square) 12) (Nat.zero_le _)
  have h3:=pushes_run first .fourth 0 (zeros (zeros (zeros bank (enumStack .word) 6) (aux .square) 12) (aux .cube) 18) (Nat.zero_le _)
  have h4:=pushes_run first .head 0 (zeros (zeros (zeros (zeros bank (enumStack .word) 6) (aux .square) 12)
    (aux .cube) 18) (aux .fourth) 24) (Nat.zero_le _)
  have h:=compose (compose (compose (compose h0 h1) h2) h3) h4
  cases first <;> exact h
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Setup
