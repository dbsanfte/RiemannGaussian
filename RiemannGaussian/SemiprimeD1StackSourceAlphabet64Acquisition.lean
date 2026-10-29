/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Setup
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Calls
/-! # Whole actual unary-marker acquisition of6a-bit counter and binary powers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Acquisition
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackSourceAlphabet64Setup
open SemiprimeD1StackProcedureTrace
/-- Literal saturated head exponent, including a0's actual binary ONE. -/
def headZeros (first:Bool) (n:Nat) :Nat :=if first then 6*(4*n-1) else 24*n
/-- Complete marker-loop physical writes; all unrelated cells remain literal. -/
def fillResult (bank:Stack→List Bool) (first:Bool) (n:Nat) :Stack→List Bool :=
  Function.update (zeros (zeros (zeros (zeros (zeros bank (enumStack .word) (6*n))
    (aux .square) (12*n)) (aux .cube) (18*n)) (aux .fourth) (24*n))
    (aux .head) (headZeros first n)) (aux .todo) []
/-- The first actual marker accounts for the six-bit saturated subtraction. -/
theorem headZeros_succ (first:Bool) (n:Nat) :
    headZeros first (n+1)=24*n+(if first then 18 else 24) :=by
  cases first <;> simp only [headZeros,Bool.false_eq_true,ite_false,ite_true] <;> omega
/-- Actual zero-push blocks combine literally; no numeric payload is re-encoded. -/
theorem fillResult_step (bank:Stack→List Bool) (first:Bool) (n:Nat) (tail:List Bool) :
    fillResult (block (Function.update bank (aux .todo) tail) first) false n=fillResult bank first (n+1) :=by
  funext k
  cases first <;> rcases k with k|k <;> cases k <;>
    simp [fillResult,block,zeros,enumStack,aux,headZeros,Nat.mul_add,List.replicate_add,List.append_assoc]
  all_goals rw [show 6*(4*n)=24*n by omega]
/-- Every actual source marker is physically consumed; all original/root width
bytes remain retained, and every binary zero/power write is charged. -/
theorem fill_run (bank:Stack→List Bool) (first:Bool) (n:Nat)
    (ht:bank (aux .todo)=List.replicate n true) :
    ∃q ≤ 90*n+1,Runs program q (.fill first) bank .enumerate (fillResult bank first n) :=by
  induction n generalizing bank first with
  | zero=>
    have he:fillResult bank first 0=Function.update bank (aux .todo) []:=by
      cases first <;> simp [fillResult,headZeros,zeros_zero]
    refine ⟨1,by omega,?_⟩
    rw [he]
    apply one_base program _ _ (.pop (aux .todo) .enumerate .abort (.pushes first .word 0)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,ht]
    · simp [SemiprimeD1StackBytecode.execute,ht]
  | succ n ih=>
    let next:=Function.update bank (aux .todo) (List.replicate n true)
    have h0:Runs program 1 (.fill first) bank (.pushes first .word 0) next:=by
      apply one_base program _ _ (.pop (aux .todo) .enumerate .abort (.pushes first .word 0)) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,ht,List.replicate_succ]
      · simp [SemiprimeD1StackBytecode.execute,ht,List.replicate_succ,next]
    have h1:=block_run next first
    have htodo:block next first (aux .todo)=List.replicate n true:=by
      simp [block,zeros,next,aux,enumStack]
    obtain ⟨q,hq,h2⟩:=ih (block next first) false htodo
    rw [show fillResult (block next first) false n=fillResult bank first (n+1) from fillResult_step bank first n _] at h2
    have h:=compose (compose h0 h1) h2
    refine ⟨_,?_,h⟩
    cases first <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;> omega
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Acquisition
