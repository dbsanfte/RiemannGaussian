/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorTable
/-! # Proof-only actual checker trace contract and whole table specification
No definition in this module is an operand of the compiler program. Concrete
clients prove the contract from their already kernel-checked literal checker.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVectorTableSpec
open SemiprimeD1StackVectorTable
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Exact ordinary checker initialization, after actual physical template copy
and assignment reversal. It is a theorem-side state view only. -/
def checkerInitial (original : K→List Bool) (raw : List Bool) : C.State K L :=
  ⟨some s.entry,none,none,Function.update original s.raw raw,[]⟩
/-- A PROVED actual trace of the fixed checker, for every raw word. The budget
and postcondition are proof arguments; neither is carried in runtime state. -/
def CheckerTrace (original : K→List Bool) (answer : List Bool→List (List Bool)) (budget : Nat→Nat) : Prop :=
  ∀raw,∃t≤ budget raw.length,∃finish:C.State K L,
    finish.pc=none ∧ finish.frames=[] ∧
    C.run s.code t (checkerInitial s original raw)=some finish ∧ finish.data s.output=SemiprimeD1TensorTapeCodec.vectorBits (answer raw)
/-- All actual original-template input bytes, including empty private fields. -/
def inputBytes [Fintype K] (original : K→List Bool) : Nat :=∑k:K,(original k).length
/-- The exact full coefficient vector returned by the fixed physical source. -/
def leafWords (answer : List Bool→List (List Bool)) (raw : List Bool) : List (List Bool) :=
  answer raw
/-- Exact original false-first/first-port-outermost tree; a specification only. -/
def tree (answer : List Bool→List (List Bool)) (front : List Bool) : (n : Nat)→SemiprimeD1TensorTables.Table n
  | 0=>.leaf (leafWords answer front)
  | n+1=>.fork (tree answer (front++[false]) n) (tree answer (front++[true]) n)
/-- Proof view of replacing the actual checker bank, leaving all other cells alone. -/
def withChecker (base : Stack K→List Bool) (live : K→List Bool) : Stack K→List Bool :=
  Sum.elim live (fun k=>base (.inr k))
/-- Actual whole template copy retains every template, scanner and caller byte. -/
def loadedData (original : K→List Bool) (bank front hist : List Bool) : Stack K→List Bool :=
  withChecker (data original bank 0 front hist) original
/-- Every ordinary checker input field is paid by actual original and raw bytes. -/
theorem initial_cell_le [Fintype K] (original : K→List Bool) (raw : List Bool) (k : K) :
    ((checkerInitial s original raw).data k).length≤ inputBytes original+raw.length := by
  by_cases h:k=s.raw
  · subst k
    change (Function.update original s.raw raw s.raw).length≤_
    rw [Function.update_self]
    omega
  · change (Function.update original s.raw raw k).length≤_
    rw [Function.update_of_ne h]
    have hs:(original k).length≤∑j:K,(original j).length:=
      Finset.single_le_sum (f:=fun j:K=>(original j).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
    unfold inputBytes
    omega
/-- Every actual checker output field has its own executed-step byte bound. -/
theorem output_cell_le [Fintype K] (original : K→List Bool) (raw : List Bool)
    (t : Nat) (finish : C.State K L)
    (hr : C.run s.code t (checkerInitial s original raw)=some finish) (k : K) :
    (finish.data k).length≤ inputBytes original+raw.length+t :=
  SemiprimeD1StackReturnLink.run_data_bound s.code t (inputBytes original+raw.length)
    _ finish (initial_cell_le s original raw) hr k
/-- The generic tree visits every finite assignment in its original local order. -/
theorem tree_entry (answer : List Bool→List (List Bool)) (front : List Bool) (n : Nat) (input : Fin n→Bool) :
    SemiprimeD1TensorTables.valueAt (tree answer front n) input=leafWords answer (front++List.ofFn input) := by
  induction n generalizing front with
  | zero=>simp only [tree,SemiprimeD1TensorTables.valueAt,List.ofFn_zero,List.append_nil]
  | succ n ih=>
    cases h:input 0
    · simp only [tree,SemiprimeD1TensorTables.valueAt,h,Bool.false_eq_true,ite_false]
      simpa only [List.ofFn_succ,h,List.append_assoc,List.singleton_append] using
        ih (front++[false]) (fun j=>input j.succ)
    · simp only [tree,SemiprimeD1TensorTables.valueAt,h,ite_true]
      simpa only [List.ofFn_succ,h,List.append_assoc,List.singleton_append] using
        ih (front++[true]) (fun j=>input j.succ)
end RiemannGaussian.SemiprimeD1StackVectorTableSpec
