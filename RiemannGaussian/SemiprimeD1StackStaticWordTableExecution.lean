/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTableDFS
/-! # Complete physical scope count, static-checker DFS and final tape reversal
Every runtime operand is a Boolean tape word. The checker program is static;
trace contracts and mathematical predicates occur only in correctness proofs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackStaticWordTableExecution
open SemiprimeD1StackStaticWordTable SemiprimeD1StackStaticWordTableSpec SemiprimeD1StackStaticWordTableDFS
open SemiprimeD1StackStaticWordTablePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits tape)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : Static K L)
/-- Actual complete output bytes, specified at the physically counted scope arity. -/
def outputTape (answer : List Bool→List Bool) (words : List (List Bool)) : List Bool :=tape (tree answer [] words.length)
/-- The final real store keeps the original template, original scope bank and
the acquired count; every checker/work/prefix/reversal scratch role is empty. -/
def result (original : K→List Bool) (words : List (List Bool)) (answer : List Bool→List Bool) : Stack K→List Bool :=
  Function.update (data original (vectorBits words) words.length [] []) (aux .output) (outputTape answer words)
/-- The real final halt clears finite Boolean/return flags and actual frames. -/
def done (original : K→List Bool) (words : List (List Bool)) (answer : List Bool→List Bool) :
    C.State (Stack K) (Label L s.roles.length) :=⟨none,none,none,result original words answer,[]⟩
omit [Fintype K] in
/-- The actual bank scanner acquires arity from real record tags, including
empty ordinal-zero fields, while retaining all original checker inputs. -/
theorem count_call (original : K→List Bool) (words : List (List Bool)) :
    Runs (program s) (SemiprimeD1StackDigitCountExecution.totalTime words+1) .start
      (data original (vectorBits words) 0 [] []) .build
      (data original (vectorBits words) words.length [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s) counter Label.counter
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))) D.program (.inl .main)
    (fun _=>rfl) .start .build rfl _
    (SemiprimeD1StackDigitCountExecution.initial (vectorBits words))
    (SemiprimeD1StackDigitCountExecution.done words)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackDigitCountExecution.acquire_run words
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k with
          | inl k=>exact (hk k rfl).elim
          | inr k=>rfl
omit [Fintype K] in
/-- Exactly one physical consuming reversal writes the complete original-order tape. -/
theorem reverse_table (original : K→List Bool) (words : List (List Bool)) (answer : List Bool→List Bool) :
    Runs (program s) (2*(outputTape answer words).length+3) .finish
      (data original (vectorBits words) words.length [] (outputTape answer words).reverse) .done
      (result original words answer) := by
  have h:=reverse_call s true .finish .done rfl
    (data original (vectorBits words) words.length [] (outputTape answer words).reverse)
  have hd:Function.update
      (data original (vectorBits words) words.length [] (outputTape answer words).reverse) (aux .reversed) []=
      data original (vectorBits words) words.length [] [] := by
    funext k
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
  change Runs (program s) (2*(outputTape answer words).reverse.length+3) .finish
    (data original (vectorBits words) words.length [] (outputTape answer words).reverse) .done
    (Function.update (Function.update
      (data original (vectorBits words) words.length [] (outputTape answer words).reverse) (aux .reversed) [])
      (aux .output) ((outputTape answer words).reverse.reverse++[])) at h
  rw [List.length_reverse,List.reverse_reverse,List.append_nil,hd] at h
  exact h
/-- This SAME source's complete actual own clock, including all scope-byte
scanning, per-leaf template copies/checks/drains, real returns and final output. -/
def timeBound (original : K→List Bool) (words : List (List Bool))
    (answer : List Bool→List Bool) (budget : Nat→Nat) : Nat :=
  SemiprimeD1StackDigitCountExecution.totalTime words+
    weight s original budget words.length*2^words.length+2*(outputTape answer words).length+7
/-- Whole actual source from only the original checker-input template and a
physical scope-ID vector. No count, raw assignment, table or verdict is input. -/
theorem source_run (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List Bool) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (words : List (List Bool)) :
    ∃t≤ timeBound s original words answer budget,C.run (program s) t
      (initial s original (vectorBits words))=some (done s original words answer) := by
  have h0:=count_call s original words
  obtain ⟨t,ht,hvisit⟩:=visit_returns s original hraw answer budget hc (vectorBits words) words.length [] []
  simp only [List.length_nil,Nat.zero_add,List.reverse_nil,List.append_nil] at ht hvisit
  have h1:=SemiprimeD1StackProcedureReturns.call (program s) t .build .visit .finish _ _ rfl hvisit
  have h2:=reverse_table s original words answer
  have h:=runs_trans (program s) _ _ _ _ _ _ _ _ h0 (runs_trans (program s) _ _ _ _ _ _ _ _ h1 h2)
  obtain ⟨finish,hr,hout⟩:=h [] (initial s original (vectorBits words)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run (program s) .done rfl (result original words answer) [] finish hout
  refine ⟨(SemiprimeD1StackDigitCountExecution.totalTime words+1)+
    ((1+t)+(2*(outputTape answer words).length+3))+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hh]
    rfl
end RiemannGaussian.SemiprimeD1StackStaticWordTableExecution
