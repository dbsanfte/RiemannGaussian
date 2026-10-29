/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
import RiemannGaussian.SemiprimeD1StackNormalizedInversePrimitives
/-! # Actual decreasing unary pair counters and physical accumulator views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseIndices
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackProcedureTrace
/-- These proof-side numbers specify THREE actual unary words; they never enter runtime control. -/
def counters (w : Words) (terms a b : ℕ) : Words :=
  {w with auxiliary:=Function.update (Function.update (Function.update w.auxiliary .terms (unary terms)) .aIndex (unary a)) .bIndex (unary b)}
/-- Exact acquired accumulator plus actual remaining pair indices. -/
def indexed (w : Words) (terms a b : ℕ) (acc : SemiprimeRationalBits.RationalWord) : Words :=
  putReg (counters w terms a b) .acc acc
/-- Every actual terms pop is only the next remaining marker write. -/
theorem update_terms (w : Words) (terms a b next : ℕ) :
    Function.update (store (counters w terms a b)) (aux .terms) (unary next)=store (counters w next a b) := by
  rw [update_aux]
  apply congrArg (fun f=>store ({w with auxiliary:=f}:Words))
  funext k;cases k <;> simp [counters]
/-- Every actual left-index pop is only its next unary word. -/
theorem update_a (w : Words) (terms a b next : ℕ) :
    Function.update (store (counters w terms a b)) (aux .aIndex) (unary next)=store (counters w terms next b) := by
  rw [update_aux]
  apply congrArg (fun f=>store ({w with auxiliary:=f}:Words))
  funext k;cases k <;> simp [counters]
/-- Every actual reversed-prefix index pop is only its next unary word. -/
theorem update_b (w : Words) (terms a b next : ℕ) :
    Function.update (store (counters w terms a b)) (aux .bIndex) (unary next)=store (counters w terms a next) := by
  rw [update_aux]
  apply congrArg (fun f=>store ({w with auxiliary:=f}:Words))
  funext k;cases k <;> simp [counters]
/-- Metadata writes commute with an actual acquired coefficient cache. -/
theorem counters_put (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) (terms a b : ℕ) :
    counters (putReg w r word) terms a b=putReg (counters w terms a b) r word := rfl
/-- A real pair-counter TRUE pop starts the next actual pair parse. -/
theorem term_succ (w : Words) (n : ℕ) (acc : SemiprimeRationalBits.RationalWord) :
    Runs program 1 (ctl .terms) (store (indexed w (n+1) (n+1) n acc)) (ctl .readA)
      (store (indexed w n (n+1) n acc)) := by
  have h:=pop_run (ctl .terms) (ctl (.seedNeg false)) (ctl (.abort 0)) (ctl .readA) (aux .terms)
    (store (indexed w (n+1) (n+1) n acc)) (true::unary n) rfl (by
      change Function.update (Function.update (Function.update w.auxiliary .terms (unary (n+1))) .aIndex (unary (n+1))) .bIndex (unary n) .terms=true::unary n
      simp [unary,List.replicate_succ])
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h
  change Runs program 1 _ _ _ (Function.update (store (counters (putReg w .acc acc) (n+1) (n+1) n)) (aux .terms) (unary n)) at h
  rw [update_terms,counters_put] at h
  exact h
/-- Both actual index pops execute, including the real EOF branch when reversed-prefix index is zero. -/
theorem decrement_run (w : Words) (n : ℕ) (acc : SemiprimeRationalBits.RationalWord) :
    Runs program 2 (ctl .decrementA) (store (indexed w n (n+1) n acc)) (ctl .terms)
      (store (indexed w n n (n-1) acc)) := by
  let base:=putReg w .acc acc
  have h0:=pop_run (ctl .decrementA) (ctl (.abort 0)) (ctl (.abort 0)) (ctl .decrementB) (aux .aIndex)
    (store (counters base n (n+1) n)) (true::unary n) rfl (by
      change Function.update (Function.update (Function.update base.auxiliary .terms (unary n)) .aIndex (unary (n+1))) .bIndex (unary n) .aIndex=true::unary n
      simp [unary,List.replicate_succ])
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_a] at h0
  have h1:=pop_run (ctl .decrementB) (ctl .terms) (ctl (.abort 0)) (ctl .terms) (aux .bIndex)
    (store (counters base n n n)) (unary n) rfl (by
      change Function.update (Function.update (Function.update base.auxiliary .terms (unary n)) .aIndex (unary n)) .bIndex (unary n) .bIndex=unary n
      exact Function.update_self _ _ _)
  have ht : (unary n).tail=unary (n-1) := by cases n <;> simp [unary,List.replicate_succ]
  have hh : SemiprimeD1StackBytecode.choose (ctl .terms) (ctl (.abort 0)) (ctl .terms) (unary n).head?=ctl .terms := by
    cases n <;> simp [unary,List.replicate_succ,SemiprimeD1StackBytecode.choose]
  rw [ht,hh,update_b] at h1
  have h:=join h0 h1
  exact h
/-- The last real terms EOF branch starts actual negation, without discarding the acquired accumulator. -/
theorem term_zero (w : Words) (acc : SemiprimeRationalBits.RationalWord) :
    Runs program 1 (ctl .terms) (store (indexed w 0 0 0 acc)) (ctl (.seedNeg false))
      (store (indexed w 0 0 0 acc)) := by
  let base:=putReg w .acc acc
  have h:=pop_run (ctl .terms) (ctl (.seedNeg false)) (ctl (.abort 0)) (ctl .readA) (aux .terms)
    (store (counters base 0 0 0)) [] rfl (by
      change Function.update (Function.update (Function.update base.auxiliary .terms []) .aIndex []) .bIndex [] .terms=[]
      rw [Function.update_of_ne (show Aux.terms≠.bIndex by decide),
        Function.update_of_ne (show Aux.terms≠.aIndex by decide),Function.update_self])
  change Runs program 1 _ _ _ (Function.update (store (counters base 0 0 0)) (aux .terms) (unary 0)) at h
  rw [update_terms,counters_put] at h
  exact h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseIndices
