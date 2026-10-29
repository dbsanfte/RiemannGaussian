/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
import RiemannGaussian.SemiprimeD1StackNormalizedInverseIndices
/-! # Both actual decreasing physical indices and remaining pair markers
The reused counter functions describe stores only. Every transition below is
proved for THIS fixed60-role program by actual Boolean pops, including EOF.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndices
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- Every q/index marker is physically present and paid. -/
def unary (n:Nat):List Bool:=List.replicate n true
/-- Proof-side view of THREE actual marker words, preserving all six original inputs. -/
def counters (w:Words) (terms a b:Nat):Words:=replace w (SemiprimeD1StackNormalizedInverseIndices.counters w.toWords terms a b)
/-- Actual accumulator plus the exact reached physical pair counters. -/
def indexed (w:Words) (terms a b:Nat) (acc:RationalWord):Words:=replace w (SemiprimeD1StackNormalizedInverseIndices.indexed w.toWords terms a b acc)
/-- One real terms pop changes precisely its actual remaining unary word. -/
theorem update_terms (w:Words) (terms a b next:Nat):
    Function.update (bank (counters w terms a b)) (aux .terms) (unary next)=bank (counters w next a b):=by
  rw [show aux .terms=helper (SemiprimeD1StackNormalizedInverse.aux .terms) from rfl,update_helper]
  dsimp only [counters,replace]
  exact congrArg (fun d:I.Stack→List Bool=>Sum.elim d w.scalarInputs)
    (SemiprimeD1StackNormalizedInverseIndices.update_terms w.toWords terms a b next)
/-- One real inverse-index pop changes precisely its actual unary index word. -/
theorem update_a (w:Words) (terms a b next:Nat):
    Function.update (bank (counters w terms a b)) (aux .aIndex) (unary next)=bank (counters w terms next b):=by
  rw [show aux .aIndex=helper (SemiprimeD1StackNormalizedInverse.aux .aIndex) from rfl,update_helper]
  dsimp only [counters,replace]
  exact congrArg (fun d:I.Stack→List Bool=>Sum.elim d w.scalarInputs)
    (SemiprimeD1StackNormalizedInverseIndices.update_a w.toWords terms a b next)
/-- One real power-index pop changes precisely its actual unary index word. -/
theorem update_b (w:Words) (terms a b next:Nat):
    Function.update (bank (counters w terms a b)) (aux .bIndex) (unary next)=bank (counters w terms a next):=by
  rw [show aux .bIndex=helper (SemiprimeD1StackNormalizedInverse.aux .bIndex) from rfl,update_helper]
  dsimp only [counters,replace]
  exact congrArg (fun d:I.Stack→List Bool=>Sum.elim d w.scalarInputs)
    (SemiprimeD1StackNormalizedInverseIndices.update_b w.toWords terms a b next)
/-- Disjoint physical counter writes commute with an acquired scalar-cache write. -/
theorem counters_put (w:Words) (r:I.Reg) (word:RationalWord) (terms a b:Nat):
    counters (putReg w r word) terms a b=putReg (counters w terms a b) r word:=rfl
/-- Actual TRUE remaining-pair pop starts the next TWO physical coefficient reads. -/
theorem term_succ (w:Words) (j n:Nat) (acc:RationalWord):
    Runs program 1 (.local .terms) (bank (indexed w (n+1) n (j+n) acc)) (.local .readInverse)
      (bank (indexed w n n (j+n) acc)):=by
  let base:=putReg w .acc acc
  have h:=P.pop_run (.local .terms) (.local (.clearIndices false)) abort (.local .readInverse) (aux .terms)
    (bank (indexed w (n+1) n (j+n) acc)) (true::unary n) rfl (by
      change Function.update (Function.update (Function.update w.auxiliary .terms (unary (n+1))) .aIndex (unary n)) .bIndex (unary (j+n)) .terms=_
      simp [unary,List.replicate_succ])
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h
  change Runs program 1 _ _ _ (Function.update (bank (counters base (n+1) n (j+n))) (aux .terms) (unary n)) at h
  rw [update_terms,counters_put] at h
  exact h
/-- Both inverse and power indices are physically popped, including literal EOF when their values are zero. -/
theorem decrement_run (w:Words) (j n:Nat) (acc:RationalWord):
    Runs program 2 (.local .decrementA) (bank (indexed w n n (j+n) acc)) (.local .terms)
      (bank (indexed w n (n-1) (j+n-1) acc)):=by
  let base:=putReg w .acc acc
  have h0:=P.pop_run (.local .decrementA) (.local .decrementB) abort (.local .decrementB) (aux .aIndex)
    (bank (counters base n n (j+n))) (unary n) rfl (by
      change Function.update (Function.update (Function.update base.auxiliary .terms (unary n)) .aIndex (unary n)) .bIndex (unary (j+n)) .aIndex=_
      simp)
  have ht:(unary n).tail=unary (n-1):=by cases n <;> simp [unary,List.replicate_succ]
  have hc:SemiprimeD1StackBytecode.choose (Label.local .decrementB) abort (.local .decrementB) (unary n).head?=.local .decrementB:=by
    cases n <;> simp [unary,List.replicate_succ,SemiprimeD1StackBytecode.choose]
  rw [ht,hc,update_a] at h0
  have h1:=P.pop_run (.local .decrementB) (.local .terms) abort (.local .terms) (aux .bIndex)
    (bank (counters base n (n-1) (j+n))) (unary (j+n)) rfl (by
      change Function.update (Function.update (Function.update base.auxiliary .terms (unary n)) .aIndex (unary (n-1))) .bIndex (unary (j+n)) .bIndex=_
      exact Function.update_self _ _ _)
  have ht1:(unary (j+n)).tail=unary (j+n-1):=by cases j+n <;> simp [unary,List.replicate_succ]
  have hc1:SemiprimeD1StackBytecode.choose (Label.local .terms) abort (.local .terms) (unary (j+n)).head?=.local .terms:=by
    cases j+n <;> simp [unary,List.replicate_succ,SemiprimeD1StackBytecode.choose]
  rw [ht1,hc1,update_b] at h1
  exact P.join h0 h1
/-- Actual terms EOF retains the acquired sum and starts full disposal of BOTH index words. -/
theorem term_zero (w:Words) (j:Nat) (acc:RationalWord):
    Runs program 1 (.local .terms) (bank (indexed w 0 0 (j-1) acc)) (.local (.clearIndices false))
      (bank (indexed w 0 0 (j-1) acc)):=by
  let base:=putReg w .acc acc
  have h:=P.pop_run (.local .terms) (.local (.clearIndices false)) abort (.local .readInverse) (aux .terms)
    (bank (counters base 0 0 (j-1))) [] rfl (by
      change Function.update (Function.update (Function.update base.auxiliary .terms []) .aIndex []) .bIndex (unary (j-1)) .terms=[]
      simp)
  change Runs program 1 _ _ _ (Function.update (bank (counters base 0 0 (j-1))) (aux .terms) (unary 0)) at h
  rw [update_terms,counters_put] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndices
