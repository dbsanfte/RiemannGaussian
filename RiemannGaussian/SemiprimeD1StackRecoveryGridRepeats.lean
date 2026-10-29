/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
/-! # Physically framed repeated slopes in original Grid104 order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRepeats
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
/-- Only the actual repetition counter and accumulated physical slope vector are mutable here. -/
def buffers (w:Words) (todo tail:List Bool) :Words:=
  {w with auxiliary:=fun k=>if k=.repeatTodo then todo else if k=.slopes then tail else w.auxiliary k}
/-- A real repetition-counter write preserves every accumulated output byte. -/
theorem update_todo (w:Words) (todo tail xs:List Bool) :
    Function.update (bank (buffers w todo tail)) (aux .repeatTodo) xs=bank (buffers w xs tail):=by
  rw [update_auxiliary]
  congr 1
  congr 1
  funext k
  cases k <;> simp [buffers]
/-- A real frame/output write preserves the actual remaining repetition markers. -/
theorem update_slopes (w:Words) (todo tail xs:List Bool) :
    Function.update (bank (buffers w todo tail)) (aux .slopes) xs=bank (buffers w todo xs):=by
  rw [update_auxiliary]
  congr 1
  congr 1
  funext k
  cases k <;> simp [buffers]
/-- Exact physical repetitions, specified in the same head-prepending direction as actual framing. -/
def rows (word:SemiprimeRationalBits.RationalWord) :Nat→List Bool→List Bool
  | 0,tail=>tail
  | n+1,tail=>rows word n (slopeRow word tail)
/-- Identical repeated slope rows commute with their own already emitted leading row. -/
theorem rows_cons (word:SemiprimeRationalBits.RationalWord) (n:Nat) (tail:List Bool) :
    rows word n (slopeRow word tail)=slopeRow word (rows word n tail):=by
  induction n generalizing tail with
  | zero=>rfl
  | succ n ih=>exact ih (slopeRow word tail)
/-- Each physical repetition corresponds exactly to the legacy forward repeated-word list. -/
theorem rows_replicate (word:SemiprimeRationalBits.RationalWord) (n:Nat) (tail:List Bool) :
    rows word n tail=(List.replicate n word).foldr slopeRow tail:=by
  induction n generalizing tail with
  | zero=>rfl
  | succ n ih=>rw [rows,rows_cons,ih,List.replicate_succ,List.foldr_cons]
/-- Every occurrence performs two actual preserving Frame calls and one actual vector tag push. -/
theorem repeats_run (w:Words) (word:SemiprimeRationalBits.RationalWord) (n:Nat) (tail:List Bool)
    (hn:w.registers (.slope,false)=signed word) (hd:w.registers (.slope,true)=word.denominator)
    (hs:w.auxiliary .frameScratch=[]) :
    Runs program (n*(6*((signed word).length+word.denominator.length)+12)+1)
      (.local .repeats) (bank (buffers w (List.replicate n true) tail))
      (.local .numeratorFold) (bank (buffers w [] (rows word n tail))):=by
  induction n generalizing tail with
  | zero=>
    have h:=PTrace.pop_run (.local .repeats) (.local .numeratorFold) (.local .abort) (.local .frameDen)
      (aux .repeatTodo) (bank (buffers w [] tail)) [] rfl rfl
    rw [update_todo] at h
    change Runs program 1 _ _ (.local .numeratorFold) (bank (buffers w [] tail)) at h
    simpa only [Nat.zero_mul,Nat.zero_add,List.replicate_zero,rows] using h
  | succ n ih=>
    have h0:=PTrace.pop_run (.local .repeats) (.local .numeratorFold) (.local .abort) (.local .frameDen)
      (aux .repeatTodo) (bank (buffers w (List.replicate (n+1) true) tail)) (true::List.replicate n true)
      rfl (by simp [bank,buffers,aux,List.replicate_succ])
    rw [update_todo] at h0
    change Runs program 1 _ _ (.local .frameDen) _ at h0
    have h1:=PTrace.frame_call true (.local .frameDen) (.local .frameSigned) rfl
      (bank (buffers w (List.replicate n true) tail)) word.denominator tail hd rfl hs
    change Runs program _ _ _ _ (Function.update _ (aux .slopes)
      (SemiprimeSourceHistogramKeyBits.frame word.denominator tail)) at h1
    rw [update_slopes] at h1
    have h2:=PTrace.frame_call false (.local .frameSigned) (.local .frameTag) rfl
      (bank (buffers w (List.replicate n true) (SemiprimeSourceHistogramKeyBits.frame word.denominator tail)))
      (signed word) (SemiprimeSourceHistogramKeyBits.frame word.denominator tail) hn rfl hs
    change Runs program _ _ _ _ (Function.update _ (aux .slopes)
      (SemiprimeSourceHistogramKeyBits.frame (signed word) (SemiprimeSourceHistogramKeyBits.frame word.denominator tail))) at h2
    rw [update_slopes] at h2
    have h3:=PTrace.push_run (.local .frameTag) (.local .repeats) (aux .slopes) true
      (bank (buffers w (List.replicate n true)
        (SemiprimeSourceHistogramKeyBits.frame (signed word) (SemiprimeSourceHistogramKeyBits.frame word.denominator tail)))) rfl
    change Runs program 1 _ _ _ (Function.update _ (aux .slopes) (slopeRow word tail)) at h3
    rw [update_slopes] at h3
    have h4:=ih (slopeRow word tail)
    have h:=PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4
    change Runs program _ _ _ _ (bank (buffers w [] (rows word (n+1) tail))) at h
    convert h using 1
    ring
end RiemannGaussian.SemiprimeD1StackRecoveryGridRepeats
