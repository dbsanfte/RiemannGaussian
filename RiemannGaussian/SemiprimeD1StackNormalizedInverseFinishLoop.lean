/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishRow
/-! # Whole actual newest-first to chronological rational-array reversal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishLoop
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInversePrimitives SemiprimeD1StackNormalizedInverseFinishBuffers
open SemiprimeD1StackNormalizedInverseFinishRow SemiprimeD1StackProcedureTrace
/-- Actual row-cap sum plus the final FALSE pop and real empty-word peek. -/
def finishTime : List SemiprimeRationalBits.RationalWord→ℕ
  | []=>2
  | word::words=>15*((signed word).length+word.denominator.length)+30+finishTime words
/-- Proof codec of the exact chronological output acquired by the actual prepend loop. -/
def outputRows (words : List SemiprimeRationalBits.RationalWord) (out : List Bool) : List Bool :=
  words.foldl (fun tail word=>row word tail) out
/-- The loop retains ALL raw coefficient fields and reverses only their row order. -/
theorem outputRows_reverse (words : List SemiprimeRationalBits.RationalWord) (out : List Bool) :
    outputRows words out=words.reverse.foldr row out := by
  rw [outputRows,List.foldl_eq_foldr_reverse]
/-- Complete actual final row loop, including empty array and real EOF validation. -/
theorem finish_run (w : Words) (words : List SemiprimeRationalBits.RationalWord) (out : List Bool)
    (hn : w.registers (.left,false)=[]) (hd : w.registers (.left,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) :
    Runs program (finishTime words) (ctl .finalTag) (store (finishBuffers w (tape words) out))
      (ctl (.clearFinal 0)) (store (finishBuffers w [] (outputRows words out))) := by
  induction words generalizing out with
  | nil=>
    have h0:=pop_run (ctl .finalTag) (ctl (.abort 0)) (ctl .finalEnd) (ctl (.finalField false)) (aux .prefixReverse)
      (store (finishBuffers w [false] out)) [false] rfl rfl
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [update_prefix] at h0
    have h1:=peek_run (ctl .finalEnd) (ctl (.clearFinal 0)) (ctl (.abort 0)) (ctl (.abort 0)) (aux .prefixReverse)
      (store (finishBuffers w [] out)) [] rfl rfl
    have h:=join h0 h1
    convert h using 1 <;> rfl
  | cons word words ih=>
    have h0:=row_run w word (tape words) out hn hd hs hv
    have h1:=ih (row word out)
    have h:=join h0 h1
    convert h using 1 <;> rfl
/-- This SAME whole physical reversal has a linear cap in its actual input array bytes. -/
theorem finishTime_le (words : List SemiprimeRationalBits.RationalWord) :
    finishTime words≤20*(tape words).length := by
  induction words with
  | nil=>decide
  | cons word words ih=>
    change 15*((signed word).length+word.denominator.length)+30+finishTime words≤20*(row word (tape words)).length
    rw [row_length]
    omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishLoop
