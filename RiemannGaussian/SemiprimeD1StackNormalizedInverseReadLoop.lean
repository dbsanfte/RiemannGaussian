/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadSteps
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadHeads
import RiemannGaussian.SemiprimeD1StackNormalizedInverseSpec
/-! # Whole actual zero-extending two-field array scan -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseReadLoop
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackNormalizedInverseReadHeads SemiprimeD1StackNormalizedInverseReadFields
open SemiprimeD1StackNormalizedInverseReadSteps SemiprimeD1StackNormalizedInverseSpec
open SemiprimeD1StackProcedureTrace
/-- Exact sum of the actual counter/tag/field/drain instructions, not a native report clock. -/
def readTime : List SemiprimeRationalBits.RationalWord→ℕ→ℕ
  | [],0=>7
  | [],n+1=>n+7
  | word::words,0=>8*((signed word).length+word.denominator.length)+(tape words).length+21
  | word::words,n+1=>9*((signed word).length+word.denominator.length)+20+readTime words n
/-- The paid physical scan returns the exact selected word or literal ZERO, restoring all reader work. -/
theorem read_loop (part : ReadSite) (w : Words) (words : List SemiprimeRationalBits.RationalWord) (n : ℕ)
    (hn : w.registers (readReg part,false)=[]) (hd : w.registers (readReg part,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) :
    Runs program (readTime words n) (.read part .count) (store (buffers w (tape words) (unary n)))
      (.read part .return) (store (success (buffers (putReg w (readReg part) (readWord words n)) [] []))) := by
  induction words generalizing n with
  | nil=>
    cases n with
    | zero=>
      have h0:=count_zero part w [false]
      have h1:=tag_eof part true w []
      have h2:=missing_run part w [] [] hn hd hv
      have h:=join (join h0 h1) h2
      convert h using 1 <;> rfl
    | succ n=>
      have h0:=count_succ part w [false] n
      have h1:=tag_eof part false w (unary n)
      have h2:=missing_run part w [] (unary n) hn hd hv
      have h:=join (join h0 h1) h2
      convert h using 1 <;> first | rfl | (simp only [readTime,unary,List.length_replicate,List.length_nil];omega)
  | cons word words ih=>
    cases n with
    | zero=>
      have h0:=count_zero part w (row word (tape words))
      have h1:=tag_row part true w
        (SemiprimeSourceHistogramKeyBits.frame (signed word)
          (SemiprimeSourceHistogramKeyBits.frame word.denominator (tape words))) []
      have h2:=fields_run part true w word (tape words) [] hn hd hs hv
      have h3:=selected_run part (putReg w (readReg part) word) (tape words) [] hv
      have h:=join (join (join h0 h1) h2) h3
      convert h using 1 <;> first | rfl | (simp only [readTime,List.length_nil];omega)
    | succ n=>
      have h0:=count_succ part w (row word (tape words)) n
      have h1:=tag_row part false w
        (SemiprimeSourceHistogramKeyBits.frame (signed word)
          (SemiprimeSourceHistogramKeyBits.frame word.denominator (tape words))) (unary n)
      have h2:=fields_run part false w word (tape words) (unary n) hn hd hs hv
      have h3:=skip_run part w word (tape words) (unary n) hn hd
      have h4:=ih n
      have h:=join (join (join (join h0 h1) h2) h3) h4
      convert h using 1 <;> first | rfl | (simp only [readTime];omega)
/-- The actual field scan has a uniform linear cap in physical array and actual unary-index bytes. -/
theorem readTime_le (words : List SemiprimeRationalBits.RationalWord) (n : ℕ) :
    readTime words n≤30*((tape words).length+n+1) := by
  induction words generalizing n with
  | nil=>cases n <;> simp only [readTime,tape,List.foldr_nil,List.length_cons,List.length_nil] <;> omega
  | cons word words ih=>
    cases n with
    | zero=>
      change 8*((signed word).length+word.denominator.length)+(tape words).length+21≤_
      change _≤30*((row word (tape words)).length+0+1)
      rw [row_length]
      omega
    | succ n=>
      have hh:=ih n
      change 9*((signed word).length+word.denominator.length)+20+readTime words n≤_
      change _≤30*((row word (tape words)).length+(n+1)+1)
      rw [row_length]
      omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseReadLoop
