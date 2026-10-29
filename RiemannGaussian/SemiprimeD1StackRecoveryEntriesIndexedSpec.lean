/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexed
import RiemannGaussian.SemiprimeD1TensorTapeCodec
/-! # Acquired binary ordinal and exact defaulting vector lookup specification
Every natural value here is mathematical interpretation of actual input or
incremented words. The actual program scans only physical vector fields.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedSpec
open SemiprimeBitArithmetic
/-- Exact full raw binary sum actually written by the real increment adder. -/
def increment (word:List Bool):List Bool:=(addBits word [true] false).bits
/-- Actual ordinal increment changes numeric value by one, without unary address materialization. -/
theorem increment_value (word:List Bool):bitValue (increment word)=bitValue word+1:=by
  rw [increment,addBits_correct]
  rfl
/-- Actual raw increment grows by at most two physical cells per scanned field. -/
theorem increment_length (word:List Bool):(increment word).length ≤word.length+2:=by
  change (addBits word [true] false).bits.length ≤word.length+2
  have h:=(addBits_counts word [true] false).2.2.2.2
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at h
  have hm:max word.length 1 ≤word.length+1:=max_le (by omega) (by omega)
  omega
/-- Mathematical view of actual numeric equality and physically scanned fields. -/
def selected (query counter:List Bool):List (List Bool) → List Bool
  | []=>[]
  | word::words=>if bitValue query=bitValue counter then word else selected query (increment counter) words
/-- Real ordinal scan returns the exact original physical payload and EOF default. -/
theorem selected_read (query counter:List Bool) (words:List (List Bool))
    (hc:bitValue counter ≤bitValue query):
    selected query counter words=(words[bitValue query-bitValue counter]?).getD []:=by
  induction words generalizing counter with
  | nil=>rfl
  | cons word words ih=>
    by_cases he:bitValue query=bitValue counter
    · rw [selected,ite_eq_left he]
      simp only [he,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
    · have hn:bitValue (increment counter) ≤bitValue query:=by rw [increment_value];omega
      rw [selected,ite_eq_right he,ih (increment counter) hn,increment_value]
      have hs:bitValue query-bitValue counter=(bitValue query-(bitValue counter+1))+1:=by omega
      conv_rhs=>rw [hs]
      rw [List.getElem?_cons_succ]
/-- Literal empty binary counter selects by the actual numeric query, including high-zero padding. -/
theorem selected_initial (query:List Bool) (words:List (List Bool)):
    selected query [] words=(words[bitValue query]?).getD []:=by
  simpa only [bitValue,Nat.sub_zero] using selected_read query [] words (Nat.zero_le _)
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedSpec
