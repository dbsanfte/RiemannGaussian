/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedOperators
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedFields
/-! # Full actual binary indexed scan, bounded by physical vector EOF
Both equal and unequal branches follow actual numeric comparator output. The
proof recurses over actual framed words, never over the numeric address value.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedLoop
open SemiprimeD1StackRecoveryEntriesIndexed SemiprimeD1StackRecoveryEntriesIndexedState
open SemiprimeD1StackRecoveryEntriesIndexedPrimitives SemiprimeD1StackRecoveryEntriesIndexedSpec
open SemiprimeD1StackRecoveryEntriesIndexedOperators SemiprimeD1StackRecoveryEntriesIndexedFields
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
/-- Exact own source scan clock: comparisons, materialized fields, binary increments and physical EOF drains. -/
def budget (query counter:List Bool):List (List Bool) → Nat
  | []=>counter.length+3
  | word::words=>(1+compareTime query counter)+
      (if bitValue query=bitValue counter then (8*word.length+8)+((vectorBits words).length+1)+(counter.length+1)
       else (9*word.length+9)+incrementTime counter+budget query (increment counter) words)
/-- Whole actual loop, including both branch-specific payload/control paths and every real return. -/
theorem loop_run (words:List (List Bool)) (cache query counter:List Bool):
    Runs program (budget query counter words) (.local .loop) (view cache query counter (vectorBits words) [])
      (.local .done) (view cache query [] [] (selected query counter words)):=by
  induction words generalizing counter with
  | nil=>exact eof_run cache query counter
  | cons word words ih=>
    have h0:=pop_run (.local .loop) (.local .clearCounter) (.local .clearReader) (.local .query) (aux .reader)
      (view cache query counter (vectorBits (word::words)) []) (true::frame word (vectorBits words)) rfl rfl
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    dsimp only [view,aux] at h0
    rw [update_reader] at h0
    have h1:=compare_run cache query counter (frame word (vectorBits words))
    by_cases he:bitValue query=bitValue counter
    · have hd:decide (bitValue query=bitValue counter)=true:=decide_eq_true he
      rw [hd] at h1
      have h2:=read_run true cache query counter word (vectorBits words)
      have h3:=cleanup_run cache query counter (vectorBits words) word
      have h:=join (join (join h0 h1) h2) h3
      simp only [budget,ite_eq_left he,selected] at ⊢
      convert h using 1 <;> first | rfl | omega
    · have hd:decide (bitValue query=bitValue counter)=false:=decide_eq_false he
      rw [hd] at h1
      have h2:=skip_run cache query counter word (vectorBits words)
      have h3:=increment_run cache query counter (vectorBits words)
      have h4:=ih (increment counter)
      have h:=join (join (join (join h0 h1) h2) h3) h4
      simp only [budget,ite_eq_right he,selected] at ⊢
      convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedLoop
