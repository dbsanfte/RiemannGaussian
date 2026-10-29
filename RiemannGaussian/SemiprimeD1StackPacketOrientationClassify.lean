/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationCoordinate
/-! # Whole actual coordinate classification and emitted packet fragment
The only branch data are the real comparator output and actual index head.
All lengths, lists and flags below specify that same physical execution.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationClassify
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationRowView SemiprimeD1StackPacketOrientationLog
open SemiprimeD1StackPacketOrientationCoordinate SemiprimeD1StackProcedureTrace
namespace Spec
export SemiprimeD1StackPacketOrientationEncoding (ordered equal low high field chunk slot next)
end Spec
local notation "ctl"=>Label.local
/-- Two actual acquired colour words, in their retained physical left/right directions. -/
def colours (left right:List Bool) (side:Bool):List Bool:=if side then right else left
/-- Fixed linear coordinate cap from actual copies, at most two real comparisons, index pop and nested logger. -/
def stepBound (left right:List Bool):Nat:=1000*(left.length+right.length+1)
/-- Both paid operand copies and the real comparison/answer pop have a fixed linear physical-width cost. -/
theorem compareTime_le (left right:List Bool):
    5*left.length+5*right.length+SemiprimeD1StackWordLessExecution.totalTime left right+10 ≤
      22*(left.length+right.length+1) :=by
  have h:=SemiprimeD1StackWordLessExecution.totalTime_le left right
  omega
/-- Whole actual coordinate: numeric trichotomy, physically consumed tie bit, exact nested packet bytes and complete work cleanup. -/
theorem coordinate_run (originals:Fin 3→List Bool) (readers:Bool→List Bool) (index left right kh sh ko so hi:List Bool):
    ∃t ≤ stepBound left right,Runs program t (ctl (.copyOperand false false))
      (rowView originals readers index (colours left right) kh sh ko so hi) (ctl .leftTag)
      (rowView originals readers (Spec.next left right index) (fun _=>[])
        ((Spec.chunk left right).reverse++kh) (Spec.slot left right index::sh) ko so hi) :=by
  have hf:=compareTime_le left right
  have hb:=compareTime_le right left
  have h0:=compare_row false originals readers index (colours left right) kh sh ko so hi
  simp only [colours,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at h0
  by_cases hl:SemiprimeD1StackWordLessExecution.answer left right=true
  · rw [hl] at h0
    simp only [ite_true] at h0
    have h1:=slot_run true false originals readers index (colours left right) kh sh ko so hi
    have he:=emitTime_le true (colours left right)
    simp only [colours,Bool.false_eq_true,ite_false,ite_true] at he
    have h:=join h0 h1
    refine ⟨_,?_,by simpa [Spec.next,Spec.slot,Spec.chunk,Spec.field,Spec.low,Spec.high,Spec.ordered,Spec.equal,
      pairField,colours,hl] using h⟩
    unfold stepBound
    omega
  · have hlf:=Bool.eq_false_of_not_eq_true hl
    rw [hlf] at h0
    simp only [Bool.false_eq_true,ite_false] at h0
    have h1:=compare_row true originals readers index (colours left right) kh sh ko so hi
    simp only [colours,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at h1
    by_cases hr:SemiprimeD1StackWordLessExecution.answer right left=true
    · rw [hr] at h1
      simp only [ite_true] at h1
      have h2:=slot_run false true originals readers index (colours left right) kh sh ko so hi
      have he:=emitTime_le false (colours left right)
      simp only [colours,Bool.false_eq_true,ite_false,ite_true] at he
      have h:=join (join h0 h1) h2
      refine ⟨_,?_,by simpa [Spec.next,Spec.slot,Spec.chunk,Spec.field,Spec.low,Spec.high,Spec.ordered,Spec.equal,
        pairField,colours,hlf,hr] using h⟩
      unfold stepBound
      omega
    · have hrf:=Bool.eq_false_of_not_eq_true hr
      rw [hrf] at h1
      simp only [Bool.false_eq_true,ite_false] at h1
      have h2:=padding_run originals readers index (colours left right) kh sh ko so hi
      have h3:=slot_run true (index.headD false) originals readers index.tail (colours left right) kh sh ko so hi
      have he:=emitTime_le true (colours left right)
      simp only [colours,Bool.false_eq_true,ite_false,ite_true] at he
      have h:=join (join (join h0 h1) h2) h3
      refine ⟨_,?_,by simpa [Spec.next,Spec.slot,Spec.chunk,Spec.field,Spec.low,Spec.high,Spec.ordered,Spec.equal,
        pairField,colours,hlf,hrf] using h⟩
      unfold stepBound
      omega
end RiemannGaussian.SemiprimeD1StackPacketOrientationClassify
