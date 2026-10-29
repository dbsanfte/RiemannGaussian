/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryStructuralByteBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoop
/-! # Additive real byte potential across the entire original-port query loop
Queries really restore their twenty work roles and arithmetic bank. The only
persistent growth is their real ordered binary answer row; original readers
shrink. This avoids feeding a prefix runtime back into later query operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsByteBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace Loop
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh freshRole fresh_step result timeBound atEOF)
end Loop
namespace One
export SemiprimeD1StackChildGroupFactoryOldPortOne (result)
end One
namespace View
export SemiprimeD1StackChildGroupFactoryOldPortOneView
  (result_other result_oldReader result_orderHistory answerWord)
end View
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket)
end B
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end P
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (role)
end Early
/-- Actual early-stop roles are among the fixed twenty restored query roles. -/
theorem early_fresh (j:Fin 11):∃n:Fin 20,Loop.freshRole n=Early.role j:=by
  fin_cases j
  all_goals first
    | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
    | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩
    | exact ⟨8,rfl⟩ | exact ⟨9,rfl⟩ | exact ⟨10,rfl⟩
/-- One actual restored query adds at most its computed binary answer row. -/
theorem one_word_le (before:Stack→List Bool) (buckets:List B.Bucket) (p:P.Point)
    (tail target:List Bool) (cap:Nat) (hc:∀k,(before k).length≤cap)
    (hf:Loop.Fresh before) (ht:tail.length≤cap):
    ∀k,(One.result before buckets p tail target k).length≤
      cap+4*(buckets.flatMap (fun b=>b.children)).length+2:=by
  have hnew:=Loop.fresh_step before buckets p tail target hf
  have ha: (View.answerWord buckets p target).length≤2*(buckets.flatMap (fun b=>b.children)).length:=
    (SemiprimeD1StackChildGroupFactoryOrderBounds.answer_bounds buckets p target).1
  intro k
  by_cases hw:∃j:Fin 20,Loop.freshRole j=k
  · obtain ⟨j,rfl⟩:=hw
    rw [hnew j]
    simp only [List.length_nil]
    omega
  · have hnot:∀j:Fin 20,Loop.freshRole j≠k:=by intro j hj;exact hw ⟨j,hj⟩
    have hearly:∀j:Fin 11,Early.role j≠k:=by
      intro j hj;obtain ⟨n,hn⟩:=early_fresh j;exact hnot n (hn.trans hj)
    by_cases hr:k=aux .oldReader
    · subst k;rw [View.result_oldReader];omega
    · by_cases hh:k=aux .orderHistory
      · subst k
        rw [View.result_orderHistory,List.length_append]
        have hlog:(SemiprimeD1StackChildGroupFactoryWordLog.row (View.answerWord buckets p target)).length≤
            4*(buckets.flatMap (fun b=>b.children)).length+2:=by
          simp only [SemiprimeD1StackChildGroupFactoryWordLog.row,List.length_cons,
            SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
          omega
        have hbefore:=hc (aux .orderHistory)
        split_ifs <;> simp only [List.length_reverse,List.length_nil] <;> omega
      · rw [View.result_other _ _ _ _ _ _ hearly hr
          (Ne.symm (hnot 11)) (Ne.symm (hnot 12)) (Ne.symm (hnot 13)) hh]
        exact (hc k).trans (by omega)
/-- Every old-record suffix is bounded by the original retained old-record tape. -/
theorem records_tail (p:P.Point) (ps:List P.Point):
    (P.records ps).length≤(P.records (p::ps)).length:=by
  simp only [P.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Whole actual loop has only additive answer-row growth across all original records. -/
theorem result_word_le (points:List P.Point) (before:Stack→List Bool) (buckets:List B.Bucket)
    (target:List Bool) (cap:Nat) (hc:∀k,(before k).length≤cap)
    (hf:Loop.Fresh before) (hr:(P.records points).length≤cap):
    ∀k,(Loop.result points before buckets target k).length≤
      cap+points.length*(4*(buckets.flatMap (fun b=>b.children)).length+2):=by
  induction points generalizing before cap with
  | nil=>
    intro k
    simp only [Loop.result,Loop.atEOF,Function.update_apply,List.length_nil,Nat.zero_mul,Nat.add_zero]
    split_ifs
    · simp only [List.length_nil];omega
    · exact hc k
  | cons p ps ih=>
    let Q:=4*(buckets.flatMap (fun b=>b.children)).length+2
    have hs:=one_word_le before buckets p (P.records ps) target cap hc hf ((records_tail p ps).trans hr)
    have hf':=Loop.fresh_step before buckets p (P.records ps) target hf
    have ht: (P.records ps).length≤cap+Q:=((records_tail p ps).trans hr).trans (Nat.le_add_right _ _)
    have h:=ih (One.result before buckets p (P.records ps) target) (cap+Q) hs hf' ht
    intro k
    have hk:=h k
    simp only [Loop.result,List.length_cons]
    dsimp only [Q] at hk
    nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsByteBounds
