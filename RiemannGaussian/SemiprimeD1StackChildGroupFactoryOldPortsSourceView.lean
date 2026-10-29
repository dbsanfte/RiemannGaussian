/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertView
/-! # Full actual ordered-port source reuse boundary for the complete vertex loop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsSourceView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryOldPortsSource
namespace LV
export SemiprimeD1StackChildGroupFactoryOldPortsLoopView (result_fresh result_other result_oldReader)
end LV
namespace PV
export SemiprimeD1StackChildGroupFactoryPortConvertView (result_other result_ordinal result_bank result_history)
end PV
namespace Reuse
export SemiprimeD1StackChildGroupFactoryPortReuse (role)
end Reuse
/-- Every actual caller/cache word outside the real old-query work, reversal and unary log is retained. -/
theorem result_other (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool) (k:Stack)
    (hf:∀j,Early.role j≠k) (ho:k≠aux .oldReader) (ha:k≠aux .answerPosition)
    (hp:k≠aux .localPosition) (ht:k≠aux .tagWord) (hh:k≠aux .orderHistory)
    (hr:∀j,Reuse.role true j≠k) (hlog:k≠aux .factorHistory):
    result before points buckets target k=before k:=by
  rw [result,PV.result_other _ _ _ k hr hlog]
  have hbank:=Ne.symm (hr 0)
  change k≠aux .orderBank at hbank
  simp only [prepared,Function.update_of_ne hbank,Function.update_of_ne hh]
  rw [scanned,LV.result_other _ _ _ _ k hf ho ha hp ht hh]
  exact Function.update_of_ne ho _ _
/-- The real old-source copy preserves all twenty actually fresh query/parser/buffer tapes. -/
theorem copied_fresh (before:Stack→List Bool) (points:List Parse.Point)
    (hf:Loop.Fresh before):Loop.Fresh (copied before points):=by
  intro j
  have hn:Loop.freshRole j≠aux .oldReader:=by fin_cases j <;> decide
  exact (Function.update_of_ne hn _ _).trans (hf j)
/-- The complete actual old-port scan restores every actual query/parser/buffer tape. -/
theorem scanned_fresh (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hf:Loop.Fresh before):Loop.Fresh (scanned before points buckets target):=
  LV.result_fresh _ _ _ _ (copied_fresh _ _ hf)
/-- Actual binary index reversal touches none of those twenty freshly restored tapes. -/
theorem prepared_fresh (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hf:Loop.Fresh before):Loop.Fresh (prepared before points buckets target):=by
  have h:=scanned_fresh before points buckets target hf
  intro j
  have hb:Loop.freshRole j≠aux .orderBank:=by fin_cases j <;> decide
  have hh:Loop.freshRole j≠aux .orderHistory:=by fin_cases j <;> decide
  exact (Function.update_of_ne hb _ _).trans ((Function.update_of_ne hh _ _).trans (h j))
/-- Real ordinal conversion, actual order-tape log and all13 physical drains retain complete twenty-role freshness. -/
theorem result_fresh (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hf:Loop.Fresh before):Loop.Fresh (result before points buckets target):=by
  have h:=prepared_fresh before points buckets target hf
  intro j
  exact (PV.result_other true _ _ (Loop.freshRole j)
    (by intro i;fin_cases i <;> fin_cases j <;> decide) (by fin_cases j <;> decide)).trans (h j)
/-- Every actual ordinal-converter tape is physically clear before the next old vertex. -/
theorem result_ordinal (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool) (k:O.Stack):
    result before points buckets target (ordinal k)=[]:=PV.result_ordinal _ _ _ _
/-- The actually generated binary order bank is physically clear. -/
theorem result_orderBank (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .orderBank)=[]:=PV.result_bank _ _ _
/-- Its real binary-order history was consumed by the actual reversal. -/
theorem result_orderHistory (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .orderHistory)=[]:=by
  rw [result,PV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
  rfl
/-- The original-port reader has really been consumed, including its FALSE/EOF pair. -/
theorem result_oldReader (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .oldReader)=[]:=by
  rw [result,PV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
  change scanned before points buckets target (aux .oldReader)=[]
  exact LV.result_oldReader _ _ _ _
/-- Exactly the actual unary original-order tape row is appended after all real first-index queries. -/
theorem result_factorHistory (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .factorHistory)=
      (SemiprimeD1StackChildGroupFactoryWordLog.row
        (SemiprimeD1StackPortOrdinalStream.result (Loop.orderWords buckets points target))).reverse++before (aux .factorHistory):=by
  have h:=PV.result_history true (prepared before points buckets target) (Loop.orderWords buckets points target)
  change SemiprimeD1StackChildGroupFactoryPortConvert.result true (prepared before points buckets target)
    (Loop.orderWords buckets points target) (aux .factorHistory)=
      (SemiprimeD1StackChildGroupFactoryWordLog.row
        (SemiprimeD1StackPortOrdinalStream.result (Loop.orderWords buckets points target))).reverse++
          prepared before points buckets target (aux .factorHistory) at h
  rw [result,h]
  change _++scanned before points buckets target (aux .factorHistory)=_
  rw [scanned,LV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsSourceView
