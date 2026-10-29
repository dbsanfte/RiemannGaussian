/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBody
/-! # Full actual per-vertex restoration and exact two ordered row logs
All twenty query/parser/buffer words and every ordinal tape are ready again.
The original vertex counter advances in binary; all other input/cache words
are retained whenever outside the fixed actual work and output-log images.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryVertexBody
namespace LV
export SemiprimeD1StackChildGroupFactoryLeftPortsSourceView (result_portBank result_portHistory result_vertexHistory)
end LV
namespace OV
export SemiprimeD1StackChildGroupFactoryOldPortsSourceView
  (result_orderBank result_orderHistory result_oldReader result_factorHistory)
end OV
/-- Fixed actual work-image exclusions, entirely proof-side and independent of operand values. -/
structure Protected (k:Stack):Prop where
  child_fields:∀j,Raw.role j≠k
  early_fields:∀j,Early.role j≠k
  endpoint_reader:k≠aux .endpointReader
  outer_reader:k≠aux .outerReader
  old_reader:k≠aux .oldReader
  answer:k≠aux .answerPosition
  local_counter:k≠aux .localPosition
  tag:k≠aux .tagWord
  port_history:k≠aux .portHistory
  order_history:k≠aux .orderHistory
  port_reuse:∀j,Reuse.role false j≠k
  order_reuse:∀j,Reuse.role true j≠k
  vertex_history:k≠aux .vertexHistory
  factor_history:k≠aux .factorHistory
  vertex_key:k≠aux .vertexKey
/-- Every protected physical caller/cache word survives the COMPLETE actual old-vertex source. -/
theorem result_other (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool) (k:Stack)
    (hk:Protected k):result before points buckets target k=before k:=by
  simp only [result,Function.update_of_ne hk.vertex_key]
  rw [OV.result_other _ _ _ _ k hk.early_fields hk.old_reader hk.answer hk.local_counter hk.tag hk.order_history
    hk.order_reuse hk.factor_history]
  exact LV.result_other _ _ _ k hk.child_fields hk.endpoint_reader hk.outer_reader hk.port_history hk.port_reuse hk.vertex_history
/-- The actual old-vertex counter has exactly the real full binary add-one output. -/
theorem result_key (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .vertexKey)=Inc.successor target:=Function.update_self _ _ _
/-- The complete actual body restores the full twenty-role query bank, including the saved-global word. -/
theorem result_fresh (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hr:Ready before):Work.Fresh (result before points buckets target):=by
  have hl:=LV.result_fresh before buckets target hr.work
  have ho:=OV.result_fresh (Left.result before buckets target) points buckets target hl
  intro j
  have hn:Work.freshRole j≠aux .vertexKey:=by fin_cases j <;> decide
  exact (Function.update_of_ne hn _ _).trans (ho j)
/-- The next old vertex receives actual restored data, never a supplied fresh-bank answer. -/
theorem result_ready (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hr:Ready before):Ready (result before points buckets target):=by
  constructor
  · intro j _;exact result_fresh _ _ _ _ hr j
  · intro k
    simpa [result,aux,arithmetic] using old_arithmetic (Left.result before buckets target) points buckets target
      (left_arithmetic before buckets target hr.arithmetic_clean) k
  · intro k
    simpa [result,aux,ordinal] using OV.result_ordinal (Left.result before buckets target) points buckets target k
  · simpa [result,aux] using OV.result_oldReader (Left.result before buckets target) points buckets target
  · have h:Old.result (Left.result before buckets target) points buckets target (aux .portBank)=[]:=
      (OV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro j;fin_cases j <;> decide) (by decide)).trans (LV.result_portBank _ _ _)
    simpa [result,aux] using h
  · have h:Old.result (Left.result before buckets target) points buckets target (aux .portHistory)=[]:=
      (OV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro j;fin_cases j <;> decide) (by decide)).trans (LV.result_portHistory _ _ _)
    simpa [result,aux] using h
  · simpa [result,aux] using OV.result_orderBank (Left.result before buckets target) points buckets target
  · simpa [result,aux] using OV.result_orderHistory (Left.result before buckets target) points buckets target
/-- Every old vertex logs exactly the physically converted unary left scope. -/
theorem result_vertexHistory (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .vertexHistory)=
      (SemiprimeD1StackChildGroupFactoryWordLog.row (SemiprimeD1StackPortOrdinalStream.result
        (SemiprimeD1StackChildGroupFactoryLeftPortsLoop.portWords buckets target))).reverse++before (aux .vertexHistory):=by
  change Old.result (Left.result before buckets target) points buckets target (aux .vertexHistory)=_
  rw [OV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro j;fin_cases j <;> decide) (by decide)]
  exact LV.result_vertexHistory _ _ _
/-- Every old vertex logs exactly the physically converted unary original-port order tape. -/
theorem result_factorHistory (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool):
    result before points buckets target (aux .factorHistory)=
      (SemiprimeD1StackChildGroupFactoryWordLog.row (SemiprimeD1StackPortOrdinalStream.result
        (SemiprimeD1StackChildGroupFactoryOldPortsLoop.orderWords buckets points target))).reverse++before (aux .factorHistory):=by
  change Old.result (Left.result before buckets target) points buckets target (aux .factorHistory)=_
  rw [OV.result_factorHistory,LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide)
    (by decide) (by decide) (by decide) (by intro j;fin_cases j <;> decide) (by decide)]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyView
