/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoop
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
/-! # Actual per-vertex bytes grow only by the two emitted rows and binary carry
The bound is a direct projection of the actual restored bank, independent of
any preceding/recursive child's runtime. Iterating it adds row bytes rather
than repeatedly raising an earlier runtime polynomial.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexByteBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready result)
end Body
namespace BV
export SemiprimeD1StackChildGroupFactoryVertexBodyView
  (Protected result_other result_key result_ready result_fresh result_vertexHistory result_factorHistory)
end BV
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (freshRole)
end Work
namespace Points
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point)
end Points
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket portWords)
end Buckets
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (orderWords)
end Old
namespace O
export SemiprimeD1StackPortOrdinalStream (result)
end O
/-- Exact additional actual row bytes plus a conservative two-cell full binary carry. -/
def rowBytes (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool):Nat:=
  (Log.row (O.result (Buckets.portWords buckets target))).length+
    (Log.row (O.result (Old.orderWords buckets points target))).length+2
/-- All physical words after one actual body have only additive emitted-row growth. -/
theorem body_word_le (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket)
    (target:List Bool) (hr:Body.Ready before) (hk:before (aux .vertexKey)=target)
    (cap:Nat) (hc:∀k,(before k).length≤cap):
    ∀k,(Body.result before points buckets target k).length≤cap+rowBytes points buckets target:=by
  have hf:=BV.result_fresh before points buckets target hr
  have hready:=BV.result_ready before points buckets target hr
  have hkey:=SemiprimeD1StackChildGroupFactoryCounterBounds.successor_length target
  have hbefore:(target).length≤cap:=by rw [←hk];exact hc _
  have hv:=BV.result_vertexHistory before points buckets target
  have ho:=BV.result_factorHistory before points buckets target
  intro k
  rcases k with k|k|k|k|k|k
  · rw [BV.result_other _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> simp [SemiprimeD1StackChildGroupFactoryChildCleanup.role,SemiprimeD1StackChildGroupFactoryTagEarlyClear.role,SemiprimeD1StackChildGroupFactoryPortReuse.role,SemiprimeD1StackChildGroupFactoryPortReuse.bankRole,aux,ordinal]) | simp [aux])]
    exact (hc _).trans (Nat.le_add_right _ _)
  · rw [BV.result_other _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> simp [SemiprimeD1StackChildGroupFactoryChildCleanup.role,SemiprimeD1StackChildGroupFactoryTagEarlyClear.role,SemiprimeD1StackChildGroupFactoryPortReuse.role,SemiprimeD1StackChildGroupFactoryPortReuse.bankRole,aux,ordinal]) | simp [aux])]
    exact (hc _).trans (Nat.le_add_right _ _)
  · change (Body.result before points buckets target (arithmetic k)).length≤_
    rw [hready.arithmetic_clean k];exact Nat.zero_le _
  · rw [BV.result_other _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> simp [SemiprimeD1StackChildGroupFactoryChildCleanup.role,SemiprimeD1StackChildGroupFactoryTagEarlyClear.role,SemiprimeD1StackChildGroupFactoryPortReuse.role,SemiprimeD1StackChildGroupFactoryPortReuse.bankRole,aux,ordinal]) | simp [aux])]
    exact (hc _).trans (Nat.le_add_right _ _)
  · change (Body.result before points buckets target (ordinal k)).length≤_
    rw [hready.ordinal_clean k];exact Nat.zero_le _
  · cases k with
    | environment=>
      change (Body.result before points buckets target (aux .environment)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | catalogue=>
      change (Body.result before points buckets target (aux .catalogue)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | owners=>
      change (Body.result before points buckets target (aux .owners)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | factors=>
      change (Body.result before points buckets target (aux .factors)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | occurrences=>
      change (Body.result before points buckets target (aux .occurrences)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | placements=>
      change (Body.result before points buckets target (aux .placements)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | packets=>
      change (Body.result before points buckets target (aux .packets)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | colourIndex=>
      change (Body.result before points buckets target (aux .colourIndex)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | group=>
      change (Body.result before points buckets target (aux .group)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | oldAxes=>
      change (Body.result before points buckets target (aux .oldAxes)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | oldPrecision=>
      change (Body.result before points buckets target (aux .oldPrecision)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | jetAxis=>
      change (Body.result before points buckets target (aux .jetAxis)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | newPrecision=>
      change (Body.result before points buckets target (aux .newPrecision)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | activation=>
      change (Body.result before points buckets target (aux .activation)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | activationMap=>
      change (Body.result before points buckets target (aux .activationMap)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | endpoints=>
      change (Body.result before points buckets target (aux .endpoints)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | oldEndpoints=>
      change (Body.result before points buckets target (aux .oldEndpoints)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | buckets=>
      change (Body.result before points buckets target (aux .buckets)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | leftPorts=>
      change (Body.result before points buckets target (aux .leftPorts)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | orders=>
      change (Body.result before points buckets target (aux .orders)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | output=>
      change (Body.result before points buckets target (aux .output)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | vertexTodo=>
      change (Body.result before points buckets target (aux .vertexTodo)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | vertexKey=>
      change (Body.result before points buckets target (aux .vertexKey)).length≤_
      rw [BV.result_key]
      change (SemiprimeD1StackChildGroupFactoryBucketIncrement.successor target).length≤_
      dsimp only [rowBytes];omega
    | selectedID=>
      change (Body.result before points buckets target (aux .selectedID)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | jointKey=>
      change (Body.result before points buckets target (aux .jointKey)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | pairReader=>
      change (Body.result before points buckets target (aux .pairReader)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | placementReader=>
      change (Body.result before points buckets target (aux .placementReader)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | packetReader=>
      change (Body.result before points buckets target (aux .packetReader)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | endpointReader=>
      change (Body.result before points buckets target (aux .endpointReader)).length≤_
      have hz:Body.result before points buckets target (aux .endpointReader)=[]:=by
        simpa [Work.freshRole] using hf (2:Fin 20)
      rw [hz];exact Nat.zero_le _
    | oldReader=>
      change (Body.result before points buckets target (aux .oldReader)).length≤_
      rw [hready.oldReader_empty];exact Nat.zero_le _
    | childReader=>
      change (Body.result before points buckets target (aux .childReader)).length≤_
      have hz:Body.result before points buckets target (aux .childReader)=[]:=by
        simpa [Work.freshRole] using hf (1:Fin 20)
      rw [hz];exact Nat.zero_le _
    | outerReader=>
      change (Body.result before points buckets target (aux .outerReader)).length≤_
      have hz:Body.result before points buckets target (aux .outerReader)=[]:=by
        simpa [Work.freshRole] using hf (0:Fin 20)
      rw [hz];exact Nat.zero_le _
    | ownerKey=>
      change (Body.result before points buckets target (aux .ownerKey)).length≤_
      have hz:Body.result before points buckets target (aux .ownerKey)=[]:=by
        simpa [Work.freshRole] using hf (4:Fin 20)
      rw [hz];exact Nat.zero_le _
    | factorKey=>
      change (Body.result before points buckets target (aux .factorKey)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | sourceKey=>
      change (Body.result before points buckets target (aux .sourceKey)).length≤_
      have hz:Body.result before points buckets target (aux .sourceKey)=[]:=by
        simpa [Work.freshRole] using hf (5:Fin 20)
      rw [hz];exact Nat.zero_le _
    | paddingKey=>
      change (Body.result before points buckets target (aux .paddingKey)).length≤_
      have hz:Body.result before points buckets target (aux .paddingKey)=[]:=by
        simpa [Work.freshRole] using hf (15:Fin 20)
      rw [hz];exact Nat.zero_le _
    | packetKey=>
      change (Body.result before points buckets target (aux .packetKey)).length≤_
      have hz:Body.result before points buckets target (aux .packetKey)=[]:=by
        simpa [Work.freshRole] using hf (14:Fin 20)
      rw [hz];exact Nat.zero_le _
    | slotWord=>
      change (Body.result before points buckets target (aux .slotWord)).length≤_
      have hz:Body.result before points buckets target (aux .slotWord)=[]:=by
        simpa [Work.freshRole] using hf (6:Fin 20)
      rw [hz];exact Nat.zero_le _
    | edgeWord=>
      change (Body.result before points buckets target (aux .edgeWord)).length≤_
      have hz:Body.result before points buckets target (aux .edgeWord)=[]:=by
        simpa [Work.freshRole] using hf (7:Fin 20)
      rw [hz];exact Nat.zero_le _
    | sideWord=>
      change (Body.result before points buckets target (aux .sideWord)).length≤_
      have hz:Body.result before points buckets target (aux .sideWord)=[]:=by
        simpa [Work.freshRole] using hf (8:Fin 20)
      rw [hz];exact Nat.zero_le _
    | validWord=>
      change (Body.result before points buckets target (aux .validWord)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | colourReader=>
      change (Body.result before points buckets target (aux .colourReader)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | colourCursor=>
      change (Body.result before points buckets target (aux .colourCursor)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | colourWord=>
      change (Body.result before points buckets target (aux .colourWord)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | activationHistory=>
      change (Body.result before points buckets target (aux .activationHistory)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | endpointHistory=>
      change (Body.result before points buckets target (aux .endpointHistory)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | oldHistory=>
      change (Body.result before points buckets target (aux .oldHistory)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | bucketHistory=>
      change (Body.result before points buckets target (aux .bucketHistory)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | factorHistory=>
      change (Body.result before points buckets target (aux .factorHistory)).length≤_
      rw [ho,List.length_append,List.length_reverse]
      have h:=hc (aux .factorHistory)
      dsimp only [rowBytes];omega
    | portHistory=>
      change (Body.result before points buckets target (aux .portHistory)).length≤_
      rw [hready.portHistory_empty];exact Nat.zero_le _
    | orderHistory=>
      change (Body.result before points buckets target (aux .orderHistory)).length≤_
      rw [hready.orderHistory_empty];exact Nat.zero_le _
    | vertexHistory=>
      change (Body.result before points buckets target (aux .vertexHistory)).length≤_
      rw [hv,List.length_append,List.length_reverse]
      have h:=hc (aux .vertexHistory)
      dsimp only [rowBytes];omega
    | tagWord=>
      change (Body.result before points buckets target (aux .tagWord)).length≤_
      have hz:Body.result before points buckets target (aux .tagWord)=[]:=by
        simpa [Work.freshRole] using hf (13:Fin 20)
      rw [hz];exact Nat.zero_le _
    | candidateTag=>
      change (Body.result before points buckets target (aux .candidateTag)).length≤_
      have hz:Body.result before points buckets target (aux .candidateTag)=[]:=by
        simpa [Work.freshRole] using hf (10:Fin 20)
      rw [hz];exact Nat.zero_le _
    | localPosition=>
      change (Body.result before points buckets target (aux .localPosition)).length≤_
      have hz:Body.result before points buckets target (aux .localPosition)=[]:=by
        simpa [Work.freshRole] using hf (12:Fin 20)
      rw [hz];exact Nat.zero_le _
    | globalPosition=>
      change (Body.result before points buckets target (aux .globalPosition)).length≤_
      have hz:Body.result before points buckets target (aux .globalPosition)=[]:=by
        simpa [Work.freshRole] using hf (9:Fin 20)
      rw [hz];exact Nat.zero_le _
    | answerPosition=>
      change (Body.result before points buckets target (aux .answerPosition)).length≤_
      have hz:Body.result before points buckets target (aux .answerPosition)=[]:=by
        simpa [Work.freshRole] using hf (11:Fin 20)
      rw [hz];exact Nat.zero_le _
    | frameBuffer=>
      change (Body.result before points buckets target (aux .frameBuffer)).length≤_
      have hz:Body.result before points buckets target (aux .frameBuffer)=[]:=by
        simpa [Work.freshRole] using hf (18:Fin 20)
      rw [hz];exact Nat.zero_le _
    | rowBuffer=>
      change (Body.result before points buckets target (aux .rowBuffer)).length≤_
      have hz:Body.result before points buckets target (aux .rowBuffer)=[]:=by
        simpa [Work.freshRole] using hf (3:Fin 20)
      rw [hz];exact Nat.zero_le _
    | copyScratch=>
      change (Body.result before points buckets target (aux .copyScratch)).length≤_
      have hz:Body.result before points buckets target (aux .copyScratch)=[]:=by
        simpa [Work.freshRole] using hf (19:Fin 20)
      rw [hz];exact Nat.zero_le _
    | sentinelScratch=>
      change (Body.result before points buckets target (aux .sentinelScratch)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | flagScratch=>
      change (Body.result before points buckets target (aux .flagScratch)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | success=>
      change (Body.result before points buckets target (aux .success)).length≤_
      rw [BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
      exact (hc _).trans (Nat.le_add_right _ _)
    | orderBank=>
      change (Body.result before points buckets target (aux .orderBank)).length≤_
      rw [hready.orderBank_empty];exact Nat.zero_le _
    | portBank=>
      change (Body.result before points buckets target (aux .portBank)).length≤_
      rw [hready.portBank_empty];exact Nat.zero_le _
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexByteBounds
