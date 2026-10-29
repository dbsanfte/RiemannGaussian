/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisit
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisit
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketHeader
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryWordLog
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
/-! # Own physical-byte bounds for actual child-factory primitive blocks
All estimates concern the same already executed parsers, sentinel comparisons,
full binary adders and preserving loggers. No native operation clock is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOperationBounds
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint payload timeBound)
end E
namespace Inc
export SemiprimeD1StackChildGroupFactoryTagIncrement (successor timeBound)
end Inc
namespace Vertex
export SemiprimeD1StackChildGroupFactoryVertexCompare (timeBound)
end Vertex
namespace Compare
export SemiprimeD1StackChildGroupFactoryTagCompare (timeBound)
end Compare
namespace Tag
export SemiprimeD1StackChildGroupFactoryTagVisit (timeBound candidate cleanupTime)
end Tag
/-- All five raw endpoint fields and a positive fixed byte allowance. -/
def endpointBytes (e:E.Endpoint):Nat:=e.vertex.length+e.packet.length+e.slot.length+e.edge.length+e.side.length+1
/-- The actual six-field emitted child payload is linear in literal raw bytes. -/
theorem child_payload_length (e:E.Endpoint) (global:List Bool):
    (SemiprimeD1StackChildGroupFactoryBucketEmit.payload e global).length≤8*(endpointBytes e+global.length+1):=by
  simp only [SemiprimeD1StackChildGroupFactoryBucketEmit.payload,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_nil,endpointBytes]
  omega
/-- Actual binary increment cost depends on physical width, never its numeric value. -/
theorem increment_time (position:List Bool):Inc.timeBound position≤100*(position.length+1):=by
  have hs:=SemiprimeD1StackChildGroupFactoryCounterBounds.successor_length position
  have hm:max position.length 1≤position.length+1:=by omega
  change (SemiprimeD1StackChildGroupFactoryBucketIncrement.successor position).length≤_ at hs
  unfold Inc.timeBound
  change (5*position.length+4)+1+(3*(max position.length 1+1)+2*
    (SemiprimeD1StackChildGroupFactoryBucketIncrement.successor position).length+3)+
    (position.length+1)+(5*(SemiprimeD1StackChildGroupFactoryBucketIncrement.successor position).length+4)+
    ((SemiprimeD1StackChildGroupFactoryBucketIncrement.successor position).length+1)≤_
  omega
/-- Actual numeric equality includes both operand copies, complete comparison and result pop. -/
theorem vertex_time (query target:List Bool):Vertex.timeBound query target≤20*(query.length+target.length+1):=by
  have h:=SemiprimeD1StackWordEqualExecution.executionTime_le query target
  unfold Vertex.timeBound
  omega
/-- Whole raw tag equality includes the two physical TRUE sentinels and their actual comparison. -/
theorem compare_time (tag candidate:List Bool):Compare.timeBound tag candidate≤30*(tag.length+candidate.length+1):=by
  have h:=SemiprimeD1StackWordEqualExecution.executionTime_le (tag++[true]) (candidate++[true])
  simp only [List.length_append,List.length_cons,List.length_nil] at h
  unfold Compare.timeBound
  omega
/-- Every actual candidate byte comes from copied raw side and actually framed edge. -/
theorem candidate_length (e:E.Endpoint):(Tag.candidate e).length≤3*endpointBytes e:=by
  simp only [Tag.candidate,SemiprimeD1StackChildGroupFactoryTagBuild.rawTag,
    SemiprimeSourceHistogramKeyBits.frame_length,endpointBytes]
  omega
/-- Actual six-field parser, numeric vertex test, sentinel tag test and possible increment/cleanup are all paid. -/
theorem tag_visit_time (e:E.Endpoint) (global target tag position:List Bool):
    Tag.timeBound e global target tag position≤
      10000*(endpointBytes e+global.length+target.length+tag.length+position.length+1):=by
  have hp:=child_payload_length e global
  have hv:=vertex_time e.vertex target
  have hc:=compare_time tag (Tag.candidate e)
  have hi:=increment_time position
  have hcl:=candidate_length e
  unfold Tag.timeBound
  by_cases hvertex:SemiprimeBitArithmetic.bitValue e.vertex=SemiprimeBitArithmetic.bitValue target
  · by_cases htag:tag=Tag.candidate e
    all_goals simp only [hvertex,htag,ite_true,ite_false]
    all_goals simp only [SemiprimeD1StackChildGroupFactoryChildParse.timeBound,
      SemiprimeD1StackChildGroupFactoryTagBuild.timeBound,Tag.cleanupTime,endpointBytes] at hp hv hc hi hcl ⊢
    all_goals first | (rw [htag] at hc;omega) | omega
  · simp only [hvertex,ite_false,SemiprimeD1StackChildGroupFactoryChildParse.timeBound,
      Tag.cleanupTime,endpointBytes] at hp hv ⊢
    omega
/-- Real one-word logger copies only its own bytes and preserves the accumulated destination tail. -/
theorem word_log_time (word:List Bool):SemiprimeD1StackChildGroupFactoryWordLog.timeBound word≤20*(word.length+1):=by
  simp only [SemiprimeD1StackChildGroupFactoryWordLog.timeBound,SemiprimeD1StackChildGroupFactoryWordLog.row,
    List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Acquired three-field bucket-header parser and literal raw packet/right-port drains have linear own cost. -/
theorem bucket_header_time (packet children ports:List Bool):
    SemiprimeD1StackChildGroupFactoryBucketHeader.timeBound packet children ports≤
      1000*(packet.length+children.length+ports.length+1):=by
  simp only [SemiprimeD1StackChildGroupFactoryBucketHeader.timeBound,
    SemiprimeD1StackChildGroupFactoryBucketRecord.payload,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOperationBounds
