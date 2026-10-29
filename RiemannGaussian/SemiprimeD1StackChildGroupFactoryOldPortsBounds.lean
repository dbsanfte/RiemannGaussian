/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsBounds
/-! # Complete actual original-port order source cost
The whole original tape is copied and scanned, every needed first-index query
runs, and real binary answers are reversed, converted to unary, logged and
physically cleared. The computed ordinal VALUE and all old records are paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace S
export SemiprimeD1StackChildGroupFactoryOldPortsSource (copied prepared timeBound)
end S
namespace Loop
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh freshRole orderWords)
end Loop
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end P
namespace Bound
export SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds (queryBudget timeBound_le)
export SemiprimeD1StackChildGroupFactoryOldPortOneBounds (pointBytes)
end Bound
/-- Complete SAME-source order acquisition bound from physical bank and actual occurrence counts. -/
theorem source_time (before:Stack→List Bool) (points:List P.Point) (buckets:List B.Bucket)
    (target:List Bool) (cap H D:Nat) (hc:∀k,(before k).length≤cap)
    (hf:Loop.Fresh before) (hp:(P.records points).length≤cap)
    (hs:before (aux .buckets)=B.records buckets) (ht:before (aux .vertexKey)=target)
    (ha:∀k,before (arithmetic k)=[]) (hbs:(B.records buckets).length≤H)
    (hpoints:∀p∈points,Bound.pointBytes p≤H) (htarget:target.length≤H)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D):
    S.timeBound before points buckets target≤1000000000*
      (cap+points.length*(4*D+2)+3*H+Bound.queryBudget H D buckets.length+D+1)*(points.length+1):=by
  have hcopy:∀k,(S.copied before points k).length≤cap:=by
    intro k
    by_cases h:k=aux .oldReader
    · subst k;exact hp
    · simpa only [S.copied,Function.update_of_ne h] using hc k
  have hf':Loop.Fresh (S.copied before points):=by
    intro j
    have h:Loop.freshRole j≠aux .oldReader:=by fin_cases j <;> decide
    exact (Function.update_of_ne h _ _).trans (hf j)
  have hloop:=Bound.timeBound_le points (S.copied before points) buckets target cap H D hcopy hf' hp
    (by simpa [S.copied,aux] using hs) (by simpa [S.copied,aux] using ht)
    (by intro k;simpa [S.copied,aux,arithmetic] using ha k) hbs hpoints htarget hd
  have hcount:=SemiprimeD1StackChildGroupFactoryOrderBounds.order_count buckets points target
  have hl:∀w∈Loop.orderWords buckets points target,w.length≤2*D:=by
    intro w hw
    have h:=(SemiprimeD1StackChildGroupFactoryOrderBounds.order_word_bounds buckets points target w hw).1
    omega
  have hv:∀w∈Loop.orderWords buckets points target,SemiprimeBitArithmetic.bitValue w≤2*D:=by
    intro w hw
    have h:=(SemiprimeD1StackChildGroupFactoryOrderBounds.order_word_bounds buckets points target w hw).2
    omega
  have hconv:=SemiprimeD1StackChildGroupFactoryPortConvertBounds.timeBound_le true
    (S.prepared before points buckets target) (Loop.orderWords buckets points target) (2*D) rfl hl hv
  have hbank:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length (Loop.orderWords buckets points target) (2*D) hl
  have hlog:=SemiprimeD1StackChildGroupFactoryLeftPortsBounds.port_log_length (Loop.orderWords buckets points target)
  have hconv':SemiprimeD1StackChildGroupFactoryPortConvert.timeBound true
      (S.prepared before points buckets target) (Loop.orderWords buckets points target)≤
      10000*(points.length+1)*(2*D+1):=by
    apply hconv.trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hbank':(SemiprimeD1TensorTapeCodec.vectorBits (Loop.orderWords buckets points target)).length≤
      points.length*(4*D+2)+1:=by nlinarith
  let base:=cap+points.length*(4*D+2)+3*H+Bound.queryBudget H D buckets.length+D+1
  let Q:=base*(points.length+1)
  have hbase:1≤base:=by dsimp only [base];omega
  have hQ:base≤Q:=Nat.le_mul_of_pos_right _ (by omega)
  have hpQ:cap≤Q:= (by dsimp only [base];omega:cap≤base).trans hQ
  have hbankQ:points.length*(4*D+2)+1≤Q:=(by dsimp only [base];omega:points.length*(4*D+2)+1≤base).trans hQ
  have hconvQ:SemiprimeD1StackChildGroupFactoryPortConvert.timeBound true
      (S.prepared before points buckets target) (Loop.orderWords buckets points target)≤20000*Q:=by
    apply hconv'.trans
    have hD:2*D+1≤2*base:=by dsimp only [base];omega
    have h:=Nat.mul_le_mul_left (10000*(points.length+1)) hD
    have he:10000*(points.length+1)*(2*base)=20000*Q:=by dsimp only [Q];ring
    rw [he] at h
    exact h
  have hloopQ:SemiprimeD1StackChildGroupFactoryOldPortsLoop.timeBound points (S.copied before points) buckets target≤10000000*Q:=by
    have he:10000000*base*(points.length+1)=10000000*Q:=by dsimp only [Q];ring
    simpa only [←he] using hloop
  dsimp only [S.timeBound]
  have he:1000000000*(cap+points.length*(4*D+2)+3*H+Bound.queryBudget H D buckets.length+D+1)*
      (points.length+1)=1000000000*Q:=by dsimp only [Q,base];ring
  rw [he]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsBounds
