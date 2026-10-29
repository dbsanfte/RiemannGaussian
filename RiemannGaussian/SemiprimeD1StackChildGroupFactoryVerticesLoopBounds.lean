/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryRates
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesByteBounds
/-! # Whole actual all-vertex loop at a fixed tenth-degree clock
Every physical boundary is bounded by the additive real row potential. The
per-body semantic envelope stays fixed across all vertices, including isolated
vertices and prepared duplicate packets. No child's runtime enters this bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoopBounds
open SemiprimeD1StackChildGroupFactoryRoles
open SemiprimeD1StackChildGroupFactoryVerticesLoop
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready result timeBound)
end Body
namespace BV
export SemiprimeD1StackChildGroupFactoryVertexBodyView (result_other result_key result_ready)
end BV
namespace Bytes
export SemiprimeD1StackChildGroupFactoryVertexByteBounds (rowBytes body_word_le)
end Bytes
namespace Bound
export SemiprimeD1StackChildGroupFactoryVertexBodyBounds (bodyBudget timeBound_le)
end Bound
namespace Rate
export SemiprimeD1StackChildGroupFactoryRates (master bodyBudget_le)
end Rate
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end P
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
/-- A body at the common physical master cap has its fixed ninth-degree clock. -/
theorem body_time (before:Stack→List Bool) (points:List P.Point) (buckets:List B.Bucket) (key:List Bool)
    (S:Nat) (hc:∀k,(before k).length≤Rate.master S) (hr:Body.Ready before)
    (hp:before (aux .oldEndpoints)=P.records points) (hb:before (aux .buckets)=B.records buckets)
    (hk:before (aux .vertexKey)=key) (hK:buckets.length≤S) (hJ:points.length≤S)
    (hD:(buckets.flatMap (fun b=>b.children)).length≤S*S)
    (hG:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤S*S):
    Body.timeBound before points buckets key≤10^40*(S+1)^9:=by
  have hbs:(B.records buckets).length≤Rate.master S:=by rw [←hb];exact hc _
  have hps:(P.records points).length≤Rate.master S:=by rw [←hp];exact hc _
  have hkey:key.length≤Rate.master S:=by rw [←hk];exact hc _
  have h:=Bound.timeBound_le before points buckets key (Rate.master S) (Rate.master S) (S*S) (S*S)
    hc hr hp hb hk hbs hps hkey hD hG
  apply h.trans
  apply le_trans ?_ (Rate.bodyBudget_le S)
  dsimp only [Bound.bodyBudget,SemiprimeD1StackChildGroupFactoryVertexBodyBounds.leftBudget,
    SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds.queryBudget]
  gcongr
/-- Actual row potential bounds every later body without feeding elapsed time into its input size. -/
theorem loop_time (todo:List Bool) (before:Stack→List Bool) (points:List P.Point)
    (buckets:List B.Bucket) (key:List Bool) (cap Q S:Nat)
    (hr:Body.Ready before) (ht:before (aux .vertexTodo)=todo)
    (hp:before (aux .oldEndpoints)=P.records points) (hb:before (aux .buckets)=B.records buckets)
    (hk:before (aux .vertexKey)=key) (hc:∀k,(before k).length≤cap)
    (hrow:∀target,Bytes.rowBytes points buckets target≤Q)
    (hpotential:cap+todo.length*Q≤Rate.master S)
    (hK:buckets.length≤S) (hJ:points.length≤S)
    (hD:(buckets.flatMap (fun b=>b.children)).length≤S*S)
    (hG:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤S*S):
    timeBound todo before points buckets key≤(10^40*(S+1)^9+1)*todo.length+1:=by
  induction todo generalizing before key cap with
  | nil=>simp only [timeBound,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons b todo ih=>
    have hpop:=SemiprimeD1StackChildGroupFactoryVerticesByteBounds.popped_word_le before todo b cap ht hc
    have hready:=popped_ready before todo hr
    have hkey:popped before todo (aux .vertexKey)=key:=by simpa [popped,aux] using hk
    have hpoints:popped before todo (aux .oldEndpoints)=P.records points:=by simpa [popped,aux] using hp
    have hbuckets:popped before todo (aux .buckets)=B.records buckets:=by simpa [popped,aux] using hb
    have hcap:cap≤Rate.master S:=by omega
    have hbody:=body_time (popped before todo) points buckets key S
      (fun k=>(hpop k).trans hcap) hready hpoints hbuckets hkey hK hJ hD hG
    have hbytes:=Bytes.body_word_le (popped before todo) points buckets key hready hkey cap hpop
    let after:=Body.result (popped before todo) points buckets key
    have hafter:∀k,(after k).length≤cap+Q:=by
      intro k;exact (hbytes k).trans (Nat.add_le_add_left (hrow key) cap)
    have ht':after (aux .vertexTodo)=todo:=
      (BV.result_other _ _ _ _ _ todo_protected).trans (Function.update_self _ _ _)
    have hp':after (aux .oldEndpoints)=P.records points:=
      (BV.result_other _ _ _ _ _ points_protected).trans hpoints
    have hb':after (aux .buckets)=B.records buckets:=
      (BV.result_other _ _ _ _ _ buckets_protected).trans hbuckets
    have hk':after (aux .vertexKey)=Inc.successor key:=BV.result_key _ _ _ _
    have hr':Body.Ready after:=BV.result_ready _ _ _ _ hready
    have hpot':cap+Q+todo.length*Q≤Rate.master S:=by simp only [List.length_cons] at hpotential;nlinarith
    have hi:=ih after (Inc.successor key) (cap+Q) hr' ht' hp' hb' hk' hafter hpot'
    simp only [timeBound,List.length_cons]
    dsimp only [after] at hi
    nlinarith
/-- Fixed tenth-degree own clock for all actual consumed markers. -/
theorem loop_time_polynomial (todo:List Bool) (before:Stack→List Bool) (points:List P.Point)
    (buckets:List B.Bucket) (key:List Bool) (cap Q S:Nat)
    (hr:Body.Ready before) (ht:before (aux .vertexTodo)=todo)
    (hp:before (aux .oldEndpoints)=P.records points) (hb:before (aux .buckets)=B.records buckets)
    (hk:before (aux .vertexKey)=key) (hc:∀k,(before k).length≤cap)
    (hrow:∀target,Bytes.rowBytes points buckets target≤Q)
    (hpotential:cap+todo.length*Q≤Rate.master S)
    (hK:buckets.length≤S) (hJ:points.length≤S) (hV:todo.length≤S)
    (hD:(buckets.flatMap (fun b=>b.children)).length≤S*S)
    (hG:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤S*S):
    timeBound todo before points buckets key≤10^42*(S+1)^10:=by
  have h:=loop_time todo before points buckets key cap Q S hr ht hp hb hk hc hrow hpotential hK hJ hD hG
  have hm:(10^40*(S+1)^9+1)*todo.length≤(10^40*(S+1)^9+1)*S:=Nat.mul_le_mul_left _ hV
  have hr:(10^40*(S+1)^9+1)*S+1≤10^42*(S+1)^10:=by ring_nf;omega
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoopBounds
