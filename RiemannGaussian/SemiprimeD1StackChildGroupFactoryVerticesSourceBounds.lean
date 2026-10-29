/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoopBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSource
/-! # Entire actual all-vertex scope/order source at a fixed polynomial clock
Two actual marker copies and both final real log reversals are included. Real
scope/order row bytes provide a fixed potential, independently of subtree time.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSourceBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace V
export SemiprimeD1StackChildGroupFactoryVerticesSource (copied timeBound result scopeDone loopBank)
end V
namespace Loop
export SemiprimeD1StackChildGroupFactoryVerticesLoop (popped_ready)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryVerticesLoopView (scopeRows orderRows)
end View
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready)
end Body
namespace Bytes
export SemiprimeD1StackChildGroupFactoryVertexByteBounds (rowBytes)
end Bytes
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end P
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
namespace Rate
export SemiprimeD1StackChildGroupFactoryRates (master master_covers_remaining)
end Rate
/-- Both actual chronological logs have only actual emitted-row growth. -/
theorem rows_length (todo:List Bool) (points:List P.Point) (buckets:List B.Bucket) (key:List Bool) (Q:Nat)
    (hq:∀target,Bytes.rowBytes points buckets target≤Q):
    (View.scopeRows todo buckets key).length+(View.orderRows todo points buckets key).length≤todo.length*Q:=by
  induction todo generalizing key with
  | nil=>simp only [View.scopeRows,View.orderRows,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons b todo ih=>
    have hh:=hq key
    have ht:=ih (SemiprimeD1StackChildGroupFactoryVertexIncrement.successor key)
    simp only [View.scopeRows,View.orderRows,List.length_append,List.length_cons]
    dsimp only [Bytes.rowBytes] at hh
    nlinarith
/-- Complete actual marker-copy/filter/query/conversion/log-reversal source clock. -/
theorem timeBound_le (before:Stack→List Bool) (owners factors:List Bool) (points:List P.Point)
    (buckets:List B.Bucket) (key:List Bool) (S:Nat)
    (hc:∀k,(before k).length≤100000000000000*(S+1)^4) (hr:Body.Ready before)
    (hp:before (aux .oldEndpoints)=P.records points) (hb:before (aux .buckets)=B.records buckets)
    (hk:before (aux .vertexKey)=key) (hV:owners.length+factors.length≤S)
    (hK:buckets.length≤S) (hJ:points.length≤S)
    (hrow:∀target,Bytes.rowBytes points buckets target≤100*(S+1)^4)
    (hD:(buckets.flatMap (fun b=>b.children)).length≤S*S)
    (hG:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤S*S):
    V.timeBound before owners factors points buckets key≤10^44*(S+1)^10:=by
  have hbase:S≤100000000000000*(S+1)^4:=by ring_nf;omega
  have hcopy:∀k,(V.copied before owners factors k).length≤100000000000000*(S+1)^4:=by
    intro k
    by_cases h:k=aux .vertexTodo
    · subst k;simp only [V.copied,Function.update_self,List.length_append];omega
    · simpa only [V.copied,Function.update_of_ne h] using hc k
  have htodo:(factors++owners).length≤S:=by simp only [List.length_append];omega
  have hloop:=SemiprimeD1StackChildGroupFactoryVerticesLoopBounds.loop_time_polynomial
    (factors++owners) (V.copied before owners factors) points buckets key
    (100000000000000*(S+1)^4) (100*(S+1)^4) S (Loop.popped_ready _ _ hr) rfl
    (by simpa [V.copied,aux] using hp) (by simpa [V.copied,aux] using hb)
    (by simpa [V.copied,aux] using hk) hcopy hrow
    (Rate.master_covers_remaining S (factors++owners).length htodo) hK hJ htodo hD hG
  have hrows:=rows_length (factors++owners) points buckets key (100*(S+1)^4) hrow
  have hrowtotal:(View.scopeRows (factors++owners) buckets key).length+
      (View.orderRows (factors++owners) points buckets key).length≤S*(100*(S+1)^4):=
    hrows.trans (Nat.mul_le_mul_right _ htodo)
  dsimp only [V.timeBound]
  have he:5*S+10^42*(S+1)^10+2*(S*(100*(S+1)^4))+16≤10^44*(S+1)^10:=by ring_nf;omega
  omega
/-- ALL115 real completed source words stay within additive semantic row bytes. -/
theorem result_word_le (before:Stack→List Bool) (owners factors:List Bool) (points:List P.Point)
    (buckets:List B.Bucket) (key:List Bool) (S:Nat)
    (hc:∀k,(before k).length≤100000000000000*(S+1)^4) (hr:Body.Ready before)
    (hk:before (aux .vertexKey)=key) (hV:owners.length+factors.length≤S)
    (hrow:∀target,Bytes.rowBytes points buckets target≤100*(S+1)^4):
    ∀k,(V.result before owners factors points buckets key k).length≤Rate.master S+1:=by
  have hbase:S≤100000000000000*(S+1)^4:=by ring_nf;omega
  have hcopy:∀k,(V.copied before owners factors k).length≤100000000000000*(S+1)^4:=by
    intro k
    by_cases h:k=aux .vertexTodo
    · subst k;simp only [V.copied,Function.update_self,List.length_append];omega
    · simpa only [V.copied,Function.update_of_ne h] using hc k
  have htodo:(factors++owners).length≤S:=by simp only [List.length_append];omega
  have hloop:=SemiprimeD1StackChildGroupFactoryVerticesByteBounds.result_word_le (factors++owners)
    (V.copied before owners factors) points buckets key (100000000000000*(S+1)^4) (100*(S+1)^4)
    (Loop.popped_ready _ _ hr) rfl (by simpa [V.copied,aux] using hk) hcopy hrow
  have hpot:=Rate.master_covers_remaining S (factors++owners).length htodo
  have hrows:=rows_length (factors++owners) points buckets key (100*(S+1)^4) hrow
  intro k
  have hl:(V.loopBank before owners factors points buckets key k).length≤Rate.master S:=
    (hloop k).trans hpot
  dsimp only [V.result,V.scopeDone]
  simp only [Function.update_apply]
  split_ifs <;> (try simp only [List.length_append,List.length_cons,List.length_nil]) <;> omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSourceBounds
