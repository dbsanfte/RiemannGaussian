/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOneBounds
/-! # Whole actual original-port loop from additive bytes and real nested searches
The acquired cache and original records determine every search. Per-query bank
growth is paid by actual answer rows, never by iterated runtime polynomials.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace One
export SemiprimeD1StackChildGroupFactoryOldPortOne (result timeBound)
end One
namespace V
export SemiprimeD1StackChildGroupFactoryOldPortOneView (result_other)
end V
namespace Loop
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh fresh_step timeBound)
end Loop
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end P
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
namespace Bounds
export SemiprimeD1StackChildGroupFactoryOldPortOneBounds (pointBytes timeBound_le tag_length)
end Bounds
namespace Search
export SemiprimeD1StackChildGroupFactoryTagSearchBounds (bucketBudget outer_time)
end Search
namespace Tag
export SemiprimeD1StackChildGroupFactoryTagLoop (timeBound)
end Tag
namespace Build
export SemiprimeD1StackChildGroupFactoryTagBuild (rawTag)
end Build
/-- Static mathematical allowance for actual nested searches; not a runtime counter or supplier. -/
def queryBudget (H D K:Nat):Nat:=(1000*H+10000*(5*H+2*D+1)*(D+1)+2)*(K+1)
/-- Every actual edge/side query has the same bound from retained physical cache bytes. -/
theorem query_time (buckets:List B.Bucket) (p:P.Point) (target:List Bool) (H D:Nat)
    (hbs:(B.records buckets).length≤H) (hp:Bounds.pointBytes p≤H) (ht:target.length≤H)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D):
    Tag.timeBound buckets target (Build.rawTag p.edge p.side) []≤queryBudget H D buckets.length:=by
  have hc:=fun p hp=>(SemiprimeD1StackChildGroupFactoryStructuralByteBounds.flattened_child_fields buckets p hp).trans hbs
  have hh:=fun b hb=>(SemiprimeD1StackChildGroupFactoryStructuralByteBounds.bucket_fields buckets b hb).trans hbs
  have h:=Search.outer_time buckets target (Build.rawTag p.edge p.side) [] H H D (2*D)
    hc hh hd (by simp only [List.length_nil,Nat.zero_add];omega)
  have htag:=Bounds.tag_length p
  apply h.trans
  dsimp only [Search.bucketBudget,queryBudget]
  gcongr
  omega
/-- All real queries retain the actual cache, vertex key and empty arithmetic bank. -/
theorem step_retained (before:Stack→List Bool) (buckets:List B.Bucket) (p:P.Point) (tail target:List Bool):
    One.result before buckets p tail target (aux .buckets)=before (aux .buckets) ∧
    One.result before buckets p tail target (aux .vertexKey)=before (aux .vertexKey) ∧
    ∀k,One.result before buckets p tail target (arithmetic k)=before (arithmetic k):=by
  constructor
  · exact V.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · exact V.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro k
    exact V.result_other _ _ _ _ _ _
      (by intro j;fin_cases j <;> simp [SemiprimeD1StackChildGroupFactoryTagEarlyClear.role,arithmetic,aux])
      (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
      (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
/-- Whole same-program old-record loop, including every actual failed/missing search and EOF. -/
theorem timeBound_le (points:List P.Point) (before:Stack→List Bool) (buckets:List B.Bucket)
    (target:List Bool) (cap H D:Nat) (hc:∀k,(before k).length≤cap)
    (hf:Loop.Fresh before) (hr:(P.records points).length≤cap)
    (hs:before (aux .buckets)=B.records buckets) (ht:before (aux .vertexKey)=target)
    (ha:∀k,before (arithmetic k)=[]) (hbs:(B.records buckets).length≤H)
    (hp:∀p∈points,Bounds.pointBytes p≤H) (htarget:target.length≤H)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D):
    Loop.timeBound points before buckets target≤10000000*
      (cap+points.length*(4*D+2)+3*H+queryBudget H D buckets.length+D+1)*(points.length+1):=by
  induction points generalizing before cap with
  | nil=>simp only [Loop.timeBound,List.length_nil,Nat.zero_mul,Nat.add_zero,Nat.zero_add,Nat.mul_one];omega
  | cons p ps ih=>
    let Q:=4*D+2
    have htail: (P.records ps).length≤cap:=
      (SemiprimeD1StackChildGroupFactoryOldPortsByteBounds.records_tail p ps).trans hr
    have hstep:=Bounds.timeBound_le before buckets p (P.records ps) target cap D hc htail hf hs ht ha hd
    have hquery:=query_time buckets p target H D hbs (hp p List.mem_cons_self) htarget hd
    have hbytes0:=SemiprimeD1StackChildGroupFactoryOldPortsByteBounds.one_word_le before buckets p
      (P.records ps) target cap hc hf htail
    have hbytes:∀k,(One.result before buckets p (P.records ps) target k).length≤cap+Q:=by
      intro k;exact (hbytes0 k).trans (by dsimp only [Q];omega)
    have hf':=Loop.fresh_step before buckets p (P.records ps) target hf
    have hret:=step_retained before buckets p (P.records ps) target
    have ht': (P.records ps).length≤cap+Q:=htail.trans (Nat.le_add_right _ _)
    have hi:=ih (One.result before buckets p (P.records ps) target) (cap+Q) hbytes hf' ht'
      (hret.1.trans hs) (hret.2.1.trans ht) (fun k=>(hret.2.2 k).trans (ha k))
      (fun q h=>hp q (List.mem_cons_of_mem p h))
    have hh:=hp p List.mem_cons_self
    simp only [Loop.timeBound,List.length_cons]
    dsimp only [Q] at hi
    have he:cap+(4*D+2)+ps.length*(4*D+2)+3*H+queryBudget H D buckets.length+D+1=
      cap+(ps.length+1)*(4*D+2)+3*H+queryBudget H D buckets.length+D+1:=by ring
    rw [he] at hi
    nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds
