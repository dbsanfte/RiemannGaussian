/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOperationBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOrderBounds
/-! # Actual first-index search clocks from physical field/visit bounds
The bounds follow actual early stops and EOF scans. Each real node is paid by
its actual primitive source, while generated local-counter widths are bounded
by physical child visits, never by recursive child runtime or binary address value.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSearchBounds
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes tag_visit_time bucket_header_time)
end Op
namespace Count
export SemiprimeD1StackChildGroupFactoryOrderBounds (advance_length inner_length)
end Count
namespace Inner
export SemiprimeD1StackChildGroupFactoryTagInner (timeBound found)
export SemiprimeD1StackChildGroupFactoryTagInnerView (finalPosition)
end Inner
namespace V
export SemiprimeD1StackChildGroupFactoryTagVisitView (hit advance)
end V
namespace Outer
export SemiprimeD1StackChildGroupFactoryTagLoop (timeBound stepTime)
end Outer
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket)
end B
/-- Same-program whole child-vector search, with physical remaining visits paying raw counter growth. -/
theorem inner_time (children:List (E.Endpoint×List Bool)) (target tag position:List Bool) (C L:Nat)
    (hc:∀p∈children,Op.endpointBytes p.1+p.2.length≤C)
    (hp:position.length+2*children.length≤L):
    Inner.timeBound children target tag position≤
      10000*(C+target.length+tag.length+L+1)*(children.length+1):=by
  induction children generalizing position with
  | nil=>simp only [Inner.timeBound,List.length_nil,Nat.zero_add,Nat.mul_one];omega
  | cons p ps ih=>
    have hw:=hc p List.mem_cons_self
    have hr:=Op.tag_visit_time p.1 p.2 target tag position
    have ha:=Count.advance_length p.1 target position
    have hc':∀q∈ps,Op.endpointBytes q.1+q.2.length≤C:=fun q h=>hc q (List.mem_cons_of_mem p h)
    have hp':(V.advance p.1 target position).length+2*ps.length≤L:=by simp only [List.length_cons] at hp;omega
    have ht:=ih (V.advance p.1 target position) hc' hp'
    simp only [List.length_cons] at hp ⊢
    by_cases hh:V.hit p.1 target tag
    · simp only [Inner.timeBound,hh,ite_true,Nat.add_zero]
      nlinarith
    · simp only [Inner.timeBound,hh,ite_false]
      nlinarith
/-- Fixed per-bucket allowance, independent of the actually reached counter word. -/
def bucketBudget (C H D L:Nat) (target tag:List Bool):Nat:=
  1000*H+10000*(C+target.length+tag.length+L+1)*(D+1)+2
/-- The entire nested search pays one real header plus complete child prefix per actual bucket. -/
theorem outer_time (buckets:List B.Bucket) (target tag position:List Bool) (C H D L:Nat)
    (hc:∀p∈buckets.flatMap (fun b=>b.children),Op.endpointBytes p.1+p.2.length≤C)
    (hh:∀b∈buckets,b.packet.length+(SemiprimeD1StackChildGroupFactoryLeftPortsInner.records b.children).length+b.ports.length+1≤H)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D)
    (hp:position.length+2*(buckets.flatMap (fun b=>b.children)).length≤L):
    Outer.timeBound buckets target tag position≤bucketBudget C H D L target tag*(buckets.length+1):=by
  induction buckets generalizing position with
  | nil=>simp only [Outer.timeBound,List.length_nil,Nat.zero_add,Nat.mul_one,bucketBudget];omega
  | cons b bs ih=>
    have hheader:=Op.bucket_header_time b.packet
      (SemiprimeD1StackChildGroupFactoryLeftPortsInner.records b.children) b.ports
    have hhhead:=hh b List.mem_cons_self
    have hchildren:=inner_time b.children target tag position C L
      (fun p h=>hc p (by simp only [List.flatMap_cons,List.mem_append];exact Or.inl h))
      (by simp only [List.flatMap_cons,List.length_append] at hp;omega)
    have hip:=Count.inner_length b.children target tag position
    have ht:=ih (Inner.finalPosition b.children target tag position)
      (fun p h=>hc p (by simp only [List.flatMap_cons,List.mem_append];exact Or.inr h))
      (fun q h=>hh q (List.mem_cons_of_mem b h))
      (by simp only [List.flatMap_cons,List.length_append] at hd;omega)
      (by simp only [List.flatMap_cons,List.length_append] at hp;omega)
    have hlen:b.children.length≤D:=by simp only [List.flatMap_cons,List.length_append] at hd;omega
    have hstep:Outer.stepTime b target tag position≤bucketBudget C H D L target tag:=by
      dsimp only [Outer.stepTime,bucketBudget]
      nlinarith
    simp only [Outer.timeBound,List.length_cons]
    by_cases hf:Inner.found b.children target tag=true
    · simp only [hf,ite_true,Nat.add_zero];nlinarith
    · simp only [hf,Bool.false_eq_true,ite_false];nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSearchBounds
