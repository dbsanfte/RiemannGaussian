/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeOrders
/-! # Complete chronological ALL-old-vertex unary scope and order streams
The source's real binary counter advances once per physically consumed owner or
factor marker. Every original vertex appears once in numeric order, including
inactive/isolated vertices; no ordering/permutation is an additional input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeStreams
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
open SemiprimeBitArithmetic (bitValue)
namespace Query
export SemiprimeD1StackChildGroupFactoryNativeTagOrder (buckets)
end Query
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (fields)
end Fld
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs)
end Act
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (rows)
end Forward
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (oldPoints frame_tail)
end Code
namespace View
export SemiprimeD1StackChildGroupFactoryVerticesLoopView (scopeRows orderRows)
end View
namespace Inc
export SemiprimeD1StackChildGroupFactoryVertexIncrement (successor)
end Inc
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (result)
end E
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point)
end P
namespace Native
export SemiprimeD1ChildAssignmentEquiv (acquired)
end Native
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Literal old unary port/order tape for actual generated natural ordinals. -/
def unaryTape (ports:List Nat):List Bool:=vectorBits (ports.map (fun id=>List.replicate id true))
/-- Actual original native canonical child scope at one old vertex. -/
def scopeAt (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a) (g:Fin 64) (v:Fin (n+F)):List Bool:=
  unaryTape (SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows
    (SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g)) v)
/-- Actual original native old-port first-index list at one old vertex. -/
def orderAt (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a) (g:Fin 64) (v:Fin (n+F)):List Bool:=
  unaryTape (SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).order
/-- Entire literal scope log with its actual FALSE terminator. -/
theorem scope_rows (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64) (hg:bitValue i.group=g.val)
    (vertices:List (Fin (n+F))) (todo key:List Bool) (start:Nat)
    (hlen:todo.length=vertices.length) (hv:vertices.map Fin.val=List.range' start vertices.length)
    (hk:bitValue key=start):
    View.scopeRows todo (Query.buckets i n F a arity owner q) key++[false]=
      vectorBits (vertices.map (scopeAt n F a arity owner q g)):=by
  induction vertices generalizing todo key start with
  | nil=>
    have ht:todo=[]:=List.eq_nil_of_length_eq_zero hlen
    subst todo
    rfl
  | cons v vs ih=>
    cases todo with
    | nil=>simp only [List.length_nil,List.length_cons] at hlen;omega
    | cons b ts=>
      change v.val::vs.map Fin.val=start::List.range' (start+1) vs.length at hv
      have ht:ts.length=vs.length:=by simp only [List.length_cons] at hlen;omega
      have hvalue:bitValue key=v.val:=hk.trans (List.cons.inj hv).1.symm
      have hrow:=SemiprimeD1StackChildGroupFactoryNativeScopes.unary_original i n F a arity owner q g hg v key hvalue
      have hs:bitValue (Inc.successor key)=start+1:=by
        have hinc:=SemiprimeD1StackChildGroupFactoryCounterBounds.successor_value key
        change bitValue (Inc.successor key)=bitValue key+1 at hinc
        exact hinc.trans (congrArg (fun value=>value+1) hk)
      have htail:=ih ts (Inc.successor key) (start+1) ht (List.cons.inj hv).2 hs
      rw [View.scopeRows,List.append_assoc,htail,hrow]
      change (true::SemiprimeSourceHistogramKeyBits.frame (scopeAt n F a arity owner q g v) [])++_= _
      rw [List.cons_append,←Code.frame_tail]
      rfl
/-- Entire literal order log with the SAME actual numeric old-vertex enumeration and FALSE terminator. -/
theorem order_rows (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64) (hg:bitValue i.group=g.val)
    (vertices:List (Fin (n+F))) (todo key:List Bool) (start:Nat)
    (hlen:todo.length=vertices.length) (hv:vertices.map Fin.val=List.range' start vertices.length)
    (hk:bitValue key=start):
    View.orderRows todo (Code.oldPoints (Forward.rows i a q.val (Act.originalIDs n F a arity owner)
      (Fld.fields n F a arity owner))) (Query.buckets i n F a arity owner q) key++[false]=
      vectorBits (vertices.map (orderAt n F a arity owner q g)):=by
  induction vertices generalizing todo key start with
  | nil=>
    have ht:todo=[]:=List.eq_nil_of_length_eq_zero hlen
    subst todo
    rfl
  | cons v vs ih=>
    cases todo with
    | nil=>simp only [List.length_nil,List.length_cons] at hlen;omega
    | cons b ts=>
      change v.val::vs.map Fin.val=start::List.range' (start+1) vs.length at hv
      have ht:ts.length=vs.length:=by simp only [List.length_cons] at hlen;omega
      have hvalue:bitValue key=v.val:=hk.trans (List.cons.inj hv).1.symm
      have hrow:=SemiprimeD1StackChildGroupFactoryNativeOrders.unary_original i n F a arity owner q g hg v key hvalue
      have hs:bitValue (Inc.successor key)=start+1:=by
        have hinc:=SemiprimeD1StackChildGroupFactoryCounterBounds.successor_value key
        change bitValue (Inc.successor key)=bitValue key+1 at hinc
        exact hinc.trans (congrArg (fun value=>value+1) hk)
      have htail:=ih ts (Inc.successor key) (start+1) ht (List.cons.inj hv).2 hs
      rw [View.orderRows,List.append_assoc,htail,hrow]
      change (true::SemiprimeSourceHistogramKeyBits.frame (orderAt n F a arity owner q g v) [])++_= _
      rw [List.cons_append,←Code.frame_tail]
      rfl
/-- At actual halt the complete scope stream remains in its real retained output tape. -/
theorem result_scopes (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64) (hg:bitValue i.group=g.val)
    (hc:i.owners.length+i.factors.length=n+F):
    E.result i a q.val (Act.originalIDs n F a arity owner)
      (SemiprimeD1StackChildGroupFactoryNativeFields.source n F a arity owner).state.packets
      (Fld.fields n F a arity owner) (aux .leftPorts)=
      vectorBits ((List.finRange (n+F)).map (scopeAt n F a arity owner q g)):=by
  unfold E.result SemiprimeD1StackChildGroupFactorySuffix.result
  rw [SemiprimeD1StackChildGroupFactoryFinish.result_retained _ _ (by decide) (by decide),
    SemiprimeD1StackChildGroupFactoryFinalFrames.result_other _ _ (by decide)]
  change View.scopeRows (i.factors++i.owners) (Query.buckets i n F a arity owner q) []++[false]=_
  exact scope_rows i n F a arity owner q g hg (List.finRange (n+F)) (i.factors++i.owners) [] 0
    (by simp only [List.length_append,List.length_finRange];omega)
    (by simp only [List.map_coe_finRange,List.length_finRange,List.range_eq_range']) rfl
/-- At actual halt the complete order stream aligns with ALL original parent vertices owner-first. -/
theorem result_orders (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64) (hg:bitValue i.group=g.val)
    (hc:i.owners.length+i.factors.length=n+F):
    E.result i a q.val (Act.originalIDs n F a arity owner)
      (SemiprimeD1StackChildGroupFactoryNativeFields.source n F a arity owner).state.packets
      (Fld.fields n F a arity owner) (aux .orders)=
      vectorBits ((List.finRange (n+F)).map (orderAt n F a arity owner q g)):=by
  unfold E.result SemiprimeD1StackChildGroupFactorySuffix.result
  rw [SemiprimeD1StackChildGroupFactoryFinish.result_retained _ _ (by decide) (by decide),
    SemiprimeD1StackChildGroupFactoryFinalFrames.result_other _ _ (by decide)]
  change View.orderRows (i.factors++i.owners) (Code.oldPoints (Forward.rows i a q.val (Act.originalIDs n F a arity owner)
      (Fld.fields n F a arity owner))) (Query.buckets i n F a arity owner q) []++[false]=_
  exact order_rows i n F a arity owner q g hg (List.finRange (n+F)) (i.factors++i.owners) [] 0
    (by simp only [List.length_append,List.length_finRange];omega)
    (by simp only [List.map_coe_finRange,List.length_finRange,List.range_eq_range']) rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeStreams
