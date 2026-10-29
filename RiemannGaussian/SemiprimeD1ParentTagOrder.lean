/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetwork
import RiemannGaussian.SemiprimeD1ChildAssignmentEndpoint

/-! # Exact original-tag order of actual cached parent tables
The original two-sided factor-major incidence stream is filtered by the actual
old vertex. Its global occurrence identifiers agree in order with the literal
parent ports; parallel occurrences and isolated vertices are retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ParentTagOrder
open SemiprimeD1TensorNetwork
open SemiprimeD1ChildPortBijection (linkVertex)

/-- Literal original endpoint tags at one unified old vertex. -/
def oldTags {n : ℕ} (rs : Rows n) (v : Fin (n+rs.length)) :=
  ((incidences rs).product [true,false]).filter
    (fun tag => decide (linkVertex (owner rs) tag=v))

/-- The original occurrence identifier ignores only the distinct endpoint side. -/
def tagEdge {n : ℕ} (rs : Rows n) (tag : Incidence rs × Bool) : ℕ := edgeID rs tag.1

/-- True endpoints belong precisely to their original left owner. -/
theorem link_left {n F : ℕ} {arity : Fin F→ℕ}
    (own : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) (v : Fin n) :
    linkVertex own (i,true)=Fin.castAdd F v ↔ own i=v := by
  simp only [linkVertex,ite_true,Fin.ext_iff,Fin.val_castAdd]

/-- False endpoints never belong to a left-namespace vertex. -/
theorem link_false_ne_left {n F : ℕ} {arity : Fin F→ℕ}
    (own : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) (v : Fin n) :
    linkVertex own (i,false)≠Fin.castAdd F v := by
  intro h
  have hv:=congrArg Fin.val h
  change n+i.1.val=v.val at hv
  omega

/-- False endpoints belong precisely to their original right factor. -/
theorem link_right {n F : ℕ} {arity : Fin F→ℕ}
    (own : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) (e : Fin F) :
    linkVertex own (i,false)=Fin.natAdd n e ↔ i.1=e := by
  simp only [linkVertex,Bool.false_eq_true,ite_false,Fin.ext_iff,Fin.val_natAdd]
  omega

/-- True endpoints never belong to a right-namespace vertex. -/
theorem link_true_ne_right {n F : ℕ} {arity : Fin F→ℕ}
    (own : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) (e : Fin F) :
    linkVertex own (i,true)≠Fin.natAdd n e := by
  intro h
  have hv:=congrArg Fin.val h
  change (own i).val=n+e.val at hv
  have hi:=(own i).isLt
  omega

/-- Filtering the literal two-sided stream by a left vertex preserves incidence order. -/
theorem left_filter {n F : ℕ} {arity : Fin F→ℕ}
    (own : ((e : Fin F)×Fin (arity e))→Fin n)
    (xs : List ((e : Fin F)×Fin (arity e))) (v : Fin n) :
    ((xs.product [true,false]).filter
      (fun t => decide (linkVertex own t=Fin.castAdd F v))).map Prod.fst=
        xs.filter (fun i => decide (own i=v)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change (((i,true)::(i,false)::xs.product [true,false]).filter
      (fun t => decide (linkVertex own t=Fin.castAdd F v))).map Prod.fst=_
    by_cases h:own i=v <;> simp [link_left,link_false_ne_left,h,ih]

/-- Filtering the literal two-sided stream by a right vertex preserves incidence order. -/
theorem right_filter {n F : ℕ} {arity : Fin F→ℕ}
    (own : ((e : Fin F)×Fin (arity e))→Fin n)
    (xs : List ((e : Fin F)×Fin (arity e))) (e : Fin F) :
    ((xs.product [true,false]).filter
      (fun t => decide (linkVertex own t=Fin.natAdd n e))).map Prod.fst=
        xs.filter (fun i => decide (i.1=e)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change (((i,true)::(i,false)::xs.product [true,false]).filter
      (fun t => decide (linkVertex own t=Fin.natAdd n e))).map Prod.fst=_
    by_cases h:i.1=e <;> simp [link_right,link_true_ne_right,h,ih]

/-- Exact ordered left ports, not merely cardinal or permutation agreement. -/
theorem oldTags_left {n : ℕ} (rs : Rows n) (v : Fin n) :
    (oldTags rs (Fin.castAdd rs.length v)).map (tagEdge rs)=leftPorts rs v := by
  change (oldTags rs (Fin.castAdd rs.length v)).map (fun t => edgeID rs t.1)=_
  simpa only [oldTags,List.map_map,Function.comp_def,leftPorts] using
    congrArg (List.map (edgeID rs)) (left_filter (owner rs) (incidences rs) v)

/-- Exact ordered right ports, retaining parallel occurrences distinctly. -/
theorem oldTags_right {n : ℕ} (rs : Rows n) (e : Fin rs.length) :
    (oldTags rs (Fin.natAdd n e)).map (tagEdge rs)=rightPorts rs e := by
  change (oldTags rs (Fin.natAdd n e)).map (fun t => edgeID rs t.1)=_
  simpa only [oldTags,List.map_map,Function.comp_def,rightPorts] using
    congrArg (List.map (edgeID rs)) (right_filter (owner rs) (incidences rs) e)

/-- Actual well-formed parent cache agrees with the original tag stream in exact order. -/
theorem oldTags_parent (net : Network) (hw : WellFormed net)
    (v : Fin (net.leftCount+net.rows.length)) :
    (oldTags net.rows v).map (tagEdge net.rows)=
      (SemiprimeD1ChildNetwork.parentVertex net v).ports := by
  refine Fin.addCases (fun u => ?_) (fun e => ?_) v
  · rw [oldTags_left]
    change leftPorts net.rows u=(net.left.toList++net.right.toList)[u.val].ports
    rw [List.getElem_append_left (by simpa only [Vector.length_toList] using u.isLt),Vector.getElem_toList]
    exact (hw.1 u).symm
  · rw [oldTags_right]
    change rightPorts net.rows e=(net.left.toList++net.right.toList)[net.leftCount+e.val].ports
    rw [List.getElem_append_right (by simp only [Vector.length_toList];omega)]
    simp only [Vector.length_toList,Nat.add_sub_cancel_left,Vector.getElem_toList]
    exact (hw.2 e).symm
/-- Fin-indexed reads enumerate an actual list in its literal order. -/
theorem map_fin_reads {A : Type} (xs : List A) :
    (List.finRange xs.length).map (fun j => xs[j.val])=xs := by
  simp only [List.finRange,List.map_ofFn]
  exact List.ofFn_getElem

/-- Actual factor-major incidence owners are exactly the flattened cached rows. -/
theorem incidence_owners {n : ℕ} (rs : Rows n) :
    (incidences rs).map (owner rs)=rs.flatten := by
  simp only [incidences,SemiprimeFiniteEnumerations.indexedIncidences,
    SemiprimeFiniteEnumerations.sigma,SemiprimeFiniteEnumerations.fin,List.map_flatMap,List.map_map,
    Function.comp_def]
  have h (e : Fin rs.length) :
      ((List.finRange (arity rs e)).map (fun j => owner rs ⟨e,j⟩))=rs[e.val] :=
    map_fin_reads _
  simp_rw [h]
  rw [List.flatMap_def]
  rw [map_fin_reads]

/-- Canonical left port counts are actual flattened owner-fibre counts. -/
theorem leftPorts_length {n : ℕ} (rs : Rows n) (v : Fin n) :
    (leftPorts rs v).length=(rs.flatten.filter (fun u => decide (u=v))).length := by
  have h:=congrArg (fun xs : List (Fin n) => (xs.filter (fun u => decide (u=v))).length)
    (incidence_owners rs)
  simpa only [leftPorts,List.length_map,List.filter_map,Function.comp_def] using h

/-- Actual original-input old-table order equals the literal two-sided row stream. -/
theorem acquired_old (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1ChildTableOrder.acquire (owner net.rows)
      (SemiprimeD1ChildPortPullback.acquire net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g) v).old=oldTags net.rows v := by
  change (((SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows)).padding.source.selection.cache.data.metadata.incidences).product
      [true,false] |>.filter (fun t => decide (linkVertex (owner net.rows) t=v)))=_
  rw [SemiprimeD1ChildGraphSemantics.original_ports,
    SemiprimeD1TensorNetworkLayout.original_ports]
  rfl

/-- Actual old-table tags read exactly the well-formed literal parent port ordering. -/
theorem acquired_old_parent (net : Network) (hw : WellFormed net) (r a : ℕ)
    (q : Fin a) (g : Fin r) (v : Fin (net.leftCount+net.rows.length)) :
    ((SemiprimeD1ChildTableOrder.acquire (owner net.rows)
      (SemiprimeD1ChildPortPullback.acquire net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g) v).old).map (tagEdge net.rows)=
      (SemiprimeD1ChildNetwork.parentVertex net v).ports := by
  rw [acquired_old]
  exact oldTags_parent net hw v

/-- No degree advice is needed to align the actual acquired old table. -/
theorem acquired_old_length (net : Network) (hw : WellFormed net) (r a : ℕ)
    (q : Fin a) (g : Fin r) (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1ChildTableOrder.acquire (owner net.rows)
      (SemiprimeD1ChildPortPullback.acquire net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g) v).old.length=
      (SemiprimeD1ChildNetwork.parentVertex net v).ports.length := by
  have h:=congrArg List.length (acquired_old_parent net hw r a q g v)
  simpa only [List.length_map] using h
end RiemannGaussian.SemiprimeD1ParentTagOrder
