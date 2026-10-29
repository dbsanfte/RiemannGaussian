/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortBijection

/-! # Cached per-old-vertex port order for eager tensor copies
Indices are computed from the actual materialized pullback, rather than chosen
from a proof of permutation. Typed finite-port comparison and list positions
are native metadata stages; their finite scans are explicitly retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1ChildTableOrder
open SemiprimeD1ChildPortBijection SemiprimeD1ChildPortPullback
open SemiprimeD1ChildPortPullbackCorrectness SemiprimeD1CollisionOriginal

/-- Typed original occurrence and endpoint side, retaining parallel occurrences. -/
abbrev Tag {F : ℕ} (arity : Fin F→ℕ) := ((e : Fin F)×Fin (arity e))×Bool

/-- Literal cached old and child orders plus their computed integer routing map. -/
structure Acquired {F : ℕ} (arity : Fin F→ℕ) where
  /-- Original factor-major endpoint order at this vertex. -/
  old : List (Tag arity)
  /-- Actual child order at this vertex from the resolved cache. -/
  child : List (Tag arity)
  /-- For each original endpoint, its searched position in the child order. -/
  order : List ℕ
  /-- Retained pullback and native finite-list search/control reports. -/
  clock : ℕ

/-- Acquire the routing map by finite equality scans of the actual cached tags. -/
def acquire {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F)) : Acquired arity :=
  let pulled := permutation data
  let all := data.source.padding.source.selection.cache.data.metadata.incidences.product [true,false]
  let old := all.filter (fun t => decide (linkVertex owner t=v))
  let child := pulled.value.filter (fun t => decide (linkVertex owner t=v))
  let order := old.map (fun t => child.idxOf t)
  ⟨old,child,order,pulled.work+6*all.length+6*pulled.value.length+
    old.length*(6*child.length+5)+order.length+10⟩

/-- The routing map has exactly one entry per original local port. -/
theorem order_length {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F)) :
    (acquire owner data v).order.length=(acquire owner data v).old.length := List.length_map _

/-- Membership in the acquired old list includes the actual original vertex. -/
theorem old_vertex {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (t : Tag arity) (ht : t∈(acquire owner data v).old) : linkVertex owner t=v := by
  exact of_decide_eq_true (List.mem_filter.mp ht).2

/-- Every selected original local port is found in the actual child cache. -/
theorem old_mem_child (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F))
    (ha : ((SemiprimeD1ChildActivation.acquire n F r a arity owner q g).bits[v.val]?).getD false=true)
    (t : Tag arity)
    (ht : t∈(acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).old) :
    t∈(acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).child := by
  have hv := old_vertex owner _ v t ht
  apply List.mem_filter.mpr
  refine ⟨?_,by simp only [hv,decide_true]⟩
  apply (permutation_perm n F r a arity owner q g).mem_iff.mpr
  apply (target_mem n F r a arity owner q g t).mpr
  simpa only [activeLink,hv] using ha

/-- Actual computed positions are in range; no inverse/permutation advice is supplied. -/
theorem order_in_range (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F))
    (ha : ((SemiprimeD1ChildActivation.acquire n F r a arity owner q g).bits[v.val]?).getD false=true)
    (i : ℕ) (hi : i∈(acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).order) :
    i<(acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).child.length := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
  exact List.idxOf_lt_length_of_mem (old_mem_child n F r a arity owner q g v ha t ht)

/-- The acquired position reads exactly the original typed port and side. -/
theorem order_reads_tag (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F))
    (ha : ((SemiprimeD1ChildActivation.acquire n F r a arity owner q g).bits[v.val]?).getD false=true)
    (t : Tag arity)
    (ht : t∈(acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).old) :
    let out := acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v
    out.child[out.child.idxOf t]?=some t := by
  exact List.getElem?_idxOf (old_mem_child n F r a arity owner q g v ha t ht)

/-- An inactive old vertex has literally no child port, including isolated vertices. -/
theorem inactive_child_empty (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F))
    (ha : ((SemiprimeD1ChildActivation.acquire n F r a arity owner q g).bits[v.val]?).getD false=false) :
    (acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).child=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro t ht
  have hm := List.mem_filter.mp ht
  have hv : linkVertex owner t=v := of_decide_eq_true hm.2
  have hp := (permutation_perm n F r a arity owner q g).mem_iff.mp hm.1
  have hb := (target_mem n F r a arity owner q g t).mp hp
  simp only [activeLink,hv,ha,Bool.false_eq_true] at hb

/-- The acquired child list has no repeated typed port or side. -/
theorem child_nodup (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F)) :
    (acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).child.Nodup :=
  (permutation_nodup n F r a arity owner q g).filter _

/-- Selected vertices retain precisely their complete original local port list. -/
theorem selected_perm (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F))
    (ha : ((SemiprimeD1ChildActivation.acquire n F r a arity owner q g).bits[v.val]?).getD false=true) :
    (acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).child.Perm
      (acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).old := by
  have hp := (permutation_perm n F r a arity owner q g).filter
    (fun t => decide (linkVertex owner t=v))
  rw [target_filter] at hp
  have hl : (originalPairs n F r a arity owner).map Prod.fst=ports n F a arity := by
    have hh := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a arity owner)
    rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hh
    exact List.map_fst_zip (by omega)
  rw [hl] at hp
  have hfilter : (((ports n F a arity).product [true,false]).filter
      (activeLink owner (SemiprimeD1ChildActivation.acquire n F r a arity owner q g))).filter
      (fun t => decide (linkVertex owner t=v))=
      ((ports n F a arity).product [true,false]).filter
        (fun t => decide (linkVertex owner t=v)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro t _
    by_cases hv : linkVertex owner t=v
    · simp only [hv,decide_true,activeLink,ha,Bool.and_self]
    · simp only [hv,decide_false,Bool.false_and]
  rw [hfilter] at hp
  change ((permutation (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g)).value.filter
    (fun t => decide (linkVertex owner t=v))).Perm _
  change List.Perm _ (((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).padding.source.selection.cache.data.metadata.incidences.product
    [true,false]).filter (fun t => decide (linkVertex owner t=v)))
  rw [SemiprimeD1ChildGraphSemantics.original_ports]
  exact hp

/-- Eager copied active tables have the same degree as their actual parent table. -/
theorem selected_degree (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F))
    (ha : ((SemiprimeD1ChildActivation.acquire n F r a arity owner q g).bits[v.val]?).getD false=true) :
    (acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).child.length=
      (acquire owner (SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g) v).old.length :=
  (selected_perm n F r a arity owner q g v ha).length_eq

end RiemannGaussian.SemiprimeD1ChildTableOrder
