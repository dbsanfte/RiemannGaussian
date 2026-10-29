/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildAssignmentEquiv

/-! # Computed child assignment positions agree with actual physical endpoints
The original port/placement pairing is retained throughout this proof. Matching
the physical ID determines the exact original typed occurrence and side, so
the global assignment partition can be used with literal packet gather lists.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ChildAssignmentEndpoint
open SemiprimeD1ChildAssignmentEquiv SemiprimeD1ChildPortBijection
open SemiprimeD1ChildPortPullbackCorrectness SemiprimeD1ChildGraph SemiprimeD1ChildActivePorts
noncomputable section

private theorem map_some_filterMap {A : Type*} (xs : List (Option A)) (hn : none ∉ xs) :
    (xs.filterMap id).map some = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : none ∉ xs := fun h => hn (List.mem_cons_of_mem x h)
    cases x with
    | none => exact False.elim (hn List.mem_cons_self)
    | some x =>
      change some x :: (xs.filterMap id).map some = some x :: xs
      exact congrArg (List.cons (some x)) (ih ht)

/-- No unresolved endpoint is discarded: the actual tag cache maps BACK to the
whole actual physical option-link cache in the same order. -/
theorem tags_some (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :
    (tags n F r a arity owner q g).map some = (acquired n F r a arity owner q g).links := by
  change ((SemiprimeD1ChildPortBijection.resolveCache _).value).map some = _
  rw [resolveCache_value]
  exact map_some_filterMap _ (no_missing n F r a arity owner q g)

/-- Every actual child endpoint retains its ORIGINAL paired typed port and placement. -/
theorem endpoint_pair (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (endpoint : Endpoint (n+F))
    (he : endpoint ∈ (acquired n F r a arity owner q g).graph.factors.flatten) :
    ∃ pair ∈ originalPairs n F r a arity owner,
      endpoint = (endpoints owner pair.1 pair.2).1 ∨ endpoint = (endpoints owner pair.1 pair.2).2 := by
  have hm := (graph_perm n F r a arity owner q g).mem_iff.mp he
  rw [endpoints_mask] at hm
  have hf := (List.mem_filter.mp hm).1
  change endpoint ∈ ((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).padding.source.selection.cache.data.metadata.incidences.zip
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements).flatMap
      (fun pair => [(endpoints owner pair.1 pair.2).1,(endpoints owner pair.1 pair.2).2]) at hf
  rw [SemiprimeD1ChildGraphSemantics.original_ports] at hf
  obtain ⟨pair, hp, hmem⟩ := List.mem_flatMap.mp hf
  refine ⟨pair, hp, ?_⟩
  simpa using hmem

/-- Physical ID lookup of an actual endpoint returns its exact original paired
port and preserves BOTH the original vertex and the endpoint side. -/
theorem resolve_endpoint (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (endpoint : Endpoint (n+F))
    (he : endpoint ∈ (acquired n F r a arity owner q g).graph.factors.flatten)
    (tag : Tag arity) (hr : resolve (acquired n F r a arity owner q g).ids endpoint = some tag) :
    linkVertex owner tag = endpoint.vertex ∧ tag.2 = endpoint.side := by
  obtain ⟨pair, hp, horigin⟩ := endpoint_pair n F r a arity owner q g endpoint he
  have hfind : (SemiprimeD1ChildPortPullback.findPort pair.2.edge
      (acquired n F r a arity owner q g).ids).value = some pair.1 := by
    apply findPort_member _ (ids_nodup n F r a arity owner q g)
    rw [ids_value]
    exact List.mem_map.mpr ⟨pair,hp,rfl⟩
  rcases horigin with heq | heq
  · subst endpoint
    change (SemiprimeD1ChildPortPullback.findPort pair.2.edge _).value.map
      (fun port => (port,true)) = some tag at hr
    rw [hfind] at hr
    have ht : (pair.1,true) = tag := Option.some.inj hr
    subst tag
    exact ⟨rfl,rfl⟩
  · subst endpoint
    change (SemiprimeD1ChildPortPullback.findPort pair.2.edge _).value.map
      (fun port => (port,false)) = some tag at hr
    rw [hfind] at hr
    have ht : (pair.1,false) = tag := Option.some.inj hr
    subst tag
    exact ⟨rfl,rfl⟩

/-- The forward child variable bijection is exactly the physically resolved ID
at that SAME actual cached endpoint position, with no permutation advice. -/
theorem childEquiv_resolve (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (j : Fin (scope n F r a arity owner q g)) :
    resolve (acquired n F r a arity owner q g).ids
      ((acquired n F r a arity owner q g).graph.factors.flatten[j.val]) =
      some (childEquiv n F r a arity owner q g j).val := by
  have h := congrArg (fun xs : List (Option (Tag arity)) => xs[j.val]?)
    (tags_some n F r a arity owner q g)
  have htags : j.val < (tags n F r a arity owner q g).length := by rw [tags_length]; exact j.isLt
  have hend : j.val < (acquired n F r a arity owner q g).graph.factors.flatten.length := j.isLt
  have hlinks : (acquired n F r a arity owner q g).links =
      (acquired n F r a arity owner q g).graph.factors.flatten.map
        (resolve (acquired n F r a arity owner q g).ids) :=
    SemiprimeD1ChildPortPullback.pull_value _ _
  rw [hlinks] at h
  simp only [List.getElem?_map,List.getElem?_eq_getElem htags,List.getElem?_eq_getElem hend,
    Option.map_some] at h
  rw [childEquiv_value]
  exact (Option.some.inj h).symm

/-- Actual child variable positions retain the correct original vertex and side. -/
theorem childEquiv_endpoint (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (j : Fin (scope n F r a arity owner q g)) :
    linkVertex owner (childEquiv n F r a arity owner q g j).val =
      ((acquired n F r a arity owner q g).graph.factors.flatten[j.val]).vertex ∧
    (childEquiv n F r a arity owner q g j).val.2 =
      ((acquired n F r a arity owner q g).graph.factors.flatten[j.val]).side :=
  resolve_endpoint n F r a arity owner q g _ (List.getElem_mem j.isLt) _
    (childEquiv_resolve n F r a arity owner q g j)

/-- One common original endpoint assignment, defined by the actual resolved ID cache. -/
def endpointBit (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (bits : Tag arity → Bool) (endpoint : Endpoint (n+F)) : Bool :=
  ((resolve (acquired n F r a arity owner q g).ids endpoint).map bits).getD false

/-- One COMMON original endpoint-bit view for every acquired child group. It
uses the original paired ID bank, never a group-dependent bit supplier. -/
def originalEndpointBit (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (bits : Tag arity → Bool) (endpoint : Endpoint (n+F)) : Bool :=
  ((resolve ((originalPairs n F r a arity owner).map (fun pair => (pair.2.edge,pair.1)))
    endpoint).map bits).getD false

/-- Every actual child reuses EXACTLY the same acquired original ID bank. -/
theorem endpointBit_original (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (bits : Tag arity → Bool) (endpoint : Endpoint (n+F)) :
    endpointBit n F r a arity owner q g bits endpoint =
      originalEndpointBit n F r a arity owner bits endpoint := by
  unfold endpointBit
  rw [ids_value]
  rfl

/-- The original endpoint bit view agrees with the independent ACTUAL child
assignment at every actual cached endpoint, not just as an unlabelled multiset. -/
theorem endpointBit_assignment (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (bits : Tag arity → Bool) (j : Fin (scope n F r a arity owner q g)) :
    endpointBit n F r a arity owner q g bits
      ((acquired n F r a arity owner q g).graph.factors.flatten[j.val]) =
      assignments n F r a arity owner q bits g j := by
  rw [endpointBit,childEquiv_resolve,assignments_value]
  rfl

/-- The COMMON original endpoint-bit assignment is the actual child assignment
at each actual child position. This specializes the all-group packet partition
with one global assignment and preserves every individual occurrence. -/
theorem originalEndpointBit_assignment (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (bits : Tag arity → Bool) (j : Fin (scope n F r a arity owner q g)) :
    originalEndpointBit n F r a arity owner bits
      ((acquired n F r a arity owner q g).graph.factors.flatten[j.val]) =
      assignments n F r a arity owner q bits g j := by
  rw [← endpointBit_original n F r a arity owner q g]
  exact endpointBit_assignment n F r a arity owner q g bits j

end
end RiemannGaussian.SemiprimeD1ChildAssignmentEndpoint
