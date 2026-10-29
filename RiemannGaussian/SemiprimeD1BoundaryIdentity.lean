import RiemannGaussian.SemiprimeD1BoundarySemantics

/-! # Exact variable accounting and the boundary merge identity

No inverse, nonzero assumption, discarded coordinate or supplied contraction
occurs. The finite identity applies to every disjoint pair of vertex sets.
-/
set_option autoImplicit false

namespace RiemannGaussian.SemiprimeD1BoundaryIdentity
open scoped BigOperators
open SemiprimeD1BoundarySemantics
variable {V E R : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [CommSemiring R]

/-- Internal variables split into the two old interiors and the crossing edges. -/
theorem internal_union (g : SemiprimeD1BoundarySemantics.Graph V E) (s t : Finset V) :
    internal g (s ∪ t) = (internal g s ∪ internal g t) ∪ crossing g s t := by
  ext e
  simp only [internal, crossing, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  tauto

omit [DecidableEq E] in
/-- Disjoint selected sets have disjoint old internal variables. -/
theorem internal_disjoint (g : SemiprimeD1BoundarySemantics.Graph V E) (s t : Finset V) (h : Disjoint s t) :
    Disjoint (internal g s) (internal g t) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hl := (Finset.mem_filter.mp he).2.1
  have hr := (Finset.mem_filter.mp hf).2.1
  exact Finset.disjoint_left.mp h hl hr

/-- A crossing edge is in neither old internal variable set. -/
theorem crossing_disjoint (g : SemiprimeD1BoundarySemantics.Graph V E) (s t : Finset V) (h : Disjoint s t) :
    Disjoint (internal g s ∪ internal g t) (crossing g s t) := by
  apply Finset.disjoint_left.mpr
  intro e he hc
  have hl : ¬(g.left e ∈ s ∧ g.left e ∈ t) := fun hh => Finset.disjoint_left.mp h hh.1 hh.2
  have hr : ¬(g.right e ∈ s ∧ g.right e ∈ t) := fun hh => Finset.disjoint_left.mp h hh.1 hh.2
  simp only [internal, crossing, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at he hc
  tauto

/-- The crossing variables are exactly the variables shared by the boundaries. -/
theorem crossing_eq_boundary_inter (g : SemiprimeD1BoundarySemantics.Graph V E) (s t : Finset V) (h : Disjoint s t) :
    crossing g s t = boundary g s ∩ boundary g t := by
  ext e
  have hl : ¬(g.left e ∈ s ∧ g.left e ∈ t) := fun hh => Finset.disjoint_left.mp h hh.1 hh.2
  have hr : ¬(g.right e ∈ s ∧ g.right e ∈ t) := fun hh => Finset.disjoint_left.mp h hh.1 hh.2
  simp only [boundary, incident, internal, crossing, Finset.mem_sdiff, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The retained boundary is precisely the symmetric difference of old boundaries. -/
theorem boundary_union (g : SemiprimeD1BoundarySemantics.Graph V E) (s t : Finset V) (h : Disjoint s t) :
    boundary g (s ∪ t) = (boundary g s \ boundary g t) ∪ (boundary g t \ boundary g s) := by
  ext e
  have hl : ¬(g.left e ∈ s ∧ g.left e ∈ t) := fun hh => Finset.disjoint_left.mp h hh.1 hh.2
  have hr : ¬(g.right e ∈ s ∧ g.right e ∈ t) := fun hh => Finset.disjoint_left.mp h hh.1 hh.2
  simp only [boundary, incident, internal, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit [Fintype E] in
private theorem patch_split (a b c x u v w : Finset E) (hu : u ⊆ a) (hv : v ⊆ b)
    (hw : w ⊆ c) (hac : Disjoint a c) (e : E) (heb : e ∉ b) :
    e ∈ patch ((a ∪ b) ∪ c) x ((u ∪ v) ∪ w) ↔ e ∈ patch a (patch c x w) u := by
  have hn : e ∉ v := fun h => heb (hv h)
  have hd : e ∈ a → e ∉ c := fun ha hc => Finset.disjoint_left.mp hac ha hc
  have hdu : e ∈ u → e ∈ a := fun he => hu he
  have hdw : e ∈ w → e ∈ c := fun he => hw he
  simp only [patch, Finset.mem_union, Finset.mem_sdiff]
  tauto

private theorem product_split (g : SemiprimeD1BoundarySemantics.Graph V E) (f : V → Finset E → R) (hf : Local g f)
    (s t : Finset V) (hst : Disjoint s t) (x u v w : Finset E)
    (hu : u ⊆ internal g s) (hv : v ⊆ internal g t) (hw : w ⊆ crossing g s t) :
    product f s (patch (internal g (s ∪ t)) x ((u ∪ v) ∪ w)) =
      product f s (patch (internal g s) (patch (crossing g s t) x w) u) := by
  apply product_congr g f hf
  intro e he
  have heb : e ∉ internal g t := by
    intro ht
    have hi := (Finset.mem_filter.mp he).2
    have ht' := (Finset.mem_filter.mp ht).2
    rcases hi with hi | hi
    · exact Finset.disjoint_left.mp hst hi ht'.1
    · exact Finset.disjoint_left.mp hst hi ht'.2
  rw [internal_union]
  exact patch_split _ _ _ _ _ _ _ hu hv hw
    ((Finset.disjoint_union_left.mp (crossing_disjoint g s t hst)).1) e heb

/-- Each union entry is the exact sum of products on its newly internal edges. -/
theorem value_merge (g : SemiprimeD1BoundarySemantics.Graph V E) (f : V → Finset E → R) (hf : Local g f)
    (s t : Finset V) (hst : Disjoint s t) (x : Finset E) :
    value g f (s ∪ t) x = ∑ w ∈ (crossing g s t).powerset,
      value g f s (patch (crossing g s t) x w) *
        value g f t (patch (crossing g s t) x w) := by
  rw [value, internal_union, sum_powerset_union _ _ (crossing_disjoint g s t hst)]
  simp_rw [sum_powerset_union _ _ (internal_disjoint g s t hst)]
  simp_rw [Finset.sum_comm (s := (internal g t).powerset) (t := (crossing g s t).powerset)]
  rw [Finset.sum_comm (s := (internal g s).powerset) (t := (crossing g s t).powerset)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [value, value, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [← internal_union, product_union f s t hst]
  congr 1
  · exact product_split g f hf s t hst x u v w
      (Finset.mem_powerset.mp hu) (Finset.mem_powerset.mp hv) (Finset.mem_powerset.mp hw)
  · have hs := product_split g f hf t s hst.symm x v u w
      (Finset.mem_powerset.mp hv) (Finset.mem_powerset.mp hu)
      (by simpa only [crossing, or_comm] using Finset.mem_powerset.mp hw)
    simpa only [Finset.union_comm, crossing, or_comm] using hs

end RiemannGaussian.SemiprimeD1BoundaryIdentity
