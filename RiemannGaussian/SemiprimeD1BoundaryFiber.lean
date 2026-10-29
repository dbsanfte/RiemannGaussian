import RiemannGaussian.SemiprimeD1BoundaryIdentity

/-! Incident-assignment fibres compute exactly the internal-variable boundary sum. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryFiber
open scoped BigOperators
open SemiprimeD1BoundarySemantics
variable {V E R : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [CommSemiring R]

omit [Fintype E] in
theorem sum_fiber (a b x : Finset E) (hd : Disjoint a b) (F : Finset E → R) :
    (∑ z ∈ (a ∪ b).powerset, if z ∩ b = x ∩ b then F z else 0) =
      ∑ z ∈ a.powerset, F (z ∪ (x ∩ b)) := by
  classical
  rw [sum_powerset_union a b hd]
  apply Finset.sum_congr rfl
  intro z hz
  have hza : z ⊆ a := Finset.mem_powerset.mp hz
  have hzb : Disjoint z b := hd.mono_left hza
  have hc : x ∩ b ∈ b.powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
  have hinner : ∀ y ∈ b.powerset, (z ∪ y) ∩ b = y := by
    intro y hy
    have hyb := Finset.mem_powerset.mp hy
    ext e
    have hn : e ∈ z → e ∉ b := fun he hb => Finset.disjoint_left.mp hzb he hb
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨he,hb⟩
      rcases he with he | he
      · exact False.elim (hn he hb)
      · exact he
    · intro he
      exact ⟨Or.inr he,hyb he⟩
  rw [Finset.sum_congr rfl (fun y hy => by rw [hinner y hy])]
  simp [hc]

/-- Summing the actually incident addresses with their retained boundary fixed
is precisely the mathematical boundary tensor. -/
theorem incident_fiber (g : SemiprimeD1BoundarySemantics.Graph V E) (f : V → Finset E → R) (hf : Local g f)
    (s : Finset V) (x : Finset E) :
    (∑ z ∈ (incident g s).powerset,
      if z ∩ boundary g s = x ∩ boundary g s then product f s z else 0) =
      value g f s x := by
  classical
  have hi : internal g s ⊆ incident g s := by
    intro e he
    simp only [internal,incident,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
    exact Or.inl he.1
  have hu : internal g s ∪ boundary g s = incident g s :=
    Finset.union_sdiff_of_subset hi
  have hd : Disjoint (internal g s) (boundary g s) := by
    apply Finset.disjoint_left.mpr
    intro e he hb
    exact (Finset.mem_sdiff.mp hb).2 he
  rw [←hu, sum_fiber _ _ x hd]
  apply Finset.sum_congr rfl
  intro z _
  apply product_congr g f hf
  intro e he
  by_cases h : e ∈ internal g s
  · simp [boundary,patch,h]
  · have hb : e ∈ boundary g s := Finset.mem_sdiff.mpr ⟨he,h⟩
    simp [patch,h,hb,or_comm]

/-- A union-address merge with symmetric-difference output is the exact graph
contraction; shared boundary variables are summed once. -/
theorem boundary_fiber (g : SemiprimeD1BoundarySemantics.Graph V E)
    (f : V → Finset E → R) (hf : Local g f) (s t : Finset V)
    (hst : Disjoint s t) (x : Finset E) :
    (∑ z ∈ (boundary g s ∪ boundary g t).powerset,
      if z ∩ boundary g (s ∪ t) = x ∩ boundary g (s ∪ t) then
        value g f s z * value g f t z else 0) = value g f (s ∪ t) x := by
  classical
  have hc := SemiprimeD1BoundaryIdentity.crossing_eq_boundary_inter g s t hst
  have hb := SemiprimeD1BoundaryIdentity.boundary_union g s t hst
  have hd : Disjoint (crossing g s t) (boundary g (s ∪ t)) := by
    rw [hc,hb]
    apply Finset.disjoint_left.mpr
    intro e he he'
    simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff] at he he'
    tauto
  have hu : crossing g s t ∪ boundary g (s ∪ t) = boundary g s ∪ boundary g t := by
    rw [hc,hb]
    ext e
    simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [←hu,sum_fiber _ _ x hd,SemiprimeD1BoundaryIdentity.value_merge g f hf s t hst]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  all_goals
    apply value_congr_boundary g f hf
    intro e he
    by_cases h : e ∈ crossing g s t
    · have hn : e ∉ boundary g (s ∪ t) := fun he' => Finset.disjoint_left.mp hd h he'
      simp [patch,h,hn]
    · have hbu : e ∈ boundary g (s ∪ t) := by
        have hh : e ∈ crossing g s t ∪ boundary g (s ∪ t) := by
          rw [hu]
          first | exact Finset.mem_union_left _ he | exact Finset.mem_union_right _ he
        exact (Finset.mem_union.mp hh).resolve_left h
      simp [patch,h,hbu,or_comm]

end RiemannGaussian.SemiprimeD1BoundaryFiber
