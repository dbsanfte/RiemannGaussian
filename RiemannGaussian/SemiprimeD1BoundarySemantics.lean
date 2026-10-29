import RiemannGaussian.SemiprimeD1TensorNetwork
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Exact boundary tensors for finite two-endpoint networks

These are proof-side finite sums, not runtime entry suppliers. Internal Boolean
variables are enumerated once, even for parallel edges or empty vertex sets.
The executable boundary leaf refines these values from its concrete records.
-/
set_option autoImplicit false

namespace RiemannGaussian.SemiprimeD1BoundarySemantics
open scoped BigOperators

/-- Two distinct endpoints for every individual edge; parallel edges stay distinct. -/
structure Graph (V E : Type*) where
  /-- First endpoint of this occurrence. -/
  left : E → V
  /-- Second endpoint of this occurrence. -/
  right : E → V
  /-- A variable joins distinct vertices. -/
  distinct : ∀ e, left e ≠ right e

section Finite
variable {V E R : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
  [CommSemiring R]

/-- Edges touching at least one selected vertex. -/
def incident (g : Graph V E) (s : Finset V) : Finset E :=
  Finset.univ.filter (fun e => g.left e ∈ s ∨ g.right e ∈ s)

/-- Edges whose two endpoints are both selected. -/
def internal (g : Graph V E) (s : Finset V) : Finset E :=
  Finset.univ.filter (fun e => g.left e ∈ s ∧ g.right e ∈ s)

/-- The variables with exactly one selected endpoint. -/
def boundary (g : Graph V E) (s : Finset V) : Finset E :=
  incident g s \ internal g s

/-- Variables between two disjoint vertex sets, independent of their orientation. -/
def crossing (g : Graph V E) (s t : Finset V) : Finset E :=
  Finset.univ.filter (fun e =>
    (g.left e ∈ s ∧ g.right e ∈ t) ∨ (g.left e ∈ t ∧ g.right e ∈ s))

/-- Replace precisely the indicated variables by their actual TRUE subset. -/
def patch (edges x z : Finset E) : Finset E := (x \ edges) ∪ z

/-- An entry depends only on the variables actually incident to its vertex. -/
def Local (g : Graph V E) (f : V → Finset E → R) : Prop :=
  ∀ v x y, (∀ e, g.left e = v ∨ g.right e = v → (e ∈ x ↔ e ∈ y)) → f v x = f v y

/-- Product of actual vertex entries, including every isolated scalar. -/
def product (f : V → Finset E → R) (s : Finset V) (x : Finset E) : R :=
  ∏ v ∈ s, f v x

/-- Sum only the internal variables; the remaining assignment is retained. -/
def value (g : Graph V E) (f : V → Finset E → R) (s : Finset V) (x : Finset E) : R :=
  ∑ z ∈ (internal g s).powerset, product f s (patch (internal g s) x z)

omit [DecidableEq E] in
/-- Internal variables of an empty group are absent. -/
@[simp] theorem internal_empty (g : Graph V E) : internal g ∅ = ∅ := by
  ext e
  simp [internal]

/-- An empty group contributes multiplicative one, with no Boolean multiplicity. -/
@[simp] theorem value_empty (g : Graph V E) (f : V → Finset E → R) (x : Finset E) :
    value g f ∅ x = 1 := by
  simp [value, product]

omit [DecidableEq E] in
/-- Every selected product respects agreement on its incident variables. -/
theorem product_congr (g : Graph V E) (f : V → Finset E → R) (hf : Local g f)
    (s : Finset V) (x y : Finset E)
    (h : ∀ e ∈ incident g s, e ∈ x ↔ e ∈ y) : product f s x = product f s y := by
  apply Finset.prod_congr rfl
  intro v hv
  apply hf v x y
  intro e he
  apply h e
  simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases he with he | he
  · exact Or.inl (he ▸ hv)
  · exact Or.inr (he ▸ hv)

omit [DecidableEq E] [Fintype E] in
/-- A disjoint pair of vertex products multiplies to the union product. -/
theorem product_union (f : V → Finset E → R) (s t : Finset V)
    (h : Disjoint s t) (x : Finset E) :
    product f (s ∪ t) x = product f s x * product f t x := by
  exact Finset.prod_union h

/-- A boundary entry is independent of every completion away from its boundary. -/
theorem value_congr_boundary (g : Graph V E) (f : V → Finset E → R) (hf : Local g f)
    (s : Finset V) (x y : Finset E)
    (h : ∀ e ∈ boundary g s, e ∈ x ↔ e ∈ y) : value g f s x = value g f s y := by
  apply Finset.sum_congr rfl
  intro z _
  apply product_congr g f hf
  intro e he
  by_cases hi : e ∈ internal g s
  · simp [patch, hi]
  · have hb : e ∈ boundary g s := Finset.mem_sdiff.mpr ⟨he, hi⟩
    simp only [patch, Finset.mem_union, Finset.mem_sdiff, hi, not_false_eq_true, and_true]
    exact or_congr (h e hb) Iff.rfl

/-- TRUE subsets and Boolean assignments correspond without adding variables. -/
def bitsEquiv : Finset E ≃ (E → Bool) where
  toFun z e := decide (e ∈ z)
  invFun bits := Finset.univ.filter (fun e => bits e = true)
  left_inv z := by ext e; simp
  right_inv bits := by
    funext e
    cases he : bits e <;> simp [he]

/-- Summing each TRUE subset once is exactly summing all Boolean assignments. -/
theorem sum_boolean (F : Finset E → R) :
    (∑ z ∈ (Finset.univ : Finset E).powerset, F z) =
      ∑ bits : E → Bool, F (bitsEquiv.symm bits) := by
  classical
  have hp : (Finset.univ : Finset E).powerset = Finset.univ := by
    ext z
    simp
  rw [hp]
  exact (bitsEquiv.symm.sum_comp F).symm

omit [Fintype E] in
/-- TRUE subsets split uniquely across disjoint variable sets. -/
theorem sum_powerset_union (a b : Finset E) (h : Disjoint a b) (F : Finset E → R) :
    (∑ z ∈ (a ∪ b).powerset, F z) =
      ∑ x ∈ a.powerset, ∑ y ∈ b.powerset, F (x ∪ y) := by
  classical
  symm
  rw [← Finset.sum_product a.powerset b.powerset (fun xy : Finset E × Finset E => F (xy.1 ∪ xy.2))]
  apply Finset.sum_bij (fun xy _ => xy.1 ∪ xy.2)
  · intro xy hxy
    simp only [Finset.mem_product, Finset.mem_powerset] at hxy ⊢
    exact Finset.union_subset_union hxy.1 hxy.2
  · intro xy hxy uv huv he
    simp only [Finset.mem_product, Finset.mem_powerset] at hxy huv
    have hd := Finset.disjoint_left.mp h
    apply Prod.ext
    · apply Finset.ext
      intro e
      have hh := Finset.ext_iff.mp he e
      simp only [Finset.mem_union] at hh
      constructor
      · intro hx
        rcases hh.mp (Or.inl hx) with hy | hy
        · exact hy
        · exact False.elim (hd (hxy.1 hx) (huv.2 hy))
      · intro hx
        rcases hh.mpr (Or.inl hx) with hy | hy
        · exact hy
        · exact False.elim (hd (huv.1 hx) (hxy.2 hy))
    · apply Finset.ext
      intro e
      have hh := Finset.ext_iff.mp he e
      simp only [Finset.mem_union] at hh
      constructor
      · intro hx
        rcases hh.mp (Or.inr hx) with hy | hy
        · exact False.elim (hd (huv.1 hy) (hxy.2 hx))
        · exact hy
      · intro hx
        rcases hh.mpr (Or.inr hx) with hy | hy
        · exact False.elim (hd (hxy.1 hy) (huv.2 hx))
        · exact hy
  · intro z hz
    refine ⟨(z ∩ a, z ∩ b), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
    · apply Finset.ext
      intro e
      have hs := Finset.mem_powerset.mp hz
      have hh : e ∈ z → e ∈ a ∨ e ∈ b := fun he => Finset.mem_union.mp (hs he)
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
  · intro xy _
    rfl

end Finite
end RiemannGaussian.SemiprimeD1BoundarySemantics
