import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.BlockPacking

namespace OAI.Algorithms

/-!
# Coordinate embeddings and packed direct sums

Extension by zero realizes copies of a local subspace on pairwise disjoint
blocks. The actual embedding is injective, so its range has the sum of the
local dimensions. No runtime claim is made for these algebraic constructions.
-/

namespace SubexponentialSAT.DirectSums

open Module
open scoped BigOperators

section Extension

variable {R α β : Type*} [Semiring R]

/-- Extend a coordinate vector by zero along an injective coordinate map. -/
noncomputable def extendLinear (e : β ↪ α) : (β → R) →ₗ[R] (α → R) where
  toFun v := Function.extend e v 0
  map_add' v w := by
    funext a
    by_cases h : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := h
      simp only [e.injective.extend_apply, Pi.add_apply]
    · simp only [Set.mem_range] at h
      simp only [Function.extend_apply' _ _ _ h, Pi.add_apply, Pi.zero_apply, zero_add]
  map_smul' c v := by
    funext a
    by_cases h : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := h
      simp only [e.injective.extend_apply, Pi.smul_apply, RingHom.id_apply]
    · simp only [Set.mem_range] at h
      simp only [Function.extend_apply' _ _ _ h, Pi.smul_apply, Pi.zero_apply,
        smul_zero, RingHom.id_apply]

@[simp] theorem extendLinear_apply (e : β ↪ α) (v : β → R) (b : β) :
    extendLinear e v (e b) = v b :=
  e.injective.extend_apply _ _ _

theorem extendLinear_zero_outside (e : β ↪ α) (v : β → R) (a : α)
    (ha : a ∉ Set.range e) : extendLinear e v a = 0 :=
  Function.extend_apply' _ _ _ ha

theorem extendLinear_injective (e : β ↪ α) :
    Function.Injective (extendLinear (R := R) e) := by
  intro v w h
  funext b
  simpa only [extendLinear_apply] using congrFun h (e b)

/-- In particular, a coordinate embedding preserves the dimension of every
local subspace; extra ambient coordinates are identically zero. -/
theorem finrank_map_extendLinear {K : Type*} [Field K] [Fintype β]
    (e : β ↪ α) (V : Submodule K (β → K)) :
    finrank K (V.map (extendLinear e)) = finrank K V :=
  (Submodule.equivMapOfInjective (extendLinear e)
    (extendLinear_injective e) V).finrank_eq.symm

/-- Extending the row and pairing with an arbitrary ambient vector is the
same as first restricting the vector to the embedded coordinates. -/
theorem sum_extendLinear_mul [Fintype α] [Fintype β]
    (e : β ↪ α) (row : β → R) (v : α → R) :
    (∑ a, extendLinear e row a * v a) = ∑ b, row b * v (e b) := by
  classical
  calc
    (∑ a, extendLinear e row a * v a) =
        ∑ a ∈ Finset.univ.map e, extendLinear e row a * v a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      have hout : a ∉ Set.range e := by
        rintro ⟨b, rfl⟩
        exact ha (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      rw [extendLinear_zero_outside e row a hout, zero_mul]
    _ = ∑ b, row b * v (e b) := by simp

/-- The pairing identity allows the local vector and the row to be over
different fields, through the supplied coefficient homomorphism. -/
theorem sum_extendLinear_mul_hom {K : Type*} [Semiring K]
    [Fintype α] [Fintype β] (e : β ↪ α) (φ : K →+* R)
    (row : β → R) (v : α → K) :
    (∑ a, extendLinear e row a * φ (v a)) = ∑ b, row b * φ (v (e b)) :=
  sum_extendLinear_mul e row (fun a => φ (v a))

end Extension

section Packed

variable {K α τ I : Type*} [Field K]

/-- Forget each local subspace proof and uncurry the block coordinates. -/
def blockCoordinates (V : Submodule K (τ → K)) :
    (I → V) →ₗ[K] (I × τ → K) where
  toFun v z := (v z.1).val z.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Place one vector from the local subspace into each disjoint block. -/
noncomputable def packedLinear (e : I × τ ↪ α) (V : Submodule K (τ → K)) :
    (I → V) →ₗ[K] (α → K) :=
  (extendLinear e).comp (blockCoordinates V)

@[simp] theorem packedLinear_apply (e : I × τ ↪ α) (V : Submodule K (τ → K))
    (v : I → V) (i : I) (u : τ) :
    packedLinear e V v (e (i, u)) = (v i).val u :=
  extendLinear_apply e _ _

theorem packedLinear_zero_outside (e : I × τ ↪ α)
    (V : Submodule K (τ → K)) (v : I → V) (a : α)
    (ha : a ∉ Set.range e) : packedLinear e V v a = 0 :=
  extendLinear_zero_outside e _ a ha

theorem packedLinear_injective (e : I × τ ↪ α) (V : Submodule K (τ → K)) :
    Function.Injective (packedLinear e V) := by
  intro v w h
  funext i
  apply Subtype.ext
  funext u
  simpa only [packedLinear_apply] using congrFun h (e (i, u))

/-- The actual ambient direct sum, represented as a subspace of all coordinates. -/
noncomputable def packedSubspace (e : I × τ ↪ α) (V : Submodule K (τ → K)) :
    Submodule K (α → K) :=
  LinearMap.range (packedLinear e V)

theorem mem_packedSubspace_iff (e : I × τ ↪ α) (V : Submodule K (τ → K))
    (r : α → K) :
    r ∈ packedSubspace e V ↔
      (∀ i, (fun u => r (e (i, u))) ∈ V) ∧
        (∀ a, a ∉ Set.range e → r a = 0) := by
  constructor
  · rintro ⟨v, rfl⟩
    constructor
    · intro i
      simpa only [packedLinear_apply] using (v i).property
    · exact packedLinear_zero_outside e V v
  · rintro ⟨hlocal, hout⟩
    refine ⟨fun i => ⟨fun u => r (e (i, u)), hlocal i⟩, ?_⟩
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨⟨i, u⟩, rfl⟩ := ha
      exact packedLinear_apply e V _ i u
    · rw [packedLinear_zero_outside e V _ a ha, hout a ha]

theorem packed_restriction_mem (e : I × τ ↪ α) (V : Submodule K (τ → K))
    {r : α → K} (hr : r ∈ packedSubspace e V) (i : I) :
    (fun u => r (e (i, u))) ∈ V :=
  ((mem_packedSubspace_iff e V r).mp hr).1 i

theorem packed_zero_outside (e : I × τ ↪ α) (V : Submodule K (τ → K))
    {r : α → K} (hr : r ∈ packedSubspace e V) (a : α)
    (ha : a ∉ Set.range e) : r a = 0 :=
  ((mem_packedSubspace_iff e V r).mp hr).2 a ha

/-- The coordinate embedding of one block inside a packed family. -/
def blockEmbedding (e : I × τ ↪ α) (i : I) : τ ↪ α where
  toFun u := e (i, u)
  inj' _ _ h := congrArg Prod.snd (e.injective h)

/-- A local annihilating row remains annihilating after extension into any
one block. Coefficients may be in a larger ring than the vector space. -/
theorem packed_annihilation {E : Type*} [Semiring E] [Fintype α] [Fintype τ]
    (e : I × τ ↪ α) (V : Submodule K (τ → K)) (i : I)
    (φ : K →+* E) (row : τ → E)
    (hrow : ∀ v ∈ V, (∑ u, row u * φ (v u)) = 0)
    {r : α → K} (hr : r ∈ packedSubspace e V) :
    (∑ a, extendLinear (blockEmbedding e i) row a * φ (r a)) = 0 := by
  rw [sum_extendLinear_mul_hom]
  exact hrow _ (packed_restriction_mem e V hr i)

/-- Explicit linear equivalence with the finite product of local spaces. -/
noncomputable def packedEquiv (e : I × τ ↪ α) (V : Submodule K (τ → K)) :
    (I → V) ≃ₗ[K] packedSubspace e V :=
  LinearEquiv.ofInjective (packedLinear e V) (packedLinear_injective e V)

theorem finrank_packedSubspace [Fintype I] [Fintype τ]
    (e : I × τ ↪ α) (V : Submodule K (τ → K)) :
    finrank K (packedSubspace e V) = Fintype.card I * finrank K V := by
  rw [← (packedEquiv e V).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Transport of a local coordinate support into all packed blocks. -/
def packedSupport (e : I × τ ↪ α) (S : Set τ) : Set α :=
  {a | ∃ i u, u ∈ S ∧ e (i, u) = a}

theorem packedSupport_disjoint (e : I × τ ↪ α) (S0 S1 : Set τ)
    (h : Disjoint S0 S1) : Disjoint (packedSupport e S0) (packedSupport e S1) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨i, u, hu, ha⟩ ⟨j, v, hv, hb⟩
  have huv : u = v := congrArg Prod.snd (e.injective (ha.trans hb.symm))
  exact Set.disjoint_left.mp h hu (huv ▸ hv)

theorem packed_supported (e : I × τ ↪ α) (V : Submodule K (τ → K))
    (S : Set τ) (hV : ∀ v ∈ V, ∀ u, u ∉ S → v u = 0)
    {r : α → K} (hr : r ∈ packedSubspace e V) (a : α)
    (ha : a ∉ packedSupport e S) : r a = 0 := by
  by_cases he : a ∈ Set.range e
  · obtain ⟨⟨i, u⟩, rfl⟩ := he
    have hu : u ∉ S := fun h => ha ⟨i, u, h, rfl⟩
    exact hV _ (packed_restriction_mem e V hr i) u hu
  · exact packed_zero_outside e V hr a he

/-- Finite-set form of the transported support used by the layout interface. -/
def packedSupportFinset [Fintype I] (e : I × τ ↪ α) (S : Finset τ) : Finset α :=
  (Finset.univ.product S).map e

@[simp] theorem mem_packedSupportFinset [Fintype I]
    (e : I × τ ↪ α) (S : Finset τ) (a : α) :
    a ∈ packedSupportFinset e S ↔ ∃ i u, u ∈ S ∧ e (i, u) = a := by
  classical
  simp [packedSupportFinset, Finset.mem_map, Prod.exists]

@[simp] theorem embedded_mem_packedSupportFinset [Fintype I]
    (e : I × τ ↪ α) (S : Finset τ) (i : I) (u : τ) :
    e (i, u) ∈ packedSupportFinset e S ↔ u ∈ S := by
  rw [mem_packedSupportFinset]
  constructor
  · rintro ⟨j, v, hv, h⟩
    have hvu : v = u := congrArg Prod.snd (e.injective h)
    exact hvu ▸ hv
  · intro hu
    exact ⟨i, u, hu, rfl⟩

theorem packedSupportFinset_disjoint [Fintype I]
    (e : I × τ ↪ α) (S0 S1 : Finset τ) (h : Disjoint S0 S1) :
    Disjoint (packedSupportFinset e S0) (packedSupportFinset e S1) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, u, hu, ha⟩ := (mem_packedSupportFinset e S0 a).mp ha
  obtain ⟨j, v, hv, hb⟩ := (mem_packedSupportFinset e S1 a).mp hb
  have huv : u = v := congrArg Prod.snd (e.injective (ha.trans hb.symm))
  exact Finset.disjoint_left.mp h hu (huv ▸ hv)

theorem packed_supported_finset [Fintype I]
    (e : I × τ ↪ α) (V : Submodule K (τ → K)) (S : Finset τ)
    (hV : ∀ v ∈ V, ∀ u, u ∉ S → v u = 0)
    {r : α → K} (hr : r ∈ packedSubspace e V) (a : α)
    (ha : a ∉ packedSupportFinset e S) : r a = 0 := by
  apply packed_supported e V (↑S) hV hr a
  intro h
  exact ha ((mem_packedSupportFinset e S a).mpr h)

/-- The manuscript's full-block proportion and three-quarter coverage imply
the required quarter-dimensional ambient subspace. -/
theorem packed_quarter_dimension [Fintype I] [Fintype τ] [Fintype α]
    (e : I × τ ↪ α) (V : Submodule K (τ → K))
    (hlocal : 7 * Fintype.card τ ≤ 16 * finrank K V)
    (hcover : 3 * Fintype.card α ≤ 4 * (Fintype.card I * Fintype.card τ)) :
    Fintype.card α ≤ 4 * finrank K (packedSubspace e V) := by
  rw [finrank_packedSubspace]
  have hm := Nat.mul_le_mul_left (Fintype.card I) hlocal
  nlinarith

/-- The quantitative bound before weakening it to a quarter. -/
theorem packed_twentyone_sixtyfour_dimension [Fintype I] [Fintype τ] [Fintype α]
    (e : I × τ ↪ α) (V : Submodule K (τ → K))
    (hlocal : 7 * Fintype.card τ ≤ 16 * finrank K V)
    (hcover : 3 * Fintype.card α ≤ 4 * (Fintype.card I * Fintype.card τ)) :
    21 * Fintype.card α ≤ 64 * finrank K (packedSubspace e V) := by
  rw [finrank_packedSubspace]
  have hm := Nat.mul_le_mul_left (Fintype.card I) hlocal
  nlinarith

/-- Direct specialization to the complete blocks constructed by BlockPacking. -/
theorem completeBlocks_quarter_dimension [Fintype τ] [Fintype α]
    {label : α → τ} {b : ℕ} (P : BlockPacking.CompleteBlocks label b)
    (V : Submodule K (τ → K))
    (hlocal : 7 * Fintype.card τ ≤ 16 * finrank K V)
    (hcover : 3 * Fintype.card α ≤ 4 * P.covered.card) :
    Fintype.card α ≤ 4 * finrank K (packedSubspace P.embed V) := by
  apply packed_quarter_dimension P.embed V hlocal
  simpa only [BlockPacking.CompleteBlocks.card_covered, Fintype.card_fin] using hcover

end Packed

end SubexponentialSAT.DirectSums

end OAI.Algorithms
