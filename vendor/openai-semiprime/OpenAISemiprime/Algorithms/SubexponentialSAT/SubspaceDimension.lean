import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.Types

namespace OAI.Algorithms

/-!
# Dimension of the universal fixed subspace

Collecting finitely many linear constraints into the product of their ranges
proves that their common kernel loses at most the sum of their ranks. We apply
this to restrictions of coordinate vectors followed by the map id - M.

All vector spaces in this file are over the same field; the result therefore
applies over the base field, without an extension-degree loss. The numerical
bounds are stated as inequalities of natural numbers with denominators cleared.
-/

namespace SubexponentialSAT.SubspaceDimension

open Module
open scoped BigOperators

section CommonKernel

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Fintype ι] [FiniteDimensional 𝕜 V]
variable {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]

/-- The vectors satisfying every constraint. -/
def commonKernel (A : (i : ι) → V →ₗ[𝕜] W i) : Submodule 𝕜 V :=
  ⨅ i, LinearMap.ker (A i)

omit [Fintype ι] [FiniteDimensional 𝕜 V] in
@[simp] theorem mem_commonKernel (A : (i : ι) → V →ₗ[𝕜] W i) (v : V) :
    v ∈ commonKernel A ↔ ∀ i, A i v = 0 := by
  simp [commonKernel]

/-- Codimension subadditivity, with the codimension written without subtraction.
No disjointness or independence between the constraints is required. -/
theorem finrank_le_commonKernel_add_sum_range
    (A : (i : ι) → V →ₗ[𝕜] W i) :
    finrank 𝕜 V ≤ finrank 𝕜 (commonKernel A) +
      ∑ i, finrank 𝕜 (LinearMap.range (A i)) := by
  let F : V →ₗ[𝕜] ((i : ι) → LinearMap.range (A i)) :=
    LinearMap.pi fun i => (A i).rangeRestrict
  have hker : LinearMap.ker F = commonKernel A := by
    simp only [F, LinearMap.ker_pi, LinearMap.ker_rangeRestrict, commonKernel]
  have hrange := Submodule.finrank_le (LinearMap.range F)
  rw [Module.finrank_pi_fintype] at hrange
  have hdim := F.finrank_range_add_finrank_ker
  rw [hker] at hdim
  omega

/-- The usual natural-number codimension formulation. -/
theorem codim_commonKernel_le_sum_range
    (A : (i : ι) → V →ₗ[𝕜] W i) :
    finrank 𝕜 V - finrank 𝕜 (commonKernel A) ≤
      ∑ i, finrank 𝕜 (LinearMap.range (A i)) := by
  have := finrank_le_commonKernel_add_sum_range A
  omega

end CommonKernel

section Coordinates

variable {𝕜 α ι : Type*} [Field 𝕜] [Fintype ι]
variable (S : Set α) (J : ι → Set α) (hJ : ∀ i, J i ⊆ S)
variable [Fintype S] [∀ i, Fintype (J i)]

/-- Restriction from a supported coordinate space to a smaller coordinate set. -/
def coordinateRestriction (i : ι) : (S → 𝕜) →ₗ[𝕜] (J i → 𝕜) where
  toFun v u := v ⟨u.val, hJ i u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every slot's restricted vector is required to be fixed by its matrix. -/
def coordinateFixedSpace
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) :
    Submodule 𝕜 (S → 𝕜) :=
  commonKernel fun i =>
    (LinearMap.id - M i).comp (coordinateRestriction S J hJ i)

omit [Fintype ι] [Fintype ↑S] [(i : ι) → Fintype ↑(J i)] in
@[simp] theorem mem_coordinateFixedSpace
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) (v : S → 𝕜) :
    v ∈ coordinateFixedSpace S J hJ M ↔
      ∀ i, coordinateRestriction S J hJ i v =
        M i (coordinateRestriction S J hJ i v) := by
  simp [coordinateFixedSpace, sub_eq_zero]

omit [Fintype ι] [Fintype ↑S] in
/-- Applying a coordinate restriction before a constraint cannot increase rank. -/
theorem finrank_range_restricted_le
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) (i : ι) :
    finrank 𝕜 (LinearMap.range
      ((LinearMap.id - M i).comp (coordinateRestriction S J hJ i))) ≤
    finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) :=
  Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- The universal-block dimension bound before inserting the numerical rank
estimate. The ambient dimension is exactly the size of the supported side. -/
theorem card_side_le_finrank_fixed_add_sum_defect
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) :
    Fintype.card S ≤ finrank 𝕜 (coordinateFixedSpace S J hJ M) +
      ∑ i, finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) := by
  have h := finrank_le_commonKernel_add_sum_range fun i =>
    (LinearMap.id - M i).comp (coordinateRestriction S J hJ i)
  rw [Module.finrank_pi] at h
  exact h.trans (Nat.add_le_add_left
    (Finset.sum_le_sum fun i _ => finrank_range_restricted_le S J hJ M i) _)

end Coordinates

section SupportedCoordinates

variable {𝕜 α ι : Type*} [Field 𝕜] [Fintype ι] [Fintype α]
variable (S : Set α) (J : ι → Set α) (hJ : ∀ i, J i ⊆ S)
variable [Fintype S] [∀ i, Fintype (J i)]

/-- Realize the supported coordinate space inside the full coordinate space. -/
noncomputable def extendByZero : (S → 𝕜) →ₗ[𝕜] (α → 𝕜) := by
  classical
  exact
    { toFun := fun v u => if hu : u ∈ S then v ⟨u, hu⟩ else 0
      map_add' := by
        intro v w
        funext u
        by_cases hu : u ∈ S <;> simp [hu]
      map_smul' := by
        intro c v
        funext u
        by_cases hu : u ∈ S <;> simp [hu] }

omit [Fintype α] [Fintype ↑S] in
theorem extendByZero_injective :
    Function.Injective (extendByZero (𝕜 := 𝕜) S) := by
  classical
  intro v w h
  funext u
  have hu := congrFun h u.val
  simpa [extendByZero, u.property] using hu

/-- The actual fixed subspace of full coordinate vectors, supported on S. -/
noncomputable def supportedFixedSpace
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) :
    Submodule 𝕜 (α → 𝕜) :=
  (coordinateFixedSpace S J hJ M).map (extendByZero S)

omit [Fintype ι] [Fintype α] [Fintype ↑S] [(i : ι) → Fintype ↑(J i)] in
theorem finrank_supportedFixedSpace
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) :
    finrank 𝕜 (supportedFixedSpace S J hJ M) =
      finrank 𝕜 (coordinateFixedSpace S J hJ M) :=
  (Submodule.equivMapOfInjective (extendByZero S)
    (extendByZero_injective S) (coordinateFixedSpace S J hJ M)).finrank_eq.symm

omit [Fintype α] [(i : ι) → Fintype ↑(J i)] in
omit [Fintype ι] [Fintype ↑S] in
theorem mem_supportedFixedSpace_iff
    (M : (i : ι) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) (r : α → 𝕜) :
    r ∈ supportedFixedSpace S J hJ M ↔
      (∀ u, u ∉ S → r u = 0) ∧
      ∀ i, (fun u : J i => r u.val) = M i (fun u : J i => r u.val) := by
  classical
  rw [supportedFixedSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    constructor
    · intro u hu
      simp [extendByZero, hu]
    · intro i
      have hi := (mem_coordinateFixedSpace S J hJ M v).mp hv i
      have hext :
          (fun u : J i => extendByZero S v u.val) =
            coordinateRestriction S J hJ i v := by
        funext u
        simp [extendByZero, coordinateRestriction, hJ i u.property]
      rw [hext]
      exact hi
  · rintro ⟨hsupport, hfixed⟩
    refine ⟨fun u : S => r u.val, ?_, ?_⟩
    · apply (mem_coordinateFixedSpace S J hJ M _).mpr
      simpa [coordinateRestriction] using hfixed
    · funext u
      by_cases hu : u ∈ S
      · simp [extendByZero, hu]
      · simp [extendByZero, hu, hsupport u hu]

end SupportedCoordinates

section NumericalBounds

/-- Summing the per-slot loss bound cancels the number of slots. This also
handles zero slots, where the sum is empty. -/
theorem sixteen_mul_sum_le {Δ s : ℕ} (r : Fin Δ → ℕ)
    (hbudget : ∀ i, 16 * Δ * r i ≤ s) :
    16 * ∑ i, r i ≤ s := by
  by_cases hzero : Δ = 0
  · subst Δ
    simp
  · have hpos : 0 < Δ := Nat.pos_of_ne_zero hzero
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbudget i)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum
    apply Nat.le_of_mul_le_mul_left (c := Δ) _ hpos
    nlinarith [hsum]

/-- The stronger 15/16 bound, using only exact natural-number inequalities. -/
theorem fifteen_sixteenths_of_rank_budget {Δ s d : ℕ} (r : Fin Δ → ℕ)
    (hdim : s ≤ d + ∑ i, r i)
    (hbudget : ∀ i, 16 * Δ * r i ≤ s) :
    15 * s ≤ 16 * d := by
  have := sixteen_mul_sum_le r hbudget
  omega

/-- Weakening 15/16 to the 7/8 proportion stated in (5.7). -/
theorem seven_eighths_of_fifteen_sixteenths {s d : ℕ}
    (h : 15 * s ≤ 16 * d) : 7 * s ≤ 8 * d := by
  omega

end NumericalBounds

section UniversalBlock

variable {𝕜 : Type*} [Field 𝕜] {Q Δ : ℕ}

/-- The universal-block subspace K^B(t,g), as full coordinate vectors. -/
noncomputable def universalFixedSpace (t : Fin Q) (g : Bool)
    (M : (i : Fin Δ) →
      (Types.Joint t g i → 𝕜) →ₗ[𝕜] (Types.Joint t g i → 𝕜)) :
    Submodule 𝕜 (Types.UniversalType Q Δ → 𝕜) :=
  supportedFixedSpace (Types.side t g) (Types.joint t g)
    (Types.joint_subset_side t g) M

theorem universalFixedSpace_mem_iff (t : Fin Q) (g : Bool)
    (M : (i : Fin Δ) →
      (Types.Joint t g i → 𝕜) →ₗ[𝕜] (Types.Joint t g i → 𝕜))
    (r : Types.UniversalType Q Δ → 𝕜) :
    r ∈ universalFixedSpace t g M ↔
      (∀ u, u ∉ Types.side t g → r u = 0) ∧
      ∀ i, (fun u : Types.Joint t g i => r u.val) =
        M i (fun u : Types.Joint t g i => r u.val) :=
  mem_supportedFixedSpace_iff _ _ _ _ _

/-- The rank bound |J|/(8Δ), with |J| = |S|/2, gives the stronger 15/16
proportion. It is valid over the base field used to define M. -/
theorem universalFixedSpace_fifteen_sixteenths (t : Fin Q) (g : Bool)
    (M : (i : Fin Δ) →
      (Types.Joint t g i → 𝕜) →ₗ[𝕜] (Types.Joint t g i → 𝕜))
    (hrank : ∀ i, 8 * Δ *
      finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) ≤
        Fintype.card (Types.Joint t g i)) :
    15 * Fintype.card (Types.Side (Δ := Δ) t g) ≤
      16 * finrank 𝕜 (universalFixedSpace t g M) := by
  rw [universalFixedSpace, finrank_supportedFixedSpace]
  apply fifteen_sixteenths_of_rank_budget
    (fun i => finrank 𝕜 (LinearMap.range (LinearMap.id - M i)))
  · exact card_side_le_finrank_fixed_add_sum_defect _ _ _ _
  · intro i
    have h := hrank i
    have hcard := Types.card_side_eq_two_mul_joint t g i
    nlinarith

/-- Equation (5.7), with denominators cleared. -/
theorem universalFixedSpace_seven_eighths (t : Fin Q) (g : Bool)
    (M : (i : Fin Δ) →
      (Types.Joint t g i → 𝕜) →ₗ[𝕜] (Types.Joint t g i → 𝕜))
    (hrank : ∀ i, 8 * Δ *
      finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) ≤
        Fintype.card (Types.Joint t g i)) :
    7 * Fintype.card (Types.Side (Δ := Δ) t g) ≤
      8 * finrank 𝕜 (universalFixedSpace t g M) :=
  seven_eighths_of_fifteen_sixteenths
    (universalFixedSpace_fifteen_sixteenths t g M hrank)

/-- Relative to the entire universal block of size N, the stronger bound is
15 N ≤ 32 dim K. The exact cardinality identities avoid natural division. -/
theorem universalFixedSpace_fifteen_thirtyseconds (t : Fin Q) (g : Bool)
    (M : (i : Fin Δ) →
      (Types.Joint t g i → 𝕜) →ₗ[𝕜] (Types.Joint t g i → 𝕜))
    (hrank : ∀ i, 8 * Δ *
      finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) ≤
        Fintype.card (Types.Joint t g i)) :
    15 * Types.blockSize Q Δ ≤
      32 * finrank 𝕜 (universalFixedSpace t g M) := by
  have h := universalFixedSpace_fifteen_sixteenths t g M hrank
  have hcard := Types.card_full_eq_two_mul_side (Δ := Δ) t g
  rw [Types.card_universalType] at hcard
  dsimp [Types.blockSize]
  omega

/-- The weaker full-block bound used by the packing argument. -/
theorem universalFixedSpace_seven_sixteenths (t : Fin Q) (g : Bool)
    (M : (i : Fin Δ) →
      (Types.Joint t g i → 𝕜) →ₗ[𝕜] (Types.Joint t g i → 𝕜))
    (hrank : ∀ i, 8 * Δ *
      finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) ≤
        Fintype.card (Types.Joint t g i)) :
    7 * Types.blockSize Q Δ ≤
      16 * finrank 𝕜 (universalFixedSpace t g M) := by
  have h := universalFixedSpace_fifteen_thirtyseconds t g M hrank
  omega

end UniversalBlock

end SubexponentialSAT.SubspaceDimension

end OAI.Algorithms
