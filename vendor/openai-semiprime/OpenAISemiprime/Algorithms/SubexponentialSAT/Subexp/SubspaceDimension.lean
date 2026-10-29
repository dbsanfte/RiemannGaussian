import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubspaceDimension
import OpenAISemiprime.Algorithms.SubexponentialSAT.MulticolorTypes

namespace OAI.Algorithms

/-!
# Multicolor fixed subspaces

The generic common-kernel and zero-extension constructions from the two-color
formalization apply unchanged to an arbitrary number of colors. Here we prove
the parameter-dependent dimension bound: per-slot rank at most τ/Δ of the joint
coordinate set loses at most τ of a side's dimension after all slots.

Every subspace is defined over the same field as the constraint maps.
-/

namespace SubexponentialSAT.Subexp.SubspaceDimension

open Module
open scoped BigOperators

/-- Sum the slot budgets, cancelling the number of slots. The zero-slot case
is included and requires only nonnegativity of the budget. -/
theorem sum_rank_le_of_slot_bounds {Δ : ℕ} (τ : ℝ) (hτ : 0 ≤ τ)
    (s : ℕ) (rank : Fin Δ → ℕ)
    (hslot : ∀ i, (Δ : ℝ) * (rank i : ℝ) ≤ τ * (s : ℝ)) :
    ((∑ i, rank i : ℕ) : ℝ) ≤ τ * (s : ℝ) := by
  by_cases hzero : Δ = 0
  · subst Δ
    simpa using mul_nonneg hτ (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  · have hpos : (0 : ℝ) < Δ := by exact_mod_cast Nat.pos_of_ne_zero hzero
    have hsum :
        (Δ : ℝ) * (∑ i, (rank i : ℝ)) ≤
          (Δ : ℝ) * (τ * (s : ℝ)) := by
      calc
        (Δ : ℝ) * (∑ i, (rank i : ℝ)) =
            ∑ i, (Δ : ℝ) * (rank i : ℝ) := Finset.mul_sum _ _ _
        _ ≤ ∑ _i : Fin Δ, τ * (s : ℝ) :=
          Finset.sum_le_sum fun i _ => hslot i
        _ = (Δ : ℝ) * (τ * (s : ℝ)) := by simp
    have h := le_of_mul_le_mul_left hsum hpos
    simpa only [Nat.cast_sum] using h

section CoordinateSpaces

variable {𝕜 α : Type*} [Field 𝕜] [Fintype α] {Δ : ℕ}
variable (S : Set α) (J : Fin Δ → Set α) (hJ : ∀ i, J i ⊆ S)
variable [Fintype S] [∀ i, Fintype (J i)]

include hJ

omit [Fintype α] in
/-- The joint index set is no larger than the side containing it. -/
theorem card_joint_le_card_side (i : Fin Δ) :
    Fintype.card (J i) ≤ Fintype.card S :=
  Fintype.card_le_of_injective
    (fun u : J i => (⟨u.val, hJ i u.property⟩ : S))
    (by
      intro u v huv
      apply Subtype.ext
      exact congrArg (fun w : S => w.val) huv)

omit [(i : Fin Δ) → Fintype ↑(J i)] in
/-- A supported fixed space has dimension no larger than its side. -/
theorem finrank_supportedFixedSpace_le
    (M : (i : Fin Δ) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜)) :
    finrank 𝕜 (SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M) ≤
      Fintype.card S := by
  rw [SubexponentialSAT.SubspaceDimension.finrank_supportedFixedSpace]
  simpa only [Module.finrank_pi] using
    (Submodule.finrank_le (SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M))

omit [Fintype α] in
/-- All slots together lose at most a τ fraction of the side. The rank
hypothesis is the actual defect-map rank, not a bound on a proxy quantity. -/
theorem supportedFixedSpace_dim_lower
    (M : (i : Fin Δ) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hrank : ∀ i, (Δ : ℝ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℝ) ≤
        τ * (Fintype.card (J i) : ℝ)) :
    (1 - τ) * (Fintype.card S : ℝ) ≤
      (finrank 𝕜 (SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M) : ℝ) := by
  have hslot : ∀ i, (Δ : ℝ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℝ) ≤
        τ * (Fintype.card S : ℝ) := by
    intro i
    apply (hrank i).trans
    apply mul_le_mul_of_nonneg_left _ hτ
    exact_mod_cast card_joint_le_card_side S J hJ i
  have hsum := sum_rank_le_of_slot_bounds τ hτ (Fintype.card S)
    (fun i => finrank 𝕜 (LinearMap.range (LinearMap.id - M i))) hslot
  have hdim := SubexponentialSAT.SubspaceDimension.card_side_le_finrank_fixed_add_sum_defect
    S J hJ M
  have hdimR :
      (Fintype.card S : ℝ) ≤
        (finrank 𝕜 (SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M) : ℝ) +
          ((∑ i, finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℕ) : ℝ) := by
    exact_mod_cast hdim
  rw [SubexponentialSAT.SubspaceDimension.finrank_supportedFixedSpace]
  nlinarith

omit [Fintype α] in
/-- Rational form for the authoritative quantitative layout interface. -/
theorem supportedFixedSpace_dim_lower_rat
    (M : (i : Fin Δ) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜))
    (τ : ℚ) (hτ : 0 ≤ τ)
    (hrank : ∀ i, (Δ : ℚ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℚ) ≤
        τ * (Fintype.card (J i) : ℚ)) :
    (1 - τ) * (Fintype.card S : ℚ) ≤
      (finrank 𝕜 (SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M) : ℚ) := by
  have hτR : (0 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ
  have hrankR : ∀ i, (Δ : ℝ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℝ) ≤
        (τ : ℝ) * (Fintype.card (J i) : ℝ) := by
    intro i
    exact_mod_cast hrank i
  have h := supportedFixedSpace_dim_lower S J hJ M (τ : ℝ) hτR hrankR
  exact_mod_cast h

end CoordinateSpaces

section DisjointSupports

variable {𝕜 α : Type*} [Field 𝕜] [Fintype α] {Δ : ℕ}
variable (S T : Set α) (J H : Fin Δ → Set α)
variable (hJ : ∀ i, J i ⊆ S) (hH : ∀ i, H i ⊆ T)
variable [Fintype S] [Fintype T] [∀ i, Fintype (J i)] [∀ i, Fintype (H i)]

omit [Fintype α] [(i : Fin Δ) → Fintype ↑(J i)] [(i : Fin Δ) → Fintype ↑(H i)] in
omit [Fintype ↑S] [Fintype ↑T] in
/-- Spaces supported on disjoint coordinate sets are disjoint, regardless of
the matrices used for their slot constraints. -/
theorem supportedFixedSpace_disjoint
    (M : (i : Fin Δ) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜))
    (N : (i : Fin Δ) → (H i → 𝕜) →ₗ[𝕜] (H i → 𝕜))
    (hST : Disjoint S T) :
    Disjoint
      (SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M)
      (SubexponentialSAT.SubspaceDimension.supportedFixedSpace T H hH N) := by
  apply Submodule.disjoint_def.mpr
  intro v hvS hvT
  have hs := (SubexponentialSAT.SubspaceDimension.mem_supportedFixedSpace_iff S J hJ M v).mp hvS
  have ht := (SubexponentialSAT.SubspaceDimension.mem_supportedFixedSpace_iff T H hH N v).mp hvT
  funext u
  by_cases hu : u ∈ S
  · have huT : u ∉ T := fun hut => Set.disjoint_left.mp hST hu hut
    exact ht.1 u huT
  · exact hs.1 u hu

end DisjointSupports

section UniversalBlock

variable {𝕜 : Type*} [Field 𝕜] {r Q Δ : ℕ}

/-- The multicolor universal subspace, defined over the same field as M and
embedded in all universal coordinates by setting the other coordinates to zero.
The joint fibers have head color g and slot color different from g. -/
noncomputable def universalFixedSpace (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜)) :
    Submodule 𝕜 (MulticolorTypes.UniversalType r Q Δ → 𝕜) :=
  SubexponentialSAT.SubspaceDimension.supportedFixedSpace
    (MulticolorTypes.side t g) (MulticolorTypes.joint t g)
    (MulticolorTypes.joint_subset_side t g) M

theorem universalFixedSpace_mem_iff (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    (z : MulticolorTypes.UniversalType r Q Δ → 𝕜) :
    z ∈ universalFixedSpace t g M ↔
      (∀ u, u ∉ MulticolorTypes.side t g → z u = 0) ∧
      ∀ i, (fun u : MulticolorTypes.Joint t g i => z u.val) =
        M i (fun u : MulticolorTypes.Joint t g i => z u.val) :=
  SubexponentialSAT.SubspaceDimension.mem_supportedFixedSpace_iff _ _ _ _ _

/-- A convenient support projection of the membership characterization. -/
theorem universalFixedSpace_supported (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    {z : MulticolorTypes.UniversalType r Q Δ → 𝕜}
    (hz : z ∈ universalFixedSpace t g M) :
    ∀ u, u ∉ MulticolorTypes.side t g → z u = 0 :=
  ((universalFixedSpace_mem_iff t g M z).mp hz).1

/-- A convenient slot fixed-point projection of membership. -/
theorem universalFixedSpace_fixed (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    {z : MulticolorTypes.UniversalType r Q Δ → 𝕜}
    (hz : z ∈ universalFixedSpace t g M) (i : Fin Δ) :
    (fun u : MulticolorTypes.Joint t g i => z u.val) =
      M i (fun u : MulticolorTypes.Joint t g i => z u.val) :=
  ((universalFixedSpace_mem_iff t g M z).mp hz).2 i

/-- No supported subspace can exceed the dimension of its head-color side. -/
theorem universalFixedSpace_dim_upper (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜)) :
    finrank 𝕜 (universalFixedSpace t g M) ≤
      Fintype.card (MulticolorTypes.Side (Δ := Δ) t g) :=
  finrank_supportedFixedSpace_le _ _ _ _

/-- Equation (3.7) as a fraction of the side size, with rational parameters.
Only nonnegativity of τ is needed by the dimension argument. -/
theorem universalFixedSpace_dim_lower (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    (τ : ℚ) (hτ : 0 ≤ τ)
    (hrank : ∀ i, (Δ : ℚ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℚ) ≤
        τ * (Fintype.card (MulticolorTypes.Joint t g i) : ℚ)) :
    (1 - τ) * (Fintype.card (MulticolorTypes.Side (Δ := Δ) t g) : ℚ) ≤
      (finrank 𝕜 (universalFixedSpace t g M) : ℚ) :=
  supportedFixedSpace_dim_lower_rat _ _ _ M τ hτ hrank

/-- Bridge from the real-valued spectral rank inequality to the rational layout
interface. The subspace and field are unchanged. -/
theorem universalFixedSpace_dim_lower_of_real_rank (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    (τ : ℚ) (hτ : 0 ≤ τ)
    (hrank : ∀ i, (Δ : ℝ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℝ) ≤
        (τ : ℝ) * (Fintype.card (MulticolorTypes.Joint t g i) : ℝ)) :
    (1 - τ) * (Fintype.card (MulticolorTypes.Side (Δ := Δ) t g) : ℚ) ≤
      (finrank 𝕜 (universalFixedSpace t g M) : ℚ) := by
  apply universalFixedSpace_dim_lower t g M τ hτ
  intro i
  exact_mod_cast hrank i

/-- Denominator-cleared universal-block dimension bound. -/
theorem universalFixedSpace_card_lower (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    (τ : ℚ) (hτ : 0 ≤ τ)
    (hrank : ∀ i, (Δ : ℚ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℚ) ≤
        τ * (Fintype.card (MulticolorTypes.Joint t g i) : ℚ)) :
    (1 - τ) * (Fintype.card (MulticolorTypes.UniversalType r Q Δ) : ℚ) ≤
      (r : ℚ) * (finrank 𝕜 (universalFixedSpace t g M) : ℚ) := by
  have h := universalFixedSpace_dim_lower t g M τ hτ hrank
  have hcard :
      (Fintype.card (MulticolorTypes.UniversalType r Q Δ) : ℚ) =
        (r : ℚ) * (Fintype.card (MulticolorTypes.Side (Δ := Δ) t g) : ℚ) := by
    exact_mod_cast MulticolorTypes.card_full_eq_mul_side (Δ := Δ) t g
  calc
    (1 - τ) * (Fintype.card (MulticolorTypes.UniversalType r Q Δ) : ℚ) =
        (r : ℚ) *
          ((1 - τ) * (Fintype.card (MulticolorTypes.Side (Δ := Δ) t g) : ℚ)) := by
      rw [hcard]
      ring
    _ ≤ (r : ℚ) * (finrank 𝕜 (universalFixedSpace t g M) : ℚ) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg r)

/-- The same bound using the paper's N = r^(Q(Δ+1)). -/
theorem universalFixedSpace_fullBlock_lower (t : Fin Q) (g : Fin r)
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    (τ : ℚ) (hτ : 0 ≤ τ)
    (hrank : ∀ i, (Δ : ℚ) *
      (finrank 𝕜 (LinearMap.range (LinearMap.id - M i)) : ℚ) ≤
        τ * (Fintype.card (MulticolorTypes.Joint t g i) : ℚ)) :
    (1 - τ) * (MulticolorTypes.blockSize r Q Δ : ℚ) ≤
      (r : ℚ) * (finrank 𝕜 (universalFixedSpace t g M) : ℚ) := by
  simpa [MulticolorTypes.blockSize] using
    universalFixedSpace_card_lower t g M τ hτ hrank

/-- Distinct head colors give disjoint subspaces at each interpolation point. -/
theorem universalFixedSpace_disjoint (t : Fin Q) {g h : Fin r}
    (M : (i : Fin Δ) →
      (MulticolorTypes.Joint t g i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t g i → 𝕜))
    (N : (i : Fin Δ) →
      (MulticolorTypes.Joint t h i → 𝕜) →ₗ[𝕜] (MulticolorTypes.Joint t h i → 𝕜))
    (hne : g ≠ h) :
    Disjoint (universalFixedSpace t g M) (universalFixedSpace t h N) :=
  supportedFixedSpace_disjoint _ _ _ _ _ _ M N
    (MulticolorTypes.side_disjoint t hne)

end UniversalBlock

section ConstraintMatrix

variable {𝕜 α : Type*} [Field 𝕜] [Fintype α] {Δ m n : ℕ}
variable (S : Set α) (J : Fin Δ → Set α) (hJ : ∀ i, J i ⊆ S)
variable [Fintype S] [∀ i, Fintype (J i)]
variable (M : (i : Fin Δ) → (J i → 𝕜) →ₗ[𝕜] (J i → 𝕜))

/-- Flatten every slot equation into one finite row index. -/
def sideConstraintMap : (S → 𝕜) →ₗ[𝕜] ((i : Fin Δ) × J i) → 𝕜 :=
  LinearMap.pi fun row =>
    (LinearMap.proj row.2).comp
      ((LinearMap.id - M row.1).comp
        (SubexponentialSAT.SubspaceDimension.coordinateRestriction S J hJ row.1))

omit [Fintype α] in
omit [Fintype ↑S] [(i : Fin Δ) → Fintype ↑(J i)] in
theorem sideConstraintMap_zero_iff (v : S → 𝕜) :
    sideConstraintMap S J hJ M v = 0 ↔
      v ∈ SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M := by
  simp only [SubexponentialSAT.SubspaceDimension.mem_coordinateFixedSpace, sideConstraintMap,
    funext_iff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Pi.zero_apply,
    Sigma.forall, sub_eq_zero]

omit [Fintype α] in
omit [Fintype ↑S] [(i : Fin Δ) → Fintype ↑(J i)] in
theorem ker_sideConstraintMap :
    LinearMap.ker (sideConstraintMap S J hJ M) =
      SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M := by
  ext v
  exact sideConstraintMap_zero_iff S J hJ M v

/-- Encode rows and columns by explicitly supplied finite equivalences. These
equivalences are inputs, so this definition invokes no choice of enumeration. -/
def encodedSideConstraintMap
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    (Fin n → 𝕜) →ₗ[𝕜] (Fin m → 𝕜) where
  toFun x a := sideConstraintMap S J hJ M (fun u => x (colE.symm u)) (rowE a)
  map_add' x y := by
    funext a
    exact congrFun (map_add (sideConstraintMap S J hJ M) _ _) (rowE a)
  map_smul' c x := by
    funext a
    exact congrFun (map_smul (sideConstraintMap S J hJ M) c _) (rowE a)

/-- A concrete rectangular matrix: evaluate the encoded constraint map on
each standard coordinate vector. This is executable whenever its inputs are. -/
def encodedConstraintMatrix
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    Fin m → Fin n → 𝕜 :=
  fun a b => encodedSideConstraintMap S J hJ M rowE colE
    (fun j => if b = j then 1 else 0) a

omit [Fintype α] [Fintype ↑S] [(i : Fin Δ) → Fintype ↑(J i)] in
theorem encodedConstraintMatrix_apply
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (x : Fin n → 𝕜) (a : Fin m) :
    (∑ b, encodedConstraintMatrix S J hJ M rowE colE a b * x b) =
      encodedSideConstraintMap S J hJ M rowE colE x a := by
  have h := congrFun
    (LinearMap.pi_apply_eq_sum_univ
      (encodedSideConstraintMap S J hJ M rowE colE) x) a
  simpa only [encodedConstraintMatrix, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h.symm

omit [Fintype α] in
omit [Fintype ↑S] [(i : Fin Δ) → Fintype ↑(J i)] in
/-- The rectangular matrix kernel is exactly the side-coordinate fixed space,
with columns translated by the supplied explicit enumeration. -/
theorem encodedConstraintMatrix_zero_iff
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (x : Fin n → 𝕜) :
    (∀ a, ∑ b, encodedConstraintMatrix S J hJ M rowE colE a b * x b = 0) ↔
      (fun u => x (colE.symm u)) ∈
        SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M := by
  rw [← sideConstraintMap_zero_iff S J hJ M]
  constructor
  · intro h
    funext u
    have hu := h (rowE.symm u)
    rw [encodedConstraintMatrix_apply] at hu
    change sideConstraintMap S J hJ M _ u = 0
    simpa only [encodedSideConstraintMap, LinearMap.coe_mk, AddHom.coe_mk,
      Equiv.apply_symm_apply] using hu
  · intro h a
    rw [encodedConstraintMatrix_apply]
    change sideConstraintMap S J hJ M _ (rowE a) = 0
    rw [h]
    rfl

omit [Fintype α] [Fintype ↑S] [(i : Fin Δ) → Fintype ↑(J i)] in
/-- Zero extension identifies the matrix kernel with the supported universal
  space. The matrix search itself only uses the n side coordinates. -/
theorem encodedConstraintMatrix_zero_iff_supported
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (x : Fin n → 𝕜) :
    (∀ a, ∑ b, encodedConstraintMatrix S J hJ M rowE colE a b * x b = 0) ↔
      SubexponentialSAT.SubspaceDimension.extendByZero S (fun u => x (colE.symm u)) ∈
        SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M := by
  rw [encodedConstraintMatrix_zero_iff]
  change _ ↔ _ ∈ (SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M).map
    (SubexponentialSAT.SubspaceDimension.extendByZero S)
  rw [Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨v, hv, heq⟩
    have heq' := SubexponentialSAT.SubspaceDimension.extendByZero_injective S heq
    simpa only [heq'] using hv

/-- Executable zero extension when membership in the coordinate side is
decidable. The earlier extension map remains its specification. -/
def decidableExtendByZero [DecidablePred (fun u => u ∈ S)] :
    (S → 𝕜) →ₗ[𝕜] (α → 𝕜) where
  toFun v u := if hu : u ∈ S then v ⟨u, hu⟩ else 0
  map_add' v w := by
    funext u
    by_cases hu : u ∈ S <;> simp [hu]
  map_smul' c v := by
    funext u
    by_cases hu : u ∈ S <;> simp [hu]

omit [Fintype α] [Fintype ↑S] in
theorem decidableExtendByZero_eq [DecidablePred (fun u => u ∈ S)] :
    decidableExtendByZero (𝕜 := 𝕜) S = SubexponentialSAT.SubspaceDimension.extendByZero S := by
  ext v u
  by_cases hu : u ∈ S <;>
    simp [decidableExtendByZero, SubexponentialSAT.SubspaceDimension.extendByZero, hu]

/-- A computable linear equivalence from the finite side-coordinate kernel
to the full supported subspace. Its inverse is explicit coordinate restriction.
No basis, complement, or enumeration is selected by choice. -/
def encodedKernelEquiv [DecidablePred (fun u => u ∈ S)]
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    LinearMap.ker (encodedSideConstraintMap S J hJ M rowE colE) ≃ₗ[𝕜]
      SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M where
  toFun x := ⟨decidableExtendByZero S (fun u => x.val (colE.symm u)), by
    rw [decidableExtendByZero_eq]
    apply (encodedConstraintMatrix_zero_iff_supported S J hJ M rowE colE x.val).mp
    intro a
    rw [encodedConstraintMatrix_apply]
    exact congrFun x.property a⟩
  invFun z := ⟨fun j => z.val (colE j).val, by
    have hz := (SubexponentialSAT.SubspaceDimension.mem_supportedFixedSpace_iff
      S J hJ M z.val).mp z.property
    have hcoord : (fun u : S => z.val u.val) ∈
        SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M := by
      apply (SubexponentialSAT.SubspaceDimension.mem_coordinateFixedSpace S J hJ M _).mpr
      simpa only [SubexponentialSAT.SubspaceDimension.coordinateRestriction,
        LinearMap.coe_mk, AddHom.coe_mk] using hz.2
    have hm := (encodedConstraintMatrix_zero_iff S J hJ M rowE colE
      (fun j => z.val (colE j).val)).mpr (by simpa only [Equiv.apply_symm_apply] using hcoord)
    funext a
    rw [← encodedConstraintMatrix_apply]
    exact hm a⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    simp [decidableExtendByZero, (colE j).property]
  right_inv z := by
    apply Subtype.ext
    funext u
    by_cases hu : u ∈ S
    · simp [decidableExtendByZero, hu]
    · have hz := (SubexponentialSAT.SubspaceDimension.mem_supportedFixedSpace_iff
        S J hJ M z.val).mp z.property
      simp [decidableExtendByZero, hu, hz.1 u hu]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (decidableExtendByZero S) _ _
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (decidableExtendByZero S) c _

end ConstraintMatrix

end SubexponentialSAT.Subexp.SubspaceDimension

end OAI.Algorithms
