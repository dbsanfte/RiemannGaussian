import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The finite Gram--Weil block defect

This file isolates the finite-dimensional linear-algebra core of the
post-Gaussian Gram--Weil program.  It assumes only two finite-dimensional
Hilbert spaces and an injective linear map `C`; no Krein--Langer
factorization, model-space realization, or statement about the xi function
is assumed.

For

`G = [[I, -C], [-C†, I]]` and `J = [[I, 0], [0, -I]]`,

their defect is

`D = G - J = [[0, -C], [-C†, 2I]]`.

We define the positive and negative indices directly as the maximal
dimensions of subspaces on which the real quadratic form is strictly
positive or strictly negative.  The null index is the dimension of the
operator kernel.  This avoids taking an undeclared spectral-inertia API for
granted.
-/

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

/-! ## An explicit, basis-free definition of finite quadratic inertia -/

/-- A real-valued quadratic function is strictly negative on a subspace. -/
def QuadraticStrictlyNegativeOn
    {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (q : V → ℝ) (W : Submodule 𝕜 V) : Prop :=
  ∀ x : W, x ≠ 0 → q x < 0

/-- A real-valued quadratic function is strictly positive on a subspace. -/
def QuadraticStrictlyPositiveOn
    {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (q : V → ℝ) (W : Submodule 𝕜 V) : Prop :=
  ∀ x : W, x ≠ 0 → 0 < q x

/-- `k` is the negative index when a `k`-dimensional negative-definite
subspace exists and every negative-definite subspace has dimension at most
`k`. -/
def HasQuadraticNegativeIndex
    {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (q : V → ℝ) (k : ℕ) : Prop :=
  (∃ W : Submodule 𝕜 V,
      Module.finrank 𝕜 W = k ∧ QuadraticStrictlyNegativeOn q W) ∧
    ∀ W : Submodule 𝕜 V,
      QuadraticStrictlyNegativeOn q W → Module.finrank 𝕜 W ≤ k

/-- Positive-index analogue of `HasQuadraticNegativeIndex`. -/
def HasQuadraticPositiveIndex
    {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (q : V → ℝ) (k : ℕ) : Prop :=
  (∃ W : Submodule 𝕜 V,
      Module.finrank 𝕜 W = k ∧ QuadraticStrictlyPositiveOn q W) ∧
    ∀ W : Submodule 𝕜 V,
      QuadraticStrictlyPositiveOn q W → Module.finrank 𝕜 W ≤ k

/-- Basis-free finite inertia, in `(negative, null, positive)` order. -/
def HasQuadraticInertia
    {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (operator : V →ₗ[𝕜] V) (q : V → ℝ)
    (negative null positive : ℕ) : Prop :=
  HasQuadraticNegativeIndex (𝕜 := 𝕜) q negative ∧
    Module.finrank 𝕜 operator.ker = null ∧
      HasQuadraticPositiveIndex (𝕜 := 𝕜) q positive

/-! ## The Gram--Weil defect operator and form -/

variable {𝕜 P N : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
  [NormedAddCommGroup N] [InnerProductSpace 𝕜 N]
  [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N]

/-- The block operator `[[0, -C], [-C†, 2I]]`. -/
def gramWeilBlockDefectOperator (C : N →ₗ[𝕜] P) :
    P × N →ₗ[𝕜] P × N where
  toFun x := (-C x.2, -C.adjoint x.1 + (2 : 𝕜) • x.2)
  map_add' x y := by
    apply Prod.ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' a x := by
    apply Prod.ext <;> simp [smul_add, smul_smul, mul_comm]

/-- The real quadratic form of `gramWeilBlockDefectOperator`. -/
def gramWeilBlockDefectQuadratic (C : N →ₗ[𝕜] P)
    (x : P × N) : ℝ :=
  2 * ‖x.2‖ ^ 2 -
    2 * RCLike.re (inner 𝕜 x.2 (C.adjoint x.1))

/-- Completing the square in the negative block. -/
theorem gramWeilBlockDefectQuadratic_eq_completedSquare
    (C : N →ₗ[𝕜] P) (x : P × N) :
    gramWeilBlockDefectQuadratic C x =
      (1 / 2 : ℝ) * ‖(2 : 𝕜) • x.2 - C.adjoint x.1‖ ^ 2 -
        (1 / 2 : ℝ) * ‖C.adjoint x.1‖ ^ 2 := by
  unfold gramWeilBlockDefectQuadratic
  rw [norm_sub_sq (𝕜 := 𝕜), norm_smul]
  rw [inner_smul_left]
  norm_num [map_mul]
  ring

/-! ## The two control maps for the completed square -/

/-- The coordinate controlling negative directions. -/
def gramWeilNegativeControl (C : N →ₗ[𝕜] P) :
    P × N →ₗ[𝕜] N :=
  C.adjoint.comp (LinearMap.fst 𝕜 P N)

/-- The completed-square coordinate controlling positive directions. -/
def gramWeilPositiveControl (C : N →ₗ[𝕜] P) :
    P × N →ₗ[𝕜] N :=
  (2 : 𝕜) • LinearMap.snd 𝕜 P N -
    C.adjoint.comp (LinearMap.fst 𝕜 P N)

@[simp] theorem gramWeilNegativeControl_apply
    (C : N →ₗ[𝕜] P) (x : P × N) :
    gramWeilNegativeControl C x = C.adjoint x.1 := rfl

@[simp] theorem gramWeilPositiveControl_apply
    (C : N →ₗ[𝕜] P) (x : P × N) :
    gramWeilPositiveControl C x =
      (2 : 𝕜) • x.2 - C.adjoint x.1 := rfl

theorem gramWeilBlockDefectQuadratic_nonnegative_of_negativeControl_eq_zero
    (C : N →ₗ[𝕜] P) {x : P × N}
    (hx : gramWeilNegativeControl C x = 0) :
    0 ≤ gramWeilBlockDefectQuadratic C x := by
  rw [gramWeilBlockDefectQuadratic_eq_completedSquare]
  rw [gramWeilNegativeControl_apply] at hx
  simp only [hx, norm_zero, pow_succ, mul_zero, sub_zero]
  positivity

theorem gramWeilBlockDefectQuadratic_nonpositive_of_positiveControl_eq_zero
    (C : N →ₗ[𝕜] P) {x : P × N}
    (hx : gramWeilPositiveControl C x = 0) :
    gramWeilBlockDefectQuadratic C x ≤ 0 := by
  rw [gramWeilBlockDefectQuadratic_eq_completedSquare]
  rw [gramWeilPositiveControl_apply] at hx
  simp only [hx, norm_zero, pow_succ, mul_zero, zero_sub]
  exact neg_nonpos.mpr (by positivity)

/-- On a strictly negative subspace the negative control is injective. -/
theorem gramWeilNegativeControl_injectiveOn_strictlyNegative
    (C : N →ₗ[𝕜] P) (W : Submodule 𝕜 (P × N))
    (hW : QuadraticStrictlyNegativeOn
      (gramWeilBlockDefectQuadratic C) W) :
    Function.Injective
      ((gramWeilNegativeControl C).comp W.subtype) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro x hx
    have hcontrol : gramWeilNegativeControl C (x : P × N) = 0 := by
      exact LinearMap.mem_ker.mp hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hnegative := hW x hxzero
      have hnonnegative :=
        gramWeilBlockDefectQuadratic_nonnegative_of_negativeControl_eq_zero
          C hcontrol
      exact False.elim ((not_lt_of_ge hnonnegative) hnegative)
  · exact bot_le

/-- On a strictly positive subspace the positive control is injective. -/
theorem gramWeilPositiveControl_injectiveOn_strictlyPositive
    (C : N →ₗ[𝕜] P) (W : Submodule 𝕜 (P × N))
    (hW : QuadraticStrictlyPositiveOn
      (gramWeilBlockDefectQuadratic C) W) :
    Function.Injective
      ((gramWeilPositiveControl C).comp W.subtype) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro x hx
    have hcontrol : gramWeilPositiveControl C (x : P × N) = 0 := by
      exact LinearMap.mem_ker.mp hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hpositive := hW x hxzero
      have hnonpositive :=
        gramWeilBlockDefectQuadratic_nonpositive_of_positiveControl_eq_zero
          C hcontrol
      exact False.elim ((not_lt_of_ge hnonpositive) hpositive)
  · exact bot_le

/-- Consequently every strictly negative subspace has dimension at most the
dimension of the `N` block. -/
theorem finrank_strictlyNegative_le_finrank_right
    (C : N →ₗ[𝕜] P) (W : Submodule 𝕜 (P × N))
    (hW : QuadraticStrictlyNegativeOn
      (gramWeilBlockDefectQuadratic C) W) :
    Module.finrank 𝕜 W ≤ Module.finrank 𝕜 N :=
  LinearMap.finrank_le_finrank_of_injective
    (gramWeilNegativeControl_injectiveOn_strictlyNegative C W hW)

/-- The same upper bound holds for every strictly positive subspace. -/
theorem finrank_strictlyPositive_le_finrank_right
    (C : N →ₗ[𝕜] P) (W : Submodule 𝕜 (P × N))
    (hW : QuadraticStrictlyPositiveOn
      (gramWeilBlockDefectQuadratic C) W) :
    Module.finrank 𝕜 W ≤ Module.finrank 𝕜 N :=
  LinearMap.finrank_le_finrank_of_injective
    (gramWeilPositiveControl_injectiveOn_strictlyPositive C W hW)

/-! ## Explicit extremal positive and negative subspaces -/

/-- The evident positive embedding `n ↦ (0,n)`. -/
def gramWeilPositiveEmbedding : N →ₗ[𝕜] P × N where
  toFun n := (0, n)
  map_add' x y := by simp
  map_smul' a x := by simp

/-- The graph on which the completed-square positive coordinate vanishes. -/
def gramWeilNegativeEmbedding (C : N →ₗ[𝕜] P) :
    N →ₗ[𝕜] P × N where
  toFun n :=
    (C n, (2 : 𝕜)⁻¹ • C.adjoint (C n))
  map_add' x y := by simp [smul_add]
  map_smul' a x := by simp [smul_smul, mul_comm]

omit [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N] in
@[simp] theorem gramWeilPositiveEmbedding_apply (n : N) :
    (gramWeilPositiveEmbedding (𝕜 := 𝕜) (P := P) n) = (0, n) := rfl

@[simp] theorem gramWeilNegativeEmbedding_apply
    (C : N →ₗ[𝕜] P) (n : N) :
    gramWeilNegativeEmbedding C n =
      (C n, (2 : 𝕜)⁻¹ • C.adjoint (C n)) := rfl

omit [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N] in
theorem gramWeilPositiveEmbedding_injective :
    Function.Injective
      (gramWeilPositiveEmbedding (𝕜 := 𝕜) (P := P) (N := N)) := by
  intro x y hxy
  exact congrArg Prod.snd hxy

theorem gramWeilNegativeEmbedding_injective
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    Function.Injective (gramWeilNegativeEmbedding C) := by
  intro x y hxy
  apply hC
  exact congrArg Prod.fst hxy

theorem adjoint_apply_apply_ne_zero_of_injective
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C)
    {n : N} (hn : n ≠ 0) :
    C.adjoint (C n) ≠ 0 := by
  intro hzero
  have hnker : n ∈ (C.adjoint ∘ₗ C).ker := by
    rw [LinearMap.mem_ker]
    exact hzero
  rw [LinearMap.ker_adjoint_comp_self] at hnker
  have hCn : C n = 0 := LinearMap.mem_ker.mp hnker
  exact hn (hC (by simpa using hCn))

theorem gramWeilBlockDefectQuadratic_positiveEmbedding_pos
    (C : N →ₗ[𝕜] P) {n : N} (hn : n ≠ 0) :
    0 < gramWeilBlockDefectQuadratic C
      (gramWeilPositiveEmbedding (𝕜 := 𝕜) (P := P) n) := by
  change 0 < 2 * ‖n‖ ^ 2 -
    2 * RCLike.re (inner 𝕜 n (C.adjoint 0))
  simp only [map_zero, inner_zero_right, map_zero]
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hn)]

theorem gramWeilPositiveControl_negativeEmbedding
    (C : N →ₗ[𝕜] P) (n : N) :
    gramWeilPositiveControl C (gramWeilNegativeEmbedding C n) = 0 := by
  change (2 : 𝕜) • ((2 : 𝕜)⁻¹ • C.adjoint (C n)) -
    C.adjoint (C n) = 0
  simp [smul_smul]

theorem gramWeilBlockDefectQuadratic_negativeEmbedding_neg
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C)
    {n : N} (hn : n ≠ 0) :
    gramWeilBlockDefectQuadratic C (gramWeilNegativeEmbedding C n) < 0 := by
  rw [gramWeilBlockDefectQuadratic_eq_completedSquare]
  have hcontrol := gramWeilPositiveControl_negativeEmbedding C n
  rw [gramWeilPositiveControl_apply] at hcontrol
  rw [hcontrol]
  have hadjoint : C.adjoint (C n) ≠ 0 :=
    adjoint_apply_apply_ne_zero_of_injective hC hn
  change (1 / 2 : ℝ) * ‖(0 : N)‖ ^ 2 -
    (1 / 2 : ℝ) * ‖C.adjoint (C n)‖ ^ 2 < 0
  have hnorm : 0 < ‖C.adjoint (C n)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hadjoint)
  norm_num
  linarith

/-- The positive witness subspace. -/
def gramWeilPositiveSubspace : Submodule 𝕜 (P × N) :=
  LinearMap.range (gramWeilPositiveEmbedding (𝕜 := 𝕜) (P := P))

/-- The negative witness subspace. -/
def gramWeilNegativeSubspace (C : N →ₗ[𝕜] P) :
    Submodule 𝕜 (P × N) :=
  LinearMap.range (gramWeilNegativeEmbedding C)

omit [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N] in
theorem finrank_gramWeilPositiveSubspace :
    Module.finrank 𝕜 (gramWeilPositiveSubspace (𝕜 := 𝕜) (P := P) (N := N)) =
      Module.finrank 𝕜 N := by
  exact LinearMap.finrank_range_of_inj
    (gramWeilPositiveEmbedding_injective (𝕜 := 𝕜) (P := P) (N := N))

theorem finrank_gramWeilNegativeSubspace
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    Module.finrank 𝕜 (gramWeilNegativeSubspace C) =
      Module.finrank 𝕜 N := by
  exact LinearMap.finrank_range_of_inj
    (gramWeilNegativeEmbedding_injective hC)

theorem gramWeilBlockDefectQuadratic_strictlyPositiveOn_positiveSubspace
    (C : N →ₗ[𝕜] P) :
    QuadraticStrictlyPositiveOn (gramWeilBlockDefectQuadratic C)
      (gramWeilPositiveSubspace (𝕜 := 𝕜) (P := P) (N := N)) := by
  intro x hx
  rcases x with ⟨x, hxrange⟩
  obtain ⟨n, rfl⟩ := hxrange
  apply gramWeilBlockDefectQuadratic_positiveEmbedding_pos C
  intro hn
  subst n
  apply hx
  apply Subtype.ext
  simp [gramWeilPositiveEmbedding]

theorem gramWeilBlockDefectQuadratic_strictlyNegativeOn_negativeSubspace
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    QuadraticStrictlyNegativeOn (gramWeilBlockDefectQuadratic C)
      (gramWeilNegativeSubspace C) := by
  intro x hx
  rcases x with ⟨x, hxrange⟩
  obtain ⟨n, rfl⟩ := hxrange
  apply gramWeilBlockDefectQuadratic_negativeEmbedding_neg hC
  intro hn
  subst n
  apply hx
  apply Subtype.ext
  simp [gramWeilNegativeEmbedding]

theorem gramWeilBlockDefect_hasNegativeIndex
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    HasQuadraticNegativeIndex (𝕜 := 𝕜)
      (gramWeilBlockDefectQuadratic C) (Module.finrank 𝕜 N) := by
  constructor
  · exact ⟨gramWeilNegativeSubspace C,
      finrank_gramWeilNegativeSubspace hC,
      gramWeilBlockDefectQuadratic_strictlyNegativeOn_negativeSubspace hC⟩
  · intro W hW
    exact finrank_strictlyNegative_le_finrank_right C W hW

theorem gramWeilBlockDefect_hasPositiveIndex
    (C : N →ₗ[𝕜] P) :
    HasQuadraticPositiveIndex (𝕜 := 𝕜)
      (gramWeilBlockDefectQuadratic C) (Module.finrank 𝕜 N) := by
  constructor
  · exact ⟨gramWeilPositiveSubspace,
      finrank_gramWeilPositiveSubspace,
      gramWeilBlockDefectQuadratic_strictlyPositiveOn_positiveSubspace C⟩
  · intro W hW
    exact finrank_strictlyPositive_le_finrank_right C W hW

/-! ## Null space and the exact inertia theorem -/

theorem mem_gramWeilBlockDefectOperator_ker_iff
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C)
    (x : P × N) :
    x ∈ (gramWeilBlockDefectOperator C).ker ↔
      x.2 = 0 ∧ C.adjoint x.1 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have hfirst : -C x.2 = 0 := by
      exact congrArg Prod.fst hx
    have hCx : C x.2 = 0 := by simpa using hfirst
    have hn : x.2 = 0 := hC (by simpa using hCx)
    have hsecond : -C.adjoint x.1 + (2 : 𝕜) • x.2 = 0 := by
      exact congrArg Prod.snd hx
    rw [hn] at hsecond
    exact ⟨hn, by simpa using hsecond⟩
  · rintro ⟨hn, hadjoint⟩
    change (-C x.2, -C.adjoint x.1 + (2 : 𝕜) • x.2) = (0, 0)
    rw [hn, hadjoint]
    simp

/-- The defect kernel is linearly equivalent to `ker C†`. -/
def gramWeilBlockDefectKerEquiv
    (C : N →ₗ[𝕜] P) (hC : Function.Injective C) :
    (gramWeilBlockDefectOperator C).ker ≃ₗ[𝕜] C.adjoint.ker where
  toFun x :=
    ⟨(x : P × N).1, LinearMap.mem_ker.mpr
      ((mem_gramWeilBlockDefectOperator_ker_iff hC x).mp x.property).2⟩
  invFun u :=
    ⟨((u : P), 0), (mem_gramWeilBlockDefectOperator_ker_iff hC _).mpr
      ⟨rfl, LinearMap.mem_ker.mp u.property⟩⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    rfl
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (((mem_gramWeilBlockDefectOperator_ker_iff hC x).mp
        x.property).1).symm
  right_inv u := by
    apply Subtype.ext
    rfl

theorem finrank_gramWeilBlockDefectOperator_ker
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    Module.finrank 𝕜 (gramWeilBlockDefectOperator C).ker =
      Module.finrank 𝕜 P - Module.finrank 𝕜 N := by
  rw [LinearEquiv.finrank_eq (gramWeilBlockDefectKerEquiv C hC)]
  have hsum := C.adjoint.finrank_range_add_finrank_ker
  rw [C.finrank_range_adjoint, C.finrank_range_of_inj hC] at hsum
  omega

/-- The abstract finite Gram--Weil defect theorem.  In
`(negative, null, positive)` order its inertia is

`(dim N, dim P - dim N, dim N)`.

Only injectivity of `C` is needed for this defect-inertia statement.  The
strict-contraction hypothesis in the analytic model is relevant to positivity
of `G` and the metric-pencil eigenvalue bounds, not to this theorem. -/
theorem gramWeilBlockDefect_hasQuadraticInertia
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    HasQuadraticInertia
      (gramWeilBlockDefectOperator C)
      (gramWeilBlockDefectQuadratic C)
      (Module.finrank 𝕜 N)
      (Module.finrank 𝕜 P - Module.finrank 𝕜 N)
      (Module.finrank 𝕜 N) := by
  exact ⟨gramWeilBlockDefect_hasNegativeIndex hC,
    finrank_gramWeilBlockDefectOperator_ker hC,
    gramWeilBlockDefect_hasPositiveIndex C⟩

end

end RiemannGaussian
