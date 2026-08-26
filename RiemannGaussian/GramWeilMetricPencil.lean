import RiemannGaussian.GramWeilBlockDefect

/-!
# The finite Gram--Weil metric pencil

This file formalizes the algebraic generalized-eigenvector reduction for the
finite block model.  As in `GramWeilBlockDefect`, no model-space or xi-function
realization is assumed.

The two block operators are

`G(u,n) = (u - C n, -C† u + n)` and `J(u,n) = (u,-n)`.

Lean checks that `G - J` is the previously studied defect and that every
nontrivial pencil equation `G x = lambda J x`, away from `lambda = 1`, reduces
to an ordinary eigenvector equation for `C† C` with eigenvalue
`1 - lambda^2`.
-/

namespace RiemannGaussian

noncomputable section

variable {𝕜 P N : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
  [NormedAddCommGroup N] [InnerProductSpace 𝕜 N]
  [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N]

/-- Ordinary Gram block `[[I,-C],[-C†,I]]`. -/
def gramWeilGramOperator (C : N →ₗ[𝕜] P) :
    P × N →ₗ[𝕜] P × N where
  toFun x := (x.1 - C x.2, -C.adjoint x.1 + x.2)
  map_add' x y := by
    apply Prod.ext <;> simp <;> module
  map_smul' a x := by
    apply Prod.ext <;> simp [smul_add, smul_sub]

/-- Weil conjugation signature block `diag(I,-I)`. -/
def gramWeilSignatureOperator : P × N →ₗ[𝕜] P × N where
  toFun x := (x.1, -x.2)
  map_add' x y := by
    apply Prod.ext <;> simp [add_comm]
  map_smul' a x := by simp

/-- The operator whose kernel is the generalized eigenspace at `lambda`. -/
def gramWeilPencilOperator (C : N →ₗ[𝕜] P) (lambda : 𝕜) :
    P × N →ₗ[𝕜] P × N :=
  gramWeilGramOperator C - lambda • gramWeilSignatureOperator
    (𝕜 := 𝕜) (P := P) (N := N)

@[simp] theorem gramWeilGramOperator_apply
    (C : N →ₗ[𝕜] P) (x : P × N) :
    gramWeilGramOperator C x =
      (x.1 - C x.2, -C.adjoint x.1 + x.2) := rfl

omit [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N] in
@[simp] theorem gramWeilSignatureOperator_apply (x : P × N) :
    gramWeilSignatureOperator (𝕜 := 𝕜) (P := P) (N := N) x =
      (x.1, -x.2) := rfl

@[simp] theorem gramWeilPencilOperator_apply
    (C : N →ₗ[𝕜] P) (lambda : 𝕜) (x : P × N) :
    gramWeilPencilOperator C lambda x =
      gramWeilGramOperator C x -
        lambda • gramWeilSignatureOperator
          (𝕜 := 𝕜) (P := P) (N := N) x := rfl

/-- The difference of the two metric blocks is exactly the defect operator
formalized in `GramWeilBlockDefect`. -/
theorem gramWeilGramOperator_sub_signature
    (C : N →ₗ[𝕜] P) :
    gramWeilGramOperator C -
        gramWeilSignatureOperator (𝕜 := 𝕜) (P := P) (N := N) =
      gramWeilBlockDefectOperator C := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;>
    simp [gramWeilGramOperator, gramWeilSignatureOperator,
      gramWeilBlockDefectOperator, two_smul, add_assoc]

/-- Coordinate form of the generalized metric-pencil equation. -/
theorem gramWeil_pencilEquation_iff
    (C : N →ₗ[𝕜] P) (lambda : 𝕜) (x : P × N) :
    gramWeilGramOperator C x =
        lambda • gramWeilSignatureOperator
          (𝕜 := 𝕜) (P := P) (N := N) x ↔
      (1 - lambda) • x.1 = C x.2 ∧
        C.adjoint x.1 = (1 + lambda) • x.2 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    change x.1 - C x.2 = lambda • x.1 at hfirst
    change -C.adjoint x.1 + x.2 = lambda • (-x.2) at hsecond
    constructor
    · rw [sub_smul, one_smul, ← hfirst]
      abel
    · rw [add_smul, one_smul]
      have hneg := congrArg Neg.neg hsecond
      have hsub : C.adjoint x.1 - x.2 = lambda • x.2 := by
        simpa [sub_eq_add_neg, smul_neg, add_comm] using hneg
      exact (sub_eq_iff_eq_add').mp hsub
  · rintro ⟨hfirst, hsecond⟩
    rw [sub_smul, one_smul] at hfirst
    rw [add_smul, one_smul] at hsecond
    apply Prod.ext
    · change x.1 - C x.2 = lambda • x.1
      exact (sub_eq_iff_eq_add).2 ((sub_eq_iff_eq_add').1 hfirst)
    · change -C.adjoint x.1 + x.2 = lambda • (-x.2)
      rw [hsecond]
      simp [smul_neg, add_comm]

/-- Eliminating the `P` coordinate gives the ordinary squared-singular-value
equation. -/
theorem gramWeil_pencilEquation_implies_adjoint_comp
    {C : N →ₗ[𝕜] P} {lambda : 𝕜} {x : P × N}
    (h : gramWeilGramOperator C x =
      lambda • gramWeilSignatureOperator
        (𝕜 := 𝕜) (P := P) (N := N) x) :
    C.adjoint (C x.2) = (1 - lambda ^ 2) • x.2 := by
  obtain ⟨hfirst, hsecond⟩ :=
    (gramWeil_pencilEquation_iff C lambda x).mp h
  calc
    C.adjoint (C x.2) = C.adjoint ((1 - lambda) • x.1) := by
      rw [hfirst]
    _ = (1 - lambda) • C.adjoint x.1 := by rw [map_smul]
    _ = (1 - lambda) • ((1 + lambda) • x.2) := by rw [hsecond]
    _ = (1 - lambda ^ 2) • x.2 := by
      rw [smul_smul]
      congr 1
      ring

/-- Away from the exceptional eigenvalue `1`, a nonzero generalized
eigenvector has a nonzero `N` coordinate. -/
theorem gramWeil_pencilEquation_right_ne_zero
    {C : N →ₗ[𝕜] P} {lambda : 𝕜} {x : P × N}
    (hlambda : lambda ≠ 1) (hx : x ≠ 0)
    (h : gramWeilGramOperator C x =
      lambda • gramWeilSignatureOperator
        (𝕜 := 𝕜) (P := P) (N := N) x) :
    x.2 ≠ 0 := by
  intro hright
  have hfirst := (gramWeil_pencilEquation_iff C lambda x).mp h |>.1
  rw [hright, map_zero] at hfirst
  have hcoeff : 1 - lambda ≠ 0 := sub_ne_zero.mpr (Ne.symm hlambda)
  have hleft : x.1 = 0 := by
    exact (smul_eq_zero.mp hfirst).resolve_left hcoeff
  apply hx
  apply Prod.ext
  · simpa using hleft
  · simpa using hright

/-- Conversely, an eigenmode of `C† C` lifts to a pencil mode whenever
`lambda ≠ 1` and its eigenvalue is `1 - lambda^2`. -/
theorem gramWeil_lift_adjointComp_eigenvector
    (C : N →ₗ[𝕜] P) {lambda : 𝕜} (hlambda : lambda ≠ 1)
    {n : N}
    (hmode : C.adjoint (C n) = (1 - lambda ^ 2) • n) :
    gramWeilGramOperator C
        ((1 - lambda)⁻¹ • C n, n) =
      lambda • gramWeilSignatureOperator
        (𝕜 := 𝕜) (P := P) (N := N)
        ((1 - lambda)⁻¹ • C n, n) := by
  apply (gramWeil_pencilEquation_iff C lambda _).2
  have hcoeff : 1 - lambda ≠ 0 := sub_ne_zero.mpr (Ne.symm hlambda)
  constructor
  · rw [smul_smul]
    field_simp
    simp
  · rw [map_smul, hmode, smul_smul]
    have hfactor : (1 - lambda)⁻¹ * (1 - lambda ^ 2) =
        1 + lambda := by
      field_simp
      ring
    rw [hfactor]

/-! ## What strict contraction really supplies -/

/-- Explicit pointwise strict-contraction hypothesis.  It is kept separate
from injectivity because neither property implies the other. -/
def GramWeilPointwiseStrictContraction (C : N →ₗ[𝕜] P) : Prop :=
  ∀ n : N, n ≠ 0 → ‖C n‖ < ‖n‖

/-- Under injectivity and strict contraction, every nonzero real eigenmode of
`C† C` has eigenvalue strictly between zero and one. -/
theorem gramWeil_adjointComp_realEigenvalue_mem_Ioo
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C)
    (hcontract : GramWeilPointwiseStrictContraction C)
    {s : ℝ} {n : N} (hn : n ≠ 0)
    (hmode : C.adjoint (C n) = (s : 𝕜) • n) :
    0 < s ∧ s < 1 := by
  have hCn : C n ≠ 0 := by
    intro hzero
    exact hn (hC (by simpa using hzero))
  have hnormn : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have hnormCn : 0 < ‖C n‖ := norm_pos_iff.mpr hCn
  have hnormlt : ‖C n‖ < ‖n‖ := hcontract n hn
  have hsquare : ‖C n‖ ^ 2 = s * ‖n‖ ^ 2 := by
    calc
      ‖C n‖ ^ 2 = RCLike.re (inner 𝕜 (C n) (C n)) :=
        norm_sq_eq_re_inner _
      _ = RCLike.re (inner 𝕜 (C.adjoint (C n)) n) := by
        rw [LinearMap.adjoint_inner_left]
      _ = RCLike.re (inner 𝕜 ((s : 𝕜) • n) n) := by rw [hmode]
      _ = s * ‖n‖ ^ 2 := by
        rw [inner_smul_left]
        simp
  constructor
  · nlinarith [sq_pos_of_pos hnormCn, sq_pos_of_pos hnormn]
  · have hsquare_lt : ‖C n‖ ^ 2 < ‖n‖ ^ 2 := by
      nlinarith [norm_nonneg (C n), norm_nonneg n]
    nlinarith [sq_pos_of_pos hnormn]

/-- Hence any *real* nonexceptional generalized eigenvalue supplied to the
pencil equation lies in `(-1,1)`.  This theorem does not assume that all
generalized eigenvalues exist or are real; those are separate spectral facts. -/
theorem gramWeil_realPencilEigenvalue_mem_Ioo
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C)
    (hcontract : GramWeilPointwiseStrictContraction C)
    {lambda : ℝ} {x : P × N}
    (hlambda : lambda ≠ 1) (hx : x ≠ 0)
    (hpencil : gramWeilGramOperator C x =
      (lambda : 𝕜) • gramWeilSignatureOperator
        (𝕜 := 𝕜) (P := P) (N := N) x) :
    -1 < lambda ∧ lambda < 1 := by
  have hlambdaField : (lambda : 𝕜) ≠ 1 := by
    exact_mod_cast hlambda
  have hright : x.2 ≠ 0 :=
    gramWeil_pencilEquation_right_ne_zero hlambdaField hx hpencil
  have hmode := gramWeil_pencilEquation_implies_adjoint_comp hpencil
  have hmodeReal : C.adjoint (C x.2) =
      ((1 - lambda ^ 2 : ℝ) : 𝕜) • x.2 := by
    rw [show ((1 - lambda ^ 2 : ℝ) : 𝕜) =
      1 - (lambda : 𝕜) ^ 2 by
        push_cast
        ring]
    exact hmode
  have hs := gramWeil_adjointComp_realEigenvalue_mem_Ioo
    hC hcontract hright hmodeReal
  constructor <;> nlinarith [sq_nonneg (lambda - 1), sq_nonneg (lambda + 1)]

/-- At `lambda = 1`, the generalized eigenspace is exactly the old positive
block's `ker C†`: its vectors are `(u,0)` with `C† u = 0`. -/
theorem gramWeil_pencilEquation_one_iff
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) (x : P × N) :
    gramWeilGramOperator C x =
        (1 : 𝕜) • gramWeilSignatureOperator
          (𝕜 := 𝕜) (P := P) (N := N) x ↔
      x.2 = 0 ∧ C.adjoint x.1 = 0 := by
  constructor
  · intro h
    obtain ⟨hfirst, hsecond⟩ :=
      (gramWeil_pencilEquation_iff C 1 x).mp h
    have hCx : C x.2 = 0 := by simpa using hfirst.symm
    have hright : x.2 = 0 := hC (by simpa using hCx)
    rw [hright] at hsecond
    exact ⟨hright, by simpa using hsecond⟩
  · rintro ⟨hright, hadjoint⟩
    apply (gramWeil_pencilEquation_iff C 1 x).2
    rw [hright, hadjoint]
    simp

/-- At `lambda = 1` the pencil operator is literally the Gram--Weil defect. -/
theorem gramWeilPencilOperator_one_eq_defect
    (C : N →ₗ[𝕜] P) :
    gramWeilPencilOperator C 1 = gramWeilBlockDefectOperator C := by
  unfold gramWeilPencilOperator
  rw [one_smul, gramWeilGramOperator_sub_signature]

/-- Therefore the exceptional generalized eigenspace has exactly the claimed
`dim P - dim N` dimension when `C` is injective. -/
theorem finrank_gramWeilPencilOperator_one_ker
    {C : N →ₗ[𝕜] P} (hC : Function.Injective C) :
    Module.finrank 𝕜 (gramWeilPencilOperator C 1).ker =
      Module.finrank 𝕜 P - Module.finrank 𝕜 N := by
  rw [gramWeilPencilOperator_one_eq_defect]
  exact finrank_gramWeilBlockDefectOperator_ker hC

end

end RiemannGaussian
