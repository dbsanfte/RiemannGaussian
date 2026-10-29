import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.Types
import OpenAISemiprime.Algorithms.SubexponentialSAT.RowInterpolation
import OpenAISemiprime.Algorithms.SubexponentialSAT.MatrixSupport
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubspaceDimension

namespace OAI.Algorithms

/-!
# Annihilation of the incidence-specific row paths

Section 5.3 is a finite linear-algebra statement once the row evaluations and
matrix support property are known.  This file proves that statement for actual
matrices and vectors, and specializes it to the universal type block.  It does
not assume the annihilation conclusion as a hypothesis.
-/

namespace SubexponentialSAT.Annihilation

open scoped BigOperators
open Matrix

variable {V K : Type*} [Fintype V] [DecidableEq V] [Ring K]

/-- Extend a row indexed by a subset by zero on its complement. -/
noncomputable def extendRow (J : Set V) (m : J → K) : V → K := by
  classical
  exact fun y => if hy : y ∈ J then m ⟨y, hy⟩ else 0

omit [Fintype V] [DecidableEq V] in
@[simp] theorem extendRow_mem (J : Set V) (m : J → K) (y : J) :
    extendRow J m y = m y := by
  classical
  simp [extendRow, y.property]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem extendRow_not_mem (J : Set V) (m : J → K)
    (y : V) (hy : y ∉ J) : extendRow J m y = 0 := by
  classical
  simp [extendRow, hy]

omit [DecidableEq V] in
/-- Zero extension preserves the sum pairing with a restricted vector. -/
theorem extendRow_dotProduct (J : Set V) [Fintype J] (m : J → K) (r : V → K) :
    extendRow J m ⬝ᵥ r = m ⬝ᵥ (fun y : J => r y) := by
  classical
  change (∑ y : V, extendRow J m y * r y) = ∑ y : J, m y * r y
  calc
    (∑ y : V, extendRow J m y * r y) =
        ∑ y ∈ J.toFinset, extendRow J m y * r y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hyJ : y ∉ J := by simpa using hy
      simp [extendRow, hyJ]
    _ = ∑ y : J, extendRow J m y * r y :=
      Finset.sum_subtype J.toFinset (fun _ => Set.mem_toFinset) _
    _ = ∑ y : J, m y * r y := by
      apply Finset.sum_congr rfl
      intro y _
      simp

omit [Fintype V] [DecidableEq V] in
/-- A row supported on `Y` stays supported on `Y` after zero extension. -/
theorem extendRow_eq_zero_outside (J : Set V) (Y : Finset V) (m : J → K)
    (hm : ∀ y : J, (y : V) ∉ Y → m y = 0)
    (y : V) (hy : y ∉ Y) : extendRow J m y = 0 := by
  classical
  by_cases hj : y ∈ J
  · simp [extendRow, hj, hm ⟨y, hj⟩ hy]
  · simp [extendRow, hj]

/-- If the selected coordinate is off the active side, all terms vanish.
Only correction values on the active side and inside `Y` need to be specified. -/
theorem annihilates_of_head_outside (S : Set V) (Y : Finset V)
    (u : V) (c r : V → K)
    (hu : u ∉ S)
    (hr : ∀ y, y ∉ S → r y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hcS : ∀ y, y ∈ S → y ∈ Y → c y = 0) :
    (Pi.single u 1 + c) ⬝ᵥ r = 0 := by
  rw [add_dotProduct, single_dotProduct, one_mul, hr u hu, zero_add]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hyS : y ∈ S
  · by_cases hyY : y ∈ Y
    · rw [hcS y hyS hyY, zero_mul]
    · rw [hc y hyY, zero_mul]
  · rw [hr y hyS, mul_zero]

/-- On the active side, the correction agrees with a negative matrix row.
The support hypothesis supplies all omitted correction coordinates. -/
theorem annihilates_of_head_inside (S J : Set V) (Y : Finset V)
    [Fintype J] (M : Matrix J J K) (u : J) (c r : V → K)
    (hr : ∀ y, y ∉ S → r y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hm : ∀ y : J, (y : V) ∉ Y → M u y = 0)
    (hcS : ∀ y, y ∈ S → y ∈ Y → c y = -extendRow J (M u) y)
    (hfix : M *ᵥ (fun y : J => r y) = fun y : J => r y) :
    (Pi.single (u : V) 1 + c) ⬝ᵥ r = 0 := by
  classical
  have hpair : c ⬝ᵥ r = (-extendRow J (M u)) ⬝ᵥ r := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hyS : y ∈ S
    · by_cases hyY : y ∈ Y
      · rw [hcS y hyS hyY]
        rfl
      · simp only [hc y hyY, Pi.neg_apply,
          extendRow_eq_zero_outside J Y (M u) hm y hyY, neg_zero, zero_mul]
    · rw [hr y hyS]
      simp
  rw [add_dotProduct, single_dotProduct, one_mul, hpair, neg_dotProduct,
    extendRow_dotProduct]
  have huFix := congrFun hfix u
  change r u + -(M *ᵥ (fun y : J => r y)) u = 0
  rw [huFix, add_neg_cancel]

section TypeBlock

open _root_.OAI.Algorithms.SubexponentialSAT.Types

variable {Q Δ : ℕ}

/-- The two head cases of Section 5.3 for the actual universal type indices.
The matrix support implication and interpolated correction values remain
explicit hypotheses; the conclusion is the required row annihilation. -/
theorem typeBlock_annihilation
    (t : Fin Q) (i : Fin Δ) (u : UniversalType Q Δ)
    (Y : Finset (UniversalType Q Δ))
    (M : Matrix (Joint t (u.slot i t) i) (Joint t (u.slot i t) i) K)
    (c r : UniversalType Q Δ → K)
    (hr : ∀ y, y.head t ≠ u.slot i t → r y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hm : ∀ (hu : u.head t = u.slot i t) (y : Joint t (u.slot i t) i),
      M ⟨u, hu, rfl⟩ y ≠ 0 → (y : UniversalType Q Δ) ∈ Y)
    (hcEval : ∀ y, y ∈ Y → y.head t = u.slot i t →
      c y = if hu : u.head t = u.slot i t then
        -extendRow (joint t (u.slot i t) i) (M ⟨u, hu, rfl⟩) y else 0)
    (hfix : M *ᵥ (fun y : Joint t (u.slot i t) i => r y) =
      fun y : Joint t (u.slot i t) i => r y) :
    (Pi.single u 1 + c) ⬝ᵥ r = 0 := by
  classical
  by_cases hu : u.head t = u.slot i t
  · apply annihilates_of_head_inside
      (side t (u.slot i t)) (joint t (u.slot i t) i) Y M ⟨u, hu, rfl⟩ c r
      hr hc ?_ ?_ hfix
    · intro y hy
      by_contra hne
      exact hy (hm hu y hne)
    · intro y hyS hyY
      simpa only [dite_eq_left hu] using hcEval y hyY hyS
  · apply annihilates_of_head_outside (side t (u.slot i t)) Y u c r
      hu hr hc
    intro y hyS hyY
    simpa only [dite_eq_right hu] using hcEval y hyY hyS

end TypeBlock

section ScalarExtension

variable {L J : Type*} [Ring L] [Fintype J]

/-- A fixed-vector equation survives a coefficient ring homomorphism. No
injectivity or extra equations on the original vector are needed. -/
theorem map_fixedVector (φ : K →+* L) (M : Matrix J J K) (r : J → K)
    (hfix : M *ᵥ r = r) : M.map φ *ᵥ (φ ∘ r) = φ ∘ r := by
  funext j
  calc
    (M.map φ *ᵥ (φ ∘ r)) j = φ ((M *ᵥ r) j) :=
      (φ.map_mulVec M r j).symm
    _ = φ (r j) := congrArg φ (congrFun hfix j)

end ScalarExtension

section UniversalPolynomial

open _root_.OAI.Algorithms.SubexponentialSAT.Types

variable {F E : Type*} [Field F] [Field E] {Q Δ : ℕ}

/-- The prescribed values of the correction polynomials from Section 5.3.
The matrix is the actual projector construction, over the base field `F`.
The homomorphism permits the interpolation polynomial to live over `E`. -/
noncomputable def universalPrescription (φ : F →+* E)
    (u : UniversalType Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (y : UniversalType Q Δ) (t : Fin Q) : E := by
  classical
  exact if hu : u.head t = u.slot i t then
    -extendRow (joint t (u.slot i t) i)
      (fun z => φ (MatrixSupport.jointMatrix i t (u.slot i t) R coeff
        ⟨u, hu, rfl⟩ z)) y
  else 0

/-- The actual incidence row polynomial on the universal type block. -/
noncomputable def universalRow (φ : F →+* E)
    (u : UniversalType Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (nodes : Fin Q → E) (hinj : Function.Injective nodes)
    (hne : ∀ t, nodes t ≠ 0) : UniversalType Q Δ → Polynomial E :=
  RowInterpolation.universalRowPath u i R nodes hinj hne
    (universalPrescription φ u i R coeff)

/-- The row starts at the coordinate-selection row, including its diagonal. -/
theorem universalRow_origin (φ : F →+* E)
    (u : UniversalType Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (nodes : Fin Q → E) (hinj : Function.Injective nodes)
    (hne : ∀ t, nodes t ≠ 0) :
    (fun y => (universalRow φ u i R coeff nodes hinj hne y).eval 0) =
      Pi.single u (1 : E) :=
  RowInterpolation.universalRowPath_eval_zero u i R nodes hinj hne _

/-- At most R interpolation constraints are imposed on each correction. -/
theorem universalRow_degree (φ : F →+* E)
    (u : UniversalType Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (nodes : Fin Q → E) (hinj : Function.Injective nodes)
    (hne : ∀ t, nodes t ≠ 0) (y : UniversalType Q Δ) :
    (universalRow φ u i R coeff nodes hinj hne y).natDegree ≤ R :=
  RowInterpolation.universalRowPath_natDegree_le u i R nodes hinj hne _ y

/-- Concrete row annihilation from support and the selected slot's fixed-vector
equation. The matrix support theorem discharges the Y-sparsity obligation. -/
theorem universalRow_annihilates_of_fixed (φ : F →+* E)
    (u : UniversalType Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (nodes : Fin Q → E) (hinj : Function.Injective nodes)
    (hne : ∀ t, nodes t ≠ 0) (t : Fin Q) (r : UniversalType Q Δ → F)
    (hr : ∀ y, y.head t ≠ u.slot i t → r y = 0)
    (hfix : MatrixSupport.jointMatrix i t (u.slot i t) R coeff *ᵥ
      (fun y : Joint t (u.slot i t) i => r y) =
      fun y : Joint t (u.slot i t) i => r y) :
    (fun y => (universalRow φ u i R coeff nodes hinj hne y).eval (nodes t))
      ⬝ᵥ (fun y => φ (r y)) = 0 := by
  classical
  unfold universalRow RowInterpolation.universalRowPath
  rw [RowInterpolation.eval_rowPath]
  apply typeBlock_annihilation t i u
    (RowInterpolation.correctionColumns (u.slot i) R)
    ((MatrixSupport.jointMatrix i t (u.slot i t) R coeff).map φ)
  · intro y hy
    simp only [hr y hy, map_zero]
  · intro y hy
    rw [RowInterpolation.universalCorrection_of_not_mem _ _ _ _ _ _ _ hy]
    simp
  · intro hu y hneM
    apply (RowInterpolation.mem_correctionColumns (u.slot i) R y.val).mpr
    have hbase : MatrixSupport.jointMatrix i t (u.slot i t) R coeff
        ⟨u, hu, rfl⟩ y ≠ 0 := by
      intro hz
      apply hneM
      simp only [Matrix.map_apply, hz, map_zero]
    exact MatrixSupport.jointMatrix_support i t (u.slot i t) R coeff
      ⟨u, hu, rfl⟩ y hbase
  · intro y hy hyt
    rw [RowInterpolation.universalCorrection_eval_node _ _ _ _ _ _ y
      ((RowInterpolation.mem_correctionColumns (u.slot i) R y).mp hy) t hyt]
    rfl
  · exact map_fixedVector φ _ _ hfix

/-- The full base-field subspace, imposing every slot's fixed-vector equation. -/
noncomputable def universalSpace (R : ℕ) (coeff : ℕ → F)
    (t : Fin Q) (g : Bool) : Submodule F (UniversalType Q Δ → F) :=
  SubspaceDimension.universalFixedSpace t g
    (fun i => (MatrixSupport.jointMatrix i t g R coeff).mulVecLin)

/-- Membership exposes the concrete support and matrix equations. -/
theorem mem_universalSpace (R : ℕ) (coeff : ℕ → F)
    (t : Fin Q) (g : Bool) (r : UniversalType Q Δ → F) :
    r ∈ universalSpace R coeff t g ↔
      (∀ y, y.head t ≠ g → r y = 0) ∧
      ∀ i : Fin Δ, MatrixSupport.jointMatrix i t g R coeff *ᵥ
        (fun y : Joint t g i => r y.val) = fun y : Joint t g i => r y.val := by
  rw [universalSpace, SubspaceDimension.universalFixedSpace_mem_iff]
  constructor
  · rintro ⟨hs, hf⟩
    exact ⟨fun y hy => hs y hy, fun i => (hf i).symm⟩
  · rintro ⟨hs, hf⟩
    exact ⟨fun y hy => hs y hy, fun i => (hf i).symm⟩

/-- Section 5.3, instantiated to the actual matrix, actual interpolated row,
and actual base-field fixed subspace. No annihilation or support hypothesis
remains: only membership in that independently defined subspace is required. -/
theorem universalRow_annihilates (φ : F →+* E)
    (u : UniversalType Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (nodes : Fin Q → E) (hinj : Function.Injective nodes)
    (hne : ∀ t, nodes t ≠ 0) (t : Fin Q) (r : UniversalType Q Δ → F)
    (hr : r ∈ universalSpace R coeff t (u.slot i t)) :
    (fun y => (universalRow φ u i R coeff nodes hinj hne y).eval (nodes t))
      ⬝ᵥ (fun y => φ (r y)) = 0 := by
  have h := (mem_universalSpace R coeff t (u.slot i t) r).mp hr
  exact universalRow_annihilates_of_fixed φ u i R coeff nodes hinj hne t r h.1 (h.2 i)

end UniversalPolynomial

end SubexponentialSAT.Annihilation

end OAI.Algorithms
