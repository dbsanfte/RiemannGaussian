import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.Annihilation
import OpenAISemiprime.Algorithms.SubexponentialSAT.MulticolorTypes
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpRowInterpolation
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.MatrixSupport

namespace OAI.Algorithms

/-!
# Simultaneous row annihilation for the multicolor layout

Section 3.3 of `source/subexponential-sat.txt`.  At a fixed interpolation
position, the same row annihilates every color different from its slot color.
The old two-color modules are preserved and used only for generic finite-sum
lemmas.
-/

namespace SubexponentialSAT.SubexpAnnihilation

open scoped BigOperators
open Matrix

section MatrixExtension

variable {V F E : Type*} [Ring F] [Ring E]

/-- Extend both row and column indices by zero. The membership tests are
explicit data, so this definition does not choose a representative. -/
def zeroExtendMatrix (J : Set V) [DecidablePred (· ∈ J)]
    (M : Matrix J J F) (u y : V) : F :=
  if hu : u ∈ J then
    if hy : y ∈ J then M ⟨u, hu⟩ ⟨y, hy⟩ else 0
  else 0

theorem zeroExtendMatrix_of_row_mem (J : Set V) [DecidablePred (· ∈ J)]
    (M : Matrix J J F) (u y : V) (hu : u ∈ J) :
    zeroExtendMatrix J M u y = Annihilation.extendRow J (M ⟨u, hu⟩) y := by
  classical
  by_cases hy : y ∈ J <;>
    simp [zeroExtendMatrix, Annihilation.extendRow, hu, hy]

@[simp] theorem zeroExtendMatrix_of_row_not_mem (J : Set V)
    [DecidablePred (· ∈ J)] (M : Matrix J J F) (u y : V) (hu : u ∉ J) :
    zeroExtendMatrix J M u y = 0 := by
  simp [zeroExtendMatrix, hu]

@[simp] theorem zeroExtendMatrix_of_column_not_mem (J : Set V)
    [DecidablePred (· ∈ J)] (M : Matrix J J F) (u y : V) (hy : y ∉ J) :
    zeroExtendMatrix J M u y = 0 := by
  by_cases hu : u ∈ J <;> simp [zeroExtendMatrix, hu, hy]

/-- Mapping coefficients commutes with the explicit zero extension. -/
theorem zeroExtendMatrix_map (J : Set V) [DecidablePred (· ∈ J)]
    (M : Matrix J J F) (φ : F →+* E) (u y : V) :
    zeroExtendMatrix J (M.map φ) u y = φ (zeroExtendMatrix J M u y) := by
  by_cases hu : u ∈ J <;> by_cases hy : y ∈ J <;>
    simp [zeroExtendMatrix, hu, hy, Matrix.map_apply]

end MatrixExtension

section TypeBlock

open MulticolorTypes

variable {K : Type*} [Ring K] {r Q Δ : ℕ}

/-- Finite-sum cancellation at any color other than the slot color. The
selected matrix row is required to be supported on `Y`; no assertion is
needed about unrelated rows. Diagonal corrections are included. -/
theorem typeBlock_annihilation
    (t : Fin Q) (i : Fin Δ) (u : UniversalType r Q Δ) (g : Fin r)
    (hg : g ≠ u.slot i t) (Y : Finset (UniversalType r Q Δ))
    (M : Matrix (Joint t g i) (Joint t g i) K)
    (c z : UniversalType r Q Δ → K)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hm : ∀ (hu : u.head t = g) (y : Joint t g i),
      M ⟨u, hu, hg.symm⟩ y ≠ 0 → (y : UniversalType r Q Δ) ∈ Y)
    (hcEval : ∀ y, y ∈ Y → y.head t = g →
      c y = -zeroExtendMatrix (joint t g i) M u y)
    (hfix : M *ᵥ (fun y : Joint t g i => z y) =
      fun y : Joint t g i => z y) :
    (Pi.single u 1 + c) ⬝ᵥ z = 0 := by
  classical
  by_cases hu : u.head t = g
  · apply Annihilation.annihilates_of_head_inside (side t g) (joint t g i)
      Y M ⟨u, hu, hg.symm⟩ c z hz hc ?_ ?_ hfix
    · intro y hy
      by_contra hne
      exact hy (hm hu y hne)
    · intro y hyS hyY
      rw [hcEval y hyY hyS,
        zeroExtendMatrix_of_row_mem (joint t g i) M u y ⟨hu, hg.symm⟩]
  · apply Annihilation.annihilates_of_head_outside (side t g) Y u c z hu hz hc
    intro y hyS hyY
    rw [hcEval y hyY hyS,
      zeroExtendMatrix_of_row_not_mem (joint t g i) M u y
        (fun h => hu h.1), neg_zero]

end TypeBlock

section Prescriptions

open MulticolorTypes

variable {F E : Type*} [Ring F] [Ring E] {r Q Δ : ℕ}

/-- Explicit values for the single row path. The column's own head color
chooses which matrix supplies the value, as required by equation (3.8). -/
def matrixPrescription (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) : E :=
  -φ (zeroExtendMatrix (joint t (y.head t) i) (M t (y.head t) i) u y)

/-- At every active-side coordinate, the same prescription is the negative
row of that side's matrix; the zero extension handles both missing indices. -/
theorem matrixPrescription_on_side (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) (g : Fin r)
    (hy : y.head t = g) :
    matrixPrescription φ M u i y t =
      -zeroExtendMatrix (joint t g i) ((M t g i).map φ) u y := by
  unfold matrixPrescription
  rw [hy, zeroExtendMatrix_map]

end Prescriptions

section InterpolatedRows

open MulticolorTypes SubexpRowInterpolation

variable {F E : Type*} [Ring F] [CommRing E] {r Q Δ : ℕ}
variable {node : Fin Q → E}

/-- The explicit multicolor polynomial row for a supplied matrix family. -/
noncomputable def rowForMatrices (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) : UniversalType r Q Δ → Polynomial E :=
  mismatchRowPath u (fun y => y.head) (u.slot i) R units
    (matrixPrescription φ M u i)

/-- Executable scalar evaluation of the same row formula, from the supplied
matrix entries, field operations, and explicit inverse data. -/
def rowEvalForMatrices (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) (x : E) : E :=
  mismatchRowEval u (fun y => y.head) (u.slot i) R units
    (matrixPrescription φ M u i) y x

theorem rowEvalForMatrices_eq (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) (x : E) :
    rowEvalForMatrices φ M u i R units y x =
      (rowForMatrices φ M u i R units y).eval x :=
  mismatchRowEval_eq _ _ _ _ _ _ _ _

/-- A finite expression tree for each polynomial row coordinate. Its
constructor is executable from the supplied matrix entries and inverse data. -/
def rowCodeForMatrices (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) : PolynomialCode E :=
  mismatchRowCode u (fun y => y.head) (u.slot i) R units
    (matrixPrescription φ M u i) y

theorem rowCodeForMatrices_denote (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) :
    (rowCodeForMatrices φ M u i R units y).denote =
      rowForMatrices φ M u i R units y :=
  mismatchRowCode_denote _ _ _ _ _ _ _

theorem rowCodeForMatrices_eval (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) (x : E) :
    (rowCodeForMatrices φ M u i R units y).eval x =
      (rowForMatrices φ M u i R units y).eval x :=
  mismatchRowCode_eval _ _ _ _ _ _ _ _

theorem rowForMatrices_origin (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) :
    (fun y => (rowForMatrices φ M u i R units y).eval 0) = Pi.single u 1 :=
  mismatchRowPath_eval_zero _ _ _ _ _ _

theorem rowForMatrices_degree (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) :
    (rowForMatrices φ M u i R units y).natDegree ≤ R :=
  mismatchRowPath_natDegree_le _ _ _ _ _ _ _

/-- The same interpolated row annihilates every other color, provided the
actual matrix family has the mismatch support asserted in equation (3.6). -/
theorem rowForMatrices_annihilates_of_fixed (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node)
    (hM : ∀ t g i (a b : Joint t g i), M t g i a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot i) b.val).card ≤ R)
    (t : Fin Q) (g : Fin r) (hg : g ≠ u.slot i t)
    (z : UniversalType r Q Δ → F)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hfix : M t g i *ᵥ (fun y : Joint t g i => z y) =
      fun y : Joint t g i => z y) :
    (fun y => (rowForMatrices φ M u i R units y).eval (node t))
      ⬝ᵥ (fun y => φ (z y)) = 0 := by
  classical
  unfold rowForMatrices mismatchRowPath
  rw [eval_rowPath]
  apply typeBlock_annihilation t i u g hg
    (correctionColumns (fun y => y.head) (u.slot i) R) ((M t g i).map φ)
  · intro y hy
    simp only [hz y hy, map_zero]
  · intro y hy
    rw [mismatchCorrection_of_not_mem _ _ _ _ _ _ hy]
    simp
  · intro hu y hne
    apply (mem_correctionColumns (fun y => y.head) (u.slot i) R y.val).mpr
    apply hM t g i ⟨u, hu, hg.symm⟩ y
    intro hzero
    exact hne (by simp only [Matrix.map_apply, hzero, map_zero])
  · intro y hy hyt
    have hcard : (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (u.slot i) y).card ≤ R :=
      (mem_correctionColumns (fun y : UniversalType r Q Δ => y.head)
        (u.slot i) R y).mp hy
    exact (mismatchCorrection_eval_other_color
      (fun y : UniversalType r Q Δ => y.head) (u.slot i) R units
      (matrixPrescription φ M u i) y hcard t g hg hyt).trans
        (matrixPrescription_on_side φ M u i y t g hyt)
  · exact Annihilation.map_fixedVector φ _ _ hfix

end InterpolatedRows

section FixedSpaces

open MulticolorTypes SubexpRowInterpolation

variable {F E : Type*} [Field F] [CommRing E] {r Q Δ : ℕ}
variable {node : Fin Q → E}

/-- Fixed-space form of the preceding theorem. The subspace is the canonical
multicolor subspace from the dimension module, not a second definition. -/
theorem rowForMatrices_annihilates (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node)
    (hM : ∀ t g i (a b : Joint t g i), M t g i a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot i) b.val).card ≤ R)
    (t : Fin Q) (g : Fin r) (hg : g ≠ u.slot i t)
    (z : UniversalType r Q Δ → F)
    (hz : z ∈ Subexp.SubspaceDimension.universalFixedSpace t g
      (fun i => (M t g i).mulVecLin)) :
    (fun y => (rowForMatrices φ M u i R units y).eval (node t))
      ⬝ᵥ (fun y => φ (z y)) = 0 := by
  have h := (Subexp.SubspaceDimension.universalFixedSpace_mem_iff t g
    (fun i => (M t g i).mulVecLin) z).mp hz
  exact rowForMatrices_annihilates_of_fixed φ M u i R units hM t g hg z
    h.1 (h.2 i).symm

end FixedSpaces

section ActualSwapMatrices

open MulticolorTypes SubexpRowInterpolation

variable {F E : Type*} [Field F] [CommRing E] {r Q Δ : ℕ}
variable {node : Fin Q → E}

/-- The single explicit polynomial row for the actual multicolor swap
matrices. The coefficients of the spectral polynomial are supplied directly. -/
noncomputable def universalRow (φ : F →+* E)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (units : NodeUnits node) : UniversalType r Q Δ → Polynomial E :=
  rowForMatrices φ (fun t g i => Subexp.MatrixSupport.jointMatrix i t g R coeff)
    u i R units

theorem universalRow_origin (φ : F →+* E)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (units : NodeUnits node) :
    (fun y => (universalRow φ u i R coeff units y).eval 0) = Pi.single u 1 :=
  rowForMatrices_origin φ _ u i R units

theorem universalRow_coeff_zero (φ : F →+* E)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (units : NodeUnits node) :
    (fun y => (universalRow φ u i R coeff units y).coeff 0) = Pi.single u 1 := by
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using
    universalRow_origin φ u i R coeff units

theorem universalRow_degree (φ : F →+* E)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (units : NodeUnits node) (y : UniversalType r Q Δ) :
    (universalRow φ u i R coeff units y).natDegree ≤ R :=
  rowForMatrices_degree φ _ u i R units y

/-- Section 3.3 for the actual swap matrix and explicit interpolation formula.
The mismatch support property is proved by the matrix construction, rather
than assumed. This one row annihilates every `g ≠ u.slot i t`. -/
theorem universalRow_annihilates (φ : F →+* E)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (coeff : ℕ → F)
    (units : NodeUnits node) (t : Fin Q) (g : Fin r) (hg : g ≠ u.slot i t)
    (z : UniversalType r Q Δ → F)
    (hz : z ∈ Subexp.SubspaceDimension.universalFixedSpace t g
      (fun i => (Subexp.MatrixSupport.jointMatrix i t g R coeff).mulVecLin)) :
    (fun y => (universalRow φ u i R coeff units y).eval (node t))
      ⬝ᵥ (fun y => φ (z y)) = 0 := by
  apply rowForMatrices_annihilates φ
    (fun t g i => Subexp.MatrixSupport.jointMatrix i t g R coeff)
    u i R units ?_ t g hg z hz
  intro t g i a b hab
  exact Subexp.MatrixSupport.jointMatrix_support i t g R coeff a b hab

end ActualSwapMatrices

end SubexponentialSAT.SubexpAnnihilation

end OAI.Algorithms
