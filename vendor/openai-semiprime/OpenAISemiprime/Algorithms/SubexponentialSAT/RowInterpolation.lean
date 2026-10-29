import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.TableInterpolation
import OpenAISemiprime.Algorithms.SubexponentialSAT.Types

namespace OAI.Algorithms

/-!
# Row correction polynomials

The interpolation construction in Section 5.3. A finite set of nonzero
nodes is augmented by the node zero, where the correction is prescribed
to vanish. The resulting actual Lagrange polynomial has degree at most
the number of nonzero constraints.
-/

noncomputable section

namespace SubexponentialSAT.RowInterpolation

variable {E ι V : Type*} [Field E] [DecidableEq ι]

/-- The extra `none` index denotes the node zero. -/
def augmentedNode (s : Finset ι) (v : ι → E) : Option {i // i ∈ s} → E
  | none => 0
  | some i => v i.val

/-- The value of a correction at the extra node is zero. -/
def augmentedValue (s : Finset ι) (d : ι → E) : Option {i // i ∈ s} → E
  | none => 0
  | some i => d i.val

omit [DecidableEq ι] in
theorem augmentedNode_injective (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) :
    Function.Injective (augmentedNode s v) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim (hne j.val j.property hij.symm)
  | some i =>
    cases j with
    | none => exact False.elim (hne i.val i.property hij)
    | some j =>
      apply congrArg some
      apply Subtype.ext
      exact hinj i.property j.property hij

omit [DecidableEq ι] in
theorem augmentedNode_unitDifferences (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) :
    TableInterpolation.UnitDifferences (augmentedNode s v) := by
  intro i j hij
  apply isUnit_iff_ne_zero.mpr
  intro h
  exact hij (augmentedNode_injective s v hinj hne (sub_eq_zero.mp h))

/-- An explicit Lagrange correction with an additional zero constraint. -/
def correctionPolynomial (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) (d : ι → E) : Polynomial E :=
  TableInterpolation.interpolate (augmentedNode s v)
    (augmentedNode_unitDifferences s v hinj hne) (augmentedValue s d)

@[simp] theorem correctionPolynomial_eval_zero (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) (d : ι → E) :
    (correctionPolynomial s v hinj hne d).eval 0 = 0 := by
  exact TableInterpolation.eval_interpolate (augmentedNode s v)
    (augmentedNode_unitDifferences s v hinj hne) (augmentedValue s d) none

@[simp] theorem correctionPolynomial_coeff_zero (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) (d : ι → E) :
    (correctionPolynomial s v hinj hne d).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact correctionPolynomial_eval_zero s v hinj hne d

theorem correctionPolynomial_eval_node (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) (d : ι → E) {i : ι} (hi : i ∈ s) :
    (correctionPolynomial s v hinj hne d).eval (v i) = d i := by
  exact TableInterpolation.eval_interpolate (augmentedNode s v)
    (augmentedNode_unitDifferences s v hinj hne) (augmentedValue s d) (some ⟨i, hi⟩)

theorem correctionPolynomial_natDegree_le (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) (d : ι → E) :
    (correctionPolynomial s v hinj hne d).natDegree ≤ s.card := by
  unfold correctionPolynomial
  simpa only [Fintype.card_option, Fintype.card_coe, Nat.add_sub_cancel]
    using TableInterpolation.natDegree_interpolate_le (augmentedNode s v)
      (augmentedNode_unitDifferences s v hinj hne) (augmentedValue s d)

/-- Existence follows from the actual polynomial above, not an interpolation axiom. -/
theorem exists_correctionPolynomial (s : Finset ι) (v : ι → E)
    (hinj : Set.InjOn v (↑s : Set ι))
    (hne : ∀ i ∈ s, v i ≠ 0) (d : ι → E) {R : ℕ} (hcard : s.card ≤ R) :
    ∃ h : Polynomial E, h.natDegree ≤ R ∧ h.eval 0 = 0 ∧
      ∀ i ∈ s, h.eval (v i) = d i := by
  refine ⟨correctionPolynomial s v hinj hne d,
    (correctionPolynomial_natDegree_le s v hinj hne d).trans hcard,
    correctionPolynomial_eval_zero s v hinj hne d, ?_⟩
  intro i hi
  exact correctionPolynomial_eval_node s v hinj hne d hi

variable [DecidableEq V]

/-- Corrections are constructed only on selected columns and are zero elsewhere. -/
def columnCorrection (Y : Finset V) (A : V → Finset ι) (v : ι → E)
    (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) (y : V) : Polynomial E :=
  if y ∈ Y then
    correctionPolynomial (A y) v hinj.injOn (fun i _hi => hne i) (d y)
  else 0

@[simp] theorem columnCorrection_of_not_mem (Y : Finset V) (A : V → Finset ι)
    (v : ι → E) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) {y : V} (hy : y ∉ Y) :
    columnCorrection Y A v hinj hne d y = 0 := by
  simp [columnCorrection, hy]

@[simp] theorem columnCorrection_eval_zero (Y : Finset V) (A : V → Finset ι)
    (v : ι → E) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) (y : V) :
    (columnCorrection Y A v hinj hne d y).eval 0 = 0 := by
  by_cases hy : y ∈ Y <;> simp [columnCorrection, hy]

theorem columnCorrection_eval_node (Y : Finset V) (A : V → Finset ι)
    (v : ι → E) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) {y : V} (hy : y ∈ Y) {i : ι} (hi : i ∈ A y) :
    (columnCorrection Y A v hinj hne d y).eval (v i) = d y i := by
  simp only [columnCorrection, ite_eq_left hy]
  exact correctionPolynomial_eval_node (A y) v hinj.injOn (fun i _hi => hne i) (d y) hi

theorem columnCorrection_natDegree_le (Y : Finset V) (A : V → Finset ι)
    (v : ι → E) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) {R : ℕ} (hcard : ∀ y ∈ Y, (A y).card ≤ R) (y : V) :
    (columnCorrection Y A v hinj hne d y).natDegree ≤ R := by
  by_cases hy : y ∈ Y
  · simp only [columnCorrection, ite_eq_left hy]
    exact (correctionPolynomial_natDegree_le (A y) v hinj.injOn
      (fun i _hi => hne i) (d y)).trans (hcard y hy)
  · simp [columnCorrection, hy]

/-- Add a correction row to the constant coordinate-selection row. -/
def rowPath (u : V) (c : V → Polynomial E) : V → Polynomial E :=
  fun y => Polynomial.C ((Pi.single u (1 : E) : V → E) y) + c y

theorem eval_rowPath (u : V) (c : V → Polynomial E) (t : E) :
    (fun y => (rowPath u c y).eval t) =
      Pi.single u (1 : E) + (fun y => (c y).eval t) := by
  funext y
  simp [rowPath]

/-- The formula includes the diagonal correction when `u` is a selected column. -/
theorem rowPath_eval_zero (u : V) (c : V → Polynomial E)
    (hc : ∀ y, (c y).eval 0 = 0) :
    (fun y => (rowPath u c y).eval 0) = Pi.single u (1 : E) := by
  funext y
  simp [rowPath, hc]

theorem rowPath_natDegree_le (u : V) (c : V → Polynomial E) {R : ℕ}
    (hc : ∀ y, (c y).natDegree ≤ R) (y : V) :
    (rowPath u c y).natDegree ≤ R := by
  unfold rowPath
  exact Polynomial.natDegree_add_le_of_degree_le (by simp) (hc y)

/-- The row path using the actual finite-node correction construction. -/
def interpolatedRowPath (u : V) (Y : Finset V) (A : V → Finset ι) (v : ι → E)
    (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) : V → Polynomial E :=
  rowPath u (columnCorrection Y A v hinj hne d)

theorem interpolatedRowPath_eval_zero (u : V) (Y : Finset V) (A : V → Finset ι)
    (v : ι → E) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) :
    (fun y => (interpolatedRowPath u Y A v hinj hne d y).eval 0) =
      Pi.single u (1 : E) :=
  rowPath_eval_zero u _ (columnCorrection_eval_zero Y A v hinj hne d)

theorem interpolatedRowPath_natDegree_le (u : V) (Y : Finset V) (A : V → Finset ι)
    (v : ι → E) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (d : V → ι → E) {R : ℕ} (hcard : ∀ y ∈ Y, (A y).card ≤ R) (y : V) :
    (interpolatedRowPath u Y A v hinj hne d y).natDegree ≤ R :=
  rowPath_natDegree_le u _ (columnCorrection_natDegree_le Y A v hinj hne d hcard) y

section UniversalTypes

variable {Q Δ : ℕ}

/-- Exactly the interpolation positions where a column is on the active side. -/
def agreementPositions (σ : Types.Word Q) (y : Types.UniversalType Q Δ) :
    Finset (Fin Q) :=
  Finset.univ.filter (fun t => y.head t = σ t)

@[simp] theorem mem_agreementPositions (σ : Types.Word Q)
    (y : Types.UniversalType Q Δ) (t : Fin Q) :
    t ∈ agreementPositions σ y ↔ y.head t = σ t := by
  simp [agreementPositions]

/-- The set `Y` of columns with at most `R` active interpolation positions. -/
def correctionColumns (σ : Types.Word Q) (R : ℕ) :
    Finset (Types.UniversalType Q Δ) :=
  Finset.univ.filter (fun y => (agreementPositions σ y).card ≤ R)

@[simp] theorem mem_correctionColumns (σ : Types.Word Q) (R : ℕ)
    (y : Types.UniversalType Q Δ) :
    y ∈ correctionColumns σ R ↔ (agreementPositions σ y).card ≤ R := by
  simp [correctionColumns]

/-- The actual family of correction polynomials on a universal type block. -/
def universalCorrection (σ : Types.Word Q) (R : ℕ) (v : Fin Q → E)
    (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) :
    Types.UniversalType Q Δ → Polynomial E :=
  columnCorrection (correctionColumns σ R) (agreementPositions σ) v hinj hne d

@[simp] theorem universalCorrection_eval_zero (σ : Types.Word Q) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) (y : Types.UniversalType Q Δ) :
    (universalCorrection σ R v hinj hne d y).eval 0 = 0 :=
  columnCorrection_eval_zero _ _ _ _ _ _ _

theorem universalCorrection_eval_node (σ : Types.Word Q) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) (y : Types.UniversalType Q Δ)
    (hy : (agreementPositions σ y).card ≤ R) (t : Fin Q) (ht : y.head t = σ t) :
    (universalCorrection σ R v hinj hne d y).eval (v t) = d y t := by
  apply columnCorrection_eval_node
  · exact (mem_correctionColumns σ R y).mpr hy
  · exact (mem_agreementPositions σ y t).mpr ht

theorem universalCorrection_natDegree_le (σ : Types.Word Q) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) (y : Types.UniversalType Q Δ) :
    (universalCorrection σ R v hinj hne d y).natDegree ≤ R := by
  apply columnCorrection_natDegree_le
  intro z hz
  exact (mem_correctionColumns σ R z).mp hz

theorem universalCorrection_of_not_mem (σ : Types.Word Q) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) (y : Types.UniversalType Q Δ)
    (hy : y ∉ correctionColumns σ R) :
    universalCorrection σ R v hinj hne d y = 0 :=
  columnCorrection_of_not_mem _ _ _ _ _ _ hy

/-- The polynomial row starting at type `u` and following its incidence slot `i`. -/
def universalRowPath (u : Types.UniversalType Q Δ) (i : Fin Δ) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) :
    Types.UniversalType Q Δ → Polynomial E :=
  rowPath u (universalCorrection (u.slot i) R v hinj hne d)

theorem universalRowPath_eval_zero (u : Types.UniversalType Q Δ) (i : Fin Δ) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) :
    (fun y => (universalRowPath u i R v hinj hne d y).eval 0) =
      Pi.single u (1 : E) :=
  rowPath_eval_zero u _ (universalCorrection_eval_zero (u.slot i) R v hinj hne d)

theorem universalRowPath_natDegree_le (u : Types.UniversalType Q Δ) (i : Fin Δ) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) (y : Types.UniversalType Q Δ) :
    (universalRowPath u i R v hinj hne d y).natDegree ≤ R :=
  rowPath_natDegree_le u _ (universalCorrection_natDegree_le (u.slot i) R v hinj hne d) y

/-- Coefficientwise lifting can preserve the starting coordinate row exactly. -/
theorem universalRowPath_coeff_zero (u : Types.UniversalType Q Δ) (i : Fin Δ) (R : ℕ)
    (v : Fin Q → E) (hinj : Function.Injective v) (hne : ∀ t, v t ≠ 0)
    (d : Types.UniversalType Q Δ → Fin Q → E) :
    (fun y => (universalRowPath u i R v hinj hne d y).coeff 0) =
      Pi.single u (1 : E) := by
  funext y
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact congrFun (universalRowPath_eval_zero u i R v hinj hne d) y

end UniversalTypes

end SubexponentialSAT.RowInterpolation

end

end OAI.Algorithms
