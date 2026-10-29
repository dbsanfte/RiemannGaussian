import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

/-- Actual invertible elements for every denominator used in interpolation. -/
structure NodeUnits (node : I → E) where
  nodeUnit : I → Eˣ
  nodeUnit_val : ∀ i, (nodeUnit i : E) = node i
  differenceUnit : (i j : I) → i ≠ j → Eˣ
  differenceUnit_val : ∀ i j hij, (differenceUnit i j hij : E) = node i - node j

namespace NodeUnits

variable {node : I → E}

/-- The supplied inverse of a nonzero interpolation node. -/
def nodeInverse (u : NodeUnits node) (i : I) : E := ↑((u.nodeUnit i)⁻¹)

/-- The diagonal branch is unused by products over `erase i`. -/
def differenceInverse (u : NodeUnits node) (i j : I) : E :=
  if hij : i ≠ j then ↑((u.differenceUnit i j hij)⁻¹) else 0

omit [DecidableEq I] in
theorem nodeInverse_mul (u : NodeUnits node) (i : I) :
    u.nodeInverse i * node i = 1 := by
  rw [nodeInverse, ← u.nodeUnit_val i]
  exact Units.inv_mul (u.nodeUnit i)

theorem differenceInverse_mul (u : NodeUnits node) {i j : I} (hij : i ≠ j) :
    u.differenceInverse i j * (node i - node j) = 1 := by
  rw [differenceInverse, dite_eq_left hij, ← u.differenceUnit_val i j hij]
  exact Units.inv_mul (u.differenceUnit i j hij)

end NodeUnits

section FieldUnits

variable {F : Type*} [Field F]

/-- Construct the unit data directly from field inversion and its laws. -/
def NodeUnits.ofField (node : I → F) (hinj : Function.Injective node)
    (hne : ∀ i, node i ≠ 0) : NodeUnits node where
  nodeUnit i := Units.mk0 (node i) (hne i)
  nodeUnit_val _ := rfl
  differenceUnit i j hij := Units.mk0 (node i - node j)
    (fun h => hij (hinj (sub_eq_zero.mp h)))
  differenceUnit_val _ _ _ := rfl

end FieldUnits

variable {node : I → E}

/-- A normalized linear factor vanishing at node `j` and equal to one at `i`. -/
noncomputable def basisDivisor (u : NodeUnits node) (i j : I) : Polynomial E :=
  Polynomial.C (u.differenceInverse i j) * (Polynomial.X - Polynomial.C (node j))

@[simp] theorem basisDivisor_eval_right (u : NodeUnits node) (i j : I) :
    (basisDivisor u i j).eval (node j) = 0 := by
  simp [basisDivisor]

theorem basisDivisor_eval_left (u : NodeUnits node) {i j : I} (hij : i ≠ j) :
    (basisDivisor u i j).eval (node i) = 1 := by
  simpa [basisDivisor] using u.differenceInverse_mul hij

theorem basisDivisor_natDegree_le (u : NodeUnits node) (i j : I) :
    (basisDivisor u i j).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa using (Polynomial.natDegree_X_le (R := E)))

/-- The source's `T / λ_i` times the Lagrange product. -/
noncomputable def basis (u : NodeUnits node) (s : Finset I) (i : I) : Polynomial E :=
  (Polynomial.C (u.nodeInverse i) * Polynomial.X) *
    ∏ j ∈ s.erase i, basisDivisor u i j

@[simp] theorem basis_eval_zero (u : NodeUnits node) (s : Finset I) (i : I) :
    (basis u s i).eval 0 = 0 := by
  simp [basis]

@[simp] theorem basis_eval_self (u : NodeUnits node) (s : Finset I) (i : I) :
    (basis u s i).eval (node i) = 1 := by
  simp only [basis, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_prod, u.nodeInverse_mul, one_mul]
  apply Finset.prod_eq_one
  intro j hj
  exact basisDivisor_eval_left u (Finset.ne_of_mem_erase hj).symm

theorem basis_eval_other (u : NodeUnits node) (s : Finset I)
    {i j : I} (hij : i ≠ j) (hj : j ∈ s) :
    (basis u s i).eval (node j) = 0 := by
  simp only [basis, Polynomial.eval_mul, Polynomial.eval_prod]
  have hprod : (∏ k ∈ s.erase i, (basisDivisor u i k).eval (node j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)
      (basisDivisor_eval_right u i j)
  rw [hprod, mul_zero]

theorem basis_eval_node (u : NodeUnits node) (s : Finset I) (i j : I) (hj : j ∈ s) :
    (basis u s i).eval (node j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, basis_eval_other u s hij hj]

theorem basis_natDegree_le (u : NodeUnits node) (s : Finset I) {i : I} (hi : i ∈ s) :
    (basis u s i).natDegree ≤ s.card := by
  have hprod : (∏ j ∈ s.erase i, basisDivisor u i j).natDegree ≤ (s.erase i).card := by
    calc
      _ ≤ ∑ j ∈ s.erase i, (basisDivisor u i j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ s.erase i, 1 :=
        Finset.sum_le_sum (fun j _hj => basisDivisor_natDegree_le u i j)
      _ = (s.erase i).card := by simp
  calc
    (basis u s i).natDegree ≤ 1 + (s.erase i).card := by
      apply Polynomial.natDegree_mul_le_of_le
      · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      · exact hprod
    _ = s.card := by rw [Nat.add_comm, Finset.card_erase_add_one hi]

/-- Explicit correction polynomial, including the empty-constraint case. -/
noncomputable def correctionPolynomial (u : NodeUnits node) (s : Finset I) (d : I → E) :
    Polynomial E :=
  ∑ i ∈ s, Polynomial.C (d i) * basis u s i

@[simp] theorem correctionPolynomial_eval_zero (u : NodeUnits node) (s : Finset I) (d : I → E) :
    (correctionPolynomial u s d).eval 0 = 0 := by
  simp [correctionPolynomial, Polynomial.eval_finsetSum]

@[simp] theorem correctionPolynomial_coeff_zero (u : NodeUnits node) (s : Finset I) (d : I → E) :
    (correctionPolynomial u s d).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, correctionPolynomial_eval_zero]

theorem correctionPolynomial_eval_node (u : NodeUnits node) (s : Finset I) (d : I → E)
    {j : I} (hj : j ∈ s) :
    (correctionPolynomial u s d).eval (node j) = d j := by
  simp [correctionPolynomial, Polynomial.eval_finsetSum, basis_eval_node u s _ _ hj, hj]

theorem correctionPolynomial_natDegree_le (u : NodeUnits node) (s : Finset I) (d : I → E) :
    (correctionPolynomial u s d).natDegree ≤ s.card := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans (basis_natDegree_le u s hi)

/-- Direct finite evaluation of the source's displayed interpolation formula. -/
def correctionEval (u : NodeUnits node) (s : Finset I) (d : I → E) (x : E) : E :=
  ∑ i ∈ s, d i * ((u.nodeInverse i * x) *
    ∏ j ∈ s.erase i, u.differenceInverse i j * (x - node j))

theorem correctionEval_eq (u : NodeUnits node) (s : Finset I) (d : I → E) (x : E) :
    correctionEval u s d x = (correctionPolynomial u s d).eval x := by
  simp [correctionEval, correctionPolynomial, basis, basisDivisor,
    Polynomial.eval_finsetSum, Polynomial.eval_prod]

variable [DecidableEq V]

/-- One correction for each selected column, and the zero polynomial elsewhere. -/
noncomputable def columnCorrection (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) (y : V) : Polynomial E :=
  if y ∈ Y then correctionPolynomial u (A y) (d y) else 0

@[simp] theorem columnCorrection_of_not_mem (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) {y : V} (hy : y ∉ Y) :
    columnCorrection Y A u d y = 0 := by
  simp [columnCorrection, hy]

@[simp] theorem columnCorrection_eval_zero (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (columnCorrection Y A u d y).eval 0 = 0 := by
  by_cases hy : y ∈ Y <;> simp [columnCorrection, hy]

theorem columnCorrection_eval_node (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) {y : V} (hy : y ∈ Y)
    {i : I} (hi : i ∈ A y) :
    (columnCorrection Y A u d y).eval (node i) = d y i := by
  simp only [columnCorrection, ite_eq_left hy]
  exact correctionPolynomial_eval_node u (A y) (d y) hi

theorem columnCorrection_natDegree_le (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) {R : ℕ}
    (hcard : ∀ y ∈ Y, (A y).card ≤ R) (y : V) :
    (columnCorrection Y A u d y).natDegree ≤ R := by
  by_cases hy : y ∈ Y
  · simp only [columnCorrection, ite_eq_left hy]
    exact (correctionPolynomial_natDegree_le u (A y) (d y)).trans (hcard y hy)
  · simp [columnCorrection, hy]

/-- Scalar execution of the column correction formula. -/
def columnEval (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) (y : V) (x : E) : E :=
  if y ∈ Y then correctionEval u (A y) (d y) x else 0

theorem columnEval_eq (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) (y : V) (x : E) :
    columnEval Y A u d y x = (columnCorrection Y A u d y).eval x := by
  by_cases hy : y ∈ Y <;> simp [columnEval, columnCorrection, hy, correctionEval_eq]

/-- The initial selector is retained even when its own column gets a correction. -/
noncomputable def rowPath (v : V) (c : V → Polynomial E) : V → Polynomial E :=
  fun y => Polynomial.C ((Pi.single v (1 : E) : V → E) y) + c y

theorem eval_rowPath (v : V) (c : V → Polynomial E) (x : E) :
    (fun y => (rowPath v c y).eval x) =
      Pi.single v (1 : E) + (fun y => (c y).eval x) := by
  funext y
  simp [rowPath]

theorem rowPath_eval_zero (v : V) (c : V → Polynomial E)
    (hc : ∀ y, (c y).eval 0 = 0) :
    (fun y => (rowPath v c y).eval 0) = Pi.single v (1 : E) := by
  funext y
  simp [rowPath, hc]

theorem rowPath_natDegree_le (v : V) (c : V → Polynomial E) {R : ℕ}
    (hc : ∀ y, (c y).natDegree ≤ R) (y : V) :
    (rowPath v c y).natDegree ≤ R := by
  exact Polynomial.natDegree_add_le_of_degree_le (by simp) (hc y)

section Mismatches

variable [Fintype I] [Fintype V] [DecidableEq C]

/-- A column needs a prescribed value exactly when its head differs from the factor color. -/
def mismatchPositions (head : V → I → C) (σ : I → C) (y : V) : Finset I :=
  Finset.univ.filter (fun t => head y t ≠ σ t)

omit [DecidableEq I] [DecidableEq V] [Fintype V] in
@[simp] theorem mem_mismatchPositions (head : V → I → C) (σ : I → C) (y : V) (t : I) :
    t ∈ mismatchPositions head σ y ↔ head y t ≠ σ t := by
  simp [mismatchPositions]

/-- The actual `Y` in Section 3.3, defined by a mismatch-count bound. -/
def correctionColumns (head : V → I → C) (σ : I → C) (R : ℕ) : Finset V :=
  Finset.univ.filter (fun y => (mismatchPositions head σ y).card ≤ R)

omit [DecidableEq I] [DecidableEq V] in
@[simp] theorem mem_correctionColumns (head : V → I → C) (σ : I → C) (R : ℕ) (y : V) :
    y ∈ correctionColumns head σ R ↔ (mismatchPositions head σ y).card ≤ R := by
  simp [correctionColumns]

/-- Simultaneous correction values: one polynomial is reused for every other color. -/
noncomputable def mismatchCorrection (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) : V → Polynomial E :=
  columnCorrection (correctionColumns head σ R) (mismatchPositions head σ) u d

@[simp] theorem mismatchCorrection_eval_zero (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (mismatchCorrection head σ R u d y).eval 0 = 0 :=
  columnCorrection_eval_zero _ _ _ _ _

theorem mismatchCorrection_of_not_mem (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V)
    (hy : y ∉ correctionColumns head σ R) :
    mismatchCorrection head σ R u d y = 0 :=
  columnCorrection_of_not_mem _ _ _ _ hy

theorem mismatchCorrection_eval_node (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V)
    (hy : (mismatchPositions head σ y).card ≤ R) (t : I) (ht : head y t ≠ σ t) :
    (mismatchCorrection head σ R u d y).eval (node t) = d y t := by
  apply columnCorrection_eval_node
  · exact (mem_correctionColumns head σ R y).mpr hy
  · exact (mem_mismatchPositions head σ y t).mpr ht

/-- Each other-color side uses the same polynomial and its unique prescription at `t`. -/
theorem mismatchCorrection_eval_other_color (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V)
    (hy : (mismatchPositions head σ y).card ≤ R) (t : I)
    (g : C) (hg : g ≠ σ t) (hyg : head y t = g) :
    (mismatchCorrection head σ R u d y).eval (node t) = d y t :=
  mismatchCorrection_eval_node head σ R u d y hy t (hyg ▸ hg)

theorem mismatchCorrection_natDegree_le (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (mismatchCorrection head σ R u d y).natDegree ≤ R := by
  apply columnCorrection_natDegree_le
  intro z hz
  exact (mem_correctionColumns head σ R z).mp hz

/-- The actual polynomial row formed from all mismatch corrections. -/
noncomputable def mismatchRowPath (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) : V → Polynomial E :=
  rowPath v (mismatchCorrection head σ R u d)

theorem mismatchRowPath_eval_zero (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) :
    (fun y => (mismatchRowPath v head σ R u d y).eval 0) = Pi.single v (1 : E) :=
  rowPath_eval_zero v _ (mismatchCorrection_eval_zero head σ R u d)

theorem mismatchRowPath_natDegree_le (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (mismatchRowPath v head σ R u d y).natDegree ≤ R :=
  rowPath_natDegree_le v _ (mismatchCorrection_natDegree_le head σ R u d) y

theorem mismatchRowPath_coeff_zero (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) :
    (fun y => (mismatchRowPath v head σ R u d y).coeff 0) = Pi.single v (1 : E) := by
  funext y
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact congrFun (mismatchRowPath_eval_zero v head σ R u d) y

/-- Execute an evaluation of a row from ring operations and the supplied units. -/
def mismatchRowEval (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) (x : E) : E :=
  (Pi.single v (1 : E) : V → E) y +
    columnEval (correctionColumns head σ R) (mismatchPositions head σ) u d y x

theorem mismatchRowEval_eq (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) (x : E) :
    mismatchRowEval v head σ R u d y x =
      (mismatchRowPath v head σ R u d y).eval x := by
  simp [mismatchRowEval, mismatchRowPath, rowPath, mismatchCorrection, columnEval_eq]

end Mismatches

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

/-- Finite arithmetic expression data for a univariate polynomial. -/
inductive PolynomialCode (E : Type*) where
  | constant (a : E)
  | indeterminate
  | add (p q : PolynomialCode E)
  | mul (p q : PolynomialCode E)

namespace PolynomialCode

/-- Mathematical meaning of the finite expression. -/
noncomputable def denote : PolynomialCode E → Polynomial E
  | constant a => Polynomial.C a
  | indeterminate => Polynomial.X
  | add p q => p.denote + q.denote
  | mul p q => p.denote * q.denote

/-- Direct execution using the supplied coefficient ring operations. -/
def eval (x : E) : PolynomialCode E → E
  | constant a => a
  | indeterminate => x
  | add p q => p.eval x + q.eval x
  | mul p q => p.eval x * q.eval x

theorem eval_eq (p : PolynomialCode E) (x : E) : p.eval x = p.denote.eval x := by
  induction p with
  | constant a => simp [eval, denote]
  | indeterminate => simp [eval, denote]
  | add p q hp hq => simp [eval, denote, hp, hq]
  | mul p q hp hq => simp [eval, denote, hp, hq]

def sum (ps : List (PolynomialCode E)) : PolynomialCode E :=
  ps.foldr add (constant 0)

def product (ps : List (PolynomialCode E)) : PolynomialCode E :=
  ps.foldr mul (constant 1)

theorem denote_sum (ps : List (PolynomialCode E)) :
    (sum ps).denote = (ps.map denote).sum := by
  induction ps with
  | nil => simp [sum, denote]
  | cons p ps ih => simp [sum, denote, ← ih, sum]

theorem denote_product (ps : List (PolynomialCode E)) :
    (product ps).denote = (ps.map denote).prod := by
  induction ps with
  | nil => simp [product, denote]
  | cons p ps ih => simp [product, denote, ← ih, product]

end PolynomialCode

section FiniteCode

variable {Q : ℕ} {node : Fin Q → E}

/-- Executable expression for a Lagrange basis with zero constant term. -/
def basisCode (u : NodeUnits node) (s : Finset (Fin Q)) (i : Fin Q) : PolynomialCode E :=
  .mul (.mul (.constant (u.nodeInverse i)) .indeterminate)
    (PolynomialCode.product (List.ofFn (fun j : Fin Q =>
      if j ∈ s.erase i then
        .mul (.constant (u.differenceInverse i j))
          (.add .indeterminate (.constant (-node j)))
      else .constant 1)))

theorem basisCode_denote (u : NodeUnits node) (s : Finset (Fin Q)) (i : Fin Q) :
    (basisCode u s i).denote = basis u s i := by
  have hs : Finset.univ.filter (fun a : Fin Q => a ≠ i ∧ a ∈ s) = s.erase i := by
    ext a
    simp
  simp [basisCode, PolynomialCode.denote, PolynomialCode.denote_product,
    List.map_ofFn, Fin.prod_ofFn, basis, basisDivisor, ← Finset.prod_filter,
    sub_eq_add_neg, apply_ite, hs]

/-- Executable constructor for the actual correction polynomial. -/
def correctionCode (u : NodeUnits node) (s : Finset (Fin Q)) (d : Fin Q → E) :
    PolynomialCode E :=
  PolynomialCode.sum (List.ofFn (fun i : Fin Q =>
    if i ∈ s then .mul (.constant (d i)) (basisCode u s i) else .constant 0))

theorem correctionCode_denote (u : NodeUnits node) (s : Finset (Fin Q)) (d : Fin Q → E) :
    (correctionCode u s d).denote = correctionPolynomial u s d := by
  simp [correctionCode, PolynomialCode.denote_sum, List.map_ofFn, Fin.sum_ofFn,
    PolynomialCode.denote, basisCode_denote, correctionPolynomial,
    apply_ite]

variable [Fintype V] [DecidableEq C]

/-- A fully finite, executable expression constructor for the multi-color row. -/
def mismatchRowCode (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (u : NodeUnits node) (d : V → Fin Q → E) (y : V) : PolynomialCode E :=
  .add (.constant ((Pi.single v (1 : E) : V → E) y))
    (if y ∈ correctionColumns head σ R then
      correctionCode u (mismatchPositions head σ y) (d y)
    else .constant 0)

theorem mismatchRowCode_denote (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (u : NodeUnits node) (d : V → Fin Q → E) (y : V) :
    (mismatchRowCode v head σ R u d y).denote = mismatchRowPath v head σ R u d y := by
  by_cases hy : (mismatchPositions head σ y).card ≤ R <;>
    simp [mismatchRowCode, PolynomialCode.denote, correctionCode_denote,
      mismatchRowPath, rowPath, mismatchCorrection, columnCorrection, hy]

theorem mismatchRowCode_eval (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (u : NodeUnits node) (d : V → Fin Q → E) (y : V) (x : E) :
    (mismatchRowCode v head σ R u d y).eval x =
      (mismatchRowPath v head σ R u d y).eval x := by
  rw [PolynomialCode.eval_eq, mismatchRowCode_denote]

end FiniteCode

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
