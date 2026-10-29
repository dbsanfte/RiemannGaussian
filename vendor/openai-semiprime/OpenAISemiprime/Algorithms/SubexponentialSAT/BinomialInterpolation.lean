import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialMatrix
import OpenAISemiprime.Algorithms.SubexponentialSAT.MatrixSupport

namespace OAI.Algorithms

/-!
# Interpolation at consecutive integer weights

The coefficient construction uses the inverse of an actual finite matrix.
It applies over any commutative ring whose evaluation matrix has unit determinant.
The binomial evaluation matrix has determinant one, including in small characteristic.
-/

namespace SubexponentialSAT.BinomialInterpolation

open scoped BigOperators
open Matrix

noncomputable section

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The coefficients solving a square interpolation system. -/
def coefficients (M : Matrix n n K) (target : n → K) : n → K :=
  M⁻¹ *ᵥ target

/-- Inverting a matrix with unit determinant realizes any prescribed target. -/
theorem mulVec_coefficients (M : Matrix n n K) (hM : IsUnit M.det)
    (target : n → K) : M *ᵥ coefficients M target = target := by
  rw [coefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM,
    Matrix.one_mulVec]

/-- The coefficient vector is the unique solution of the interpolation system. -/
theorem coefficients_unique (M : Matrix n n K) (hM : IsUnit M.det)
    (target c : n → K) (hc : M *ᵥ c = target) : c = coefficients M target := by
  calc
    c = M⁻¹ *ᵥ (M *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
    _ = coefficients M target := by rw [hc, coefficients]

theorem existsUnique_mulVec_eq (M : Matrix n n K) (hM : IsUnit M.det)
    (target : n → K) : ∃! c : n → K, M *ᵥ c = target := by
  exact ⟨coefficients M target, mulVec_coefficients M hM target,
    fun c hc => coefficients_unique M hM target c hc⟩

/-- The determinant-one binomial matrix is invertible in every characteristic. -/
theorem isUnit_det_binomial (A R : ℕ) :
    IsUnit (BinomialMatrix.B K A R).det := by
  rw [BinomialMatrix.det_B]
  exact isUnit_one

/-- Coefficients realizing a target on the consecutive integer weights
`A, ..., A + R - 1`. These are integer binomial evaluations, not ordinary
univariate evaluations at the residues of these weights. -/
def binomialCoefficients (A R : ℕ) (target : Fin R → K) : Fin R → K :=
  coefficients (BinomialMatrix.B K A R) target

theorem binomialCoefficients_spec (A R : ℕ) (target : Fin R → K) (d : Fin R) :
    ∑ j : Fin R, binomialCoefficients A R target j *
      ((A + d.val).choose j.val : K) = target d := by
  have h := congrFun
    (mulVec_coefficients (BinomialMatrix.B K A R) (isUnit_det_binomial A R) target) d
  simpa only [binomialCoefficients, Matrix.mulVec, dotProduct,
    BinomialMatrix.B_apply, mul_comm] using h

/-- Arbitrary target values admit a unique binomial-basis coefficient vector. -/
theorem existsUnique_binomial_interpolation (A R : ℕ) (target : Fin R → K) :
    ∃! c : Fin R → K, ∀ d : Fin R,
      ∑ j : Fin R, c j * ((A + d.val).choose j.val : K) = target d := by
  refine ⟨binomialCoefficients A R target, binomialCoefficients_spec A R target, ?_⟩
  intro c hc
  apply coefficients_unique (BinomialMatrix.B K A R) (isUnit_det_binomial A R) target c
  funext d
  simpa only [Matrix.mulVec, dotProduct, BinomialMatrix.B_apply, mul_comm] using hc d

/-- The coefficient vector used for the alternating target in equation (5.3). -/
def parityCoefficients (A R : ℕ) : Fin R → K :=
  binomialCoefficients A R (fun d => (-1 : K) ^ (A + d.val))

theorem parityCoefficients_spec (A R : ℕ) (d : Fin R) :
    ∑ j : Fin R, parityCoefficients (K := K) A R j *
      ((A + d.val).choose j.val : K) = (-1 : K) ^ (A + d.val) :=
  binomialCoefficients_spec A R (fun d => (-1 : K) ^ (A + d.val)) d

/-- The scalar eigenvalue of the corrected permutation product. -/
def spectralValue {R : ℕ} (c : Fin R → K) (w : ℕ) : K :=
  (-1 : K) ^ w * ∑ j : Fin R, c j * (w.choose j.val : K)

theorem spectralValue_parity (A R : ℕ) (d : Fin R) :
    spectralValue (parityCoefficients (K := K) A R) (A + d.val) = 1 := by
  rw [spectralValue, parityCoefficients_spec, ← mul_pow]
  simp

/-- The corrected eigenvalue equals one at every integer weight in the chosen interval. -/
theorem spectralValue_parity_of_mem (A R w : ℕ) (hA : A ≤ w) (hR : w < A + R) :
    spectralValue (parityCoefficients (K := K) A R) w = 1 := by
  let d : Fin R := ⟨w - A, Nat.sub_lt_right_of_lt_add hA (by simpa [Nat.add_comm] using hR)⟩
  have hd : A + d.val = w := Nat.add_sub_of_le hA
  simpa only [hd] using spectralValue_parity (K := K) A R d

/-- Extend a finite coefficient vector by zero outside its specified range. -/
def extendCoefficients {R : ℕ} (c : Fin R → K) (j : ℕ) : K :=
  if h : j < R then c ⟨j, h⟩ else 0

@[simp] theorem extendCoefficients_fin {R : ℕ} (c : Fin R → K) (j : Fin R) :
    extendCoefficients c j.val = c j := by
  simp [extendCoefficients, j.isLt]

theorem extendCoefficients_eq_zero {R : ℕ} (c : Fin R → K) (j : ℕ) (hj : R ≤ j) :
    extendCoefficients c j = 0 := by
  simp [extendCoefficients, Nat.not_lt.mpr hj]

/-- The zero extension connects finite-vector sums to the matrix construction's
natural-number-indexed sum over `range R`. -/
theorem sum_range_extendCoefficients {R : ℕ} (c : Fin R → K) (w : ℕ) :
    (∑ j ∈ Finset.range R, extendCoefficients c j * (w.choose j : K)) =
      ∑ j : Fin R, c j * (w.choose j.val : K) := by
  simpa only [extendCoefficients_fin] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => extendCoefficients c j * (w.choose j : K)) R).symm

theorem sum_range_extend_parity (A R : ℕ) (d : Fin R) :
    (∑ j ∈ Finset.range R, extendCoefficients (parityCoefficients (K := K) A R) j *
      ((A + d.val).choose j : K)) = (-1 : K) ^ (A + d.val) := by
  rw [sum_range_extendCoefficients, parityCoefficients_spec]

theorem sum_range_extend_parity_of_mem (A R w : ℕ) (hA : A ≤ w) (hR : w < A + R) :
    (∑ j ∈ Finset.range R, extendCoefficients (parityCoefficients (K := K) A R) j *
      (w.choose j : K)) = (-1 : K) ^ w := by
  let d : Fin R := ⟨w - A, Nat.sub_lt_right_of_lt_add hA (by simpa [Nat.add_comm] using hR)⟩
  have hd : A + d.val = w := Nat.add_sub_of_le hA
  simpa only [hd] using sum_range_extend_parity (K := K) A R d

section ElementarySymmetric

variable {S : Type*} [CommSemiring S]

omit [Fintype n] in
/-- The elementary symmetric sum of an indicator is the binomial coefficient
in the integer size of its support. The ambient set may be larger than the support. -/
theorem sum_powersetCard_prod_indicator (active ones : Finset n)
    (hsubset : ones ⊆ active) (j : ℕ) :
    (∑ t ∈ active.powersetCard j, ∏ i ∈ t, if i ∈ ones then (1 : S) else 0) =
      (ones.card.choose j : S) := by
  classical
  have hfilter :
      (active.powersetCard j).filter
          (fun t => t ⊆ ones) = ones.powersetCard j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hto⟩
      exact ⟨hto, hcard⟩
    · rintro ⟨hto, hcard⟩
      exact ⟨⟨Finset.Subset.trans hto hsubset, hcard⟩, hto⟩
  simp only [Finset.prod_boole]
  trans ∑ t ∈ active.powersetCard j,
    if t ⊆ ones then (1 : S) else 0
  · apply Finset.sum_congr rfl
    intro t _
    by_cases h : t ⊆ ones
    · have h' : ∀ i ∈ t, i ∈ ones := fun i hi => h hi
      rw [ite_eq_left h', ite_eq_left h]
    · have h' : ¬(∀ i ∈ t, i ∈ ones) := fun h' => h (fun i hi => h' i hi)
      rw [ite_eq_right h', ite_eq_right h]
  · rw [Finset.sum_boole, hfilter, Finset.card_powersetCard]

/-- Evaluating the actual elementary symmetric polynomial on an indicator
vector counts subsets of its support, with no division by factorials. -/
theorem eval_esymm_indicator (ones : Finset n) (j : ℕ) :
    MvPolynomial.eval (fun i => if i ∈ ones then (1 : S) else 0)
      (MvPolynomial.esymm n S j) = (ones.card.choose j : S) := by
  classical
  simp only [MvPolynomial.esymm, MvPolynomial.eval_sum,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]
  exact sum_powersetCard_prod_indicator Finset.univ ones (Finset.subset_univ ones) j

/-- The elementary symmetric value of a zero-one vector is a binomial
coefficient in the integer number of ones, subsequently cast to the ring. -/
theorem eval_esymm_zero_one [DecidableEq S] (f : n → S) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (j : ℕ) :
    MvPolynomial.eval f (MvPolynomial.esymm n S j) =
      (((Finset.univ.filter (fun i => f i = 1)).card).choose j : S) := by
  classical
  let ones : Finset n := Finset.univ.filter (fun i => f i = 1)
  have hfun : f = fun i => if i ∈ ones then (1 : S) else 0 := by
    funext i
    by_cases h1 : f i = 1
    · simp [ones, h1]
    · have h0 : f i = 0 := (hf i).resolve_right h1
      simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and, h1, ite_false]
      exact h0
  change MvPolynomial.eval f (MvPolynomial.esymm n S j) = (ones.card.choose j : S)
  rw [hfun]
  exact eval_esymm_indicator ones j

end ElementarySymmetric

end

section MatrixEigenvalue

variable {K : Type*} [Field K] {Q : ℕ}

/-- The actual matrix eigenvalue at a sign vector is the binomial-weighted
scalar from the interpolation argument. The weight is the integer number of
negative signs. -/
theorem matrixEigenvalue_signIndicator (h2 : (2 : K) ≠ 0) (t : Fin Q)
    (R : ℕ) (c : ℕ → K) (ones : Finset (Fin Q))
    (hsub : ones ⊆ MatrixSupport.activePositions t) :
    MatrixSupport.matrixEigenvalue t R c
        (fun l => if l ∈ ones then (-1 : K) else 1) =
      (-1 : K) ^ ones.card *
        ∑ j ∈ Finset.range R, c j * (ones.card.choose j : K) := by
  classical
  have hfilter :
      (MatrixSupport.activePositions t).filter (fun l => l ∈ ones) = ones := by
    ext l
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hprod :
      (∏ l ∈ MatrixSupport.activePositions t, if l ∈ ones then (-1 : K) else 1) =
        (-1 : K) ^ ones.card := by
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one, hfilter]
  have hprojector (l : Fin Q) :
      (1 - (if l ∈ ones then (-1 : K) else 1)) / 2 =
        if l ∈ ones then (1 : K) else 0 := by
    by_cases hl : l ∈ ones
    · simp only [ite_eq_left hl, sub_neg_eq_add, one_add_one_eq_two]
      exact div_self h2
    · simp [hl]
  unfold MatrixSupport.matrixEigenvalue
  rw [hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp_rw [hprojector]
  exact sum_powersetCard_prod_indicator (MatrixSupport.activePositions t) ones hsub j

/-- With the parity-interpolation coefficients, the actual matrix eigenvalue
is one throughout the prescribed interval of integer weights. -/
theorem matrixEigenvalue_parity_of_mem (h2 : (2 : K) ≠ 0) (t : Fin Q)
    (A R : ℕ) (ones : Finset (Fin Q))
    (hsub : ones ⊆ MatrixSupport.activePositions t)
    (hA : A ≤ ones.card) (hR : ones.card < A + R) :
    MatrixSupport.matrixEigenvalue t R
        (extendCoefficients (parityCoefficients (K := K) A R))
        (fun l => if l ∈ ones then (-1 : K) else 1) = 1 := by
  rw [matrixEigenvalue_signIndicator h2 t R _ ones hsub,
    sum_range_extend_parity_of_mem A R ones.card hA hR, ← mul_pow]
  simp

end MatrixEigenvalue

end SubexponentialSAT.BinomialInterpolation

end OAI.Algorithms
