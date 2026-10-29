import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Consecutive binomial matrices

The matrix with entries choose (A + d) j factors into a lower
unitriangular Pascal matrix and an upper unitriangular translation matrix.
The upper factor is explicitly zero below the diagonal: natural subtraction
alone would give the wrong entries there.

All identities are obtained by casting integer-valued binomial coefficients,
so the determinant calculation remains valid in arbitrary characteristic.
-/

namespace SubexponentialSAT.BinomialMatrix

open scoped BigOperators

/-- The consecutive-integer binomial evaluation matrix. -/
def B (K : Type*) [Semiring K] (A R : ℕ) : Matrix (Fin R) (Fin R) K :=
  fun d j => ((A + d.val).choose j.val : K)

/-- The lower unitriangular Pascal matrix. -/
def L (K : Type*) [Semiring K] (R : ℕ) : Matrix (Fin R) (Fin R) K :=
  fun d s => (d.val.choose s.val : K)

/-- The upper unitriangular translation matrix, with explicit zero extension. -/
def U (K : Type*) [Semiring K] (A R : ℕ) : Matrix (Fin R) (Fin R) K :=
  fun s j => if s.val ≤ j.val then (A.choose (j.val - s.val) : K) else 0

@[simp] theorem B_apply (K : Type*) [Semiring K] (A R : ℕ) (d j : Fin R) :
    B K A R d j = ((A + d.val).choose j.val : K) := rfl

@[simp] theorem L_apply (K : Type*) [Semiring K] (R : ℕ) (d s : Fin R) :
    L K R d s = (d.val.choose s.val : K) := rfl

@[simp] theorem U_apply (K : Type*) [Semiring K] (A R : ℕ) (s j : Fin R) :
    U K A R s j =
      if s.val ≤ j.val then (A.choose (j.val - s.val) : K) else 0 := rfl

/-- Vandermonde convolution, extended by zero to any range containing j. -/
theorem choose_add_sum (A d j R : ℕ) (hj : j < R) :
    (A + d).choose j =
      ∑ s ∈ Finset.range R, d.choose s *
        (if s ≤ j then A.choose (j - s) else 0) := by
  calc
    (A + d).choose j =
        ∑ s ∈ Finset.range (j + 1), d.choose s * A.choose (j - s) := by
      rw [Nat.add_comm A d, Nat.add_choose_eq]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun s t => d.choose s * A.choose t) j
    _ = ∑ s ∈ Finset.range (j + 1), d.choose s *
        (if s ≤ j then A.choose (j - s) else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hs))]
    _ = ∑ s ∈ Finset.range R, d.choose s *
        (if s ≤ j then A.choose (j - s) else 0) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj))
      intro s _ hs
      have hsj : ¬s ≤ j := fun h =>
        hs (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp [hsj]

/-- The factorization is valid already over an arbitrary semiring. -/
theorem factorization (K : Type*) [Semiring K] (A R : ℕ) :
    B K A R = L K R * U K A R := by
  ext d j
  change ((A + d.val).choose j.val : K) =
    ∑ s : Fin R, (d.val.choose s.val : K) *
      (if s.val ≤ j.val then (A.choose (j.val - s.val) : K) else 0)
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (d.val.choose s : K) *
    (if s ≤ j.val then (A.choose (j.val - s) : K) else 0)) R]
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero] using
    congrArg (fun n : ℕ => (n : K)) (choose_add_sum A d.val j.val R j.isLt)

theorem L_lowerTriangular (K : Type*) [Semiring K] (R : ℕ) :
    (L K R).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have h : i.val < j.val := hij
  simp [L, Nat.choose_eq_zero_of_lt h]

theorem U_upperTriangular (K : Type*) [Semiring K] (A R : ℕ) :
    (U K A R).BlockTriangular id := by
  intro i j hij
  have h : ¬i.val ≤ j.val := Nat.not_le_of_lt hij
  simp [U, h]

@[simp] theorem det_L (K : Type*) [CommRing K] (R : ℕ) :
    (L K R).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (L_lowerTriangular K R)]
  simp [L]

@[simp] theorem det_U (K : Type*) [CommRing K] (A R : ℕ) :
    (U K A R).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (U_upperTriangular K A R)]
  simp [U]

/-- Consecutive binomial evaluation has determinant one in every
commutative ring, with no characteristic or size restriction. -/
@[simp] theorem det_B (K : Type*) [CommRing K] (A R : ℕ) :
    (B K A R).det = 1 := by
  rw [factorization, Matrix.det_mul, det_L, det_U, one_mul]

/-- In particular, the determinant is exactly one over the integers. -/
theorem det_B_int (A R : ℕ) : (B ℤ A R).det = 1 :=
  det_B ℤ A R

end SubexponentialSAT.BinomialMatrix

end OAI.Algorithms
