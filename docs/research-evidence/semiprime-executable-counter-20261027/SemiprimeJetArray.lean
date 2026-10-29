/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetRecurrence

/-!
# Cached inverse jets on actual coefficient arrays

Each inverse coefficient is appended once and later read from the stored array.
The loop's rational-operation and coefficient-read counts are quadratic. These
are explicit operation counts, not a unit-cost rational bit-time assertion.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeJetArray
open scoped BigOperators
open Polynomial
open RiemannGaussian.SemiprimeJetRecurrence
open RiemannGaussian.SemiprimeHermiteRecovery

/-- Read an actual retained coefficient, with zero beyond the stored width. -/
def coefficient (a : Array ℚ) (i : ℕ) : ℚ := a[i]?.getD 0

theorem coefficient_zero {a : Array ℚ} {i : ℕ} (hi : a.size ≤ i) : coefficient a i = 0 := by
  simp [coefficient, Array.getElem?_eq_none (by omega)]

/-- Scalar output and exact counts for the multiply-add prefix loop. -/
structure DotReport where
  /-- Actual rational accumulator. -/
  value : ℚ
  /-- Rational additions and multiplications executed. -/
  arithmetic : ℕ
  /-- Coefficient-array accesses executed. -/
  reads : ℕ

/-- The first len terms of the inverse recurrence's scalar product.
Only stored coefficients are read; this never recursively computes an inverse. -/
def dotPrefix (a b : Array ℚ) (n : ℕ) : ℕ → DotReport
  | 0 => ⟨0, 0, 0⟩
  | len + 1 =>
      let s := dotPrefix a b n len
      ⟨s.value + coefficient a (len + 1) * coefficient b (n - len),
        s.arithmetic + 2, s.reads + 2⟩

theorem dotPrefix_value (a b : Array ℚ) (n len : ℕ) :
    (dotPrefix a b n len).value =
      ∑ i ∈ Finset.range len, coefficient a (i + 1) * coefficient b (n - i) := by
  induction len with
  | zero => simp [dotPrefix]
  | succ len ih => simp [dotPrefix, Finset.sum_range_succ, ih]

theorem dotPrefix_arithmetic (a b : Array ℚ) (n len : ℕ) :
    (dotPrefix a b n len).arithmetic = 2 * len := by
  induction len with
  | zero => rfl
  | succ len ih => simp [dotPrefix, ih]; omega

theorem dotPrefix_reads (a b : Array ℚ) (n len : ℕ) :
    (dotPrefix a b n len).reads = 2 * len := by
  induction len with
  | zero => rfl
  | succ len ih => simp [dotPrefix, ih]; omega

/-- Actual output array and accumulated rational-operation/access counts. -/
structure InverseReport where
  /-- Retained inverse coefficients, in increasing order. -/
  coefficients : Array ℚ
  /-- Rational additions, multiplications, negations and reciprocal operations. -/
  arithmetic : ℕ
  /-- Input and previously stored coefficient-array accesses. -/
  reads : ℕ

/-- One new coefficient, with a precomputed reciprocal c of the constant input. -/
def nextCoefficient (a b : Array ℚ) (c : ℚ) : ℕ → DotReport
  | 0 => ⟨c, 0, 0⟩
  | n + 1 =>
      let s := dotPrefix a b n (n + 1)
      ⟨-c * s.value, s.arithmetic + 2, s.reads⟩

/-- Cached finite construction: the sole recursive call returns the entire
previous prefix, and each next coefficient is pushed exactly once. -/
def buildInverse (a : Array ℚ) (c : ℚ) : ℕ → InverseReport
  | 0 => ⟨#[], 0, 0⟩
  | J + 1 =>
      let old := buildInverse a c J
      let next := nextCoefficient a old.coefficients c J
      ⟨old.coefficients.push next.value, old.arithmetic + next.arithmetic,
        old.reads + next.reads⟩

/-- Compute the reciprocal once, then execute the cached coefficient loop. -/
def inverse (a : Array ℚ) (J : ℕ) : InverseReport :=
  let out := buildInverse a (coefficient a 0)⁻¹ J
  ⟨out.coefficients, out.arithmetic + 1, out.reads + 1⟩

theorem buildInverse_size (a : Array ℚ) (c : ℚ) (J : ℕ) :
    (buildInverse a c J).coefficients.size = J := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [buildInverse, Array.size_push, ih]

theorem inverse_size (a : Array ℚ) (J : ℕ) : (inverse a J).coefficients.size = J :=
  buildInverse_size a _ J

/-- The cached array equals the earlier proved recurrence at every retained index. -/
theorem buildInverse_coefficient (a : Array ℚ) (J i : ℕ) (hi : i < J) :
    coefficient (buildInverse a (coefficient a 0)⁻¹ J).coefficients i =
      inverseCoeff (coefficient a) i := by
  induction J generalizing i with
  | zero => omega
  | succ J ih =>
    simp only [buildInverse, coefficient, Array.getElem?_push, buildInverse_size]
    by_cases heq : i = J
    · subst i
      simp only [ite_true, Option.getD_some]
      cases J with
      | zero => simp only [nextCoefficient, inverseCoeff, coefficient]
      | succ n =>
        simp only [nextCoefficient, dotPrefix_value, inverseCoeff]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun x : ℚ => coefficient a (j+1) * x) (ih (n-j) (by omega))
    · simp only [ite_eq_right heq]
      exact ih i (by omega)

theorem inverse_coefficient (a : Array ℚ) (J i : ℕ) (hi : i < J) :
    coefficient (inverse a J).coefficients i = inverseCoeff (coefficient a) i :=
  buildInverse_coefficient a J i hi

/-- Counts are attached to the executed scalar loop, not to recursive recomputation. -/
theorem buildInverse_arithmetic_le (a : Array ℚ) (c : ℚ) (J : ℕ) :
    (buildInverse a c J).arithmetic ≤ 2 * J ^ 2 := by
  induction J with
  | zero => simp [buildInverse]
  | succ J ih =>
    cases J with
    | zero => simp [buildInverse, nextCoefficient]
    | succ n =>
      change (buildInverse a c (n+1)).arithmetic +
        ((dotPrefix a (buildInverse a c (n+1)).coefficients n (n+1)).arithmetic + 2) ≤ _
      rw [dotPrefix_arithmetic]
      nlinarith

theorem buildInverse_reads_le (a : Array ℚ) (c : ℚ) (J : ℕ) :
    (buildInverse a c J).reads ≤ J ^ 2 := by
  induction J with
  | zero => simp [buildInverse]
  | succ J ih =>
    cases J with
    | zero => simp [buildInverse, nextCoefficient]
    | succ n =>
      change (buildInverse a c (n+1)).reads +
        (dotPrefix a (buildInverse a c (n+1)).coefficients n (n+1)).reads ≤ _
      rw [dotPrefix_reads]
      nlinarith

/-- One reciprocal, quadratically many rational operations and coefficient reads,
and exactly J stored output coefficients. Rational bit costs remain separate. -/
theorem inverse_work (a : Array ℚ) (J : ℕ) :
    (inverse a J).arithmetic ≤ 2 * J ^ 2 + 1 ∧
      (inverse a J).reads ≤ J ^ 2 + 1 ∧ (inverse a J).coefficients.size = J := by
  refine ⟨Nat.add_le_add_right (buildInverse_arithmetic_le a _ J) 1,
    Nat.add_le_add_right (buildInverse_reads_le a _ J) 1, inverse_size a J⟩

/-- One ordinary convolution coefficient, reusing the stored-prefix scalar loop. -/
def convolution (a b : Array ℚ) (n : ℕ) : DotReport :=
  let s := dotPrefix a b (n-1) n
  ⟨coefficient a 0 * coefficient b n + s.value, s.arithmetic + 2, s.reads + 2⟩

theorem convolution_value (a b : Array ℚ) (n : ℕ) :
    (convolution a b n).value =
      ∑ i ∈ Finset.range (n+1), coefficient a i * coefficient b (n-i) := by
  rw [Finset.sum_range_succ']
  simp only [convolution, dotPrefix_value, Nat.sub_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  omega

/-- Truncated multiplication writes each convolution coefficient once. -/
def multiply (a b : Array ℚ) : ℕ → InverseReport
  | 0 => ⟨#[], 0, 0⟩
  | J+1 =>
      let old := multiply a b J
      let next := convolution a b J
      ⟨old.coefficients.push next.value, old.arithmetic + next.arithmetic,
        old.reads + next.reads⟩

theorem multiply_size (a b : Array ℚ) (J : ℕ) : (multiply a b J).coefficients.size = J := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [multiply, Array.size_push, ih]

theorem multiply_coefficient (a b : Array ℚ) (J i : ℕ) (hi : i < J) :
    coefficient (multiply a b J).coefficients i =
      ∑ k ∈ Finset.range (i+1), coefficient a k * coefficient b (i-k) := by
  induction J generalizing i with
  | zero => omega
  | succ J ih =>
    simp only [multiply, coefficient, Array.getElem?_push, multiply_size]
    by_cases heq : i = J
    · subst i
      simp only [ite_true, Option.getD_some]
      exact convolution_value a b J
    · simp only [ite_eq_right heq]
      exact ih i (by omega)

/-- The actual convolution loop has quadratic arithmetic and access counts. -/
theorem multiply_work (a b : Array ℚ) (J : ℕ) :
    (multiply a b J).arithmetic = J*(J+1) ∧
      (multiply a b J).reads = J*(J+1) := by
  induction J with
  | zero => simp [multiply]
  | succ J ih =>
    change (multiply a b J).arithmetic + (convolution a b J).arithmetic = _ ∧
      (multiply a b J).reads + (convolution a b J).reads = _
    simp only [convolution, dotPrefix_arithmetic, dotPrefix_reads, ih.1, ih.2]
    constructor <;> ring

/-- Execute the inverse and truncated multiplication used by one Hermite quotient. -/
def quotient (H L : Array ℚ) (J : ℕ) : InverseReport :=
  let inv := inverse L J
  let prod := multiply H inv.coefficients J
  ⟨prod.coefficients, inv.arithmetic + prod.arithmetic, inv.reads + prod.reads⟩

theorem quotient_work (H L : Array ℚ) (J : ℕ) :
    (quotient H L J).arithmetic ≤ 3*J^2 + J + 1 ∧
      (quotient H L J).reads ≤ 2*J^2 + J + 1 ∧
      (quotient H L J).coefficients.size = J := by
  have hi := inverse_work L J
  have hm := multiply_work H (inverse L J).coefficients J
  refine ⟨?_, ?_, multiply_size H _ J⟩
  · change (inverse L J).arithmetic + (multiply H (inverse L J).coefficients J).arithmetic ≤ _
    rw [hm.1]
    nlinarith [hi.1]
  · change (inverse L J).reads + (multiply H (inverse L J).coefficients J).reads ≤ _
    rw [hm.2]
    nlinarith [hi.2.1]

/-- Polynomial interpretation of a concrete finite coefficient array. -/
noncomputable def asPolynomial (a : Array ℚ) : Polynomial ℚ :=
  jetPolynomial (coefficient a) a.size

theorem asPolynomial_coeff (a : Array ℚ) (i : ℕ) :
    (asPolynomial a).coeff i = coefficient a i := by
  rw [asPolynomial, jetPolynomial_coeff]
  split_ifs with hi
  · rfl
  · exact (coefficient_zero (by omega)).symm

theorem inverse_asPolynomial (a : Array ℚ) (J : ℕ) :
    asPolynomial (inverse a J).coefficients = jetPolynomial (inverseCoeff (coefficient a)) J := by
  ext i
  rw [asPolynomial_coeff, jetPolynomial_coeff]
  split_ifs with hi
  · exact inverse_coefficient a J i hi
  · exact coefficient_zero (by rw [inverse_size]; omega)

theorem multiply_asPolynomial (a b : Array ℚ) (J : ℕ) :
    asPolynomial (multiply a b J).coefficients = (asPolynomial a * asPolynomial b) %ₘ X^J := by
  ext i
  rw [asPolynomial_coeff, coeff_mod_X_pow]
  split_ifs with hi
  · rw [multiply_coefficient a b J i hi, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k _
    rw [asPolynomial_coeff, asPolynomial_coeff]
  · exact coefficient_zero (by rw [multiply_size]; omega)

/-- These cached output arrays give the actual Hermite local quotient. -/
theorem inverse_localQuotient (H : Polynomial ℚ) (a : Array ℚ) (J : ℕ)
    (ha : coefficient a 0 = 1) :
    (H * asPolynomial (inverse a J).coefficients) %ₘ X^J =
      localQuotient H (asPolynomial a) J := by
  rw [inverse_asPolynomial]
  have hc : (asPolynomial a).coeff = coefficient a := funext (asPolynomial_coeff a)
  have h := recurrence_localQuotient H (asPolynomial a) J (by rw [asPolynomial_coeff, ha])
  simpa only [hc] using h

/-- Full cached local-quotient execution, including the actual multiplication array. -/
theorem quotient_correct (H L : Array ℚ) (J : ℕ) (hL : coefficient L 0 = 1) :
    asPolynomial (quotient H L J).coefficients = localQuotient (asPolynomial H) (asPolynomial L) J := by
  change asPolynomial (multiply H (inverse L J).coefficients J).coefficients = _
  rw [multiply_asPolynomial]
  exact inverse_localQuotient (asPolynomial H) L J hL

#print axioms inverse_work
#print axioms inverse_localQuotient
#print axioms quotient_work
#print axioms quotient_correct
end RiemannGaussian.SemiprimeJetArray
