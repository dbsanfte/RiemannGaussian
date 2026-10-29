import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialInterpolation
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.MatrixSupport

namespace OAI.Algorithms

/-!
# Integer numerators for the actual universal swap matrices

The parity coefficients are the immutable library's coefficients, instantiated
over the integers. Their images are the same coefficients over every
commutative ring. Clearing the projector denominators uses only powers of two.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

theorem parityCoefficients_intCast (K : Type*) [CommRing K] (A R : ℕ)
    (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j : K) =
      parityCoefficients (K := K) A R j := by
  have hs : ∀ d : Fin R,
      ∑ j : Fin R, (parityCoefficients (K := ℤ) A R j : K) *
        ((A + d.val).choose j.val : K) = (-1 : K) ^ (A + d.val) := by
    intro d
    have hz := congrArg (Int.castRingHom K) (parityCoefficients_spec (K := ℤ) A R d)
    simpa using hz
  have h := (existsUnique_binomial_interpolation (K := K) A R
    (fun d : Fin R => (-1 : K) ^ (A + d.val))).unique
      hs (parityCoefficients_spec A R)
  exact congrFun h j

theorem extend_parityCoefficients_intCast (K : Type*) [CommRing K]
    (A R j : ℕ) :
    ((extendCoefficients (parityCoefficients (K := ℤ) A R) j : ℤ) : K) =
      extendCoefficients (parityCoefficients (K := K) A R) j := by
  by_cases hj : j < R
  · simp [extendCoefficients, hj, parityCoefficients_intCast]
  · simp [extendCoefficients, hj]

variable {r Q Δ : ℕ}

/-- The same ordered difference product, without requiring a field. -/
def integerDifference (i : Fin Δ) : List (Fin Q) →
    (UniversalType r Q Δ → ℤ) → UniversalType r Q Δ → ℤ
  | [], f, u => f u
  | a :: as, f, u => integerDifference i as f u -
      integerDifference i as f (swapPositions i {a} u)

theorem integerDifference_cast (K : Type*) [Field K] (i : Fin Δ)
    (as : List (Fin Q)) (f : UniversalType r Q Δ → ℤ)
    (u : UniversalType r Q Δ) :
    (integerDifference i as f u : K) =
      differenceProduct i as (fun v => (f v : K)) u := by
  induction as generalizing u with
  | nil => rfl
  | cons a as ih => simp only [integerDifference, Int.cast_sub, differenceProduct, ih]

def integerDelta (y x : UniversalType r Q Δ) : ℤ :=
  if x = y then 1 else 0

theorem integerDelta_cast (K : Type*) [Field K]
    (y x : UniversalType r Q Δ) : (integerDelta y x : K) = delta y x := by
  simp [integerDelta, delta]

def denominator (R : ℕ) : ℤ := 2 ^ (R - 1)

/-- Each summand is a literal integer; no rational rounding is used. -/
noncomputable def entry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) : ℤ :=
  ∑ j ∈ Finset.range R,
    extendCoefficients (parityCoefficients (K := ℤ) A R) j *
      2 ^ (R - 1 - j) *
      ∑ S ∈ (activePositions t).powersetCard j,
        integerDifference i S.toList (integerDelta y)
          (swapPositions i (activePositions t) u)

noncomputable def joint (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Matrix (Joint t g i) (Joint t g i) ℤ :=
  fun u y => entry i t A R u.val y.val

theorem pow_two_clear (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (R j : ℕ) (hj : j < R) :
    (2 : K) ^ (R - 1 - j) =
      2 ^ (R - 1) * (2 : K)⁻¹ ^ j := by
  have hle : j ≤ R - 1 := by omega
  have hp : (2 : K) ^ (R - 1) = 2 ^ (R - 1 - j) * 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hc : (2 : K) ^ j * (2 : K)⁻¹ ^ j = 1 := by
    rw [← mul_pow]
    simp [h2]
  rw [hp, mul_assoc, hc, mul_one]

theorem entry_cast (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    (entry i t A R u y : K) =
      (denominator R : K) * matrixEntry i t R
        (extendCoefficients (parityCoefficients (K := K) A R)) u y := by
  classical
  simp only [entry, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    extend_parityCoefficients_intCast, matrixEntry, denominator]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_two_clear K h2 R j (Finset.mem_range.mp hj)]
  simp only [elementaryProjector, projectorProduct, Finset.length_toList,
    integerDifference_cast]
  simp_rw [integerDelta_cast]
  have hsum :
      (∑ S ∈ (activePositions t).powersetCard j,
        (2 : K)⁻¹ ^ S.card *
          differenceProduct i S.toList (delta y)
            (swapPositions i (activePositions t) u)) =
      (2 : K)⁻¹ ^ j *
        ∑ S ∈ (activePositions t).powersetCard j,
          differenceProduct i S.toList (delta y)
            (swapPositions i (activePositions t) u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [hsum]
  ring

theorem joint_cast (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (u y : Joint t g i) :
    (joint i t g A R u y : K) =
      (denominator R : K) * jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := K) A R)) u y :=
  entry_cast K h2 i t A R u.val y.val

theorem joint_support (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (u y : Joint t g i) (hne : joint i t g A R u y ≠ 0) :
    (mismatches i u.val y.val).card ≤ R := by
  apply jointMatrix_support i t g R
    (extendCoefficients (parityCoefficients (K := ℚ) A R)) u y
  intro hz
  have hc := joint_cast ℚ (by norm_num) i t g A R u y
  rw [hz, mul_zero] at hc
  exact hne (by exact_mod_cast hc)

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
