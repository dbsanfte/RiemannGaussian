import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

namespace OAI.Algorithms

/-! Bounds on the literal integer numerator entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

theorem integerDifference_natAbs_le (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → ℤ) (M : ℕ) (hf : ∀ u, (f u).natAbs ≤ M)
    (u : UniversalType r Q Δ) :
    (integerDifference i as f u).natAbs ≤ M * 2 ^ as.length := by
  induction as generalizing u with
  | nil => simpa [integerDifference] using hf u
  | cons a as ih =>
    calc
      _ ≤ (integerDifference i as f u).natAbs +
          (integerDifference i as f (swapPositions i {a} u)).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ M * 2 ^ as.length + M * 2 ^ as.length := add_le_add (ih u) (ih _)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

theorem integerDelta_natAbs_le (y x : UniversalType r Q Δ) :
    (integerDelta y x).natAbs ≤ 1 := by
  unfold integerDelta
  split_ifs <;> norm_num

theorem elementaryDifference_natAbs_le (i : Fin Δ) (t : Fin Q) (j : ℕ)
    (u y : UniversalType r Q Δ) :
    (∑ S ∈ (activePositions t).powersetCard j,
      integerDifference i S.toList (integerDelta y) u).natAbs ≤
        (activePositions t).card.choose j * 2 ^ j := by
  calc
    _ ≤ ∑ S ∈ (activePositions t).powersetCard j,
        (integerDifference i S.toList (integerDelta y) u).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ S ∈ (activePositions t).powersetCard j, 2 ^ j := by
      apply Finset.sum_le_sum
      intro S hS
      have hc := (Finset.mem_powersetCard.mp hS).2
      simpa [hc] using integerDifference_natAbs_le i S.toList
        (integerDelta y) 1 (integerDelta_natAbs_le y) u
    _ = _ := by simp [Finset.card_powersetCard]

theorem entry_natAbs_le_weighted (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    (entry i t A R u y).natAbs ≤
      ∑ j ∈ Finset.range R,
        (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs *
          2 ^ (R - 1) * (activePositions t).card.choose j := by
  classical
  unfold entry
  refine (Int.natAbs_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hjR : j ≤ R - 1 := by have := Finset.mem_range.mp hj; omega
  simp only [Int.natAbs_mul, Int.natAbs_pow ]
  calc
    _ ≤ (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs *
        2 ^ (R - 1 - j) * ((activePositions t).card.choose j * 2 ^ j) :=
      Nat.mul_le_mul_left _ (elementaryDifference_natAbs_le i t j _ _)
    _ = _ := by
      have hp : (2 : ℕ) ^ (R - 1 - j) * 2 ^ j = 2 ^ (R - 1) := by
        rw [← pow_add, Nat.sub_add_cancel hjR]
      calc
        _ = (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs *
            (2 ^ (R - 1 - j) * 2 ^ j) * (activePositions t).card.choose j := by ring
        _ = _ := by rw [hp]

theorem active_choose_le (t : Fin Q) (j : ℕ) :
    (activePositions t).card.choose j ≤ Q ^ j := by
  apply (Nat.choose_le_pow _ _).trans
  apply Nat.pow_le_pow_left
  simpa using Finset.card_le_card (Finset.subset_univ (activePositions t))

/-- A coefficient bound with the correct remaining degree gives a small
numerator. The coefficient hypothesis is discharged in the companion file. -/
theorem entry_natAbs_le_of_coefficients (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (hc : ∀ j : Fin R, (parityCoefficients (K := ℤ) A R j).natAbs ≤
      R * 2 ^ (R - 1) * Q ^ (R - 1 - j.val))
    (u y : UniversalType r Q Δ) :
    (entry i t A R u y).natAbs ≤ R ^ 2 * 4 ^ (R - 1) * Q ^ (R - 1) := by
  calc
    _ ≤ ∑ j ∈ Finset.range R,
        (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs *
          2 ^ (R - 1) * (activePositions t).card.choose j :=
      entry_natAbs_le_weighted i t A R u y
    _ ≤ ∑ j ∈ Finset.range R, R * 4 ^ (R - 1) * Q ^ (R - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjR : j < R := Finset.mem_range.mp hj
      have hcoeff := hc ⟨j, hjR⟩
      simp only [] at hcoeff
      have hext : extendCoefficients (parityCoefficients (K := ℤ) A R) j =
          parityCoefficients (K := ℤ) A R ⟨j, hjR⟩ := by
        simp [extendCoefficients, hjR]
      rw [hext]
      calc
        _ ≤ (R * 2 ^ (R - 1) * Q ^ (R - 1 - j)) *
            2 ^ (R - 1) * Q ^ j := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hcoeff) (active_choose_le t j)
        _ = _ := by
          have hq : Q ^ (R - 1 - j) * Q ^ j = Q ^ (R - 1) := by
            rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ R - 1)]
          have htwo : (2 : ℕ) ^ (R - 1) * 2 ^ (R - 1) = 4 ^ (R - 1) := by
            rw [← mul_pow]
            norm_num
          calc
            _ = R * (2 ^ (R - 1) * 2 ^ (R - 1)) *
                (Q ^ (R - 1 - j) * Q ^ j) := by ring
            _ = _ := by rw [hq, htwo]
    _ = _ := by simp; ring

theorem small_bound_le (Q R : ℕ) (hQ : 1 ≤ Q) :
    R ^ 2 * 4 ^ (R - 1) * Q ^ (R - 1) ≤ (8 * Q) ^ (2 * R) := by
  have hR : R ≤ 2 ^ R := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (2 ^ R) ^ 2 * 4 ^ R * Q ^ R := by gcongr <;> omega
    _ = (16 * Q) ^ R := by rw [← pow_mul, Nat.mul_comm R 2, pow_mul, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (64 * Q ^ 2) ^ R := by
      apply Nat.pow_le_pow_left
      nlinarith
    _ = (8 * Q) ^ (2 * R) := by rw [pow_mul]; congr 1; ring

/-- A uniform coefficient estimate also suffices for the target bit bound. -/
theorem entry_natAbs_le_of_uniform_coefficients (i : Fin Δ) (t : Fin Q)
    (A R : ℕ) (hQ : 1 ≤ Q)
    (hc : ∀ j : Fin R, (parityCoefficients (K := ℤ) A R j).natAbs ≤ (4 * Q) ^ R)
    (u y : UniversalType r Q Δ) :
    (entry i t A R u y).natAbs ≤ (8 * Q) ^ (2 * R) := by
  have hraw : (entry i t A R u y).natAbs ≤
      R * (4 * Q) ^ R * 2 ^ (R - 1) * Q ^ (R - 1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range R,
          (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs *
            2 ^ (R - 1) * (activePositions t).card.choose j :=
        entry_natAbs_le_weighted i t A R u y
      _ ≤ ∑ j ∈ Finset.range R,
          (4 * Q) ^ R * 2 ^ (R - 1) * Q ^ (R - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjR : j < R := Finset.mem_range.mp hj
        have hcj : (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs ≤
            (4 * Q) ^ R := by simpa [extendCoefficients, hjR] using hc ⟨j, hjR⟩
        have hchoose : (activePositions t).card.choose j ≤ Q ^ (R - 1) :=
          (active_choose_le t j).trans (Nat.pow_le_pow_right hQ (by omega))
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hcj) hchoose
      _ = _ := by simp; ring
  have hR : R ≤ 2 ^ R := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ R * (4 * Q) ^ R * 2 ^ (R - 1) * Q ^ (R - 1) := hraw
    _ ≤ 2 ^ R * (4 * Q) ^ R * 2 ^ R * Q ^ R := by gcongr <;> omega
    _ = (16 * Q ^ 2) ^ R := by simp only [← mul_pow]; congr 1; ring
    _ ≤ (64 * Q ^ 2) ^ R := by gcongr; norm_num
    _ = (8 * Q) ^ (2 * R) := by rw [pow_mul]; congr 1; ring

theorem entry_natAbs_le (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (u y : UniversalType r Q Δ) :
    (entry i t A R u y).natAbs ≤ (8 * Q) ^ (2 * R) :=
  entry_natAbs_le_of_uniform_coefficients i t A R hQ
    (LayoutCoefficientBounds.natAbs_parityCoefficients_le A R Q hAQ hQ) u y

theorem joint_natAbs_le (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (u y : Joint t g i) :
    (joint i t g A R u y).natAbs ≤ (8 * Q) ^ (2 * R) :=
  entry_natAbs_le i t A R hAQ hQ u.val y.val

theorem joint_abs_le (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (u y : Joint t g i) :
    |joint i t g A R u y| ≤ ((8 * Q) ^ (2 * R) : ℕ) := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast joint_natAbs_le i t g A R hAQ hQ u y

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
