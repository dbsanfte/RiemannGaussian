import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialInterpolation

namespace OAI.Algorithms

/-! Explicit exponential-in-R bounds for the existing integer parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open Matrix

theorem triangular_sum_bound (R M : ℕ) (b : Fin R → ℕ)
    (hb : ∀ j, b j ≤ M + ∑ k : Fin R, if j.val < k.val then b k else 0) :
    (∑ j, b j) + M ≤ M * 2 ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
    have htail : ∀ j : Fin R, b j.succ ≤
        M + ∑ k : Fin R, if j.val < k.val then b k.succ else 0 := by
      intro j
      simpa [Fin.sum_univ_succ] using hb j.succ
    have hrest := ih (fun j => b j.succ) htail
    have hzero : b 0 ≤ M + ∑ k : Fin R, b k.succ := by
      simpa [Fin.sum_univ_succ] using hb 0
    rw [Fin.sum_univ_succ, pow_succ]
    nlinarith

theorem pascal_power_sum (R : ℕ) (d : Fin R) :
    (∑ j : Fin R, (d.val.choose j.val : ℤ) * (-2 : ℤ) ^ j.val) =
      (-1 : ℤ) ^ d.val := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (d.val.choose j : ℤ) * (-2 : ℤ) ^ j) R]
  calc
    (∑ j ∈ Finset.range R, (d.val.choose j : ℤ) * (-2 : ℤ) ^ j) =
        ∑ j ∈ Finset.range (d.val + 1), (d.val.choose j : ℤ) * (-2 : ℤ) ^ j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjd
      have h : d.val < j := by simpa using hjd
      simp [Nat.choose_eq_zero_of_lt h]
    _ = (-1 : ℤ) ^ d.val := by
      have h := add_pow (-2 : ℤ) 1 d.val
      norm_num only [one_pow, mul_one, show (-2 : ℤ) + 1 = -1 by norm_num] at h
      simpa [mul_comm] using h.symm

theorem upper_mulVec_parity (A R : ℕ) :
    (SubexponentialSAT.BinomialMatrix.U ℤ A R) *ᵥ parityCoefficients (K := ℤ) A R =
      fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val := by
  let c := parityCoefficients (K := ℤ) A R
  let g : Fin R → ℤ := fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val
  have hg : (SubexponentialSAT.BinomialMatrix.L ℤ R) *ᵥ g =
      fun d => (-1 : ℤ) ^ (A + d.val) := by
    funext d
    simp only [Matrix.mulVec, dotProduct, SubexponentialSAT.BinomialMatrix.L_apply, g]
    calc
      (∑ j : Fin R, (d.val.choose j.val : ℤ) *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val)) =
          (-1 : ℤ) ^ A * ∑ j : Fin R,
            (d.val.choose j.val : ℤ) * (-2 : ℤ) ^ j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (-1 : ℤ) ^ (A + d.val) := by rw [pascal_power_sum, pow_add]
  have hc : (SubexponentialSAT.BinomialMatrix.L ℤ R) *ᵥ
        ((SubexponentialSAT.BinomialMatrix.U ℤ A R) *ᵥ c) =
      fun d => (-1 : ℤ) ^ (A + d.val) := by
    rw [Matrix.mulVec_mulVec, ← SubexponentialSAT.BinomialMatrix.factorization]
    exact mulVec_coefficients _ (isUnit_det_binomial A R) _
  have hu : IsUnit (SubexponentialSAT.BinomialMatrix.L ℤ R).det := by simp
  have h1 := coefficients_unique _ hu _ _ hc
  have h2 := coefficients_unique _ hu _ _ hg
  exact h1.trans h2.symm

theorem parity_upper_recurrence (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) A R j =
      (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val -
        ∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0 := by
  have heq := congrFun (upper_mulVec_parity A R) j
  simp only [Matrix.mulVec, dotProduct] at heq
  have hsplit :
      (∑ k : Fin R, SubexponentialSAT.BinomialMatrix.U ℤ A R j k *
        parityCoefficients (K := ℤ) A R k) =
      parityCoefficients (K := ℤ) A R j +
        ∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0 := by
    calc
      _ = ∑ k : Fin R,
          ((if k = j then parityCoefficients (K := ℤ) A R j else 0) +
          (if j.val < k.val then (A.choose (k.val - j.val) : ℤ) *
            parityCoefficients (K := ℤ) A R k else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k = j
        · subst k
          simp [SubexponentialSAT.BinomialMatrix.U]
        · by_cases hjk : j.val < k.val
          · simp [SubexponentialSAT.BinomialMatrix.U, h, hjk, Nat.le_of_lt hjk]
          · have hn : ¬j.val ≤ k.val := by
              have hne : k.val ≠ j.val := fun he => h (Fin.ext he)
              omega
            simp [SubexponentialSAT.BinomialMatrix.U, h, hjk, hn]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit] at heq
  omega

theorem natAbs_parity_recurrence (A R : ℕ) (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j).natAbs ≤
      2 ^ j.val + ∑ k : Fin R, if j.val < k.val then
        A.choose (k.val - j.val) * (parityCoefficients (K := ℤ) A R k).natAbs
        else 0 := by
  rw [parity_upper_recurrence A R j]
  calc
    _ ≤ ((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val).natAbs +
        (∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0).natAbs := Int.natAbs_sub_le _ _
    _ ≤ _ := by
      have h := Int.natAbs_sum_le (Finset.univ : Finset (Fin R))
        (fun k => if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k else 0)
      have htwo : (2 : ℤ).natAbs = 2 := by norm_num
      simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
        Int.natAbs_natCast, htwo, one_pow, one_mul, apply_ite Int.natAbs,
        Int.natAbs_zero] using
        Nat.add_le_add_left h (((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val).natAbs)

/-- A coarse uniform bound suffices for O(R log Q) coefficient bit length. -/
theorem natAbs_parityCoefficients_le (A R Q : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q)
    (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j).natAbs ≤ (4 * Q) ^ R := by
  let b : Fin R → ℕ := fun k => Q ^ k.val *
    (parityCoefficients (K := ℤ) A R k).natAbs
  let M := Q ^ R * 2 ^ R
  have hb : ∀ i, b i ≤ M + ∑ k : Fin R, if i.val < k.val then b k else 0 := by
    intro i
    calc
      b i ≤ Q ^ i.val * (2 ^ i.val + ∑ k : Fin R, if i.val < k.val then
          A.choose (k.val - i.val) * (parityCoefficients (K := ℤ) A R k).natAbs
          else 0) := Nat.mul_le_mul_left _ (natAbs_parity_recurrence A R i)
      _ = Q ^ i.val * 2 ^ i.val + ∑ k : Fin R, if i.val < k.val then
          Q ^ i.val * (A.choose (k.val - i.val) *
            (parityCoefficients (K := ℤ) A R k).natAbs) else 0 := by
        rw [Nat.mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ M + ∑ k : Fin R, if i.val < k.val then b k else 0 := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul (Nat.pow_le_pow_right hQ (Nat.le_of_lt i.isLt))
            (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt i.isLt))
        · apply Finset.sum_le_sum
          intro k hk
          split_ifs with hik
          · have hc : A.choose (k.val - i.val) ≤ Q ^ (k.val - i.val) :=
              (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hAQ _)
            calc
              _ ≤ Q ^ i.val * (Q ^ (k.val - i.val) *
                  (parityCoefficients (K := ℤ) A R k).natAbs) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
              _ = b k := by
                rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hik)]
          · exact Nat.le_refl _
  have hs := triangular_sum_bound R M b hb
  have hj : b j ≤ ∑ i, b i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hsmall : (parityCoefficients (K := ℤ) A R j).natAbs ≤ b j := by
    dsimp [b]
    have hp : 1 ≤ Q ^ j.val := one_le_pow₀ hQ
    simpa using Nat.mul_le_mul_right (parityCoefficients (K := ℤ) A R j).natAbs hp
  calc
    _ ≤ M * 2 ^ R := hsmall.trans (hj.trans (le_trans (Nat.le_add_right _ _) hs))
    _ = (4 * Q) ^ R := by
      dsimp [M]
      rw [mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      ring

theorem natAbs_extend_parityCoefficients_le (A R Q j : ℕ)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) :
    (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs ≤
      (4 * Q) ^ R := by
  by_cases hj : j < R
  · simpa [extendCoefficients, hj] using
      natAbs_parityCoefficients_le A R Q hAQ hQ ⟨j, hj⟩
  · simp [extendCoefficients, hj]

end SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

end OAI.Algorithms
