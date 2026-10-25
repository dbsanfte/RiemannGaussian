/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellation
import RiemannGaussian.SuzukiProperPrimePowerWork

/-!
# Bounded proper-prime-power cost in the exact local Suzuki comparison

The complete proper-prime-power part of the fixed signed packet has one
uniform constant bound. The remaining ordinary-prime comparison is unchanged;
no bound for its negative part or RH conclusion is asserted.
-/

namespace RiemannGaussian
noncomputable section
open scoped BigOperators

/-- The fixed local kernel is bounded independently of the logarithmic base. -/
theorem abs_suzukiLocalSignedKernel_le (v : ℝ) :
    |suzukiLocalSignedKernel v| ≤ (Real.sqrt 2 + 1) * Real.log 2 := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb (u : ℝ) : 0 ≤ suzukiLocalTriangle (Real.log 2) u ∧
      suzukiLocalTriangle (Real.log 2) u ≤ Real.log 2 := by
    unfold suzukiLocalTriangle
    exact ⟨le_max_left _ _, max_le hh (by linarith [abs_nonneg (u - Real.log 2)])⟩
  unfold suzukiLocalSignedKernel
  calc
    _ ≤ |Real.sqrt 2 * suzukiLocalTriangle (Real.log 2) v| +
        |suzukiLocalTriangle (Real.log 2) (v - Real.log 2)| := abs_sub _ _
    _ = Real.sqrt 2 * suzukiLocalTriangle (Real.log 2) v +
        suzukiLocalTriangle (Real.log 2) (v - Real.log 2) := by
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hb v).1),
        abs_of_nonneg (hb _).1]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (hb v).2 (Real.sqrt_nonneg 2),
      (hb (v - Real.log 2)).2]

/-- The ordinary-prime part on the very same finite signed-kernel window. -/
def suzukiLocalOrdinaryPrimeComparison (t : ℝ) : ℝ :=
  ∑ n ∈ suzukiArithmeticPrimeWindow (t + 3 * Real.log 2),
    if n.Prime then ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      suzukiLocalSignedKernel (Real.log n - t) else 0

private def localProperCoefficient (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

private theorem localProperCoefficient_nonneg (n : ℕ) :
    0 ≤ localProperCoefficient n := by
  unfold localProperCoefficient
  split_ifs <;> positivity

private theorem localProperCoefficient_prefix (t : ℝ) :
    (∑ n ∈ suzukiArithmeticPrimeWindow t, localProperCoefficient n) =
      Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) := by
  have hzero : (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, localProperCoefficient n) =
      ∑ n ∈ Finset.Icc 0 ⌊Real.exp t⌋₊, localProperCoefficient n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc] at hn hn'
        omega
      subst n
      simp [localProperCoefficient]
  rw [suzukiArithmeticPrimeWindow, hzero, Chebyshev.psi_eq_sum_Icc,
    Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp [localProperCoefficient, hp, ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [localProperCoefficient, hp]

private theorem localProperDifference (t : ℝ) :
    suzukiLocalPrimeComparison t - suzukiLocalOrdinaryPrimeComparison t =
      ∑ n ∈ suzukiArithmeticPrimeWindow (t + 3 * Real.log 2),
        localProperCoefficient n / Real.sqrt n *
          suzukiLocalSignedKernel (Real.log n - t) := by
  rw [suzukiLocalPrimeComparison_eq_sum_signed_kernel,
    suzukiLocalOrdinaryPrimeComparison, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime <;> simp [localProperCoefficient, hp]

/-- The complete proper-prime-power deletion has one constant cost for every
nonnegative real logarithmic base, retaining the exact finite endpoint. -/
theorem abs_suzukiLocalPrimeComparison_sub_ordinary_le {t : ℝ} (ht : 0 ≤ t) :
    |suzukiLocalPrimeComparison t - suzukiLocalOrdinaryPrimeComparison t| ≤
      54 * ((Real.sqrt 2 + 1) * Real.log 2) := by
  let K : ℝ := (Real.sqrt 2 + 1) * Real.log 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hroot : 0 < Real.sqrt (Real.exp t) := Real.sqrt_pos.2 (Real.exp_pos t)
  have hterm (n : ℕ) :
      |localProperCoefficient n / Real.sqrt n *
          suzukiLocalSignedKernel (Real.log n - t)| ≤
        (K / Real.sqrt (Real.exp t)) * localProperCoefficient n := by
    by_cases hn : (n : ℝ) < Real.exp t
    · have hlog : Real.log n - t ≤ 0 := by
        by_cases hn0 : n = 0
        · subst n; simpa using ht
        · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
          exact sub_nonpos.mpr ((Real.log_lt_iff_lt_exp hnpos).2 hn).le
      have hz : suzukiLocalSignedKernel (Real.log n - t) = 0 := by
        unfold suzukiLocalSignedKernel
        rw [suzukiLocalTriangle_eq_zero_of_nonpos
          (Real.log_nonneg (by norm_num)) hlog,
          suzukiLocalTriangle_eq_zero_of_nonpos
            (Real.log_nonneg (by norm_num)) (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])]
        ring
      rw [hz, mul_zero, abs_zero]
      exact mul_nonneg (div_nonneg hK hroot.le) (localProperCoefficient_nonneg n)
    · have hn' : Real.exp t ≤ n := le_of_not_gt hn
      have hs : Real.sqrt (Real.exp t) ≤ Real.sqrt n := Real.sqrt_le_sqrt hn'
      have hnroot : 0 < Real.sqrt (n : ℝ) := hroot.trans_le hs
      rw [abs_mul, abs_of_nonneg (div_nonneg (localProperCoefficient_nonneg n)
        (Real.sqrt_nonneg _))]
      calc
        _ ≤ localProperCoefficient n / Real.sqrt n * K :=
          mul_le_mul_of_nonneg_left (abs_suzukiLocalSignedKernel_le _)
            (div_nonneg (localProperCoefficient_nonneg n) (Real.sqrt_nonneg _))
        _ ≤ _ := by
          have hi := one_div_le_one_div_of_le hroot hs
          have hm := mul_le_mul_of_nonneg_left hi
            (mul_nonneg (localProperCoefficient_nonneg n) hK)
          convert hm using 1 <;> ring
  have hmass := chebyshevPsi_sub_theta_le_eighteen_sqrt
    (show (1 : ℝ) ≤ Real.exp (t + 3 * Real.log 2) by
      apply Real.one_le_exp
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  have hshift : Real.exp (t + 3 * Real.log 2) = 8 * Real.exp t := by
    rw [Real.exp_add, show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  have hsr : Real.sqrt (Real.exp (t + 3 * Real.log 2)) ≤ 3 * Real.sqrt (Real.exp t) := by
    rw [hshift]
    have hs := Real.sqrt_le_sqrt (show 8 * Real.exp t ≤ 9 * Real.exp t by
      linarith [Real.exp_pos t])
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)] at hs
    norm_num at hs
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] using hs
  rw [localProperDifference]
  calc
    _ ≤ ∑ n ∈ suzukiArithmeticPrimeWindow (t + 3 * Real.log 2),
        |localProperCoefficient n / Real.sqrt n *
          suzukiLocalSignedKernel (Real.log n - t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ suzukiArithmeticPrimeWindow (t + 3 * Real.log 2),
        K / Real.sqrt (Real.exp t) * localProperCoefficient n :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = K / Real.sqrt (Real.exp t) *
        (Chebyshev.psi (Real.exp (t + 3 * Real.log 2)) -
          Chebyshev.theta (Real.exp (t + 3 * Real.log 2))) := by
      rw [← Finset.mul_sum, localProperCoefficient_prefix]
    _ ≤ K / Real.sqrt (Real.exp t) * (18 * (3 * Real.sqrt (Real.exp t))) :=
      mul_le_mul_of_nonneg_left (hmass.trans
        (mul_le_mul_of_nonneg_left hsr (by norm_num))) (div_nonneg hK hroot.le)
    _ = _ := by dsimp [K]; field_simp; ring

/-- The ordinary-prime signed comparison at a real multiplicative base. -/
def suzukiLocalOrdinaryArithmeticComparison (X : ℝ) : ℝ :=
  suzukiLocalOrdinaryPrimeComparison (Real.log X)

/-- Proper prime powers have one uniform bounded cost in the literal real-base
`G(X)`, for every real `X ≥ 1`, including both support endpoints. -/
theorem abs_suzukiLocalArithmeticComparison_sub_ordinary_le {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalArithmeticComparison X - suzukiLocalOrdinaryArithmeticComparison X| ≤
      54 * ((Real.sqrt 2 + 1) * Real.log 2) := by
  have hpos : 0 < X := zero_lt_one.trans_le hX
  have he := suzukiLocalArithmeticComparison_exp (Real.log X)
  rw [Real.exp_log hpos] at he
  rw [he, suzukiLocalOrdinaryArithmeticComparison]
  exact abs_suzukiLocalPrimeComparison_sub_ordinary_le (Real.log_nonneg hX)

end
end RiemannGaussian
