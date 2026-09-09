/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseExactDivision
import RiemannGaussian.ZetaPhaseQuotientCenter
import RiemannGaussian.ZetaPhasePrimalEnclosure
import RiemannGaussian.ZetaPhaseExactFamily

/-!
# The exact optimizer for the fixed-shift linear height cost

The canonical quotient is close to a uniformly positive rational
polynomial. This proves feasibility of the exact family and closes the
attainment gap in the all-frequency dual bound. The resulting uniqueness
and support statements concern the specified shift and cost; they are
not an intrinsic assertion about zeta zeros or a proof of RH.
-/

open scoped Classical Polynomial
open Polynomial

namespace RiemannGaussian

noncomputable section

private theorem exactCoefficient_le_one (i : Fin 9) : phaseContactExactCoefficients i ≤ 1 := by
  have hw (j : Fin 9) : 1 ≤ phaseContactCost (phaseContactFrequency j) := by
    fin_cases j <;> norm_num [phaseContactFrequency, phaseContactCost]
  have h := Finset.single_le_sum (f := fun j : Fin 9 ↦
    phaseContactExactCoefficients j * phaseContactCost (phaseContactFrequency j))
    (fun j _ ↦ mul_nonneg (phaseContactExactCoefficients_pos j).le (by linarith [hw j]))
    (Finset.mem_univ i)
  rw [phaseContactExactCoefficients_cost] at h
  exact (le_mul_of_one_le_right (phaseContactExactCoefficients_pos i).le (hw i)).trans h

set_option maxHeartbeats 4000000 in
private theorem quotient_center_combination (k : Fin 17) :
    |(∑ i : Fin 3, phaseContactPrimalCenterQ ⟨i.val + 6, by omega⟩ *
        phaseContactDivisionCenterQ i 8 k.val) - phaseContactQuotientCenterQ k.val| ≤ (1 / 10 ^ 18 : ℚ) := by
  fin_cases k <;> norm_num [phaseContactPrimalCenterQ, phaseContactDivisionCenterQ_final,
    phaseContactQuotientCenterQ, Fin.sum_univ_succ]

/-- The canonical quotient's coefficients lie close to the positive
rational center. Only the three genuine high-frequency contributions
enter this estimate. -/
theorem abs_phaseContactExactQuotient_coeff_sub_center_le (k : Fin 17) :
    |phaseContactExactQuotient.coeff k.val - (phaseContactQuotientCenterQ k.val : ℝ)| ≤
      (1 / 10 ^ 5 : ℝ) := by
  let q : Fin 4 → ℝ := fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j)
  let v (i : Fin 3) : ℝ := (phaseContactDeflate q
    (Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ))).coeff k.val
  let c (i : Fin 3) : ℝ := (phaseContactDivisionCenterQ i 8 k.val : ℝ)
  have hv (i : Fin 3) : |v i - c i| ≤ (1 / 10 ^ 10 : ℝ) :=
    abs_phaseContactDeflate_high_coeff_sub_center_le i ⟨k.val, by omega⟩
  have hc (i : Fin 3) : |c i| ≤ (10 ^ 9 : ℝ) := by
    dsimp only [c]
    exact_mod_cast abs_phaseContactDivisionCenterQ_le i 8 k.val
  have hterm (i : Fin 3) :
      |phaseContactExactCoefficients ⟨i.val + 6, by omega⟩ * v i -
        phaseContactPrimalCenter ⟨i.val + 6, by omega⟩ * c i| ≤ (2 / 10 ^ 6 : ℝ) := by
    let l : Fin 9 := ⟨i.val + 6, by omega⟩
    have hde := abs_phaseContactExactCoefficients_sub_center_le l
    have ha : |phaseContactExactCoefficients l| ≤ 1 := by
      rw [abs_of_pos (phaseContactExactCoefficients_pos l)]
      exact exactCoefficient_le_one l
    have h1 : |phaseContactExactCoefficients l * (v i - c i)| ≤ (1 / 10 ^ 10 : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul ha (hv i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have h2 : |(phaseContactExactCoefficients l - phaseContactPrimalCenter l) * c i| ≤
        (1 / 10 ^ 6 : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul hde (hc i) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hid : phaseContactExactCoefficients l * v i - phaseContactPrimalCenter l * c i =
        phaseContactExactCoefficients l * (v i - c i) +
          (phaseContactExactCoefficients l - phaseContactPrimalCenter l) * c i := by ring
    change |phaseContactExactCoefficients l * v i - phaseContactPrimalCenter l * c i| ≤ _
    rw [hid]
    linarith [abs_add_le (phaseContactExactCoefficients l * (v i - c i))
      ((phaseContactExactCoefficients l - phaseContactPrimalCenter l) * c i)]
  have hsum : |phaseContactExactQuotient.coeff k.val -
      ∑ i : Fin 3, phaseContactPrimalCenter ⟨i.val + 6, by omega⟩ * c i| ≤ (6 / 10 ^ 6 : ℝ) := by
    rw [phaseContactExactQuotient_eq_three_frequencies]
    simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ ↦ hterm i)).trans_eq (by norm_num))
  have hrat : |(∑ i : Fin 3, phaseContactPrimalCenter ⟨i.val + 6, by omega⟩ * c i) -
      (phaseContactQuotientCenterQ k.val : ℝ)| ≤ (1 / 10 ^ 18 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (quotient_center_combination k)
    push_cast at h
    exact h
  have ht := abs_sub_le (phaseContactExactQuotient.coeff k.val)
    (∑ i : Fin 3, phaseContactPrimalCenter ⟨i.val + 6, by omega⟩ * c i)
    (phaseContactQuotientCenterQ k.val : ℝ)
  linarith

/-- The exact quotient stays close to its rational center throughout the
entire cosine interval, including both endpoints. -/
theorem abs_phaseContactExactQuotient_eval_sub_center_le {x : ℝ} (hx : |x| ≤ 1) :
    |phaseContactExactQuotient.eval x - phaseContactQuotientCenter.eval x| ≤ (17 / 10 ^ 5 : ℝ) := by
  have he : phaseContactExactQuotient.eval x =
      ∑ k : Fin 17, phaseContactExactQuotient.coeff k.val * x ^ k.val := by
    have hn : phaseContactExactQuotient.natDegree < 17 := by
      have h := phaseContactExactQuotient_natDegree_le
      omega
    rw [eval_eq_sum_range' hn]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [he]
  simp only [phaseContactQuotientCenter, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    ← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ k : Fin 17, |phaseContactExactQuotient.coeff k.val -
        (phaseContactQuotientCenterQ k.val : ℝ)| * |x ^ k.val| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (s := (Finset.univ : Finset (Fin 17)))
        (f := fun k ↦ (phaseContactExactQuotient.coeff k.val - (phaseContactQuotientCenterQ k.val : ℝ)) * x ^ k.val)
    _ ≤ ∑ _k : Fin 17, (1 / 10 ^ 5 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hpow : |x ^ k.val| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) hx
      exact (mul_le_mul (abs_phaseContactExactQuotient_coeff_sub_center_le k) hpow
        (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
    _ = _ := by norm_num

/-- A uniform rational lower bound survives the full transfer from the
central polynomial to the canonical exact quotient. -/
theorem phaseContactExactQuotient_lower {x : ℝ} (hx : |x| ≤ 1) :
    (483 / 100000 : ℝ) ≤ phaseContactExactQuotient.eval x := by
  have hc := phaseContactQuotientCenter_lower hx
  have he := (abs_le.mp (abs_phaseContactExactQuotient_eval_sub_center_le hx)).1
  linarith

/-- The canonical quotient is strictly positive everywhere on `[-1,1]`.
Its squared contact factors are the only zeros of the exact kernel there. -/
theorem phaseContactExactQuotient_pos {x : ℝ} (hx : |x| ≤ 1) :
    0 < phaseContactExactQuotient.eval x :=
  lt_of_lt_of_le (by norm_num) (phaseContactExactQuotient_lower hx)

/-- The exact candidate satisfies global phase-kernel nonnegativity. -/
theorem phaseContactExactFamily_kernel_nonneg (t : ℝ) :
    0 ≤ phaseContactKernel phaseContactExactFamily t := by
  rw [phaseContactExactFamily_kernel]
  exact phaseContactExactKernel_nonneg_of_quotient
    (phaseContactExactQuotient_pos (Real.abs_cos_le_one t)).le

/-- The exact family attains the largest source among all cost-one,
nonnegative, globally feasible phase sequences, including infinite ones. -/
theorem phaseContactExactFamily_maximizes {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) (hb : phaseContactBudget a = 1) :
    phaseContactSource a ≤ phaseContactSource phaseContactExactFamily := by
  rw [phaseContactExactFamily_source]
  simpa only [hb, mul_one] using phaseContactSource_le_exactContactBound ha hs hp

/-- Equality with the attained optimum determines the complete coefficient
sequence uniquely. The nine selected coefficients include the constant. -/
theorem phaseContactExactFamily_unique_optimizer {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) (hb : phaseContactBudget a = 1) :
    phaseContactSource a = phaseContactSource phaseContactExactFamily ↔ a = phaseContactExactFamily := by
  constructor
  · intro he
    rw [phaseContactExactFamily_source] at he
    exact phaseContactExactFamily_unique_at_bound ha hs hp hb he
  · rintro rfl
    rfl

/-- Every selected frequency is necessary for optimality, including the
very small higher-frequency terms: setting even one to zero strictly
lowers the achievable source under the same constraints. -/
theorem phaseContactExactFamily_strict_of_missing_frequency {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) (hb : phaseContactBudget a = 1)
    {n : ℕ} (hn : n ∈ phaseContactFrequencies) (hzero : a n = 0) :
    phaseContactSource a < phaseContactSource phaseContactExactFamily := by
  apply lt_of_le_of_ne (phaseContactExactFamily_maximizes ha hs hp hb)
  intro he
  have heq := (phaseContactExactFamily_unique_optimizer ha hs hp hb).mp he
  rw [heq] at hzero
  exact (phaseContactExactFamily_ne_zero_iff n).mpr hn hzero

/-- The exact kernel vanishes precisely at the four proved contact
cosines. The positive quotient introduces no hidden additional contact. -/
theorem phaseContactExactKernel_eq_zero_iff {x : ℝ} (hx : |x| ≤ 1) :
    phaseContactExactKernel x = 0 ↔
      ∃ j : Fin 4, x = phaseContactExactRoot (phaseContactCosineCoordinate j) := by
  rw [← phaseContactExactPolynomial_eval, phaseContactExactPolynomial_eq_factor_mul_quotient,
    eval_mul, mul_eq_zero]
  have hq := ne_of_gt (phaseContactExactQuotient_pos hx)
  simp only [hq, or_false, phaseContactFactor, eval_prod, eval_pow, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sq_eq_zero_iff, sub_eq_zero]

/-- The near-contact at angle pi is strictly positive in the exact
optimizer. It is not a fifth contact concealed by numerical precision. -/
theorem phaseContactExactKernel_neg_one_pos : 0 < phaseContactExactKernel (-1) := by
  have hp := phaseContactExactKernel_nonneg_of_quotient
    (phaseContactExactQuotient_pos (x := -1) (by norm_num)).le
  apply lt_of_le_of_ne hp
  intro hz
  obtain ⟨j, hj⟩ := (phaseContactExactKernel_eq_zero_iff (x := -1) (by norm_num)).mp hz.symm
  have hq := (abs_lt.mp (abs_phaseContactExactRoot_cosine_lt_one j)).1
  linarith

/-- Precisely eight nonconstant frequencies occur in the exact optimizer.
Finite support was deduced from the all-frequency bound. -/
theorem phaseContactExactFamily_nonconstant_count :
    Set.ncard {n : ℕ | 0 < n ∧ phaseContactExactFamily n ≠ 0} = 8 := by
  have hs : {n : ℕ | 0 < n ∧ phaseContactExactFamily n ≠ 0} =
      (↑(phaseContactFrequencies.erase 0) : Set ℕ) := by
    ext n
    simp [phaseContactExactFamily_ne_zero_iff, Nat.pos_iff_ne_zero, and_comm]
  rw [hs, Set.ncard_coe_finset]
  decide

/-- There exists exactly one globally feasible, cost-one phase sequence
attaining the exact all-frequency contact bound. All convergence and
positivity obligations for the constructed sequence are discharged. -/
theorem existsUnique_phaseContactOptimizer :
    ∃! a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧
      HasSum (fun n ↦ phaseContactCost n * a n) 1 ∧
      (∀ t, 0 ≤ phaseContactKernel a t) ∧ phaseContactSource a = phaseContactExactRoot 8 := by
  refine ⟨phaseContactExactFamily, ⟨phaseContactExactFamily_nonneg,
    phaseContactExactFamily_hasSum_budget, phaseContactExactFamily_kernel_nonneg,
    phaseContactExactFamily_source⟩, ?_⟩
  intro a ha
  exact phaseContactExactFamily_unique_at_bound ha.1 ha.2.1.summable ha.2.2.1
    ha.2.1.tsum_eq ha.2.2.2

end

end RiemannGaussian
