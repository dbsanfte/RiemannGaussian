/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiResonantBudget
import RiemannGaussian.GaussianFermiProfileSurplus

/-!
# Height bounds for the Gaussian Fermi exclusion comparison

The already proved zero-free margin supplies the required normalized
interval at height `48*t`. Explicit elementary bounds control the Gaussian
scale, nonconstant poles and gamma costs for the existing exact phase
family. The only remaining height tail is the earlier uniformly vanishing
whole-divisor allowance.
-/

namespace RiemannGaussian.GaussianFermiHeightBounds

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiDerivativeBounds GaussianFermiMovingAllowance GaussianFermiLaplaceOrder
open GaussianFermiProfileSurplus

/-- The actual reserve margin lies in the entire profile interval after
normalization by the logarithm of the original ordinate. -/
theorem normalized_margin_bounds {t : ℝ} (ht : 0 < t) (hlog : 2000 ≤ Real.log t) :
    1 / 10 ≤ Real.log t * zetaPoleReserveZeroMargin (48 * t) ∧
      Real.log t * zetaPoleReserveZeroMargin (48 * t) ≤ 21 / 200 := by
  let L := Real.log t
  let S := Real.log (48 * t + 2)
  have hL : 0 < L := by dsimp [L]; linarith
  have ht1 : 1 ≤ t := by
    by_contra hn
    have hnlog := Real.log_neg ht (lt_of_not_ge hn)
    linarith
  have hS0 : L ≤ S := Real.log_le_log ht (by linarith)
  have hS1 : S ≤ L + 49 := by
    calc
      _ ≤ Real.log (50 * t) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 50 + L := Real.log_mul (by norm_num) ht.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 50)]
  have hD : 0 < 7625 * S - 2000 := by dsimp [L] at hS0; linarith
  have hE : 0 < 45750 * S - 35725 := by dsimp [L] at hS0; linarith
  have hlow : (1 / 10 : ℝ) ≤ L * (792 / (7625 * S - 2000)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    dsimp [L] at hS1 ⊢
    linarith
  have hu0 : L * (792 / (7625 * S - 2000)) ≤ (21 / 200 : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hD).mpr
    dsimp [L] at hS0 ⊢
    linarith
  have hu1 : L * (4752 / (45750 * S - 35725)) ≤ (21 / 200 : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hE).mpr
    dsimp [L] at hS0 ⊢
    linarith
  have he : zetaPoleReserveZeroMargin (48 * t) =
      max (792 / (7625 * S - 2000))
        (min (4 / 39) (4752 / (45750 * S - 35725))) := by
    rw [zetaPoleReserveZeroMargin, zetaSignedPoleZeroMargin, zetaPoleReserveFixedMargin_eq,
      abs_of_pos (by positivity : 0 < 48 * t)]
    rw [max_eq_right (show (13 / 10 : ℝ) ≤ Real.log (48 * t + 2) by
      change 13 / 10 ≤ S
      dsimp [L] at hS0
      linarith)]
  change 1 / 10 ≤ L * zetaPoleReserveZeroMargin (48 * t) ∧
    L * zetaPoleReserveZeroMargin (48 * t) ≤ 21 / 200
  rw [he, mul_max_of_nonneg _ _ hL.le]
  constructor
  · exact hlow.trans (le_max_left _ _)
  · apply max_le hu0
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le).trans hu1

/-- The chosen Gaussian scale belongs to the full admissible interval
whenever the normalized interior margin belongs to the profile interval. -/
theorem scale_admissible {L m : ℝ} (hL : 1 ≤ L) (hm : 0 ≤ m)
    (hmu : L * m ≤ 21 / 200) :
    m ^ 2 ≤ 1 / (9 * L ^ 2) ∧ 1 / (9 * L ^ 2) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hmle : m ≤ 1 / (3 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : (1 / (3 * L)) ^ 2 = 1 / (9 * L ^ 2) := by field_simp; ring
  constructor
  · rw [← he]
    exact pow_le_pow_left₀ hm hmle 2
  · apply (div_le_one (by positivity)).mpr
    nlinarith

/-- An explicit constant bounds the previously proved inverse-margin
derivative cost; no numerical xi-growth constant enters this estimate. -/
theorem integralCost_le_log {m b L : ℝ} (hm : 0 < m) (hmu : m ≤ 1 / 4)
    (hb : b ≤ 1) (hscale : m ^ 2 ≤ b) (hml : 1 / 10 ≤ L * m) :
    integralCost (1 - 2 * m) b m ≤ 3440 * L := by
  have he : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    norm_num at h
    exact h
  have hp : Real.sqrt Real.pi ≤ 2 := by
    nlinarith [Real.pi_lt_four, Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi]
  have hc : 86 * Real.exp (1 / 2) * Real.sqrt Real.pi ≤ 344 := by
    calc
      _ ≤ (86 : ℝ) * 2 * 2 := by gcongr
      _ = _ := by norm_num
  have hi : 1 / m ≤ 10 * L := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  calc
    _ ≤ _ := integralCost_le_inverse_margin hm hmu hscale hb
    _ ≤ 344 / m := div_le_div_of_nonneg_right hc hm.le
    _ = 344 * (1 / m) := by ring
    _ ≤ 344 * (10 * L) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

/-- Every frequency in the existing exact family lies in the stated
finite height range. -/
theorem exact_frequency_le (j : Fin 9) : phaseContactFrequency j ≤ 24 := by
  fin_cases j <;> norm_num [phaseContactFrequency]

/-- Only the actual constant mode has zero frequency. -/
theorem exact_frequency_eq_zero_iff (j : Fin 9) :
    phaseContactFrequency j = 0 ↔ j = 0 := by
  fin_cases j <;> norm_num [phaseContactFrequency]

/-- The explicit gamma cost in the selected-zero phase formula. -/
def gammaUpper (v : ℝ) : ℝ :=
  (Real.log (5 / 4 + |v|) - Real.log Real.pi) / 4 + 7 / (8 * (5 / 4 + |v|))

/-- All bounded-ratio nonconstant frequencies have leading gamma cost
at most one quarter of the logarithm, with one common absolute remainder. -/
theorem gammaUpper_le {t v : ℝ} (ht : 1 ≤ t) (hv : |v| ≤ 24 * t) :
    gammaUpper v ≤ Real.log t / 4 + 7 := by
  have htp : 0 < t := by linarith
  have hA : 0 < (5 / 4 : ℝ) + |v| := by positivity
  have hlog : Real.log (5 / 4 + |v|) ≤ Real.log t + 25 := by
    calc
      _ ≤ Real.log (26 * t) := Real.log_le_log hA (by linarith)
      _ = Real.log 26 + Real.log t := Real.log_mul (by norm_num) htp.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 26)]
  have hp : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have he : 7 / (8 * (5 / 4 + |v|)) ≤ (7 / 10 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [abs_nonneg v]
  unfold gammaUpper
  linarith

/-- The constant mode pays no logarithmic-height gamma cost. -/
theorem gammaUpper_zero_le : gammaUpper 0 ≤ 7 := by
  have h := gammaUpper_le (t := 1) (v := 0) (by norm_num) (by norm_num)
  simpa using h

/-- At sufficiently large logarithmic height every nonconstant exact-family
pole is at most one, uniformly over the admissible Gaussian scales. -/
theorem nonzero_poleUpper_le_one {γ m b : ℝ} (hγ : γ ≠ 0)
    (hlog : 4000 ≤ Real.log |γ|) (hm : 0 < m) (hmu : m ≤ 1 / 4)
    (hb : b ≤ 1) (hscale : m ^ 2 ≤ b) (hml : 1 / 10 ≤ Real.log |γ| * m)
    (j : Fin 9) (hj : j ≠ 0) :
    poleUpper b (1 - m) ((phaseContactFrequency j : ℝ) * γ) ≤ 1 := by
  have ht : 0 < |γ| := abs_pos.mpr hγ
  have hlogle := Real.log_le_sub_one_of_pos ht
  have hc := integralCost_le_log hm hmu hb hscale hml
  have hc1 : integralCost (1 - 2 * m) b m ≤ |γ| ^ 2 := by
    nlinarith
  have hfn : phaseContactFrequency j ≠ 0 := by
    intro h
    exact hj ((exact_frequency_eq_zero_iff j).mp h)
  have hf : (1 : ℝ) ≤ phaseContactFrequency j := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hfn)
  have hv : (phaseContactFrequency j : ℝ) * γ ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hfn) hγ
  have habs : |γ| ≤ |(phaseContactFrequency j : ℝ) * γ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ phaseContactFrequency j)]
    nlinarith
  have hs : |γ| ^ 2 ≤ ((phaseContactFrequency j : ℝ) * γ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg γ) habs 2
  unfold poleUpper
  rw [if_neg hv, show 2 * (1 - m) - 1 = 1 - 2 * m by ring,
    show 1 - (1 - m) = m by ring]
  exact (div_le_one (sq_pos_of_ne_zero hv)).mpr (hc1.trans hs)

/-- The exact finite family's complete pole and gamma costs are at most
the Gaussian constant pole plus the nonconstant logarithmic mass and eight.
Every selected higher frequency remains in the coefficient sums. -/
theorem exact_phase_cost_le {γ m b : ℝ} (hγ : γ ≠ 0)
    (hlog : 4000 ≤ Real.log |γ|) (hm : 0 < m) (hmu : m ≤ 1 / 4)
    (hb : b ≤ 1) (hscale : m ^ 2 ≤ b) (hml : 1 / 10 ≤ Real.log |γ| * m) :
    (∑ j : Fin 9, phaseContactExactCoefficients j *
      (poleUpper b (1 - m) ((phaseContactFrequency j : ℝ) * γ) +
        gammaUpper ((phaseContactFrequency j : ℝ) * γ))) ≤
      phaseContactExactCoefficients 0 * halfGaussian b (-m) +
        (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) *
          Real.log |γ| / 4 + 8 := by
  have ht : 0 < |γ| := abs_pos.mpr hγ
  have ht1 : 1 ≤ |γ| := by linarith [Real.log_le_sub_one_of_pos ht]
  have hpoint (j : Fin 9) : phaseContactExactCoefficients j *
      (poleUpper b (1 - m) ((phaseContactFrequency j : ℝ) * γ) +
        gammaUpper ((phaseContactFrequency j : ℝ) * γ)) ≤
      (if j = 0 then phaseContactExactCoefficients j * halfGaussian b (-m) else 0) +
        (if j = 0 then 0 else phaseContactExactCoefficients j) * Real.log |γ| / 4 +
          8 * phaseContactExactCoefficients j := by
    have hw := (phaseContactExactCoefficients_pos j).le
    by_cases hj : j = 0
    · subst j
      simp only [phaseContactFrequency, Matrix.cons_val_zero, Nat.cast_zero, zero_mul,
        poleUpper, if_true, zero_div, add_zero]
      rw [show 1 - m - 1 = -m by ring]
      nlinarith [gammaUpper_zero_le]
    · have hp := nonzero_poleUpper_le_one hγ hlog hm hmu hb hscale hml j hj
      have hg := gammaUpper_le ht1 (v := (phaseContactFrequency j : ℝ) * γ) (by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ phaseContactFrequency j)]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast exact_frequency_le j) (abs_nonneg γ))
      simp only [if_neg hj, zero_add]
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  have he : (∑ j : Fin 9,
      ((if j = 0 then phaseContactExactCoefficients j * halfGaussian b (-m) else 0) +
        (if j = 0 then 0 else phaseContactExactCoefficients j) * Real.log |γ| / 4 +
          8 * phaseContactExactCoefficients j)) =
      phaseContactExactCoefficients 0 * halfGaussian b (-m) +
        (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) *
          Real.log |γ| / 4 + 8 * (∑ j : Fin 9, phaseContactExactCoefficients j) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_div,
      ← Finset.sum_mul, ← Finset.mul_sum]
  rw [he] at hsum
  linarith [exact_total_mass_upper]

end
end RiemannGaussian.GaussianFermiHeightBounds
