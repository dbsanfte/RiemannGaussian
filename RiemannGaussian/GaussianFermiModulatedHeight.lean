/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiModulatedSource
import RiemannGaussian.GaussianModulatedLaplace
import RiemannGaussian.GaussianFermiHeightBounds

/-!
# Full height costs for the three coupled Fermi evaluations

Bounded modulation preserves separation from every nonconstant pole and
the leading quarter-log gamma cost. At the constant mode the three pole
evaluations are combined before comparison, preserving the modulated
Laplace gain. The final estimate retains every original phase coefficient.
-/

namespace RiemannGaussian.GaussianFermiModulatedHeight
noncomputable section
open MeasureTheory hiding average
open GaussianFermiModulatedBudget GaussianFermiModulatedSource GaussianModulatedLaplace
open GaussianFermiHeightBounds GaussianFermiProfileSurplus GaussianFermiLaplaceOrder
open GaussianFermiGammaBound GaussianFermiGaussianMixture GaussianFermiPoleFormula
open GaussianFermiDerivativeBounds

/-- Slightly shifted bounded-ratio ordinates keep the quarter-log gamma cost. -/
theorem gammaUpper_le_shifted {t v : ℝ} (ht : 1 ≤ t) (hv : |v| ≤ 25 * t) :
    gammaUpper v ≤ Real.log t / 4 + 8 := by
  have htp : 0 < t := by linarith
  have hA : 0 < (5 / 4 : ℝ) + |v| := by positivity
  have hlog : Real.log (5 / 4 + |v|) ≤ Real.log t + 26 := by
    calc
      _ ≤ Real.log (27 * t) := Real.log_le_log hA (by linarith)
      _ = Real.log 27 + Real.log t := Real.log_mul (by norm_num) htp.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 27)]
  have hp : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have he : 7 / (8 * (5 / 4 + |v|)) ≤ (7 / 10 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [abs_nonneg v]
  unfold gammaUpper
  linarith

/-- Every bounded shift of a nonconstant original phase remains far
from zero and inside the enlarged complete height band. -/
theorem frequency_shift_bounds {γ s : ℝ} (ht : 2 ≤ |γ|) (hs : |s| ≤ 1)
    (j : Fin 9) (hj : j ≠ 0) :
    |γ| / 2 ≤ |(phaseContactFrequency j : ℝ) * γ + s| ∧
      |(phaseContactFrequency j : ℝ) * γ + s| ≤ 25 * |γ| := by
  have hfn : phaseContactFrequency j ≠ 0 := by
    intro h
    exact hj ((exact_frequency_eq_zero_iff j).mp h)
  have hf : (1 : ℝ) ≤ phaseContactFrequency j := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hfn)
  have hfu : (phaseContactFrequency j : ℝ) ≤ 24 := by exact_mod_cast exact_frequency_le j
  have hbase : |γ| ≤ |(phaseContactFrequency j : ℝ) * γ| ∧
      |(phaseContactFrequency j : ℝ) * γ| ≤ 24 * |γ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ phaseContactFrequency j)]
    constructor <;> nlinarith [abs_nonneg γ]
  have hlow : |(phaseContactFrequency j : ℝ) * γ| ≤
      |(phaseContactFrequency j : ℝ) * γ + s| + |s| := by
    simpa using abs_sub ((phaseContactFrequency j : ℝ) * γ + s) s
  constructor
  · linarith [hbase.1]
  · linarith [hbase.2, abs_add_le ((phaseContactFrequency j : ℝ) * γ) s]

/-- Any ordinate separated by half the original height has uniformly
bounded pole cost at all admissible Gaussian widths. -/
theorem polePair_le_one {γ v m B : ℝ} (hγ : γ ≠ 0) (hlog : 100000 ≤ Real.log |γ|)
    (hm : 0 < m) (hmu : m ≤ 1 / 4) (hB : 0 < B) (hBu : B ≤ 1)
    (hscale : m ^ 2 ≤ B) (hml : 1 / 10 ≤ Real.log |γ| * m) (hv : |γ| / 2 ≤ |v|) :
    polePair B (1 - m) v ≤ 1 := by
  have ht : 0 < |γ| := abs_pos.mpr hγ
  have hlogle := Real.log_le_sub_one_of_pos ht
  have hc := integralCost_le_log hm hmu hBu hscale hml
  have htlarge : 13760 ≤ |γ| := by linarith
  have hs : integralCost (1 - 2 * m) B m ≤ |γ| ^ 2 / 4 := by
    nlinarith [mul_nonneg (abs_nonneg γ) (sub_nonneg.mpr htlarge)]
  have hvp : 0 < |v| := by linarith
  have hv0 : v ≠ 0 := abs_pos.mp hvp
  have hsquare : |γ| ^ 2 / 4 ≤ v ^ 2 := by nlinarith [sq_abs v]
  have hp := abs_polePair_le hB (show (1 / 2 : ℝ) ≤ 1 - m by linarith)
    (show 1 - m ≤ 1 by linarith) (by simpa using hscale) hv0
  rw [show 2 * (1 - m) - 1 = 1 - 2 * m by ring,
    show 1 - (1 - m) = m by ring] at hp
  exact (le_abs_self _).trans (hp.trans ((div_le_one (sq_pos_of_ne_zero hv0)).mpr (hs.trans hsquare)))

/-- The actual digamma average has the same elementary gamma upper cost
at each of the three ordinates, with all smoothing hypotheses discharged. -/
theorem digamma_cost_le {m b c : ℝ} (hm : 0 ≤ m) (hmu : m ≤ 1 / 4)
    (hb : 0 < b) (hc : 0 < c) (hBu : b + c ≤ 1) (v : ℝ) :
    -Real.log Real.pi / 4 + digammaAverage (1 - 2 * m) b c v ≤ gammaUpper v := by
  have h := digammaAverage_le_uniform_quarter_log (by linarith : 0 < 1 - 2 * m)
    (by linarith : 1 - 2 * m ≤ 1) hb hc hBu v
  unfold gammaUpper
  linarith

/-- The entire exact-family cost has only the coupled constant pole,
the original nonconstant logarithmic mass, and a fixed remainder of nine. -/
theorem exact_average_phase_cost_le {γ m b c δ : ℝ} (hγ : γ ≠ 0)
    (hlog : 100000 ≤ Real.log |γ|) (hm : 0 < m) (hmu : m ≤ 1 / 4)
    (hb : 0 < b) (hc : 0 < c) (hBu : b + c ≤ 1) (hscale : m ^ 2 ≤ b + c)
    (hml : 1 / 10 ≤ Real.log |γ| * m) (hδ : |δ| ≤ 1) :
    (∑ j : Fin 9, phaseContactExactCoefficients j * average δ
      (fun v ↦ polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
        digammaAverage (1 - 2 * m) b c v) ((phaseContactFrequency j : ℝ) * γ)) ≤
      phaseContactExactCoefficients 0 * halfModulated (b + c) δ (-m) +
        (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * Real.log |γ| / 4 + 9 := by
  have ht : 0 < |γ| := abs_pos.mpr hγ
  have ht2 : 2 ≤ |γ| := by linarith [Real.log_le_sub_one_of_pos ht]
  have hpoint (j : Fin 9) : phaseContactExactCoefficients j * average δ
      (fun v ↦ polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
        digammaAverage (1 - 2 * m) b c v) ((phaseContactFrequency j : ℝ) * γ) ≤
      (if j = 0 then phaseContactExactCoefficients j * halfModulated (b + c) δ (-m) else 0) +
        (if j = 0 then 0 else phaseContactExactCoefficients j) * Real.log |γ| / 4 +
          9 * phaseContactExactCoefficients j := by
    have hw := (phaseContactExactCoefficients_pos j).le
    have hg (v : ℝ) := digamma_cost_le hm.le hmu hb hc hBu v
    by_cases hj : j = 0
    · subst j
      simp only [phaseContactFrequency, Matrix.cons_val_zero, Nat.cast_zero, zero_mul,
        if_true, zero_div, add_zero]
      have hp := average_pole_zero_le (add_pos hb hc) δ (show 1 - m ≤ 1 by linarith)
      rw [show 1 - m - 1 = -m by ring] at hp
      change average δ (polePair (b + c) (1 - m)) 0 ≤ halfModulated (b + c) δ (-m) at hp
      have hg0 := gammaUpper_zero_le
      have hgp := gammaUpper_le (t := 1) (v := δ) (by norm_num) (by linarith)
      have hgn := gammaUpper_le (t := 1) (v := -δ) (by norm_num) (by simpa using hδ.trans (by norm_num))
      norm_num only [Real.log_one, zero_div, zero_add] at hgp hgn
      have hc0 := hg 0
      have hcp := hg δ
      have hcn := hg (-δ)
      unfold average at hp ⊢
      simp only [zero_add, zero_sub] at hp ⊢
      nlinarith
    · have hbound (s : ℝ) (hs : |s| ≤ 1) :
          polePair (b + c) (1 - m) ((phaseContactFrequency j : ℝ) * γ + s) - Real.log Real.pi / 4 +
            digammaAverage (1 - 2 * m) b c ((phaseContactFrequency j : ℝ) * γ + s) ≤
              Real.log |γ| / 4 + 9 := by
        have hv := frequency_shift_bounds ht2 hs j hj
        have hp := polePair_le_one hγ hlog hm hmu (add_pos hb hc) hBu hscale hml hv.1
        have hc' := gammaUpper_le_shifted (by linarith : 1 ≤ |γ|) hv.2
        have hg' := hg ((phaseContactFrequency j : ℝ) * γ + s)
        linarith
      have h0 := hbound 0 (by norm_num)
      have hp := hbound δ hδ
      have hn := hbound (-δ) (by simpa using hδ)
      simp only [add_zero, ← sub_eq_add_neg] at h0 hp hn
      simp only [if_neg hj, zero_add, average]
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hpoint j)
  have he : (∑ j : Fin 9,
      ((if j = 0 then phaseContactExactCoefficients j * halfModulated (b + c) δ (-m) else 0) +
        (if j = 0 then 0 else phaseContactExactCoefficients j) * Real.log |γ| / 4 +
          9 * phaseContactExactCoefficients j)) =
      phaseContactExactCoefficients 0 * halfModulated (b + c) δ (-m) +
        (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * Real.log |γ| / 4 +
          9 * (∑ j : Fin 9, phaseContactExactCoefficients j) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_div,
      ← Finset.sum_mul, ← Finset.mul_sum]
  rw [he] at hsum
  linarith [exact_total_mass_upper]

end
end RiemannGaussian.GaussianFermiModulatedHeight
