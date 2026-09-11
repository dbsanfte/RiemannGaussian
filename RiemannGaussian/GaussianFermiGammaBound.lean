/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiSpectralMoment
import RiemannGaussian.GaussianDigammaLogEnvelope
import RiemannGaussian.GaussianFermiPhaseBudget

/-!
# An explicit quarter-logarithm gamma budget for Fermi phase tests

The real digamma logarithmic tangent is integrated against the actual
Gaussian and Fermi probability density. Exact mass and spectral moments
give an explicit error decreasing with the comparison ordinate. The
bound is uniform as the time-Gaussian scale shrinks and feeds directly
into the general selected-zero phase budget.
-/

namespace RiemannGaussian.GaussianFermiGammaBound

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiSpectralWeight GaussianFermiSpectralMoment GaussianDigammaLogEnvelope
open GaussianFermiPrimeFormula GaussianFermiPoleFormula GaussianFermiPhaseBudget
open GaussianFermiZeroTail GaussianFermiMovingAllowance

/-- Exact conversion of the full Gaussian mass to the explicit-formula
normalization. -/
theorem gaussian_mass_ratio {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (Real.pi / ε) / Real.pi = 1 / Real.sqrt (Real.pi * ε) := by
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have he : Real.sqrt ε ≠ 0 := by positivity
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul Real.pi_pos.le]
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

/-- The Gaussian digamma tangent in the exact square-root convention
used by the Fermi average. -/
theorem gaussianDigammaIntegral_le_normalized {ε : ℝ} (hε : 0 < ε) (t y : ℝ) :
    gaussianDigammaIntegral ε (t - y) ≤
      (1 / Real.sqrt (Real.pi * ε)) *
        (Real.log (5 / 4 + |t|) + |y| / (5 / 4 + |t|)) +
      (1 / (Real.pi * ε)) / (5 / 4 + |t|) := by
  calc
    _ ≤ _ := gaussianDigammaIntegral_le_tangent hε t y
    _ = (Real.sqrt (Real.pi / ε) / Real.pi) *
        (Real.log (5 / 4 + |t|) + |y| / (5 / 4 + |t|)) +
        (1 / (Real.pi * ε)) / (5 / 4 + |t|) := by ring
    _ = _ := by rw [gaussian_mass_ratio hε]

/-- The gamma upper bound retains the actual first absolute spectral
moment before its sharp second-moment bound is applied. -/
theorem digammaAverage_le_moment {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (t : ℝ) :
    digammaAverage a b c t ≤ Real.log (5 / 4 + |t|) / 4 +
      ((∫ y : ℝ, density a c y * |y|) / 4 +
        1 / (4 * Real.sqrt (Real.pi * (1 / (4 * b))))) / (5 / 4 + |t|) := by
  let A := 5 / 4 + |t|
  let ε := 1 / (4 * b)
  let T := Real.sqrt (Real.pi * ε)
  have hA : 0 < A := by dsimp [A]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hTsq : T ^ 2 = Real.pi * ε := Real.sq_sqrt (by positivity)
  have hd := integrable_density ha.le hc
  have hm := integrable_density_abs ha hc
  let E : ℝ → ℝ := fun y => (1 / T) *
    (Real.log A * density a c y + (density a c y * |y|) / A) +
    ((1 / (Real.pi * ε)) / A) * density a c y
  have hE : Integrable E :=
    (((hd.const_mul (Real.log A)).add (hm.div_const A)).const_mul (1 / T)).add
      (hd.const_mul ((1 / (Real.pi * ε)) / A))
  have hpoint (y : ℝ) : density a c y * gaussianDigammaIntegral ε (t - y) ≤ E y := by
    calc
      _ ≤ density a c y * ((1 / T) * (Real.log A + |y| / A) +
          (1 / (Real.pi * ε)) / A) :=
        mul_le_mul_of_nonneg_left (gaussianDigammaIntegral_le_normalized hε t y)
          (density_nonneg ha hc y)
      _ = E y := by
        dsimp only [E]
        ring
  have hupper := integral_mono (integrable_density_digamma ha.le hc hε t) hE hpoint
  have hvalue : (∫ y : ℝ, E y) = (1 / T) *
      (Real.log A + (∫ y : ℝ, density a c y * |y|) / A) + (1 / (Real.pi * ε)) / A := by
    have hlog : Integrable (fun y : ℝ => Real.log A * density a c y) := hd.const_mul _
    have habs : Integrable (fun y : ℝ => density a c y * |y| / A) := hm.div_const A
    have hleft : Integrable (fun y : ℝ => (1 / T) *
        (Real.log A * density a c y + density a c y * |y| / A)) :=
      (hlog.add habs).const_mul _
    have hright : Integrable (fun y : ℝ => ((1 / (Real.pi * ε)) / A) * density a c y) :=
      hd.const_mul _
    dsimp only [E]
    rw [integral_add hleft hright, integral_const_mul, integral_add hlog habs,
      integral_const_mul, integral_div, integral_const_mul, integral_density ha.le hc,
      mul_one, mul_one]
  rw [hvalue] at hupper
  have hn : (Real.sqrt (Real.pi / b) / 8) *
      ((1 / T) * (Real.log A + (∫ y : ℝ, density a c y * |y|) / A) +
        (1 / (Real.pi * ε)) / A) = Real.log A / 4 +
      ((∫ y : ℝ, density a c y * |y|) / 4 + 1 / (4 * T)) / A := by
    rw [sqrt_scale_ratio b]
    change (2 * T / 8) * ((1 / T) * (Real.log A +
      (∫ y : ℝ, density a c y * |y|) / A) + (1 / (Real.pi * ε)) / A) = _
    rw [← hTsq]
    field_simp
    ring
  unfold digammaAverage
  exact (mul_le_mul_of_nonneg_left hupper (by positivity)).trans_eq hn

/-- A quantitative gamma bound with exact leading coefficient `1/4`
and explicit dependence on both positive Gaussian scales. -/
theorem digammaAverage_le_quarter_log {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (t : ℝ) :
    digammaAverage a b c t ≤ Real.log (5 / 4 + |t|) / 4 +
      (Real.sqrt (2 * c + a ^ 2 / 4) / 4 +
        1 / (4 * Real.sqrt (Real.pi * (1 / (4 * b))))) / (5 / 4 + |t|) := by
  apply (digammaAverage_le_moment ha hb hc t).trans
  gcongr
  exact integral_density_abs_le_sqrt ha hc

/-- One explicit inverse-height error controls every positive scale
split with total scale at most one, throughout `0<a<=1`. -/
theorem digammaAverage_le_uniform_quarter_log {a b c : ℝ} (ha : 0 < a)
    (hau : a ≤ 1) (hb : 0 < b) (hc : 0 < c) (hscale : b + c ≤ 1) (t : ℝ) :
    digammaAverage a b c t ≤ Real.log (5 / 4 + |t|) / 4 + 7 / (8 * (5 / 4 + |t|)) := by
  have hb1 : b ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hs : Real.sqrt (2 * c + a ^ 2 / 4) ≤ 3 / 2 := by
    have hm : 2 * c + a ^ 2 / 4 ≤ 9 / 4 := by nlinarith
    exact (Real.sqrt_le_sqrt hm).trans_eq (by norm_num)
  have he : (1 / 4 : ℝ) ≤ Real.pi * (1 / (4 * b)) := by
    rw [mul_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have ht : 1 / 2 ≤ Real.sqrt (Real.pi * (1 / (4 * b))) := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.pi * (1 / (4 * b)) by positivity)
    nlinarith [Real.sqrt_nonneg (Real.pi * (1 / (4 * b)))]
  have hi : 1 / (4 * Real.sqrt (Real.pi * (1 / (4 * b)))) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  calc
    _ ≤ _ := digammaAverage_le_quarter_log ha hb hc t
    _ ≤ Real.log (5 / 4 + |t|) / 4 + ((3 / 2 : ℝ) / 4 + 1 / 2) / (5 / 4 + |t|) := by
      gcongr
    _ = _ := by field_simp; ring

/-- At every nonzero ordinate the gamma term has the exact leading
quarter-logarithm and an explicit `19/(16*abs(t))` upper error. -/
theorem digammaAverage_le_log_abs {a b c : ℝ} (ha : 0 < a)
    (hau : a ≤ 1) (hb : 0 < b) (hc : 0 < c) (hscale : b + c ≤ 1)
    {t : ℝ} (ht : t ≠ 0) :
    digammaAverage a b c t ≤ Real.log |t| / 4 + 19 / (16 * |t|) := by
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hlog := Real.log_le_sub_one_of_pos (div_pos
    (by positivity : 0 < (5 / 4 : ℝ) + |t|) htpos)
  rw [Real.log_div (by positivity : (5 / 4 : ℝ) + |t| ≠ 0) htpos.ne'] at hlog
  have he : ((5 / 4 : ℝ) + |t|) / |t| - 1 = 5 / (4 * |t|) := by field_simp; ring
  rw [he] at hlog
  have htail : 7 / (8 * (5 / 4 + |t|)) ≤ 7 / (8 * |t|) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith [abs_nonneg t]
  have h := digammaAverage_le_uniform_quarter_log ha hau hb hc hscale t
  have hsum : (5 / (4 * |t|)) / 4 + 7 / (8 * |t|) = 19 / (16 * |t|) := by ring
  linarith

/-- The actual general phase budget now has a fully explicit gamma
allowance. Only the retained pole and target-zero terms remain to compare;
the prime sign and gamma upper bound are discharged. -/
theorem selected_zero_phase_log_budget {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {H b c t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hscale : zetaPoleReserveZeroMargin H ^ 2 ≤ b + c) (hupper : b + c ≤ 1)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    let σ := 1 - zetaPoleReserveZeroMargin H;
    (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) ≤
      (∑ j ∈ J, w j * (polePair (b + c) σ (ω j * t) +
        (Real.log (5 / 4 + |ω j * t|) - Real.log Real.pi) / 4 +
        7 / (8 * (5 / 4 + |ω j * t|)))) + (∑ j ∈ J, w j) * allowance (b + c) H := by
  let σ := 1 - zetaPoleReserveZeroMargin H
  have hm := zetaPoleReserveZeroMargin_bounds H
  have ha : 0 < 2 * σ - 1 := by dsimp [σ]; linarith [hm.2]
  have hau : 2 * σ - 1 ≤ 1 := by dsimp [σ]; linarith [hm.1]
  apply (selected_zero_phase_budget J w ω hw hphase hH hb hc hscale ht S hS).trans
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  have h := digammaAverage_le_uniform_quarter_log ha hau hb hc hupper (ω j * t)
  change polePair (b + c) σ (ω j * t) - Real.log Real.pi / 4 +
    digammaAverage (2 * σ - 1) b c (ω j * t) ≤ _
  linarith

end
end RiemannGaussian.GaussianFermiGammaBound
