/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerCorrectionDeletion

/-!
# Entire multipliers and shifted physical phases of the full Euler correction

Arbitrary fixed entire arithmetic coefficients and real frequency shifts preserve genuine frequency integrability and the original factorial-filter decay. The physical denominator remains the original length. All finite families are covered; no independent floor for the full signed carrier is asserted.
-/

namespace RiemannGaussian.ZetaRieszEulerMultiplier
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter
open ZetaRieszEulerCutoff ZetaRieszEulerMoments ZetaRieszEulerCorrectionDeletion
open ZetaRieszEulerCorrectionEnergy

/-- A fixed entire arithmetic coefficient and a fixed logarithmic
frequency shift act on the full correction before any factorial moment. -/
def weightedKernel (A : ℂ → ℂ) (Q : Finset ℕ) (delta L xi : ℝ) (s : ℂ) : ℂ :=
  A s * (shiftedCorrection Q (zetaPrimeFeature s) (fun p => Real.log p)
    (delta - L) xi / (xi : ℂ) ^ 2)

/-- A shifted physical cutoff costs only the fixed translation in
addition to the original normalized phase allowance. -/
theorem phaseTailCost_shift_div_le (sigma : ℝ) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L)
    (delta : ℝ) :
    phaseTailCost sigma (delta - L) / L ≤ phaseTailCost sigma (a + |delta|) / a := by
  let B : ℝ := (32 + 64 * massCeiling sigma * (2 + Real.exp (8 * massCeiling sigma)) +
    4 * (2 + Real.exp (8 * massCeiling sigma))) * (Real.pi / 2)
  let D : ℝ := 4 * Real.pi * (2 + Real.exp (8 * massCeiling sigma)) / Real.log 16
  have hM : 0 ≤ massCeiling sigma := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he (x : ℝ) : phaseTailCost sigma x = B + D * |x| := by
    unfold phaseTailCost
    dsimp [B, D]
    ring
  have hL0 : 0 < L := ha.trans_le hL
  have htri : |delta - L| ≤ |delta| + L := by
    simpa only [abs_of_pos hL0] using abs_sub delta L
  rw [he, he, abs_of_pos (show 0 < a + |delta| by positivity)]
  apply (div_le_div_iff₀ hL0 ha).mpr
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htri hD) ha.le
  have hb := mul_le_mul_of_nonneg_left hL (show 0 ≤ B + D * |delta| by positivity)
  nlinarith

/-- The fixed coefficient preserves analyticity of every shifted
correction on the closed Cauchy disc. -/
theorem analyticAt_weightedKernel (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (delta L xi : ℝ) :
    AnalyticAt ℂ (weightedKernel A Q delta L xi) s :=
  (hA.analyticAt s).mul (analyticAt_actual_shiftedCorrection_div Q h16 hs (delta - L) xi)

/-- The exact fixed coefficient and translated cutoff remain jointly
measurable, before differentiating or taking a frequency integral. -/
theorem stronglyMeasurable_weightedKernel (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (delta L : ℝ) :
    StronglyMeasurable (fun v : ℝ × ℂ => weightedKernel A Q delta L v.1 v.2) := by
  exact (hA.continuous.stronglyMeasurable.comp_measurable measurable_snd).mul
    (stronglyMeasurable_actual_shiftedCorrection_div Q (delta - L))

/-- An arbitrary fixed entire multiplier costs only its bound on the
same Cauchy circle. All correction phases and factorial orders are retained. -/
theorem norm_weightedMoment_le (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R C : ℝ}
    (hR : 0 < R) (hhalf : 1 / 2 ≤ s.re - R)
    (hC : ∀ z ∈ Metric.sphere s R, ‖A z‖ ≤ C) (delta L xi : ℝ) (n : ℕ) :
    ‖signedTaylorMoment n (weightedKernel A Q delta L xi) s‖ ≤
      (C * phaseMajorant Q (zetaPrimeFeature ((s.re - R : ℝ) : ℂ))
        (fun p => Real.log p) (delta - L) xi) / R ^ n := by
  have hd : DiffContOnCl ℂ (weightedKernel A Q delta L xi) (Metric.ball s R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    intro z hz
    exact (analyticAt_weightedKernel A hA Q h16
      (hhalf.trans (disc_re_lower_bound hz)) delta L xi).differentiableAt.differentiableWithinAt
  apply norm_signedTaylorMoment_le hR hd
  intro z hz
  unfold weightedKernel
  rw [norm_mul]
  apply mul_le_mul (hC z hz)
    (norm_actual_shiftedCorrection_le_majorant Q h16 hhalf
      (disc_re_lower_bound (Metric.sphere_subset_closedBall hz)) (delta - L) xi)
    (norm_nonneg _)
  exact (norm_nonneg _).trans (hC z hz)

/-- Cauchy's exact parametric representation preserves measurability
at every factorial order for the weighted and translated correction. -/
theorem stronglyMeasurable_weightedMoment (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R : ℝ}
    (hR : 0 < R) (hhalf : 1 / 2 ≤ s.re - R) (delta L : ℝ) (n : ℕ) :
    StronglyMeasurable (fun xi : ℝ => signedTaylorMoment n (weightedKernel A Q delta L xi) s) := by
  have he (xi : ℝ) := signedTaylorMoment_eq_circleIntegral hR
    (show DiffContOnCl ℂ (weightedKernel A Q delta L xi) (Metric.ball s R) from by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball s hR.ne']
      intro z hz
      exact (analyticAt_weightedKernel A hA Q h16
        (hhalf.trans (disc_re_lower_bound hz)) delta L xi).differentiableAt.differentiableWithinAt) n
  simp_rw [he]
  exact (stronglyMeasurable_parametric_circle _ (stronglyMeasurable_weightedKernel A hA Q delta L)
    s R n).const_mul _

/-- The weighted factorial moment has a genuine ordinary frequency
integral; no divergent integral is hidden behind the bound. -/
theorem integrable_weightedMoment (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R C : ℝ}
    (hR : 0 < R) (hhalf : 1 / 2 ≤ s.re - R)
    (hC : ∀ z ∈ Metric.sphere s R, ‖A z‖ ≤ C) (delta L : ℝ) (n : ℕ) :
    IntegrableOn (fun xi : ℝ => signedTaylorMoment n (weightedKernel A Q delta L xi) s)
      (Ioi 0) := by
  apply (((integrable_phaseMajorant Q (zetaPrimeFeature ((s.re - R : ℝ) : ℂ))
    (fun p => Real.log p) (delta - L)).const_mul C).div_const (R ^ n)).mono'
  · exact (stronglyMeasurable_weightedMoment A hA Q h16 hR hhalf delta L n).aestronglyMeasurable
  · filter_upwards [] with xi
    exact norm_weightedMoment_le A hA Q h16 hR hhalf hC delta L xi n

/-- Every weighted factorial moment has the literal prime-square tail
allowance, with the fixed arithmetic multiplier and shift kept explicit. -/
theorem integral_norm_weightedMoment_le (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R C : ℝ}
    (hR : 0 < R) (hhalf : 1 / 2 < s.re - R) (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ Metric.sphere s R, ‖A z‖ ≤ C)
    (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) (delta L : ℝ) (n : ℕ) :
    (∫ xi : ℝ in Ioi 0, ‖signedTaylorMoment n (weightedKernel A Q delta L xi) s‖) ≤
      (C * (phaseTailCost (s.re - R) (delta - L) *
        ZetaPrimeNonlinearTail.squareLogTail (s.re - R) K)) / R ^ n := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0,
        (C * phaseMajorant Q (zetaPrimeFeature ((s.re - R : ℝ) : ℂ))
          (fun p => Real.log p) (delta - L) xi) / R ^ n :=
      integral_mono_ae (integrable_weightedMoment A hA Q h16 hR hhalf.le hC delta L n).norm
        (((integrable_phaseMajorant Q _ _ (delta - L)).const_mul C).div_const _)
        (Filter.Eventually.of_forall (fun xi =>
          norm_weightedMoment_le A hA Q h16 hR hhalf.le hC delta L xi n))
    _ ≤ _ := by
      rw [integral_div, integral_const_mul, integral_phaseMajorant]
      apply div_le_div_of_nonneg_right _ (pow_nonneg hR.le n)
      exact mul_le_mul_of_nonneg_left (actual_phaseBudget_le_tail Q h16 hhalf (by simp) K hK
        (delta - L)) hC0

/-- The phase allowance is nonnegative, independently of any claim of
summability at a half-plane boundary. -/
theorem phaseTailCost_nonneg (sigma L : ℝ) : 0 ≤ phaseTailCost sigma L := by
  have hM : 0 ≤ massCeiling sigma := tsum_nonneg fun _ => (Real.exp_pos _).le
  unfold phaseTailCost
  have hlog : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  positivity

/-- A fixed translation costs a finite explicit amount after the
original physical inverse-length normalization. -/
def shiftBudget (sigma a delta : ℝ) (K : ℕ) : ℝ :=
  (phaseTailCost sigma (a + |delta|) / a) * ZetaPrimeNonlinearTail.squareLogTail sigma K

/-- The shifted arithmetic budget is nonnegative in the required domain. -/
theorem shiftBudget_nonneg {sigma a : ℝ} (hsigma : 1 / 2 < sigma) (ha : 0 < a)
    (delta : ℝ) (K : ℕ) : 0 ≤ shiftBudget sigma a delta K :=
  mul_nonneg (div_nonneg (phaseTailCost_nonneg _ _) ha.le)
    (ZetaPrimeNonlinearTail.squareLogTail_nonneg hsigma K)

/-- The complete weighted and translated moment keeps the original
physical denominator, rather than normalizing by its shifted length. -/
def weightedMomentResponse (A : ℂ → ℂ) (Q : Finset ℕ) (s : ℂ) (delta L : ℝ) (n : ℕ) : ℂ :=
  (∫ xi : ℝ in Ioi 0, signedTaylorMoment n (weightedKernel A Q delta L xi) s) / (L : ℂ)

/-- An arbitrary fixed entire coefficient and logarithmic shift have a
cutoff-uniform integrated moment bound at every factorial order. -/
theorem norm_weightedMomentResponse_le (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R C : ℝ}
    (hR : 0 < R) (hhalf : 1 / 2 < s.re - R) (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ Metric.sphere s R, ‖A z‖ ≤ C)
    (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L)
    (delta : ℝ) (n : ℕ) :
    ‖weightedMomentResponse A Q s delta L n‖ ≤
      (C * shiftBudget (s.re - R) a delta K) / R ^ n := by
  have hL0 : 0 < L := ha.trans_le hL
  unfold weightedMomentResponse
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  apply (div_le_div_of_nonneg_right ((norm_integral_le_integral_norm _).trans
    (integral_norm_weightedMoment_le A hA Q h16 hR hhalf hC0 hC K hK delta L n)) hL0.le).trans
  calc
    _ = (C * ((phaseTailCost (s.re - R) (delta - L) / L) *
        ZetaPrimeNonlinearTail.squareLogTail (s.re - R) K)) / R ^ n := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (phaseTailCost_shift_div_le (s.re - R) ha hL delta)
        (ZetaPrimeNonlinearTail.squareLogTail_nonneg hhalf K)) hC0) (pow_nonneg hR.le n)

/-- The entire original factorial filter acts on the weighted shifted
correction, including the logarithmic mark and all polynomial offsets. -/
def weightedFilteredResponse (A : ℂ → ℂ) (Q : Finset ℕ) (P : Polynomial ℂ) (N : ℕ)
    (s : ℂ) (delta L : ℝ) : ℂ :=
  zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * weightedMomentResponse A Q s delta L (k + 1)) N

/-- The original source normalization still gives a geometric allowance
for the full fixed filter after any fixed entire coefficient and phase shift. -/
theorem norm_scaled_weightedFilteredResponse_le (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) (P : Polynomial ℂ) (N : ℕ)
    {s : ℂ} {R C u : ℝ} (hR : 0 < R) (hu : 0 ≤ u) (hhalf : 1 / 2 < s.re - R) (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ Metric.sphere s R, ‖A z‖ ≤ C)
    (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) (delta : ℝ) :
    ‖(u : ℂ) ^ (N + 1) * weightedFilteredResponse A Q P N s delta L‖ ≤
      (C * shiftBudget (s.re - R) a delta K * filterRadiusCost P R) *
        (((N : ℝ) + 1) * (u / R) ^ (N + 1)) := by
  have hb := norm_logMomentFilter_le P (weightedMomentResponse A Q s delta L)
    (mul_nonneg hC0 (shiftBudget_nonneg hhalf ha delta K)) hR
    (fun n => norm_weightedMomentResponse_le A hA Q h16 hR hhalf hC0 hC K hK ha hL delta n) N
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hu _)).trans_eq
  rw [div_pow]
  ring

/-- Every fixed entire coefficient has a finite independent bound on
the closed Cauchy disc, so no unproved arithmetic bound is assumed here. -/
theorem exists_coefficient_circle_bound (A : ℂ → ℂ) (hA : Differentiable ℂ A) (s : ℂ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.sphere s R, ‖A z‖ ≤ C := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall s R).image_of_continuousOn
    hA.continuous.continuousOn).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hB _ ⟨z, Metric.sphere_subset_closedBall hz, rfl⟩).trans (le_max_left _ _)

/-- Every fixed entire multiplier and every fixed frequency shift
preserve the full correction's source-scale decay, uniformly over growing
finite prime selections and unbounded physical cutoff lengths. -/
theorem tendsto_weightedFilteredResponse (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (P : Polynomial ℂ) (Q : ℕ → Finset ℕ) (h16 : ∀ N p, p ∈ Q N → 16 ≤ p)
    (L : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (hL : ∀ N, a ≤ L N) (delta : ℝ)
    {s : ℂ} {R u : ℝ} (hu : 0 ≤ u) (huR : u < R) (hhalf : 1 / 2 < s.re - R) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      weightedFilteredResponse A (Q N) P N s delta (L N)) Filter.atTop (nhds 0) := by
  have hR : 0 < R := lt_of_le_of_lt hu huR
  obtain ⟨C, hC0, hC⟩ := exists_coefficient_circle_bound A hA s R
  have hb (N : ℕ) := norm_scaled_weightedFilteredResponse_le A hA (Q N) (h16 N) P N
    hR hu hhalf hC0 hC 0 (fun _ _ => Nat.zero_le _) ha (hL N) delta
  apply squeeze_zero_norm hb
  have ht := (tendsto_self_mul_const_pow_of_lt_one (div_nonneg hu hR.le)
    ((div_lt_one hR).mpr huR)).comp (Filter.tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, mul_zero] using
    ht.const_mul (C * shiftBudget (s.re - R) a delta 0 * filterRadiusCost P R)

/-- The original Riesz length and Euler center support every fixed entire
coefficient and fixed frequency shift, for all source scales below one. -/
theorem tendsto_physical_weightedFilteredResponse (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (P : Polynomial ℂ) (y delta : ℝ) (Q : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ Q N → 16 ≤ p) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      weightedFilteredResponse A (Q N) P N (3 / 2 + Complex.I * y) delta
        (SquarefreeVaughanLogSource.length u N)) Filter.atTop (nhds 0) := by
  let R : ℝ := (u + 1) / 2
  apply tendsto_weightedFilteredResponse A hA P Q h16 (SquarefreeVaughanLogSource.length u)
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (ZetaRieszFixedCofactor.length_ge_log_four u)
    delta hu.le (show u < R by dsimp [R]; linarith)
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs]
  dsimp [R]
  linarith

/-- Any fixed finite family of entire coefficients and real frequencies
can stay coupled. Its full correction response decays at the original
physical cutoff for every fixed factorial polynomial filter. -/
theorem tendsto_finite_weighted_correction {ι : Type*} (S : Finset ι)
    (A : ι → ℂ → ℂ) (hA : ∀ j ∈ S, Differentiable ℂ (A j)) (delta : ι → ℝ)
    (P : Polynomial ℂ) (y : ℝ) (Q : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ Q N → 16 ≤ p) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ j ∈ S, weightedFilteredResponse (A j) (Q N) P N (3 / 2 + Complex.I * y) (delta j)
        (SquarefreeVaughanLogSource.length u N)) Filter.atTop (nhds 0) := by
  have h := tendsto_finsetSum S (fun j hj =>
    tendsto_physical_weightedFilteredResponse (A j) (hA j hj) P y (delta j) Q h16 hu hu1)
  simpa only [Finset.mul_sum, Finset.sum_const_zero] using h

end
end RiemannGaussian.ZetaRieszEulerMultiplier
