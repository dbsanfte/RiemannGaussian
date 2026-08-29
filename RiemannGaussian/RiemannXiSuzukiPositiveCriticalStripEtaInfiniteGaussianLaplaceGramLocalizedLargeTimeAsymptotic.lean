import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalizedLargeTimeCoefficient
import Mathlib.Analysis.Calculus.Taylor

/-!
# Actual multiplicity-scale asymptotics of the localized infinite eta Gram

The preceding module identifies the first formally surviving coefficient in
the large-proper-time expansion of the localized eta product kernel.  Here we
justify that expansion analytically.  A global Lagrange-remainder estimate for
`exp(-x)` supplies the polynomial product-measure majorant, while the local
exponential series gives the exact scaled pointwise limit.

These lemmas are deliberately proved before any integral limit is taken.  The
remaining steps in this module apply them to the literal eta product measure,
use the already-proved cancellation of all lower difference moments, and
identify the actual scaled localized Gram limit.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Global factorial Taylor-remainder bound for `exp(-x)` on the nonnegative
half-line.  Unlike a generic complex exponential bound, this estimate has no
`exp(x)` loss and is therefore suitable for the eta product measure. -/
theorem abs_exp_neg_sub_sum_range_succ_le
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x) - ∑ k ∈ Finset.range (n + 1),
        (-x) ^ k / (k.factorial : ℝ)| ≤
      x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rcases hx.eq_or_lt with rfl | hxpos
  · have hsum : (∑ k ∈ Finset.range (n + 1),
        (0 : ℝ) ^ k / (k.factorial : ℝ)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp [zero_pow hk0]
      · simp
    simp only [neg_zero]
    rw [hsum]
    norm_num
  · have hne : (0 : ℝ) ≠ -x := by linarith
    obtain ⟨c, hc, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.exp) (x := -x) (x₀ := 0) (n := n)
        hne Real.contDiff_exp.contDiffOn
    have htaylor :
        taylorWithinEval Real.exp n (uIcc 0 (-x)) 0 (-x) =
          ∑ k ∈ Finset.range (n + 1),
            (-x) ^ k / (k.factorial : ℝ) := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_uIcc hne) Real.contDiff_exp.contDiffAt
        left_mem_uIcc]
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
      simp [smul_eq_mul, div_eq_mul_inv]
      ring
    rw [← htaylor, hrem, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp]
    have hc0 : c < 0 := by
      have hcpair : -x < c ∧ c < 0 := by
        simpa [uIoo, min_eq_right (by linarith : -x ≤ 0),
          max_eq_left (by linarith : -x ≤ 0)] using hc
      exact hcpair.2
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos c), abs_pow,
      sub_zero, abs_neg, abs_of_nonneg hx,
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hexp : Real.exp c ≤ 1 := Real.exp_le_one_iff.mpr hc0.le
    have hpow : 0 ≤ x ^ (n + 1) := pow_nonneg hx _
    have hfac : 0 < ((n + 1).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    apply (div_le_div_iff_of_pos_right hfac).2
    nlinarith [Real.exp_nonneg c]

/-- Dividing the exponential remainder after order `m-1` by `x^m` tends to
the exact coefficient `1/m!` on the punctured neighborhood of zero. -/
theorem tendsto_exp_sub_sum_range_div_pow_nhdsWithin_zero
    (m : ℕ) :
    Tendsto (fun x : ℝ ↦
      (Real.exp x - ∑ k ∈ Finset.range m,
        x ^ k / (k.factorial : ℝ)) / x ^ m)
      (𝓝[({0} : Set ℝ)ᶜ] 0)
      (nhds (1 / (m.factorial : ℝ))) := by
  have hsmallFull :=
    (Real.exp_sub_sum_range_succ_isLittleO_pow m).tendsto_div_nhds_zero
  have hsmall : Tendsto (fun x : ℝ ↦
      (Real.exp x - ∑ k ∈ Finset.range (m + 1),
        x ^ k / (k.factorial : ℝ)) / x ^ m)
      (𝓝[({0} : Set ℝ)ᶜ] 0) (nhds 0) :=
    hsmallFull.mono_left inf_le_left
  have hconst : Tendsto (fun _x : ℝ ↦ 1 / (m.factorial : ℝ))
      (𝓝[({0} : Set ℝ)ᶜ] 0) (nhds (1 / (m.factorial : ℝ))) :=
    tendsto_const_nhds
  have hadd : Tendsto (fun x : ℝ ↦
      1 / (m.factorial : ℝ) +
        (Real.exp x - ∑ k ∈ Finset.range (m + 1),
          x ^ k / (k.factorial : ℝ)) / x ^ m)
      (𝓝[({0} : Set ℝ)ᶜ] 0) (nhds (1 / (m.factorial : ℝ))) := by
    simpa only [add_zero] using hconst.add hsmall
  refine hadd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [Finset.sum_range_succ]
  field_simp [hx0, Nat.factorial_ne_zero]
  ring

/-- Exact pointwise scaling law for the order-`m` remainder after substituting
`x = -a/tau`. -/
theorem tendsto_pow_mul_exp_neg_div_sub_sum_range_atTop
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun tau : ℝ ↦
      tau ^ m *
        (Real.exp (-a / tau) -
          ∑ k ∈ Finset.range m,
            (-a / tau) ^ k / (k.factorial : ℝ)))
      atTop (nhds ((-a) ^ m / (m.factorial : ℝ))) := by
  rcases ha.eq_or_lt with rfl | hapos
  · cases m with
    | zero => simp
    | succ m =>
        have hsum : ∀ tau : ℝ,
            (∑ k ∈ Finset.range (m + 1),
              (-(0 : ℝ) / tau) ^ k / (k.factorial : ℝ)) = 1 := by
          intro tau
          rw [Finset.sum_eq_single 0]
          · simp
          · intro k hk hk0
            simp [zero_pow hk0]
          · simp
        have heq : (fun tau : ℝ ↦
            tau ^ (m + 1) *
              (Real.exp (-(0 : ℝ) / tau) -
                ∑ k ∈ Finset.range (m + 1),
                  (-(0 : ℝ) / tau) ^ k / (k.factorial : ℝ))) =
            fun _tau : ℝ ↦ 0 := by
          funext tau
          rw [hsum tau]
          norm_num
        rw [heq]
        norm_num
  · have hxzero : Tendsto (fun tau : ℝ ↦ -a / tau)
        atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hxne : ∀ᶠ tau : ℝ in atTop,
        -a / tau ∈ ({0} : Set ℝ)ᶜ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero (neg_ne_zero.mpr hapos.ne') htau.ne'
    have hxwithin : Tendsto (fun tau : ℝ ↦ -a / tau)
        atTop (𝓝[({0} : Set ℝ)ᶜ] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxzero, hxne⟩
    have hratio :=
      (tendsto_exp_sub_sum_range_div_pow_nhdsWithin_zero m).comp
        hxwithin
    have hconst : Tendsto (fun _tau : ℝ ↦ (-a) ^ m) atTop
        (nhds ((-a) ^ m)) := tendsto_const_nhds
    have hproduct : Tendsto (fun tau : ℝ ↦
        (-a) ^ m *
          ((Real.exp (-a / tau) -
            ∑ k ∈ Finset.range m,
              (-a / tau) ^ k / (k.factorial : ℝ)) /
            (-a / tau) ^ m))
        atTop (nhds ((-a) ^ m / (m.factorial : ℝ))) := by
      convert hconst.mul hratio using 1 <;>
        simp [div_eq_mul_inv]
    refine hproduct.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    have htau0 : tau ≠ 0 := htau.ne'
    have ha0 : a ≠ 0 := hapos.ne'
    have hx0 : -a / tau ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr ha0) htau0
    have hxpow : tau ^ m * (-a / tau) ^ m = (-a) ^ m := by
      rw [div_pow]
      field_simp [htau0]
    have hxpow0 : (-a / tau) ^ m ≠ 0 := pow_ne_zero m hx0
    have hcancel : (-a / tau) ^ m *
        ((Real.exp (-a / tau) -
          ∑ k ∈ Finset.range m,
            (-a / tau) ^ k / (k.factorial : ℝ)) /
          (-a / tau) ^ m) =
        Real.exp (-a / tau) -
          ∑ k ∈ Finset.range m,
            (-a / tau) ^ k / (k.factorial : ℝ) := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ hxpow0
    calc
      (-a) ^ m *
          ((Real.exp (-a / tau) -
            ∑ k ∈ Finset.range m,
              (-a / tau) ^ k / (k.factorial : ℝ)) /
            (-a / tau) ^ m) =
        (tau ^ m * (-a / tau) ^ m) *
          ((Real.exp (-a / tau) -
            ∑ k ∈ Finset.range m,
              (-a / tau) ^ k / (k.factorial : ℝ)) /
            (-a / tau) ^ m) := by rw [hxpow]
      _ = tau ^ m *
          ((-a / tau) ^ m *
            ((Real.exp (-a / tau) -
              ∑ k ∈ Finset.range m,
                (-a / tau) ^ k / (k.factorial : ℝ)) /
              (-a / tau) ^ m)) := by ring
      _ = _ := by rw [hcancel]

/-- The order-`m` exponentially damped Taylor remainder, already scaled by
`tau^m`, and multiplied by the undamped localized eta kernel at a zero of
multiplicity `m`. -/
def pairedEtaLocalizedGaussianScaledRemainderKernel
    (rho : NontrivialZetaZero) (tau : ℝ) (p : ℝ × ℝ) : ℝ :=
  pairedEtaUndampedLocalizedLaplaceKernel rho.1.re rho.1.im p *
    (tau ^ analyticZetaZeroMultiplicity rho *
      (Real.exp (-((p.1 - p.2) ^ 2 / 4) / tau) -
        ∑ k ∈ Finset.range (analyticZetaZeroMultiplicity rho),
          (-((p.1 - p.2) ^ 2 / 4) / tau) ^ k /
            (k.factorial : ℝ)))

/-- The pointwise limit integrand supplied by the first surviving Gaussian
Taylor coefficient. -/
def pairedEtaLocalizedGaussianLeadingIntegrand
    (rho : NontrivialZetaZero) (p : ℝ × ℝ) : ℝ :=
  pairedEtaUndampedLocalizedLaplaceKernel rho.1.re rho.1.im p *
    ((-((p.1 - p.2) ^ 2 / 4)) ^
        analyticZetaZeroMultiplicity rho /
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ))

/-- Pointwise, the scaled localized Gaussian remainder tends to its exact
order-`m` polynomial integrand. -/
theorem tendsto_pairedEtaLocalizedGaussianScaledRemainderKernel_atTop
    (rho : NontrivialZetaZero) (p : ℝ × ℝ) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p)
      atTop
      (nhds (pairedEtaLocalizedGaussianLeadingIntegrand rho p)) := by
  unfold pairedEtaLocalizedGaussianScaledRemainderKernel
    pairedEtaLocalizedGaussianLeadingIntegrand
  exact tendsto_const_nhds.mul
    (tendsto_pow_mul_exp_neg_div_sub_sum_range_atTop
      (analyticZetaZeroMultiplicity rho)
      (div_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)))

/-- An integrable candidate majorant, expressed through the norm of the
already-integrable complex order-`2m` difference kernel. -/
def pairedEtaLocalizedGaussianScaledRemainderMajorant
    (rho : NontrivialZetaZero) (p : ℝ × ℝ) : ℝ :=
  ((((4 : ℝ) ^ analyticZetaZeroMultiplicity rho) *
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ))⁻¹) *
    ‖pairedEtaComplexLogDifferenceKernel
      (2 * analyticZetaZeroMultiplicity rho)
      rho.1.re rho.1.im p‖

/-- The norm of the complex difference kernel is exactly its polynomial
envelope; the oscillatory exponential has unit norm. -/
theorem norm_pairedEtaComplexLogDifferenceKernel
    (n : ℕ) (sigma gamma : ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaComplexLogDifferenceKernel n sigma gamma p‖ =
      |p.1 - p.2| ^ n * Real.exp (-sigma * (p.1 + p.2)) := by
  unfold pairedEtaComplexLogDifferenceKernel
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]

/-- Exact cancellation of the proper-time scale in the polynomial remainder
majorant. -/
theorem pow_mul_gaussianDifferenceScale_eq
    (m : ℕ) (d tau : ℝ) (htau : 0 < tau) :
    tau ^ m * ((((d ^ 2 / 4) / tau) ^ m) /
        (m.factorial : ℝ)) =
      ((((4 : ℝ) ^ m) * (m.factorial : ℝ))⁻¹) *
        |d| ^ (2 * m) := by
  have htau0 : tau ≠ 0 := htau.ne'
  have hfac0 : (m.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have habs : |d| ^ (2 * m) = (d ^ 2) ^ m := by
    rw [pow_mul, sq_abs]
  rw [habs]
  rw [div_pow, div_pow]
  field_simp [htau0, hfac0]

/-- At every positive proper time, the scaled Taylor-remainder kernel is
dominated by the fixed integrable polynomial majorant. -/
theorem norm_pairedEtaLocalizedGaussianScaledRemainderKernel_le
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    ‖pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p‖ ≤
      pairedEtaLocalizedGaussianScaledRemainderMajorant rho p := by
  let m := analyticZetaZeroMultiplicity rho
  have hmpos : 0 < m := analyticZetaZeroMultiplicity_positive rho
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  let d := p.1 - p.2
  let x := (d ^ 2 / 4) / tau
  have hx : 0 ≤ x := by
    exact div_nonneg (div_nonneg (sq_nonneg d) (by norm_num)) htau.le
  have hrem0 := abs_exp_neg_sub_sum_range_succ_le n hx
  have hrem :
      |Real.exp (-(d ^ 2 / 4) / tau) -
          ∑ k ∈ Finset.range m,
            (-(d ^ 2 / 4) / tau) ^ k / (k.factorial : ℝ)| ≤
        x ^ m / (m.factorial : ℝ) := by
    rw [hn]
    simpa only [x, neg_div] using hrem0
  have hundamped :
      |pairedEtaUndampedLocalizedLaplaceKernel
          rho.1.re rho.1.im p| ≤
        Real.exp (-rho.1.re * (p.1 + p.2)) := by
    unfold pairedEtaUndampedLocalizedLaplaceKernel
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.abs_cos_le_one _)
  have htauPow : 0 ≤ tau ^ m := pow_nonneg htau.le _
  have hscaled :
      tau ^ m *
          |Real.exp (-(d ^ 2 / 4) / tau) -
            ∑ k ∈ Finset.range m,
              (-(d ^ 2 / 4) / tau) ^ k / (k.factorial : ℝ)| ≤
        tau ^ m * (x ^ m / (m.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left hrem htauPow
  calc
    ‖pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p‖ =
        |pairedEtaUndampedLocalizedLaplaceKernel
            rho.1.re rho.1.im p| *
          (tau ^ m *
            |Real.exp (-(d ^ 2 / 4) / tau) -
              ∑ k ∈ Finset.range m,
                (-(d ^ 2 / 4) / tau) ^ k /
                  (k.factorial : ℝ)|) := by
      unfold pairedEtaLocalizedGaussianScaledRemainderKernel
      dsimp only [m, d]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_pos htau]
    _ ≤ Real.exp (-rho.1.re * (p.1 + p.2)) *
          (tau ^ m * (x ^ m / (m.factorial : ℝ))) := by
      exact mul_le_mul hundamped hscaled
        (mul_nonneg htauPow (abs_nonneg _)) (Real.exp_pos _).le
    _ = pairedEtaLocalizedGaussianScaledRemainderMajorant rho p := by
      unfold pairedEtaLocalizedGaussianScaledRemainderMajorant
      rw [norm_pairedEtaComplexLogDifferenceKernel]
      rw [show tau ^ m * (x ^ m / (m.factorial : ℝ)) =
          ((((4 : ℝ) ^ m) * (m.factorial : ℝ))⁻¹) *
            |d| ^ (2 * m) by
        exact pow_mul_gaussianDifferenceScale_eq m d tau htau]
      dsimp only [m, d]
      ring

/-- The polynomial majorant is integrable against the literal eta product
measure. -/
theorem integrable_pairedEtaLocalizedGaussianScaledRemainderMajorant
    (rho : NontrivialZetaZero) :
    Integrable (pairedEtaLocalizedGaussianScaledRemainderMajorant rho)
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  exact (integrable_pairedEtaComplexLogDifferenceKernel
    (2 * analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) rho.1.im).norm.const_mul _

/-- Dominated convergence for the multiplicity-scaled localized eta
remainder kernel. -/
theorem
    tendsto_integral_pairedEtaLocalizedGaussianScaledRemainderKernel_atTop
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      ∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure))
      atTop
      (nhds (∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLeadingIntegrand rho p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure))) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (pairedEtaLocalizedGaussianScaledRemainderMajorant rho)
  · exact Eventually.of_forall fun tau =>
      (show Continuous
        (pairedEtaLocalizedGaussianScaledRemainderKernel rho tau) by
          unfold pairedEtaLocalizedGaussianScaledRemainderKernel
            pairedEtaUndampedLocalizedLaplaceKernel
          fun_prop).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    exact Eventually.of_forall fun p =>
      norm_pairedEtaLocalizedGaussianScaledRemainderKernel_le
        rho htau p
  · exact
      integrable_pairedEtaLocalizedGaussianScaledRemainderMajorant rho
  · exact Eventually.of_forall fun p =>
      tendsto_pairedEtaLocalizedGaussianScaledRemainderKernel_atTop rho p

/-- The integral of the pointwise leading integrand is exactly the explicit
strictly positive coefficient from the formal product-moment calculation. -/
theorem integral_pairedEtaLocalizedGaussianLeadingIntegrand_eq_coefficient
    (rho : NontrivialZetaZero) :
    (∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLeadingIntegrand rho p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  let m := analyticZetaZeroMultiplicity rho
  let c : ℝ := (-1 : ℝ) ^ m /
    (((4 : ℝ) ^ m) * (m.factorial : ℝ))
  have hpoint : pairedEtaLocalizedGaussianLeadingIntegrand rho =
      fun p : ℝ × ℝ ↦ c *
        ((p.1 - p.2) ^ (2 * m) *
          pairedEtaUndampedLocalizedLaplaceKernel
            rho.1.re rho.1.im p) := by
    funext p
    unfold pairedEtaLocalizedGaussianLeadingIntegrand
    dsimp only [m, c]
    have hfac0 : ((analyticZetaZeroMultiplicity rho).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [neg_pow, div_pow, pow_two, pow_mul]
    field_simp [hfac0]
  rw [hpoint, integral_const_mul]
  exact pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_eq rho

/-- The integral of the scaled remainder kernel therefore converges to the
explicit positive leading coefficient. -/
theorem
    tendsto_integral_pairedEtaLocalizedGaussianScaledRemainderKernel_atTop_coefficient
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      ∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure))
      atTop
      (nhds (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)) := by
  simpa [integral_pairedEtaLocalizedGaussianLeadingIntegrand_eq_coefficient]
    using
      tendsto_integral_pairedEtaLocalizedGaussianScaledRemainderKernel_atTop
        rho

/-- Every polynomial difference moment of the undamped localized kernel is
integrable at a positive horizontal tilt. -/
theorem integrable_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel
    (n : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      (p.1 - p.2) ^ n *
        pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p)
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  have hcomplex :=
    (integrable_pairedEtaComplexLogDifferenceKernel
      n hsigma gamma).re
  apply hcomplex.congr
  exact Eventually.of_forall fun p => by
    rw [RCLike.re_eq_complex_re]
    exact pairedEtaComplexLogDifferenceKernel_re n sigma gamma p

/-- The lower Gaussian Taylor polynomial, written as a finite sum of
integrable polynomial eta product kernels. -/
def pairedEtaLocalizedGaussianLowerTaylorKernel
    (rho : NontrivialZetaZero) (tau : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ k ∈ Finset.range (analyticZetaZeroMultiplicity rho),
    (((-1 : ℝ) / (4 * tau)) ^ k / (k.factorial : ℝ)) *
      ((p.1 - p.2) ^ (2 * k) *
        pairedEtaUndampedLocalizedLaplaceKernel
          rho.1.re rho.1.im p)

/-- The lower Taylor kernel is integrable term by term. -/
theorem integrable_pairedEtaLocalizedGaussianLowerTaylorKernel
    (rho : NontrivialZetaZero) (tau : ℝ) :
    Integrable (pairedEtaLocalizedGaussianLowerTaylorKernel rho tau)
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  unfold pairedEtaLocalizedGaussianLowerTaylorKernel
  apply integrable_finsetSum
  intro k hk
  exact (integrable_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel
    (2 * k) (NontrivialZetaZero.zero_lt_re rho) rho.1.im).const_mul _

/-- Every term in the lower Taylor polynomial integrates to zero at a zero of
exact multiplicity `m`. -/
theorem integral_pairedEtaLocalizedGaussianLowerTaylorKernel_eq_zero
    (rho : NontrivialZetaZero) (tau : ℝ) :
    (∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLowerTaylorKernel rho tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) = 0 := by
  unfold pairedEtaLocalizedGaussianLowerTaylorKernel
  rw [integral_finsetSum (Finset.range
    (analyticZetaZeroMultiplicity rho))]
  · apply Finset.sum_eq_zero
    intro k hk
    rw [integral_const_mul,
      integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_eq_zero_of_lt_twice_multiplicity
        rho (by
          have hkm := Finset.mem_range.mp hk
          omega), mul_zero]
  · intro k hk
    exact (integrable_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel
      (2 * k) (NontrivialZetaZero.zero_lt_re rho) rho.1.im).const_mul _

/-- At positive proper time, the finite polynomial kernel is exactly the
undamped kernel times the lower exponential Taylor sum. -/
theorem pairedEtaLocalizedGaussianLowerTaylorKernel_eq
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    pairedEtaLocalizedGaussianLowerTaylorKernel rho tau p =
      pairedEtaUndampedLocalizedLaplaceKernel
          rho.1.re rho.1.im p *
        (∑ k ∈ Finset.range (analyticZetaZeroMultiplicity rho),
          (-((p.1 - p.2) ^ 2 / 4) / tau) ^ k /
            (k.factorial : ℝ)) := by
  unfold pairedEtaLocalizedGaussianLowerTaylorKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have htau0 : tau ≠ 0 := htau.ne'
  have hbase : -((p.1 - p.2) ^ 2 / 4) / tau =
      ((-1 : ℝ) / (4 * tau)) * (p.1 - p.2) ^ 2 := by
    field_simp [htau0]
  rw [hbase, mul_pow, pow_two, pow_mul]
  ring

/-- The damped localized kernel is the undamped kernel times the same scalar
exponential used in the remainder definition. -/
theorem pairedEtaLocalizedGaussianLaplaceKernel_eq_undamped_mul_exp
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    pairedEtaLocalizedGaussianLaplaceKernel
        rho.1.re tau rho.1.im p =
      pairedEtaUndampedLocalizedLaplaceKernel
          rho.1.re rho.1.im p *
        Real.exp (-((p.1 - p.2) ^ 2 / 4) / tau) := by
  unfold pairedEtaLocalizedGaussianLaplaceKernel
    pairedEtaFiniteGaussianLaplaceKernel
    pairedEtaUndampedLocalizedLaplaceKernel
  have htau0 : tau ≠ 0 := htau.ne'
  have hexponent : -(p.1 - p.2) ^ 2 / (4 * tau) =
      -((p.1 - p.2) ^ 2 / 4) / tau := by
    field_simp [htau0]
  rw [hexponent]
  ring

/-- The scaled remainder kernel is exactly `tau^m` times the difference
between the true localized kernel and its lower Taylor polynomial. -/
theorem pairedEtaLocalizedGaussianScaledRemainderKernel_eq_sub
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p =
      tau ^ analyticZetaZeroMultiplicity rho *
        (pairedEtaLocalizedGaussianLaplaceKernel
            rho.1.re tau rho.1.im p -
          pairedEtaLocalizedGaussianLowerTaylorKernel rho tau p) := by
  rw [pairedEtaLocalizedGaussianLowerTaylorKernel_eq rho htau p,
    pairedEtaLocalizedGaussianLaplaceKernel_eq_undamped_mul_exp
      rho htau p]
  unfold pairedEtaLocalizedGaussianScaledRemainderKernel
  ring

/-- After integration, all lower Taylor terms disappear and the scaled
remainder integral is exactly `tau^m` times the true localized kernel
integral. -/
theorem
    integral_pairedEtaLocalizedGaussianScaledRemainderKernel_eq_integral
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau) :
    (∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianScaledRemainderKernel rho tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      tau ^ analyticZetaZeroMultiplicity rho *
        (∫ p : ℝ × ℝ,
          pairedEtaLocalizedGaussianLaplaceKernel
            rho.1.re tau rho.1.im p
          ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) := by
  have hlocalized :=
    integrable_pairedEtaLocalizedGaussianLaplaceKernel
      (NontrivialZetaZero.zero_lt_re rho) htau rho.1.im
  have hlower :=
    integrable_pairedEtaLocalizedGaussianLowerTaylorKernel rho tau
  rw [show pairedEtaLocalizedGaussianScaledRemainderKernel rho tau =
      fun p : ℝ × ℝ ↦
        tau ^ analyticZetaZeroMultiplicity rho *
          (pairedEtaLocalizedGaussianLaplaceKernel
              rho.1.re tau rho.1.im p -
            pairedEtaLocalizedGaussianLowerTaylorKernel rho tau p) by
    funext p
    exact pairedEtaLocalizedGaussianScaledRemainderKernel_eq_sub
      rho htau p]
  rw [integral_const_mul, integral_sub hlocalized hlower,
    integral_pairedEtaLocalizedGaussianLowerTaylorKernel_eq_zero,
    sub_zero]

/-- Removing the explicit Fourier prefactor rewrites the localized norm as
the literal localized eta product-kernel integral. -/
theorem pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_eq_integral
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau) :
    pairedEtaLocalizedGaussianLaplaceNorm
        rho.1.re tau rho.1.im /
        Real.sqrt (Real.pi / tau) =
      ∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLaplaceKernel
          rho.1.re tau rho.1.im p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  rw [pairedEtaLocalizedGaussianLaplaceNorm_eq_gram
    (NontrivialZetaZero.zero_lt_re rho) htau rho.1.im]
  unfold pairedEtaLocalizedGaussianLaplaceGram
  field_simp [(Real.sqrt_pos.2 (div_pos Real.pi_pos htau)).ne']

/-- The formal coefficient is the actual multiplicity-scaled large-time
limit of the normalized localized eta Gaussian norm. -/
theorem
    tendsto_pow_mul_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop_coefficient
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      tau ^ analyticZetaZeroMultiplicity rho *
        (pairedEtaLocalizedGaussianLaplaceNorm
            rho.1.re tau rho.1.im /
          Real.sqrt (Real.pi / tau)))
      atTop
      (nhds (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)) := by
  refine
    (tendsto_integral_pairedEtaLocalizedGaussianScaledRemainderKernel_atTop_coefficient
      rho).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
  rw [integral_pairedEtaLocalizedGaussianScaledRemainderKernel_eq_integral
    rho htau,
    pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_eq_integral rho htau]

/-- The complementary localized norm has the corresponding actual scaled
limit at the reflected zero. -/
theorem
    tendsto_pow_mul_pairedEtaLocalizedGaussianLaplaceNorm_complementary_div_sqrt_atTop_coefficient
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      tau ^ analyticZetaZeroMultiplicity rho *
        (pairedEtaLocalizedGaussianLaplaceNorm
            (1 - rho.1.re) tau rho.1.im /
          Real.sqrt (Real.pi / tau)))
      atTop
      (nhds (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
        (NontrivialZetaZero.conjugatePartner rho))) := by
  have h :=
    tendsto_pow_mul_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop_coefficient
      (NontrivialZetaZero.conjugatePartner rho)
  simpa only [analyticZetaZeroMultiplicity_conjugatePartner,
    NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re, Complex.sub_im,
    Complex.one_im, Complex.conj_im, zero_sub, neg_neg] using h

/-- Consequently, the first actual scaled coefficient of the localized
completion distortion is the difference of the two explicit positive raw
coefficients. -/
theorem
    tendsto_pow_mul_pairedEtaLocalizedCompletionWeightDistortionIntegral_div_sqrt_atTop_coefficient
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      tau ^ analyticZetaZeroMultiplicity rho *
        (pairedEtaLocalizedCompletionWeightDistortionIntegral
            rho.1.re tau rho.1.im /
          Real.sqrt (Real.pi / tau)))
      atTop
      (nhds (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho))) := by
  have hleft :=
    tendsto_pow_mul_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop_coefficient
      rho
  have hright :=
    tendsto_pow_mul_pairedEtaLocalizedGaussianLaplaceNorm_complementary_div_sqrt_atTop_coefficient
      rho
  refine (hleft.sub hright).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
  rw [
    pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_norm_sub_complementary
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho) htau rho.1.im]
  ring

/-- The coefficient-level complementary relation is exactly completion-weight
balance when written with the existing completed Laplace weight. -/
theorem
    pairedEtaCompletedLaplaceWeight_mul_largeTimeLeadingCoefficient_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaCompletedLaplaceWeight
        (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) =
      pairedEtaCompletedLaplaceWeight rho.1 *
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  simpa only [pairedEtaCompletedLaplaceWeight,
    Complex.normSq_eq_norm_sq, norm_mul] using
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner
        rho

/-- Because both coefficients and both completion weights are strictly
positive, equality of the two raw coefficients is equivalent to equality of
the two completion weights. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_eq_conjugatePartner_iff_weight_eq
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho =
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) ↔
      pairedEtaCompletedLaplaceWeight rho.1 =
        pairedEtaCompletedLaplaceWeight
          (NontrivialZetaZero.conjugatePartner rho).1 := by
  have hbalance :=
    pairedEtaCompletedLaplaceWeight_mul_largeTimeLeadingCoefficient_conjugatePartner
      rho
  have hcoefficientPartner :
      0 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
        (NontrivialZetaZero.conjugatePartner rho) :=
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos _
  have hweightPartner :
      0 < pairedEtaCompletedLaplaceWeight
        (NontrivialZetaZero.conjugatePartner rho).1 :=
    pairedEtaCompletedLaplaceWeight_pos
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))
  constructor
  · intro hcoefficient
    rw [hcoefficient] at hbalance
    exact (mul_right_cancel₀ hcoefficientPartner.ne' hbalance).symm
  · intro hweight
    rw [hweight] at hbalance
    exact (mul_left_cancel₀ hweightPartner.ne' hbalance).symm

/-- Thus vanishing of the first actual scaled completion-distortion
coefficient is exactly equality of the explicit completion weights at the
complementary zero pair. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_weight_eq
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) = 0 ↔
      pairedEtaCompletedLaplaceWeight rho.1 =
        pairedEtaCompletedLaplaceWeight
          (NontrivialZetaZero.conjugatePartner rho).1 := by
  rw [sub_eq_zero]
  exact
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_eq_conjugatePartner_iff_weight_eq
      rho

end

end RiemannGaussian
