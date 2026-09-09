/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeColourArithmetic

/-!
# A global bound for the complete coupled prime-colour moment

The prime-power and mixed-prime responses share an explicit analytic
sum after their common pole at one is removed. Cauchy's estimate gives
a geometric sub-source bound for that sum at every right-half-zero
scale. The exact signed identity and both individual moments are kept:
decay of their sum is not a bound for either contribution separately.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The explicit analytic common response after removing the full
double pole at one. Its value at one is supplied by this genuine formula. -/
def zetaPrimeDivisorRegular (s : ℂ) : ℂ :=
  riemannZeta₁ s - (s - 1) * deriv riemannZeta₁ s -
    (s - 1) * riemannZeta₁ s * zetaProperPrimePowerSeries s

/-- The common response after pole removal is analytic throughout
the larger half-plane, with no exclusion of zeta zeros or the point one. -/
theorem analyticAt_zetaPrimeDivisorRegular {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ zetaPrimeDivisorRegular s := by
  have hz := differentiable_riemannZeta₁.analyticAt (z := s)
  have hc : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) s := analyticAt_id.sub analyticAt_const
  exact (hz.sub (hc.mul hz.deriv)).sub
    ((hc.mul hz).mul (analyticAt_zetaProperPrimePowerSeries hs))

/-- The filled value retains the exact leading coefficient of the
common double pole at one. -/
theorem zetaPrimeDivisorRegular_one : zetaPrimeDivisorRegular 1 = 1 := by
  simp [zetaPrimeDivisorRegular, riemannZeta₁_one]

/-- Away from one, the explicit analytic function is exactly the
original divisor response multiplied by the common quadratic factor. -/
theorem zetaPrimeDivisorRegular_eq {s : ℂ} (hs : s ≠ 1) :
    zetaPrimeDivisorRegular s = (s - 1) ^ 2 * zetaPrimeDivisorResponse s := by
  rw [zetaPrimeDivisorRegular, zetaPrimeDivisorResponse,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
  have h := sub_ne_zero.mpr hs
  field_simp
  ring

/-- The complete signed coupling remains exact after removal of the
common pole; no individual colour is replaced by a norm. -/
theorem zetaPrimeColourRegular_sum {s : ℂ} (hs : s ≠ 1) :
    (s - 1) ^ 2 * (-logDeriv riemannZeta s) +
      (s - 1) ^ 2 * zetaMixedPrimeResponse s = zetaPrimeDivisorRegular s := by
  rw [← mul_add, zetaPrimeColourResponse_sum, zetaPrimeDivisorRegular_eq hs]

/-- The prime-power moment after the common pole at one is removed. -/
def zetaPoleClearedPrimeMoment (N : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment N (fun z ↦ (z - 1) ^ 2 * (-logDeriv riemannZeta z)) s

/-- The mixed-prime moment with the identical pole-removing factor. -/
def zetaPoleClearedMixedMoment (N : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment N (fun z ↦ (z - 1) ^ 2 * zetaMixedPrimeResponse z) s

private theorem analytic_log {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (logDeriv riemannZeta) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact hz.deriv.div hz (riemannZeta_ne_zero_of_one_lt_re hs)

private theorem analytic_mixed {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ zetaMixedPrimeResponse s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact ((analytic_log hs).sub hz.deriv).sub
    (hz.mul (analyticAt_zetaProperPrimePowerSeries (by linarith)))

/-- All signed factorial moments retain the exact arithmetic-colour
sum; analyticity of both actual Euler responses is discharged. -/
theorem zetaPrimeColourMoment_sum (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPoleClearedPrimeMoment N s + zetaPoleClearedMixedMoment N s =
      signedTaylorMoment N zetaPrimeDivisorRegular s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hc : AnalyticAt ℂ (fun z : ℂ ↦ (z - 1) ^ 2) s :=
    (analyticAt_id.sub analyticAt_const).pow 2
  have hp : AnalyticAt ℂ (fun z ↦ (z - 1) ^ 2 * (-logDeriv riemannZeta z)) s :=
    hc.mul (analytic_log hs).neg
  have hm : AnalyticAt ℂ (fun z ↦ (z - 1) ^ 2 * zetaMixedPrimeResponse z) s :=
    hc.mul (analytic_mixed hs)
  have he : (fun z ↦ (z - 1) ^ 2 * (-logDeriv riemannZeta z) +
      (z - 1) ^ 2 * zetaMixedPrimeResponse z) =ᶠ[𝓝 s] zetaPrimeDivisorRegular := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact zetaPrimeColourRegular_sum hz
  rw [zetaPoleClearedPrimeMoment, zetaPoleClearedMixedMoment,
    ← signedTaylorMoment_add N hp hm, signedTaylorMoment_congr N he]

private theorem disc_re_gt_half {s z : ℂ} {R : ℝ}
    (hR : R < s.re - 1 / 2) (hz : z ∈ closedBall s R) : 1 / 2 < z.re := by
  have hn : ‖z - s‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hn)).1
  simp only [Complex.sub_re] at hr
  linarith

/-- An independent Cauchy bound for the common analytic response on
any closed disc strictly within the larger half-plane. It needs no zero data. -/
theorem exists_zetaPrimeDivisorRegular_moment_bound {s : ℂ} {R : ℝ}
    (hR : 0 < R) (hhalf : R < s.re - 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖signedTaylorMoment N zetaPrimeDivisorRegular s‖ ≤ C / R ^ N := by
  have ha : AnalyticOnNhd ℂ zetaPrimeDivisorRegular (closedBall s R) :=
    fun _ hz ↦ analyticAt_zetaPrimeDivisorRegular (disc_re_gt_half hhalf hz)
  obtain ⟨B, hb⟩ := ((isCompact_closedBall s R).image_of_continuousOn ha.continuousOn).isBounded.exists_norm_le
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb _ ⟨s, mem_closedBall_self hR.le, rfl⟩)
  have hd : DiffContOnCl ℂ zetaPrimeDivisorRegular (ball s R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    exact ha.differentiableOn
  refine ⟨B + 1, by positivity, fun N ↦ ?_⟩
  apply norm_signedTaylorMoment_le hR hd
  intro z hz
  exact (hb _ ⟨z, sphere_subset_closedBall hz, rfl⟩).trans (by linarith)

/-- At every hypothetical right-half-zero scale the complete coupled
moment has an independent geometric bound, with the exact complex sum
kept inside the norm. This is not a bound for either colour alone. -/
theorem exists_zetaPrimeColourMoment_geometric_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ N *
        (zetaPoleClearedPrimeMoment N (zetaWronskianMomentCenter rho) +
          zetaPoleClearedMixedMoment N (zetaWronskianMomentCenter rho))‖ ≤ C * q ^ N := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hR : 0 < zetaWronskianMomentRadius rho := hspec.1.trans hspec.2.1
  have hhalf : zetaWronskianMomentRadius rho <
      (zetaWronskianMomentCenter rho).re - 1 / 2 := by
    norm_num [zetaWronskianMomentCenter]
    exact hspec.2.2
  obtain ⟨C, hC, hb⟩ := exists_zetaPrimeDivisorRegular_moment_bound hR hhalf
  let q := ‖zetaWronskianMomentCenter rho - rho.1‖ / zetaWronskianMomentRadius rho
  refine ⟨C, q, hC, div_pos hspec.1 hR, (div_lt_one hR).mpr hspec.2.1, fun N ↦ ?_⟩
  rw [zetaPrimeColourMoment_sum N (by norm_num [zetaWronskianMomentCenter]), norm_mul, norm_pow]
  calc
    _ ≤ ‖zetaWronskianMomentCenter rho - rho.1‖ ^ N *
        (C / zetaWronskianMomentRadius rho ^ N) :=
      mul_le_mul_of_nonneg_left (hb N) (pow_nonneg (norm_nonneg _) _)
    _ = C * q ^ N := by rw [div_pow]; ring

/-- The complete signed coupling vanishes at every right-half-zero
geometric scale, with the preceding uniform geometric error bound. -/
theorem tendsto_zetaPrimeColourMoment (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (zetaWronskianMomentCenter rho - rho.1) ^ N *
      (zetaPoleClearedPrimeMoment N (zetaWronskianMomentCenter rho) +
        zetaPoleClearedMixedMoment N (zetaWronskianMomentCenter rho))) atTop (𝓝 0) := by
  obtain ⟨C, q, _, hq0, hq1, hb⟩ := exists_zetaPrimeColourMoment_geometric_bound rho hrho
  exact squeeze_zero_norm hb (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul C)

/-- The full common arithmetic kernel includes all derivatives of
the quadratic pole-removing factor and retains the complex phase. -/
def zetaPrimeColourMomentKernel (N : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  zetaPrimeFeature s n * ∑ k ∈ Finset.range (N + 1),
    signedTaylorMoment k (fun z : ℂ ↦ (z - 1) ^ 2) s *
      ((Real.log n : ℂ) ^ (N - k) / ((N - k).factorial : ℂ))

private theorem weighted_series_moment {c : ℕ → ℂ} {V : ℂ → ℂ} (hc0 : c 0 = 0)
    (hV : ∀ s : ℂ, 1 < s.re → LSeriesHasSum c s (V s)) {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    HasSum (fun n ↦ c n * zetaPrimeColourMomentKernel N s n)
      (signedTaylorMoment N (fun z ↦ (z - 1) ^ 2 * V z) s) := by
  have hb : LSeries.abscissaOfAbsConv c ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro x hx
    exact (hV x (by simpa using hx)).LSeriesSummable
  have he : (fun z ↦ (z - 1) ^ 2 * V z) =ᶠ[𝓝 s]
      (fun z ↦ (z - 1) ^ 2 * LSeries c z) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    rw [(hV z hz).LSeries_eq]
  rw [signedTaylorMoment_congr N he]
  have h := hasSum_signedTaylorMoment_mul_LSeries c hc0
    (show AnalyticAt ℂ (fun z : ℂ ↦ (z - 1) ^ 2) s from
      (analyticAt_id.sub analyticAt_const).pow 2)
    (lt_of_le_of_lt hb (by exact_mod_cast hs)) N
  simpa only [zetaPrimeColourMomentKernel, mul_assoc] using h

/-- The prime-power contribution uses its literal nonnegative
von-Mangoldt weights and the unchanged complex common kernel. -/
theorem hasSum_zetaPoleClearedPrimeMoment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * zetaPrimeColourMomentKernel N s n)
      (zetaPoleClearedPrimeMoment N s) := by
  apply weighted_series_moment (by simp) _ hs N
  intro z hz
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hz).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz] at h
  simpa only [logDeriv_apply, neg_div] using h

/-- The mixed-prime contribution retains precisely the complementary
nonnegative coefficients and the identical common kernel. -/
theorem hasSum_zetaPoleClearedMixedMoment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (zetaMixedPrimeArithmetic n : ℂ) * zetaPrimeColourMomentKernel N s n)
      (zetaPoleClearedMixedMoment N s) :=
  weighted_series_moment (by simp) (fun _ hz ↦ LSeriesHasSum_zetaMixedPrimeResponse hz) hs N

/-- The independently bounded coupled moment is a genuine convergent
arithmetic sum over the full prime-divisor weight. The two disjoint
colour contributions remain available in the preceding HasSum theorems. -/
theorem hasSum_zetaPrimeColourMoment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (zetaPrimeDivisorCoefficient n : ℂ) * zetaPrimeColourMomentKernel N s n)
      (zetaPoleClearedPrimeMoment N s + zetaPoleClearedMixedMoment N s) := by
  have h := (hasSum_zetaPoleClearedPrimeMoment N hs).add (hasSum_zetaPoleClearedMixedMoment N hs)
  apply h.congr_fun
  intro n
  simp only [zetaPrimeDivisorCoefficient, Complex.ofReal_add, add_mul]

/-- The literal coupled arithmetic sum has the same independent
geometric bound at every hypothetical right-half-zero scale. -/
theorem exists_zetaPrimeColourArithmetic_geometric_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ N *
        ∑' n : ℕ, (zetaPrimeDivisorCoefficient n : ℂ) *
          zetaPrimeColourMomentKernel N (zetaWronskianMomentCenter rho) n‖ ≤ C * q ^ N := by
  obtain ⟨C, q, hC, hq0, hq1, hb⟩ := exists_zetaPrimeColourMoment_geometric_bound rho hrho
  refine ⟨C, q, hC, hq0, hq1, fun N ↦ ?_⟩
  rw [(hasSum_zetaPrimeColourMoment N (by norm_num [zetaWronskianMomentCenter])).tsum_eq]
  exact hb N

/-- The composite response with the identical quadratic factor on
each colour. The selected double-pole source is retained below. -/
def zetaPoleClearedCompositeMoment (N : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment N (fun z ↦ (z - 1) ^ 4 * zetaPositiveCompositeResponse z) s

/-- The complete quadratic moment form keeps every interaction
between the prime-power and mixed-prime moment orders. -/
theorem zetaPoleClearedCompositeMoment_eq_cross (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPoleClearedCompositeMoment N s = ∑ k ∈ Finset.range (N + 1),
      zetaPoleClearedPrimeMoment k s * zetaPoleClearedMixedMoment (N - k) s := by
  have he : (fun z ↦ (z - 1) ^ 4 * zetaPositiveCompositeResponse z) =ᶠ[𝓝 s]
      (fun z ↦ ((z - 1) ^ 2 * (-logDeriv riemannZeta z)) *
        ((z - 1) ^ 2 * zetaMixedPrimeResponse z)) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    rw [zetaPositiveCompositeResponse_eq_prime_mul_mixed (riemannZeta_ne_zero_of_one_lt_re hz)]
    ring
  have hc : AnalyticAt ℂ (fun z : ℂ ↦ (z - 1) ^ 2) s :=
    (analyticAt_id.sub analyticAt_const).pow 2
  have hp : AnalyticAt ℂ (fun z ↦ (z - 1) ^ 2 * (-logDeriv riemannZeta z)) s :=
    hc.mul (analytic_log hs).neg
  have hm : AnalyticAt ℂ (fun z ↦ (z - 1) ^ 2 * zetaMixedPrimeResponse z) s :=
    hc.mul (analytic_mixed hs)
  rw [zetaPoleClearedCompositeMoment, signedTaylorMoment_congr N he, signedTaylorMoment_mul hp hm N]
  rfl

/-- The controlled common moment enters the full quadratic form
without discarding any cross term. The surviving prime quadratic form
is explicit and remains the source-bearing part requiring a new bound. -/
theorem zetaPoleClearedCompositeMoment_eq_common_sub_square (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPoleClearedCompositeMoment N s =
      (∑ k ∈ Finset.range (N + 1), zetaPoleClearedPrimeMoment k s *
        signedTaylorMoment (N - k) zetaPrimeDivisorRegular s) -
      ∑ k ∈ Finset.range (N + 1), zetaPoleClearedPrimeMoment k s *
        zetaPoleClearedPrimeMoment (N - k) s := by
  have he (k : ℕ) : zetaPoleClearedMixedMoment k s =
      signedTaylorMoment k zetaPrimeDivisorRegular s - zetaPoleClearedPrimeMoment k s := by
    linear_combination zetaPrimeColourMoment_sum k hs
  rw [zetaPoleClearedCompositeMoment_eq_cross N hs]
  simp only [he, mul_sub, Finset.sum_sub_distrib]

/-- The entire quadratic moment still equals its genuine convergent
positive-coefficient arithmetic series with the full quartic cofactor
kernel. The kernel itself is complex and is not declared nonnegative. -/
theorem hasSum_zetaPoleClearedCompositeMoment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ) * zetaPrimeFeature s n *
      ∑ k ∈ Finset.range (N + 1), signedTaylorMoment k (fun z : ℂ ↦ (z - 1) ^ 4) s *
        ((Real.log n : ℂ) ^ (N - k) / ((N - k).factorial : ℂ)))
      (zetaPoleClearedCompositeMoment N s) :=
  hasSum_signedTaylorMoment_mul_zetaPositiveCompositeResponse hs
    ((analyticAt_id.sub analyticAt_const).pow 4) N

/-- Keeping the quadratic cross form preserves the exact selected
double-pole coefficient after removing the pole at one. -/
theorem tendsto_zetaPoleClearedCompositeSource (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * ((s - 1) ^ 4 * zetaPositiveCompositeResponse s))
      (𝓝[≠] rho.1) (𝓝 ((rho.1 - 1) ^ 4 * (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2))) := by
  have hc : Tendsto (fun s : ℂ ↦ (s - 1) ^ 4) (𝓝[≠] rho.1) (𝓝 ((rho.1 - 1) ^ 4)) :=
    (((continuous_id.sub continuous_const).pow 4).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h := hc.mul (tendsto_zetaPositiveCompositeResponse_mul_sq rho hrho)
  apply h.congr'
  filter_upwards with s
  ring

/-- Removal of the pole at one does not erase the selected double-pole
source of any nontrivial zero, for its full genuine multiplicity. -/
theorem zetaPoleClearedCompositeSource_ne_zero (rho : NontrivialZetaZero) :
    (rho.1 - 1) ^ 4 * (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2) ≠ 0 := by
  have h1 : rho.1 - 1 ≠ 0 := by
    intro h
    have hr := NontrivialZetaZero.re_lt_one rho
    simp [sub_eq_zero.mp h] at hr
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))
  exact mul_ne_zero (pow_ne_zero 4 h1) (neg_ne_zero.mpr (pow_ne_zero 2 hm))

end

end RiemannGaussian
