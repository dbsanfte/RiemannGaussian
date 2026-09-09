/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Landau continuation for a positive Laplace measure

If a nonnegative random variable has a moment-generating integral on a left
half-line, and its real germ extends analytically along a larger left
half-line, then the integral genuinely converges throughout that larger
half-line. No probability or finite-measure assumption is needed.

The proof retains positivity through the Taylor coefficients. Recentring
an analytic power series at a point just inside a putative finite abscissa
makes its positive moment series summable beyond the abscissa. Tonelli and
the exponential series then prove actual integrability there, a contradiction.

This is the analytic continuation step needed to connect arithmetic Suzuki
positivity to zero exclusion. It supplies no arithmetic positivity estimate.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace RiemannGaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

private theorem integrable_exp_of_summable_moments
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) {b h : ℝ} (hh : 0 ≤ h)
    (hb : b ∈ interior (integrableExpSet X μ))
    (hs : Summable (fun n : ℕ =>
      ((∫ ω, X ω ^ n * Real.exp (b * X ω) ∂μ) / n.factorial) * h ^ n)) :
    Integrable (fun ω => Real.exp ((b + h) * X ω)) μ := by
  let f : ℕ → Ω → ℝ := fun n ω =>
    (X ω ^ n * Real.exp (b * X ω) / n.factorial) * h ^ n
  have hi (n : ℕ) : Integrable (f n) μ :=
    ((integrable_pow_mul_exp_of_mem_interior_integrableExpSet hb n).div_const
      (n.factorial : ℝ)).mul_const (h ^ n)
  have hpos (n : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ f n ω := by
    filter_upwards [hX] with ω hω
    exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg hω n)
      (Real.exp_pos _).le) (Nat.cast_nonneg _)) (pow_nonneg hh n)
  have hint (n : ℕ) : (∫ ω, ‖f n ω‖ ∂μ) =
      ((∫ ω, X ω ^ n * Real.exp (b * X ω) ∂μ) / n.factorial) * h ^ n := by
    calc
      (∫ ω, ‖f n ω‖ ∂μ) = ∫ ω, f n ω ∂μ := integral_congr_ae
        ((hpos n).mono fun _ hp => Real.norm_of_nonneg hp)
      _ = _ := by dsimp [f]; rw [integral_mul_const, integral_div]
  have hsNorm : Summable (fun n => ∫ ω, ‖f n ω‖ ∂μ) := by
    simpa only [hint] using hs
  have his : Integrable (fun ω => ∑' n, f n ω) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hi n).aestronglyMeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ ω, ‖∑' n, f n ω‖ₑ ∂μ) ≤ ∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂μ :=
        lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
      _ = ∑' n, ∫⁻ ω, ‖f n ω‖ₑ ∂μ :=
        lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)
      _ = ∑' n, ENNReal.ofReal (∫ ω, ‖f n ω‖ ∂μ) := by
        apply tsum_congr
        intro n
        exact (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
      _ < ⊤ := hsNorm.tsum_ofReal_lt_top
  convert his using 1
  funext ω
  have he := (NormedSpace.expSeries_div_hasSum_exp (h * X ω)).mul_left
    (Real.exp (b * X ω))
  rw [← Real.exp_eq_exp_ℝ] at he
  have heq : (fun n : ℕ => Real.exp (b * X ω) * ((h * X ω) ^ n / n.factorial)) =
      fun n => f n ω := by
    funext n
    dsimp [f]
    rw [mul_pow]
    ring
  rw [heq] at he
  rw [he.tsum_eq, ← Real.exp_add]
  congr 1
  ring

private theorem isLowerSet_integrableExpSet_of_nonneg
    (hX : AEMeasurable X μ) (hpos : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    IsLowerSet (integrableExpSet X μ) := by
  intro b a hab hb
  exact hb.mono' ((hX.const_mul a).exp.aestronglyMeasurable) (by
    filter_upwards [hpos] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hω))

private theorem not_analyticAt_mgf_abscissa
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) {A : ℝ}
    (hleft : Iio A ⊆ interior (integrableExpSet X μ))
    (hupper : ∀ b ∈ integrableExpSet X μ, b ≤ A)
    {F : ℝ → ℝ} (hF : AnalyticAt ℝ F A)
    (heq : EqOn F (mgf X μ) (Iio A)) : False := by
  obtain ⟨p, R, hp⟩ := hF
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  let d : ℝ := r / 4
  have hd : 0 < d := by dsimp [d]; positivity
  have hdr : 3 * d < r := by dsimp [d]; linarith
  have hn : ‖-d‖₊ < r := by
    change ‖-d‖ < (r : ℝ)
    rw [norm_neg, Real.norm_of_nonneg hd.le]
    linarith
  have hp' := (hp.mono hr0 hrR.le).changeOrigin
    (y := -d) (show (‖-d‖₊ : ℝ≥0∞) < r from ENNReal.coe_lt_coe.mpr hn)
  have hb : A + -d ∈ interior (integrableExpSet X μ) := hleft (by
    change A + -d < A
    linarith)
  have hlocal : F =ᶠ[𝓝 (A + -d)] mgf X μ :=
    Filter.Eventually.mono
      (isOpen_Iio.mem_nhds (show A + -d ∈ Iio A by change A + -d < A; linarith))
      (fun _ hz => heq hz)
  have hcoeff := hp'.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    (hasFPowerSeriesAt_mgf hb) hlocal
  have hmem : 2 * d ∈ Metric.eball (0 : ℝ) ((r : ℝ≥0∞) - ‖-d‖₊) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm,
      ← ENNReal.coe_sub, ENNReal.coe_lt_coe]
    rw [← NNReal.coe_lt_coe, NNReal.coe_sub hn.le]
    change ‖2 * d‖ < (r : ℝ) - ‖-d‖
    rw [norm_neg, Real.norm_of_nonneg hd.le,
      Real.norm_of_nonneg (by positivity : 0 ≤ 2 * d)]
    linarith
  have hs := (hp'.hasSum hmem).summable
  rw [hcoeff] at hs
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  have hi := integrable_exp_of_summable_moments hX
    (show 0 ≤ 2 * d by positivity) hb hs
  have hbound := hupper ((A + -d) + 2 * d) hi
  linarith

/-- A positive moment-generating integral cannot stop converging at a real
point through which its germ has a real-analytic continuation. -/
theorem Iio_subset_interior_integrableExpSet_of_analytic_mgf
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {a c : ℝ} (hsafe : Iio a ⊆ integrableExpSet X μ)
    {F : ℝ → ℝ} (hF : AnalyticOnNhd ℝ F (Iio c))
    (heq : EqOn F (mgf X μ) (Iio a)) :
    Iio c ⊆ interior (integrableExpSet X μ) := by
  have hlower := isLowerSet_integrableExpSet_of_nonneg hXm hX
  have hsub : Iio c ⊆ integrableExpSet X μ := by
    intro t ht
    by_contra hnot
    have hne : (integrableExpSet X μ).Nonempty :=
      ⟨a - 1, hsafe (by change a - 1 < a; linarith)⟩
    have htupper : ∀ b ∈ integrableExpSet X μ, b ≤ t := by
      intro b hb
      by_contra hbt
      exact hnot (hlower (le_of_lt (lt_of_not_ge hbt)) hb)
    have hbounded : BddAbove (integrableExpSet X μ) := ⟨t, htupper⟩
    let A := sSup (integrableExpSet X μ)
    have hAc : A < c := lt_of_le_of_lt (csSup_le hne htupper) ht
    have hleft : Iio A ⊆ interior (integrableExpSet X μ) := by
      intro b hb
      obtain ⟨v, hv, hbv⟩ := (lt_csSup_iff hbounded hne).mp hb
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (isOpen_Iio.mem_nhds hbv) (hlower.Iio_subset hv))
    have hfg : EqOn F (mgf X μ) (Iio A) := by
      have hFa : AnalyticOnNhd ℝ F (Iio A) :=
        hF.mono (Iio_subset_Iio hAc.le)
      have hga : AnalyticOnNhd ℝ (mgf X μ) (Iio A) :=
        analyticOnNhd_mgf.mono hleft
      let b := min a A - 1
      have hbA : b ∈ Iio A := by
        change min a A - 1 < A
        linarith [min_le_right a A]
      have hba : b ∈ Iio a := by
        change min a A - 1 < a
        linarith [min_le_left a A]
      exact hFa.eqOn_of_preconnected_of_eventuallyEq hga
        (convex_Iio A).isPreconnected hbA
        (Filter.Eventually.mono (isOpen_Iio.mem_nhds hba) (fun _ hz => heq hz))
    exact not_analyticAt_mgf_abscissa hX hleft
      (fun b hb => le_csSup hbounded hb) (hF A hAc) hfg
  simpa only [interior_Iio] using interior_mono hsub

end RiemannGaussian
