import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Polynomial upper control of the critical zeta endpoint

This module constructs the paired Dirichlet eta series directly on the open
half-plane `0 < re s`. An interval-integral identity supplies a locally
uniform summable majorant, so the series is analytic there. The usual eta
factorization is first proved from the absolutely convergent zeta series on
`1 < re s`, then continued through the upper-right quadrant by the analytic
identity principle.

On the critical line the eta factor stays uniformly away from zero. This
gives a polynomial upper bound for `|zeta (1 / 2 + I * T)|`, hence proves that
the positive part of its logarithm is `o(T)` along the selected quantitative
heights. The terminal theorem feeds this into the checked static-contour
identity and isolates the negative logarithmic part as the only remaining
critical-zeta endpoint obstruction.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The `n`th odd-even pair in the Dirichlet eta series. -/
def pairedEtaCoreSummand (s : ℂ) (n : ℕ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)

/-- The paired Dirichlet eta series, defined as a complex `tsum`. -/
def pairedEtaCore (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaCoreSummand s n

/-- Each eta pair is the integral of the derivative of `x ^ (-s)`. -/
lemma pairedEtaCoreSummand_eq_integral (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      s * ∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
        ((x : ℂ) ^ (-s - 1)) := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hderiv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) x := by
    by_cases hs : s = 0
    · subst s
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ)))
    · convert hasDerivAt_ofReal_cpow_const (x := x)
        (by
          rw [uIcc_of_le (by
            dsimp [a, b]
            exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))] at hx
          exact (ha.trans_le hx.1).ne')
        (neg_ne_zero.mpr hs) using 1
  have hint : IntervalIntegrable
      (fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hp : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (uIcc a b) := by
      apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
      intro x hx
      rw [uIcc_of_le (by
        dsimp [a, b]
        exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))] at hx
      exact Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)
    exact continuousOn_const.mul hp
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hfund
  dsimp [pairedEtaCoreSummand, a, b]
  have hs : (-s) *
        (∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
          (x : ℂ) ^ (-s - 1)) =
      ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
    simpa only using hfund
  calc
    ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) =
        -((-s) *
          (∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
            (x : ℂ) ^ (-s - 1))) := by rw [hs]; ring
    _ = s * ∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
          (x : ℂ) ^ (-s - 1) := by ring

/-- An integrable power majorant for one paired eta summand on `0 < re s`. -/
lemma norm_pairedEtaCoreSummand_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖pairedEtaCoreSummand s n‖ ≤
      ‖s‖ * (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega)
  rw [pairedEtaCoreSummand_eq_integral, norm_mul]
  have hIntegral :
      ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤
        a ^ (-s.re - 1) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
    simp only [neg_re, sub_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos ha hx.1.le (by linarith)
  calc
    ‖s‖ * ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤
        ‖s‖ * (a ^ (-s.re - 1) * |b - a|) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ = ‖s‖ * a ^ (-s.re - 1) := by
      have hba : b - a = 1 := by
        dsimp [a, b]
        push_cast
        ring
      rw [hba, abs_one]
      ring
    _ = ‖s‖ * (a ^ (s.re + 1))⁻¹ := by
      rw [← Real.rpow_neg ha.le]
      congr 2
      ring
    _ = ‖s‖ * (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := rfl

/-- The paired eta series is absolutely summable throughout `0 < re s`. -/
lemma summable_pairedEtaCoreSummand {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaCoreSummand s) := by
  have hfull : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (s.re + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (s.re + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hfull.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  apply Summable.of_norm_bounded (hodd.mul_left ‖s‖)
  exact norm_pairedEtaCoreSummand_le hs

/-- The eta sum is bounded by the `tsum` of its explicit power majorant. -/
lemma norm_pairedEtaCore_le_tsum_majorant
    {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaCore s‖ ≤
      ∑' n : ℕ, ‖s‖ *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by
  unfold pairedEtaCore
  have hsum := summable_pairedEtaCoreSummand hs
  have hnorm : Summable (fun n => ‖pairedEtaCoreSummand s n‖) :=
    summable_norm_iff.mpr hsum
  have hmajor : Summable (fun n : ℕ => ‖s‖ *
      ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) := by
    have hfull : Summable
        (fun m : ℕ => ((((m : ℝ) + 1) ^ (s.re + 1)))⁻¹) := by
      have h :=
        (Real.summable_one_div_nat_add_rpow 1 (s.re + 1)).mpr (by linarith)
      apply h.congr
      intro m
      rw [abs_of_nonneg (by positivity)]
      simp only [one_div]
    have hodd : Summable
        (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) := by
      simpa [Function.comp_def] using
        hfull.comp_injective (i := fun n : ℕ => 2 * n) (by
          intro n m h
          exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
    exact hodd.mul_left ‖s‖
  calc
    ‖∑' n : ℕ, pairedEtaCoreSummand s n‖ ≤
        ∑' n : ℕ, ‖pairedEtaCoreSummand s n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖s‖ *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ :=
      hnorm.tsum_le_tsum (norm_pairedEtaCoreSummand_le hs) hmajor

/-- The paired eta series is complex differentiable on `0 < re s`. -/
lemma differentiableOn_pairedEtaCore :
    DifferentiableOn ℂ pairedEtaCore {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let delta : ℝ := z.re / 2
  let radius : ℝ := z.re / 2
  let K : ℝ := ‖z‖ + radius
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbase : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (delta + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (delta + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hbase.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have hmajor : Summable
      (fun n : ℕ => K *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) :=
    hodd.mul_left K
  have hterms (n : ℕ) :
      DifferentiableOn ℂ (fun w : ℂ => pairedEtaCoreSummand w n)
        (Metric.ball z radius) := by
    unfold pairedEtaCoreSummand
    have hleft : Differentiable ℂ
        (fun w : ℂ => ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-w)) :=
      differentiable_neg.const_cpow (Or.inl (by
        exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)))
    have hright : Differentiable ℂ
        (fun w : ℂ => ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-w)) :=
      differentiable_neg.const_cpow (Or.inl (by
        exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)))
    exact (hleft.sub hright).differentiableOn
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball z radius) :
      ‖pairedEtaCoreSummand w n‖ ≤
        K * ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹ := by
    have hdist : dist w z < radius := by simpa [Metric.mem_ball] using hw
    have hreNorm : |w.re - z.re| ≤ dist w z := by
      calc
        |w.re - z.re| = |(w - z).re| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ = dist w z := by rw [dist_eq_norm]
    have hwre : delta < w.re := by
      dsimp [delta, radius] at *
      linarith [neg_le_abs (w.re - z.re)]
    have hwNorm : ‖w‖ ≤ K := by
      calc
        ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ K := by dsimp [K]; linarith
    have hraw := norm_pairedEtaCoreSummand_le (s := w) (hdelta.trans hwre) n
    let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    have ha1 : 1 ≤ a := by dsimp [a]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hpow : a ^ (-w.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    rw [← Real.rpow_neg ha0, show -(w.re + 1) = -w.re - 1 by ring] at hraw
    rw [← Real.rpow_neg ha0, show -(delta + 1) = -delta - 1 by ring]
    calc
      ‖pairedEtaCoreSummand w n‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
        simpa [a] using hraw
      _ ≤ K * a ^ (-delta - 1) :=
        mul_le_mul hwNorm hpow (Real.rpow_nonneg ha0 _) hK
  have hlocal : DifferentiableOn ℂ pairedEtaCore (Metric.ball z radius) := by
    unfold pairedEtaCore
    exact Complex.differentiableOn_tsum_of_summable_norm
      hmajor hterms Metric.isOpen_ball hbound
  exact (hlocal.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hradius))).differentiableWithinAt

/-- The paired eta series is analytic near every point with positive real part. -/
lemma analyticOnNhd_pairedEtaCore :
    AnalyticOnNhd ℂ pairedEtaCore {s : ℂ | 0 < s.re} :=
  differentiableOn_pairedEtaCore.analyticOnNhd (Complex.isOpen_re_gt 0)

/-- The shifted power series sums to zeta in its absolute-convergence half-plane. -/
lemma hasSum_nat_add_one_cpow_neg_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s))
      (riemannZeta s) := by
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1 : ℝ)) (by norm_num : (1 : ℝ) ∈ Icc 0 1) hs
  have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨1, by norm_num⟩
  rw [hone, HurwitzZeta.hurwitzZeta_zero] at h
  simpa [Complex.cpow_neg] using h

/-- The eta factorization obtained by splitting the zeta series into parity classes. -/
lemma pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)
  have hfull : HasSum f (riemannZeta s) := by
    simpa [f] using hasSum_nat_add_one_cpow_neg_riemannZeta hs
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hfull.summable.comp_injective (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hfull.summable.comp_injective (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel h))
  have hevenSum : HasSum (fun n : ℕ => f (2 * n + 1))
      ((2 : ℂ) ^ (-s) * riemannZeta s) := by
    apply (hfull.mul_left ((2 : ℂ) ^ (-s))).congr_fun
    intro n
    dsimp [f]
    calc
      ((((2 * n + 1 + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) =
          ((((2 : ℝ) * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) ^ (-s) := by
        congr 2
        push_cast
        ring
      _ = (((2 : ℝ) : ℂ)) ^ (-s) *
          (((((n + 1 : ℕ) : ℝ)) : ℂ)) ^ (-s) := by
        simpa only [Complex.ofReal_mul] using
          (Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ))
            (b := ((n + 1 : ℕ) : ℝ)) (by norm_num) (by positivity) (-s))
      _ = (2 : ℂ) ^ (-s) * (((n + 1 : ℕ) : ℂ)) ^ (-s) := by norm_num
  have hsplit :
      (∑' n : ℕ, f (2 * n)) +
          (2 : ℂ) ^ (-s) * riemannZeta s = riemannZeta s := by
    exact (HasSum.even_add_odd hodd.hasSum hevenSum).unique hfull
  have hpaired : pairedEtaCore s =
      (∑' n : ℕ, f (2 * n)) -
        ∑' n : ℕ, f (2 * n + 1) := by
    unfold pairedEtaCore
    rw [← hodd.tsum_sub heven]
    apply tsum_congr
    intro n
    dsimp [pairedEtaCoreSummand, f]
  rw [hpaired, hevenSum.tsum_eq]
  linear_combination hsplit

/-- The connected pole-free quadrant used to continue the eta factorization. -/
def pairedEtaUpperRightDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ 0 < s.im}

/-- The upper-right eta continuation domain is open. -/
lemma isOpen_pairedEtaUpperRightDomain : IsOpen pairedEtaUpperRightDomain := by
  rw [pairedEtaUpperRightDomain, ofPred_and]
  exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_im_gt 0)

/-- The upper-right eta continuation domain is preconnected. -/
lemma isPreconnected_pairedEtaUpperRightDomain :
    IsPreconnected pairedEtaUpperRightDomain := by
  apply Convex.isPreconnected
  rw [pairedEtaUpperRightDomain, ofPred_and]
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

/-- Analytic continuation of the eta factorization into the upper-right quadrant. -/
lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    {s : ℂ} (hsre : 0 < s.re) (hsim : 0 < s.im) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let rhs : ℂ → ℂ := fun w =>
    (1 - 2 * (2 : ℂ) ^ (-w)) * riemannZeta w
  have hlhs : AnalyticOnNhd ℂ pairedEtaCore pairedEtaUpperRightDomain :=
    analyticOnNhd_pairedEtaCore.mono (by
      intro w hw
      exact hw.1)
  have hrhsDiff : DifferentiableOn ℂ rhs pairedEtaUpperRightDomain := by
    intro w hw
    have hfactor : DifferentiableAt ℂ
        (fun u : ℂ => 1 - 2 * (2 : ℂ) ^ (-u)) w := by
      fun_prop (disch := norm_num)
    have hwone : w ≠ 1 := by
      intro h
      subst w
      simpa [pairedEtaUpperRightDomain] using hw.2
    exact hfactor.mul (differentiableAt_riemannZeta hwone) |>.differentiableWithinAt
  have hrhs : AnalyticOnNhd ℂ rhs pairedEtaUpperRightDomain :=
    hrhsDiff.analyticOnNhd isOpen_pairedEtaUpperRightDomain
  let z0 : ℂ := 2 + Complex.I
  have hz0 : z0 ∈ pairedEtaUpperRightDomain := by
    simp [z0, pairedEtaUpperRightDomain]
  have hevent : pairedEtaCore =ᶠ[𝓝 z0] rhs := by
    filter_upwards [
      (Complex.isOpen_re_gt 1).mem_nhds
        (show 1 < z0.re by simp [z0])] with w hw
    exact pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re hw
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs
    isPreconnected_pairedEtaUpperRightDomain hz0 hevent ⟨hsre, hsim⟩


/-- The nonconstant term in the eta factor has norm `sqrt 2` on the critical line. -/
lemma norm_two_mul_two_cpow_neg_critical (T : ℝ) :
    ‖(2 : ℂ) * (2 : ℂ) ^
        (-((((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)))‖ =
      Real.sqrt 2 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I
  change ‖(2 : ℂ) * (2 : ℂ) ^ (-s)‖ = Real.sqrt 2
  have hsre : (-s).re = -(1 / 2 : ℝ) := by simp [s]
  calc
    ‖(2 : ℂ) * (2 : ℂ) ^ (-s)‖ = 2 * ‖(2 : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      norm_num
    _ = 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      congr 1
      change ‖(((2 : ℝ) : ℂ) ^ (-s))‖ = (2 : ℝ) ^ (-(1 / 2 : ℝ))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hsre]
    _ = Real.sqrt 2 := by
      calc
        2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) =
            (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_one]
        _ = (2 : ℝ) ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ = (2 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
        _ = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm

/-- A uniform positive lower bound for the eta factor on the critical line. -/
lemma one_third_le_norm_pairedEtaFactor_critical (T : ℝ) :
    (1 / 3 : ℝ) ≤
      ‖1 - (2 : ℂ) * (2 : ℂ) ^
        (-((((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)))‖ := by
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt 2) ^ 2 = 2 := by
      rw [sq, Real.mul_self_sqrt (by norm_num)]
    nlinarith
  have hreverse := norm_sub_norm_le
    ((2 : ℂ) * (2 : ℂ) ^
      (-((((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)))) (1 : ℂ)
  rw [norm_two_mul_two_cpow_neg_critical, norm_one] at hreverse
  rw [norm_sub_rev]
  linarith

/-- The fixed summable mass majorizing the paired eta series on the critical line. -/
def staticContourCriticalPairedEtaMass : ℝ :=
  ∑' n : ℕ, ((((2 * n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))⁻¹

/-- The critical paired-eta majorant has finite mass. -/
lemma summable_staticContourCriticalPairedEtaMass :
    Summable (fun n : ℕ =>
      ((((2 * n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))⁻¹) := by
  have hfull : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (3 / 2 : ℝ)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).mpr (by norm_num)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  simpa [Function.comp_def] using
    hfull.comp_injective (i := fun n : ℕ => 2 * n) (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)

/-- The critical paired-eta mass contains its initial unit summand. -/
lemma one_le_staticContourCriticalPairedEtaMass :
    1 ≤ staticContourCriticalPairedEtaMass := by
  unfold staticContourCriticalPairedEtaMass
  have hone : ((((2 * 0 + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))⁻¹ = 1 := by norm_num
  rw [← hone]
  apply summable_staticContourCriticalPairedEtaMass.le_tsum 0
  intro n _hn
  positivity

/-- The critical-line eta value grows at most linearly in the endpoint norm. -/
lemma norm_pairedEtaCore_critical_le (T : ℝ) :
    ‖pairedEtaCore (staticContourCriticalEndpoint T)‖ ≤
      ‖staticContourCriticalEndpoint T‖ *
        staticContourCriticalPairedEtaMass := by
  have h := norm_pairedEtaCore_le_tsum_majorant
    (s := staticContourCriticalEndpoint T)
    (by simp [staticContourCriticalEndpoint])
  have hmass := summable_staticContourCriticalPairedEtaMass
  have hre : (staticContourCriticalEndpoint T).re + 1 = (3 / 2 : ℝ) := by
    norm_num [staticContourCriticalEndpoint]
  simp only [hre] at h
  rw [hmass.tsum_mul_left ‖staticContourCriticalEndpoint T‖] at h
  simpa [staticContourCriticalPairedEtaMass] using h

/-- The eta factorization transfers the paired-series bound to critical-line zeta. -/
lemma norm_riemannZeta_criticalLine_le
    {T : ℝ} (hT : 0 < T) :
    ‖riemannZeta (staticContourCriticalEndpoint T)‖ ≤
      3 * ‖staticContourCriticalEndpoint T‖ *
        staticContourCriticalPairedEtaMass := by
  let s : ℂ := staticContourCriticalEndpoint T
  have heta := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := s) (by simp [s, staticContourCriticalEndpoint])
    (by simpa [s, staticContourCriticalEndpoint] using hT)
  have hetaNorm : ‖pairedEtaCore s‖ =
      ‖1 - 2 * (2 : ℂ) ^ (-s)‖ * ‖riemannZeta s‖ := by
    rw [heta, norm_mul]
  have hfactor : (1 / 3 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
    simpa [s, staticContourCriticalEndpoint] using
      one_third_le_norm_pairedEtaFactor_critical T
  have hEtaBound : ‖pairedEtaCore s‖ ≤
      ‖s‖ * staticContourCriticalPairedEtaMass := by
    simpa [s] using norm_pairedEtaCore_critical_le T
  have hzetaNonneg : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  rw [hetaNorm] at hEtaBound
  nlinarith

/-- The critical endpoint norm is at most `T + 1` for nonnegative height. -/
lemma norm_staticContourCriticalEndpoint_le_add_one
    {T : ℝ} (hT : 0 ≤ T) :
    ‖staticContourCriticalEndpoint T‖ ≤ T + 1 := by
  unfold staticContourCriticalEndpoint
  calc
    ‖((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I‖ ≤
        ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) + |T| := by simp
    _ = (1 / 2 : ℝ) + T := by rw [abs_of_nonneg hT]
    _ ≤ T + 1 := by linarith

/-- An unconditional linear upper bound for zeta on the positive critical line. -/
lemma norm_riemannZeta_criticalLine_le_linear
    {T : ℝ} (hT : 0 < T) :
    ‖riemannZeta (staticContourCriticalEndpoint T)‖ ≤
      (3 * staticContourCriticalPairedEtaMass) * (T + 1) := by
  have hmass : 0 ≤ staticContourCriticalPairedEtaMass :=
    zero_le_one.trans one_le_staticContourCriticalPairedEtaMass
  calc
    ‖riemannZeta (staticContourCriticalEndpoint T)‖ ≤
        3 * ‖staticContourCriticalEndpoint T‖ *
          staticContourCriticalPairedEtaMass :=
      norm_riemannZeta_criticalLine_le hT
    _ ≤ 3 * (T + 1) * staticContourCriticalPairedEtaMass := by
      gcongr
      exact norm_staticContourCriticalEndpoint_le_add_one hT.le
    _ = (3 * staticContourCriticalPairedEtaMass) * (T + 1) := by ring

/-- Zeta is nonzero at every selected critical endpoint used by the contour limit. -/
lemma riemannZeta_staticContourCriticalEndpoint_quantitative_ne_zero
    (n : ℕ) :
    riemannZeta
        (staticContourCriticalEndpoint
          (quantitativeSpectralBoundaryTruncation n)) ≠ 0 := by
  let s : ℂ := staticContourCriticalEndpoint
    (quantitativeSpectralBoundaryTruncation n)
  have hsre : 0 < s.re := by
    simp [s, staticContourCriticalEndpoint]
  have hsone : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, staticContourCriticalEndpoint] at hre
  intro hzeta
  apply riemannXi_staticContourCriticalEndpoint_quantitative_ne_zero n
  rw [show staticContourCriticalEndpoint
      (quantitativeSpectralBoundaryTruncation n) = s by rfl,
    riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hsre hsone,
    hzeta, mul_zero]

/-- The positive critical-zeta logarithm is bounded by a logarithmic majorant. -/
lemma criticalZeta_log_positivePart_le_log_linear
    {T : ℝ} (hT : 0 < T) :
    max 0 (Real.log ‖riemannZeta (staticContourCriticalEndpoint T)‖) ≤
      Real.log ((3 * staticContourCriticalPairedEtaMass) * (T + 1)) := by
  let C : ℝ := 3 * staticContourCriticalPairedEtaMass
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [one_le_staticContourCriticalPairedEtaMass]
  have hCpos : 0 < C := one_pos.trans_le hC
  have hTp1 : 1 ≤ T + 1 := by linarith
  have hproduct : 1 ≤ C * (T + 1) :=
    one_le_mul_of_one_le_of_one_le hC hTp1
  have hzero : 0 ≤ Real.log (C * (T + 1)) := Real.log_nonneg hproduct
  have hnorm := norm_riemannZeta_criticalLine_le_linear hT
  by_cases hzeta : riemannZeta (staticContourCriticalEndpoint T) = 0
  · rw [hzeta, norm_zero, Real.log_zero, max_self]
    exact hzero
  · have hnormPos : 0 < ‖riemannZeta (staticContourCriticalEndpoint T)‖ :=
      norm_pos_iff.mpr hzeta
    have hlog : Real.log ‖riemannZeta (staticContourCriticalEndpoint T)‖ ≤
        Real.log (C * (T + 1)) := by
      exact Real.log_le_log hnormPos (by simpa [C] using hnorm)
    exact max_le hzero hlog

/-- The normalized logarithmic majorant vanishes along the quantitative heights. -/
lemma tendsto_log_criticalZeta_linear_majorant_div_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        Real.log
            ((3 * staticContourCriticalPairedEtaMass) *
              (quantitativeSpectralBoundaryTruncation n + 1)) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let C : ℝ := 3 * staticContourCriticalPairedEtaMass
  have hT : Tendsto T atTop atTop :=
    tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hshift : Tendsto (fun n : ℕ => T n + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hT
  have hconst : Tendsto (fun n : ℕ => Real.log C / T n)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hT
  have hlog : Tendsto (fun n : ℕ => Real.log (T n + 1) / T n)
      atTop (nhds 0) := by
    have hraw :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hshift
    refine hraw.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hsum : Tendsto
      (fun n : ℕ => Real.log C / T n + Real.log (T n + 1) / T n)
      atTop (nhds 0) := by
    simpa using hconst.add hlog
  refine hsum.congr' (Eventually.of_forall fun n => ?_)
  have hTpos : 0 < T n :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [one_le_staticContourCriticalPairedEtaMass]
  change Real.log C / T n + Real.log (T n + 1) / T n =
    Real.log (C * (T n + 1)) / T n
  rw [Real.log_mul hCpos.ne' (by linarith : T n + 1 ≠ 0)]
  ring

/-- The positive part of critical-line `log |zeta|`, divided by height, tends to zero. -/
lemma tendsto_criticalZeta_log_positivePart_div_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        max 0
            (Real.log ‖riemannZeta
              (staticContourCriticalEndpoint
                (quantitativeSpectralBoundaryTruncation n))‖) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by
      have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
        (Nat.cast_nonneg n).trans_lt
          (quantitativeSpectralBoundaryTruncation_spec n).1
      exact div_nonneg (le_max_left _ _) hT.le
  · exact Eventually.of_forall fun n => by
      have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
        (Nat.cast_nonneg n).trans_lt
          (quantitativeSpectralBoundaryTruncation_spec n).1
      exact div_le_div_of_nonneg_right
        (criticalZeta_log_positivePart_le_log_linear hT) hT.le
  · exact tendsto_log_criticalZeta_linear_majorant_div_quantitative_zero

/--
The normalized static contour is asymptotic to the negative part of the
critical-line zeta logarithm; its positive part has been eliminated.
-/
lemma tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_criticalZeta_log_negativePart_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ =>
        -Complex.I *
            xiSpectralBlaschkeSignedVerticalRemainderWindow
              (quantitativeSpectralBoundaryTruncation n) 0
              ((v : ℂ) * Complex.I) +
          (((4 / quantitativeSpectralBoundaryTruncation n) *
            max 0 (-Real.log ‖riemannZeta
              (staticContourCriticalEndpoint
                (quantitativeSpectralBoundaryTruncation n))‖) : ℝ) : ℂ))
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let L : ℕ → ℝ := fun n =>
    Real.log ‖riemannZeta (staticContourCriticalEndpoint (T n))‖
  let P : ℕ → ℝ := fun n => max 0 (L n)
  let N : ℕ → ℝ := fun n => max 0 (-L n)
  let V : ℕ → ℂ := fun n =>
    -Complex.I * xiSpectralBlaschkeSignedVerticalRemainderWindow
      (T n) 0 ((v : ℂ) * Complex.I)
  have hbase : Tendsto
      (fun n : ℕ => V n - (((4 / T n) * L n : ℝ) : ℂ))
      atTop (nhds 0) := by
    simpa [T, L, V] using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_sub_criticalZeta_logNorm_main_quantitative_zero
        hv
  have hpositive : Tendsto (fun n : ℕ => P n / T n) atTop (nhds 0) := by
    simpa [P, L, T] using
      tendsto_criticalZeta_log_positivePart_div_quantitative_zero
  have hpositiveComplex : Tendsto
      (fun n : ℕ => (((4 * (P n / T n) : ℝ)) : ℂ))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => 4 * (P n / T n))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpositive
    simpa using hreal.ofReal
  have hcombined : Tendsto
      (fun n : ℕ =>
        V n - (((4 / T n) * L n : ℝ) : ℂ) +
          (((4 * (P n / T n) : ℝ)) : ℂ))
      atTop (nhds 0) := by
    simpa using hbase.add hpositiveComplex
  apply hcombined.congr'
  exact Eventually.of_forall fun n => by
    have hdecomp : P n - N n = L n := by
      simpa [P, N, max_comm] using
        (max_zero_sub_max_neg_zero_eq_self (L n))
    change V n - (((4 / T n) * L n : ℝ) : ℂ) +
        (((4 * (P n / T n) : ℝ)) : ℂ) =
      V n + ((((4 / T n) * N n : ℝ)) : ℂ)
    push_cast
    rw [← hdecomp]
    push_cast
    ring

end


end RiemannGaussian
