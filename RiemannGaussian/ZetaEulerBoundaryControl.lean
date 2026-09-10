/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerPoissonBound
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionHighOrdinateRigidity

/-!
# Logarithmic control of the pole-removed Euler boundary

Removing the actual pole before estimation leaves a continuous signed
logarithmic derivative on the closed Euler half-plane. The full zero mass
bound controls its real part uniformly through `sigma=1`. A compactness
argument covers the bounded-height region, including the filled pole.

This is a dominator for complete phase-family limits. It does not give the
one-sided arithmetic estimate required to contradict a right-half zero.
-/

namespace RiemannGaussian
noncomputable section
open Complex Set Filter
open scoped Topology

/-- The actual pole-removed logarithmic derivative is analytic at every
point of the closed Euler half-plane, including the filled pole at one. -/
theorem analyticAt_logDeriv_riemannZeta₁_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (logDeriv riemannZeta₁) s := by
  have h := differentiable_riemannZeta₁.analyticAt s
  simpa only [logDeriv] using h.deriv.div h (riemannZeta₁_ne_zero_of_one_le_re hs)

/-- The regular completion has a uniform lower bound independent of
height. The shifted digamma representation retains the original sign. -/
theorem re_zetaGlobalRegularCorrection_lower {s : ℂ} (hs : 1 ≤ s.re) :
    -2 ≤ (zetaGlobalRegularCorrection s).re := by
  let z := s / 2 + 1
  have hz : 1 ≤ z.re := by dsimp [z]; simp; linarith
  have hbase := re_digamma_of_one_le_of_re_pos hz
  have hsum := Complex.hasSum_digammaRealDifferenceTerm (by linarith : 0 < z.re) z.im
  have hnonneg : 0 ≤ (Complex.digamma z).re - (Complex.digamma (z.re : ℂ)).re := by
    have he : (z.re : ℂ) + (z.im : ℂ) * I = z := by apply Complex.ext <;> simp
    rw [he] at hsum
    rw [← hsum.tsum_eq]
    exact tsum_nonneg (Complex.digammaRealDifferenceTerm_nonneg (by simpa using (show 0 < z.re by linarith)) _)
  have hpi := Real.log_le_sub_one_of_pos Real.pi_pos
  have heuler := Real.eulerMascheroniConstant_lt_two_thirds
  rw [zetaGlobalRegularCorrection_eq_shifted (by linarith)]
  change -2 ≤ (Complex.digamma z / 2 - Complex.log Real.pi / 2).re
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_four]

/-- The full complex logarithmic identity after the actual zeta pole
has been removed. It also holds at the filled pole `s=1`. -/
theorem logDeriv_riemannXi_eq_regular_add_poleRemoved {s : ℂ} (hs : 0 < s.re)
    (hz : riemannZeta₁ s ≠ 0) :
    logDeriv riemannXi s = zetaGlobalRegularCorrection s + logDeriv riemannZeta₁ s := by
  have hs0 := ne_zero_of_re_pos hs
  have hg := Gammaℝ_ne_zero_of_re_pos hs
  have hd := differentiableAt_Gammaℝ_of_re_pos hs
  have hlocal : riemannXi =ᶠ[𝓝 s]
      (fun z : ℂ => (-1 : ℂ) * ((z * Complex.Gammaℝ z) * riemannZeta₁ z)) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with z hzr
    by_cases hz1 : z = 1
    · subst z
      norm_num [riemannXi_one, riemannZeta₁_one, Complex.Gammaℝ_one]
    · rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hzr hz1,
        riemannZeta₁_eq_sub_one_mul hz1]
      ring
  rw [(logDeriv_congr_nhds hlocal).self_of_nhds,
    logDeriv_const_mul s (-1) (by norm_num),
    logDeriv_mul (f := fun z : ℂ => z * Complex.Gammaℝ z) (g := riemannZeta₁)
      s (mul_ne_zero hs0 hg) hz (((by fun_prop) : DifferentiableAt ℂ (fun z : ℂ => z) s).mul hd)
      differentiable_riemannZeta₁.differentiableAt,
    logDeriv_mul (f := fun z : ℂ => z) (g := Complex.Gammaℝ) s hs0 hg (by fun_prop) hd,
    logDeriv_id', logDeriv_Gammaℝ hs]
  unfold zetaGlobalRegularCorrection
  ring

/-- The complete signed pole-removed arithmetic and actual zero mass
share precisely the regular completion. The pole cancels before either
of its terms is estimated. -/
theorem zeta_poleRemoved_global_real_budget {s : ℂ} (hs : 1 ≤ s.re) :
    (-logDeriv riemannZeta₁ s).re +
      (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand s rho) =
        (zetaGlobalRegularCorrection s).re := by
  rw [tsum_zetaGlobalPoissonSummand hs,
    logDeriv_riemannXi_eq_regular_add_poleRemoved (by linarith)
      (riemannZeta₁_ne_zero_of_one_le_re hs), Complex.add_re, Complex.neg_re]
  ring

/-- The real pole-removed derivative has an explicit logarithmic bound
at large height, uniform on `1 <= sigma <= 3`, including the boundary. -/
theorem abs_re_logDeriv_riemannZeta₁_euler_le {σ t : ℝ}
    (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (ht : 5 ≤ |t|) :
    |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ 326 * zetaEulerLogHeight t := by
  have hs : 1 ≤ (((σ : ℂ) + I * t) : ℂ).re := by simpa using hσ
  have he := zeta_poleRemoved_global_real_budget hs
  have hlow := re_zetaGlobalRegularCorrection_lower hs
  have hu := re_zetaGlobalRegularCorrection_le hs
  have hlog : Real.log (σ + |t|) ≤ zetaEulerLogHeight t := by
    apply Real.log_le_log (by positivity)
    linarith
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_self, add_zero] at hu
  have hZ := tsum_zetaGlobalPoissonSummand_euler_le hσ hσ3 ht
  have hZ0 : 0 ≤ ∑' rho : NontrivialZetaZero,
      zetaGlobalPoissonSummand ((σ : ℂ) + I * t) rho :=
    tsum_nonneg (zetaGlobalPoissonSummand_nonneg hs)
  have hL := three_lt_zetaEulerLogHeight t
  simp only [Complex.neg_re] at he
  rw [abs_le]
  constructor <;> linarith

/-- One absolute constant bounds the real pole-removed logarithmic
derivative at every height and every line in the closed three-strip.
The bounded-height part follows from actual analyticity and nonvanishing,
not from an assumed zero-free compact region. -/
theorem exists_re_logDeriv_riemannZeta₁_euler_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ 3 → ∀ t : ℝ,
      |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ C * zetaEulerLogHeight t := by
  let f : ℝ × ℝ → ℝ := fun p => (logDeriv riemannZeta₁ ((p.1 : ℂ) + I * p.2)).re
  have hf : ContinuousOn f (Icc (1 : ℝ) 3 ×ˢ Icc (-5 : ℝ) 5) := by
    intro p hp
    have hz : 1 ≤ (((p.1 : ℂ) + I * p.2) : ℂ).re := by simpa using hp.1.1
    have hc : ContinuousAt (logDeriv riemannZeta₁) ((p.1 : ℂ) + I * p.2) :=
      (analyticAt_logDeriv_riemannZeta₁_of_one_le_re hz).continuousAt
    have hm : ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ) + I * q.2) p := by fun_prop
    have hcomp : ContinuousAt (fun q : ℝ × ℝ =>
        logDeriv riemannZeta₁ ((q.1 : ℂ) + I * q.2)) p :=
      hc.comp (f := fun q : ℝ × ℝ => (q.1 : ℂ) + I * q.2) hm
    exact (Complex.continuous_re.continuousAt.comp hcomp).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf
  refine ⟨|B| + 326, by positivity, ?_⟩
  intro σ hσ hσ3 t
  have hL := three_lt_zetaEulerLogHeight t
  by_cases ht : 5 ≤ |t|
  · have h := abs_re_logDeriv_riemannZeta₁_euler_le hσ hσ3 ht
    nlinarith [abs_nonneg B]
  · have hmem : (σ, t) ∈ Icc (1 : ℝ) 3 ×ˢ Icc (-5 : ℝ) 5 := by
      have hh := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨⟨hσ, hσ3⟩, ⟨hh.1.le, hh.2.le⟩⟩
    have h := hB (σ, t) hmem
    rw [Real.norm_eq_abs] at h
    change |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ B at h
    have hb := le_abs_self B
    nlinarith [abs_nonneg B]

/-- The real completion admits the same logarithmic dominator on the
closed strip, with no zero-avoidance condition at individual heights. -/
theorem abs_re_zetaGlobalRegularCorrection_euler_le {σ t : ℝ}
    (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) :
    |(zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re| ≤ 2 * zetaEulerLogHeight t := by
  have hs : 1 ≤ (((σ : ℂ) + I * t) : ℂ).re := by simpa using hσ
  have hl := re_zetaGlobalRegularCorrection_lower hs
  have hu := re_zetaGlobalRegularCorrection_le hs
  have hlog : Real.log (σ + |t|) ≤ zetaEulerLogHeight t := by
    apply Real.log_le_log (by positivity)
    linarith
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_self, add_zero] at hu
  rw [abs_le]
  constructor <;> linarith [three_lt_zetaEulerLogHeight t]

/-- A real frequency costs only its logarithmic moment in the Euler
boundary dominator. Zero and arbitrarily small frequencies are included. -/
theorem zetaEulerLogHeight_mul_le_logFrequency (v y : ℝ) :
    zetaEulerLogHeight (v * y) ≤ zetaEulerLogHeight y + Real.log (1 + |v|) := by
  unfold zetaEulerLogHeight
  rw [abs_mul]
  calc
    Real.log (|v| * |y| + 26) ≤ Real.log ((1 + |v|) * (|y| + 26)) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg v, abs_nonneg y])
    _ = Real.log (|y| + 26) + Real.log (1 + |v|) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      ring

/-- All Euler boundary dominators are summable for every nonnegative
summable family with a finite logarithmic frequency moment. -/
theorem summable_zetaPhase_eulerHeight_of_logMoment {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|))) (y : ℝ) :
    Summable (fun n => a n * zetaEulerLogHeight (ω n * y)) := by
  apply ((hs.mul_right (zetaEulerLogHeight y)).add hlog).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (ha n) (by linarith [three_lt_zetaEulerLogHeight (ω n * y)]))]
  have h := mul_le_mul_of_nonneg_left (zetaEulerLogHeight_mul_le_logFrequency (ω n) y) (ha n)
  linarith

end
end RiemannGaussian
