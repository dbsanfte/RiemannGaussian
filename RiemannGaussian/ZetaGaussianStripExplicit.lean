/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianStripPhaseFamily

/-!
# An explicit full-family Gaussian strip cost

The exact signed Gaussian strip budget is bounded without a phase count or
coefficient search. The rational pole cancellation is used before bounding
the smoothing remainder, leaving only a cubic height tail. Coupling on the
right line charges both Euler prime responses only to the constant channel.
The resulting cost retains the actual half-Gaussian and the selected zero's
Poisson reserve, with all other terms explicitly evaluated or bounded.
-/

namespace RiemannGaussian.ZetaGaussianStripExplicit
noncomputable section
open Complex
open ZetaNearOneLocalDisc ZetaNearOneBudgetLimit ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance ZetaGaussianStripPhaseFamily ZetaGaussianPhaseAllowance
open DerivativeOrderComparison GaussianFermiLaplaceOrder

/-- The original pole cancellation leaves only the cubic Gaussian height
remainder and the complete Archimedean averaging error. -/
theorem extra_le (k : ℕ) (hk : 2 ≤ k) {B x t : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ht : 2 ≤ |t|) :
    (extra B x t).re ≤ 12 * B / |t| ^ 3 + 4 * B / GaussianPolynomialTransport.mass B := by
  have hz : 0 ≤ ((x : ℂ) + I * t).re := by simpa using hx.le
  have hn : |t| ≤ ‖(x : ℂ) + I * t‖ := by simpa using Complex.abs_im_le_norm ((x : ℂ) + I * t)
  have hr := GaussianLaplacePoleRemainder.norm_remainder_le hB hz
    (Complex.ne_zero_of_re_pos (by simpa using hx))
  have hrr : (GaussianLaplacePoleRemainder.remainder B ((x : ℂ) + I * t)).re ≤ 12 * B / |t| ^ 3 := by
    apply (Complex.re_le_norm _).trans (hr.trans ?_)
    gcongr
  have hp := center_pole_nonpos k hk hx hx' ht
  have hc := (Complex.re_le_norm
    (ZetaGaussianCompletionAverage.response B (center x t) - zetaGlobalRegularCorrection (center x t))).trans
      (ZetaGaussianCompletionAverage.norm_response_sub_center_le hB
        (by simp [center]; linarith : 0 < (center x t).re))
  have hm : center x t - 1 = (x : ℂ) + I * t := by unfold center; push_cast; ring
  have hplus : center x t + 1 = ((2 + x : ℝ) : ℂ) + I * t := by unfold center; push_cast; ring
  rw [hm, hplus, Complex.sub_re] at hp
  simp only [extra, GaussianLaplacePoleRemainder.remainder, Complex.add_re, Complex.sub_re] at hrr hc ⊢
  linarith

/-- The cubic pole remainder improves as any nonconstant frequency grows;
one common height allowance suffices for the whole family. -/
theorem extra_mul_le (k : ℕ) (hk : 2 ≤ k) {B x t ω : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ht : 2 ≤ |t|) (hω : 1 ≤ ω) :
    (extra B x (ω * t)).re ≤ 12 * B / |t| ^ 3 + 4 * B / GaussianPolynomialTransport.mass B := by
  have hh : |t| ≤ |ω * t| := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ ω)]
    nlinarith [abs_nonneg t]
  apply (extra_le k hk hB hx hx' (ht.trans hh)).trans
  gcongr

/-- The full signed smoothing correction is bounded by the nonconstant
mass, with no linear-frequency cost. -/
theorem extraTotal_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) (k : ℕ) (hk : 2 ≤ k) {B x t : ℝ}
    (hB : 0 < B) (hx : 0 < x) (hx' : x ≤ delta k / 4) (ht : 2 ≤ |t|) :
    extraTotal B x t a ω ≤ mass a *
      (12 * B / |t| ^ 3 + 4 * B / GaussianPolynomialTransport.mass B) := by
  have h := (summable_extra_re (ω := ω) (tail_nonneg ha) (tail_summable ha hs) hB hx t).tsum_le_tsum
    (fun n => show tail a n * (extra B x (ω n * t)).re ≤ tail a n *
      (12 * B / |t| ^ 3 + 4 * B / GaussianPolynomialTransport.mass B) from by
      by_cases hn : n = 0
      · simp [tail, hn]
      · exact mul_le_mul_of_nonneg_left (extra_mul_le k hk hB hx hx' ht (hω n hn)) (tail_nonneg ha n))
    ((tail_summable ha hs).mul_right _)
  simpa only [extraTotal, mass, tsum_mul_right] using h

/-- The constant Gaussian prime channel has its actual half-Gaussian
upper bound, using the sign of the complete zero mass. -/
theorem ordinarySum_zero_le {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    GaussianFermiPrimeComparison.ordinarySum (1 + x) B 0 ≤
      halfGaussian B x + Real.log (1 + x) / 2 + 4 * B / GaussianPolynomialTransport.mass B := by
  have h := ZetaGaussianSmoothedIdentity.prime_add_zero_mass (by linarith : 1 < 1 + x) hB 0
  have hz : 0 ≤ ∑' ρ : NontrivialZetaZero, ZetaGaussianLaplaceMass.mass B ((1 + x : ℝ) : ℂ) ρ :=
    tsum_nonneg (ZetaGaussianLaplaceMass.mass_nonneg hB (by simp; linarith))
  have hc := (Complex.re_le_norm (ZetaGaussianCompletionAverage.response B ((1 + x : ℝ) : ℂ) -
    zetaGlobalRegularCorrection ((1 + x : ℝ) : ℂ))).trans
      (ZetaGaussianCompletionAverage.norm_response_sub_center_le hB (by simpa using (show 0 < 1 + x by linarith)))
  have hr := re_zetaGlobalRegularCorrection_le_half_log (show 1 ≤ 1 + x by linarith) 0
  have he : ((1 + x : ℝ) : ℂ) - 1 = (x : ℂ) := by push_cast; ring
  simp only [Complex.ofReal_zero, mul_zero, add_zero, he, GaussianComplexHalfMoments.transform_real,
    Complex.ofReal_re, Complex.sub_re, abs_zero] at h hc hr
  linarith

/-- At every order at least three, the original center schedule stays
inside the proved local real-axis Euler allowance. -/
theorem right_shift_le_quarter (k : ℕ) (hk : 3 ≤ k) {x : ℝ} (hx' : x ≤ delta k / 4) :
    delta k + 2 * x ≤ 1 / 4 := by
  have hd := delta_antitone hk
  have hthree : delta 3 = 1 / 6 := by norm_num [delta, DerivativePowerExponents.alpha]
  rw [hthree] at hd
  linarith

/-- The three constant-channel costs are bounded explicitly, retaining
the actual half-Gaussian rather than replacing it by an unsmoothed pole. -/
theorem constantWork_le (k : ℕ) (hk : 3 ≤ k) {B x : ℝ}
    (hB : 0 < B) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    constantWork k B x ≤ halfGaussian B x + Real.log (1 + x) / 2 +
      4 * B / GaussianPolynomialTransport.mass B +
      factor k B x * (1 / (delta k + 2 * x) + 448 * localZetaLogHeight 0) +
      Real.log (1 + 1 / (delta k + 2 * x)) / (2 * halfWidth k x) := by
  have hD := neg_logDeriv_riemannZeta_real_le_local
    (show 0 < delta k + 2 * x by linarith [delta_pos k]) (right_shift_le_quarter k hk hx')
  have he : rightLine k x = 1 + (delta k + 2 * x) := by unfold rightLine; ring
  rw [← he] at hD
  have hmean := (ZetaSechPrimeBoundary.mean_zero_le (rightLine_gt_one k hx) (verticalScale k x)).trans
    (ZetaStripPhaseFamily.log_norm_zeta_le_euler
      (s := (rightLine k x : ℂ)) (by simpa using rightLine_gt_one k hx))
  have hd : (rightLine k x : ℂ).re - 1 = delta k + 2 * x := by simp [rightLine]; ring
  rw [hd] at hmean
  have hf : 0 ≤ factor k B x := by unfold factor; positivity
  have hh := halfWidth_pos k hx
  have hDm := mul_le_mul_of_nonneg_left hD hf
  have hMm := div_le_div_of_nonneg_right hmean (by positivity : 0 ≤ 2 * halfWidth k x)
  unfold constantWork
  linarith [ordinarySum_zero_le hB hx]

/-- The complete explicit Gaussian strip cost for an arbitrary phase
family, retaining the half-Gaussian and only mass and logarithmic frequency costs. -/
def budget (k : ℕ) (B x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  a 0 * (halfGaussian B x + Real.log (1 + x) / 2 +
    4 * B / GaussianPolynomialTransport.mass B +
    factor k B x * (1 / (delta k + 2 * x) + 448 * localZetaLogHeight 0) +
    Real.log (1 + 1 / (delta k + 2 * x)) / (2 * halfWidth k x)) +
  (mass a * (ZetaClippedEulerMean.allowance k t (verticalScale k x) +
    8 * rightLine k x / t ^ 2 + 2 * RationalVerticalCorrection.profile (rightLine k x) 0 *
      Real.exp (-|t| / |verticalScale k x|)) + 2 * frequencyCost a ω) / (2 * halfWidth k x) +
  mass a * (12 * B / |t| ^ 3 + 4 * B / GaussianPolynomialTransport.mass B) +
  factor k B x * (mass a * ((delta k + 2 * x) / t ^ 2 + Real.log (rightLine k x + |t|) / 2) +
    frequencyCost a ω / 2)

/-- Every term of the original signed budget has a proved explicit
allowance. The common right-line Euler cost remains a constant-channel charge. -/
theorem exactBudget_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω0 : ω 0 = 0) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 3 ≤ k) {B x t M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ht : 2 ≤ |t|) (hscale : 1 ≤ scale t) (hM : 0 ≤ M) :
    exactBudget k B M x t a ω ≤ budget k B x t a ω := by
  have ht0 : t ≠ 0 := by intro he; subst t; norm_num at ht
  have hh := halfWidth_pos k hx
  have hf : 0 ≤ factor k B x := by unfold factor; positivity
  have hconstant := mul_le_mul_of_nonneg_left (constantWork_le k hk hB hx hx') (ha 0)
  have hleft := (ZetaClippedEulerFamily.totalMean_le ha hs hω hlog k (by omega) hM
    (verticalScale k x) hscale).trans
      (ZetaClippedEulerFamily.totalAllowance_le ha hs hω hlog k (verticalScale k x) hscale)
  have hrat := ZetaRegularizedSechMean.rationalTotal_le ha hs hω (rightLine_gt_one k hx) ht0
    (verticalScale_pos k hx).ne'
  have hboundary := div_le_div_of_nonneg_right (add_le_add hleft hrat)
    (by positivity : 0 ≤ 2 * halfWidth k x)
  have hextra := extraTotal_le ha hs hω k (by omega) hB hx hx' ht
  have hresponse : (∑' n, tail a n * rightResponse (rightLine k x) (ω n * t)) ≤
      mass a * ((delta k + 2 * x) / t ^ 2 + Real.log (rightLine k x + |t|) / 2) +
        frequencyCost a ω / 2 := by
    have h := tsum_xi_add_arithmetic_le ha hs hω0 hω hlog (rightLine_gt_one k hx) ht0
    rw [tsum_xi_add_arithmetic_eq ha hs hω0 hω hlog (rightLine_gt_one k hx) t] at h
    have he : rightLine k x - 1 = delta k + 2 * x := by unfold rightLine; ring
    rw [he] at h
    linarith
  have hrscaled := mul_le_mul_of_nonneg_left hresponse hf
  unfold exactBudget budget
  simp only [div_eq_mul_inv] at hconstant hboundary hextra hrscaled ⊢
  nlinarith only [hconstant, hboundary, hextra, hrscaled]

/-- The selected actual Gaussian source and all three original prime
responses fit inside the complete explicit cost for every eligible family. -/
theorem source_add_mixedWork_le_budget {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 3 ≤ k) {B x M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (hM : 0 ≤ M) (ρ : NontrivialZetaZero)
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im) :
    a 1 * ZetaGaussianNearCancellation.compensated B (halfWidth k x) (center x ρ.1.im) ρ +
      mixedWork k B x ρ.1.im a ω ≤ budget k B x ρ.1.im a ω :=
  (source_add_mixedWork_le_exactBudget ha hs hω0 hω1 hω hlog k (by omega) hB hx hx' hM ρ hscale).trans
    (exactBudget_le_budget ha hs hω0 hω hlog k hk hB hx hx' ht hscale hM)

/-- Nonnegativity of the common phase kernel discharges all three entire
prime series, leaving the actual selected source and a full explicit cost. -/
theorem source_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 3 ≤ k) {B x : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ρ : NontrivialZetaZero)
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im) :
    a 1 * ZetaGaussianNearCancellation.compensated B (halfWidth k x) (center x ρ.1.im) ρ ≤
      budget k B x ρ.1.im a ω := by
  have h := source_add_mixedWork_le_budget ha hs hω0 hω1 hω hlog k hk hB hx hx' (M := 0)
    (by rfl) ρ ht hscale
  linarith [mixedWork_nonneg ha hs hp k hB hx ρ.1.im]

/-- Every actual zero above the balanced Euler line forces its original
half-Gaussian and shifted Poisson source below the complete general-family
cost. No omitted nearby zero, prime tail or completion allowance remains. -/
theorem gaussian_source_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 3 ≤ k) {B x : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ρ : NontrivialZetaZero)
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im) (hnear : DirichletPowerParameters.line k < ρ.1.re) :
    a 1 * ((analyticZetaZeroMultiplicity ρ : ℝ) *
        (halfGaussian B (1 + x - ρ.1.re) - Real.pi ^ 2 * (1 + x - ρ.1.re) / (8 * halfWidth k x ^ 2)) +
      factor k B x * ((analyticZetaZeroMultiplicity ρ : ℝ) / (1 + x + halfWidth k x - ρ.1.re))) ≤
        budget k B x ρ.1.im a ω := by
  have hd : 1 + x - ρ.1.re < halfWidth k x := by
    unfold halfWidth
    rw [delta_eq_one_sub_line]
    linarith
  have h := mul_le_mul_of_nonneg_left
    (ZetaGaussianStripBound.compensated_at_ordinate_lower (show 1 ≤ 1 + x by linarith)
      (halfWidth_pos k hx) B ρ hd) (ha 1)
  have hu := source_le_budget ha hs hp hω0 hω1 hω hlog k hk hB hx hx' ρ ht hscale
  simpa only [factor, center] using h.trans hu

end
end RiemannGaussian.ZetaGaussianStripExplicit
