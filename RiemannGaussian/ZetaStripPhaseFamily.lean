/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStripEulerConstraint

/-!
# The full phase-family budget on the sharp Euler strip

The actual multiplicity-weighted cotangent source is controlled for every
nonnegative summable phase family with nonnegative prime kernel and a finite
logarithmic frequency moment. The first budget retains every signed left
mean, the constant channel's exact averaged prime mass, and the full rational
correction. Its explicit upper bound is independent of the retained negative
depth. The complete right prime family is coupled before any estimate.
-/

namespace RiemannGaussian.ZetaStripPhaseFamily
noncomputable section
open Complex ZetaNearOneLocalDisc ZetaNearOneBudgetLimit
open DerivativeOrderComparison ZetaAngularPhaseAllowance ZetaStripEulerConstraint

/-- The exact signed left-family budget after the common right prime
kernel is used, with its original rational masses still retained. -/
def exactBudget (k : ℕ) (M x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  448 * a 0 * localZetaLogHeight 0 +
    (ZetaClippedEulerFamily.totalMean k M t (verticalScale k x) a ω +
      a 0 * ZetaSechPrimeBoundary.mean (rightLine k x) 0 (verticalScale k x) +
      ZetaRegularizedSechMean.rationalTotal (rightLine k x) t (verticalScale k x) a ω) /
      (2 * halfWidth k x)

/-- A completely explicit analytic allowance apart from the original
real-axis zeta value; the right logarithm costs only the constant channel. -/
def budget (k : ℕ) (x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  448 * a 0 * localZetaLogHeight 0 +
    (mass a * (ZetaClippedEulerMean.allowance k t (verticalScale k x) +
      8 * rightLine k x / t ^ 2 +
      2 * RationalVerticalCorrection.profile (rightLine k x) 0 *
        Real.exp (-|t| / |verticalScale k x|)) +
      2 * frequencyCost a ω + a 0 * Real.log ‖riemannZeta (rightLine k x : ℂ)‖) /
      (2 * halfWidth k x)

/-- The actual selected zero keeps its full multiplicity and exact strip
source in the complete finite or countably infinite phase-family inequality.
All channel sums are genuinely summable before their inequalities are added. -/
theorem source_le_exactBudget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x M : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hM : 0 ≤ M)
    (hnear : DirichletPowerParameters.line k < ρ.1.re) :
    a 1 * (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * halfWidth k x)) *
      Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)) ≤
      a 0 / x + exactBudget k M x ρ.1.im a ω := by
  let D (n : ℕ) := (-logDeriv riemannZeta (center x (ω n * ρ.1.im))).re
  let S := (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * halfWidth k x)) *
    Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x))
  have hσ : 1 < 1 + x := by linarith
  have hD : Summable (fun n ↦ a n * D n) :=
    summable_zetaPhase_logDeriv (ω := ω) ha hs hσ ρ.1.im
  have hprime : 0 ≤ ∑' n, a n * D n :=
    zetaPhase_logDeriv_nonneg (ω := ω) ha hs hp hσ ρ.1.im
  have hL := ZetaClippedEulerFamily.summable_means ha hs hω hlog k (by omega) hM
    (verticalScale k x) hscale
  have hR := ZetaRegularizedSechMean.summable_means (ω := ω)
    (tail_nonneg ha) (tail_summable ha hs) (rightLine_gt_one k hx) ρ.1.im (verticalScale k x)
  have hU := (hL.sub hR).div_const (2 * halfWidth k x)
  have hsingle := (hasSum_ite_eq (1 : ℕ) (a 1 * S)).summable
  have hrealSingle :=
    (hasSum_ite_eq (0 : ℕ) (a 0 * (1 / x + 448 * localZetaLogHeight 0))).summable
  have hpoint (n : ℕ) : a n * D n + (if n = 1 then a 1 * S else 0) ≤
      (if n = 0 then a 0 * (1 / x + 448 * localZetaLogHeight 0) else 0) +
        (tail a n * ZetaClippedEulerMean.mean k M (ω n * ρ.1.im) (verticalScale k x) -
          tail a n * ZetaRegularizedSechMean.mean (rightLine k x) (ω n * ρ.1.im)
            (verticalScale k x)) / (2 * halfWidth k x) := by
    by_cases hn0 : n = 0
    · subst n
      have hxsmall : x ≤ 1 / 4 := by
        have hd := ZetaNearOneFullDisc.delta_le_two_sevenths hk
        linarith
      have hreal := mul_le_mul_of_nonneg_left
        (neg_logDeriv_riemannZeta_real_le_local hx hxsmall) (ha 0)
      simpa [D, center, hω0, tail] using hreal
    · by_cases hn1 : n = 1
      · subst n
        have hz := mul_le_mul_of_nonneg_left
          (selected_source_le_means k hk ρ hx hx' ht hM hnear) (ha 1)
        simp only [D, S, hω1, one_mul, tail, if_true, if_false,
          show (1 : ℕ) ≠ 0 by norm_num, zero_add] at hz ⊢
        simp only [div_eq_mul_inv] at hz ⊢
        nlinarith only [hz]
      · have hw := hω n hn0
        have hfreq : 2 ≤ |ω n * ρ.1.im| := by
          rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ ω n)]
          nlinarith
        have hz := mul_le_mul_of_nonneg_left
          (logDeriv_le_means k hk hx hx' hfreq hM) (ha n)
        simp only [D, tail, hn0, hn1, if_false, add_zero, zero_add]
        simp only [div_eq_mul_inv] at hz ⊢
        nlinarith only [hz]
  have hb := (hD.add hsingle).tsum_le_tsum hpoint (hrealSingle.add hU)
  rw [hD.tsum_add hsingle, hrealSingle.tsum_add hU] at hb
  simp only [tsum_ite_eq, tsum_div_const, hL.tsum_sub hR] at hb
  have hr := ZetaRegularizedSechMean.negative_nonconstant_le_exact ha hs hp hω0
    (rightLine_gt_one k hx) ρ.1.im (verticalScale k x)
  have hr' := div_le_div_of_nonneg_right hr (by linarith [halfWidth_pos k hx] :
    0 ≤ 2 * halfWidth k x)
  dsimp only [S] at hb
  unfold exactBudget ZetaClippedEulerFamily.totalMean
  simp only [div_eq_mul_inv] at hb hr' ⊢
  nlinarith only [hb, hr', hprime]

/-- The retained signed arithmetic budget admits the explicit sharp Euler
bound uniformly in every finite negative depth. No right-channel triangle
estimate is introduced. -/
theorem exactBudget_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 1 ≤ k) {x t M : ℝ} (hx : 0 < x) (ht : t ≠ 0)
    (hscale : 1 ≤ scale t) (hM : 0 ≤ M) :
    exactBudget k M x t a ω ≤ budget k x t a ω := by
  have hleft := (ZetaClippedEulerFamily.totalMean_le ha hs hω hlog k hk hM
    (verticalScale k x) hscale).trans
    (ZetaClippedEulerFamily.totalAllowance_le ha hs hω hlog k (verticalScale k x) hscale)
  have hright := mul_le_mul_of_nonneg_left
    (ZetaSechPrimeBoundary.mean_zero_le (rightLine_gt_one k hx) (verticalScale k x)) (ha 0)
  have hrat := ZetaRegularizedSechMean.rationalTotal_le ha hs hω (rightLine_gt_one k hx) ht
    (verticalScale_pos k hx).ne'
  have hsum := add_le_add (add_le_add hleft hright) hrat
  have hdiv := div_le_div_of_nonneg_right hsum (by linarith [halfWidth_pos k hx] :
    0 ≤ 2 * halfWidth k x)
  unfold exactBudget budget
  simp only [div_eq_mul_inv] at hdiv ⊢
  nlinarith only [hdiv]

/-- Every eligible phase family bounds the full actual cotangent source by
the explicit arithmetic allowance, independently of any boundary clipping. -/
theorem source_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : DirichletPowerParameters.line k < ρ.1.re) :
    a 1 * (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * halfWidth k x)) *
      Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)) ≤
      a 0 / x + budget k x ρ.1.im a ω := by
  have h := source_le_exactBudget ha hs hp hω0 hω1 hω hlog k hk ρ ht hscale hx hx'
    (show (0 : ℝ) ≤ 0 by rfl) hnear
  exact h.trans (add_le_add le_rfl (exactBudget_le_budget ha hs hω hlog k (by omega) hx
    (NontrivialZetaZero.im_ne_zero_of_eta_mass ρ) hscale (by rfl)))

/-- The complete positive Dirichlet mass bounds the original logarithm
throughout the genuine Euler half-plane. No zeta value remains to be estimated. -/
theorem log_norm_zeta_le_euler {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ ≤ Real.log (1 + 1 / (s.re - 1)) := by
  have hsum := summable_riemannZetaSummand hs
  have hnorm : ‖riemannZeta s‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
    rw [← tsum_riemannZetaSummand hs]
    calc
      _ ≤ ∑' n : ℕ, ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) n‖ :=
        norm_tsum_le_tsum_norm hsum
      _ = _ := by
        apply tsum_congr
        intro n
        simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
            (by rw [neg_re]; linarith), neg_re]
  exact Real.log_le_log (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs))
    (hnorm.trans (ZetaEulerReciprocalAllowance.pseries_mass_bound hs))

/-- The finite-height strip budget expressed entirely in elementary
functions and the family's mass and logarithmic frequency moment. -/
def elementaryBudget (k : ℕ) (x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  448 * a 0 * localZetaLogHeight 0 +
    (mass a * (ZetaClippedEulerMean.allowance k t (verticalScale k x) +
      8 * rightLine k x / t ^ 2 +
      2 * RationalVerticalCorrection.profile (rightLine k x) 0 *
        Real.exp (-|t| / |verticalScale k x|)) +
      2 * frequencyCost a ω + a 0 * Real.log (1 + 1 / (delta k + 2 * x))) /
      (2 * halfWidth k x)

/-- The elementary replacement charges only the constant channel;
the original real-axis value remains in the sharper upstream budget. -/
theorem budget_le_elementaryBudget {a ω : ℕ → ℝ} (ha : 0 ≤ a 0)
    (k : ℕ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    budget k x t a ω ≤ elementaryBudget k x t a ω := by
  have h := log_norm_zeta_le_euler (s := (rightLine k x : ℂ))
    (by simpa using rightLine_gt_one k hx)
  have hr : (rightLine k x : ℂ).re - 1 = delta k + 2 * x := by
    simp only [Complex.ofReal_re, rightLine]
    ring
  rw [hr] at h
  unfold budget elementaryBudget
  gcongr
  linarith [halfWidth_pos k hx]

/-- An actual selected zero obeys the completely elementary cotangent
budget for every eligible family, with all analytic inputs discharged. -/
theorem source_le_elementaryBudget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : DirichletPowerParameters.line k < ρ.1.re) :
    a 1 * (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * halfWidth k x)) *
      Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)) ≤
      a 0 / x + elementaryBudget k x ρ.1.im a ω :=
  (source_le_budget ha hs hp hω0 hω1 hω hlog k hk ρ ht hscale hx hx' hnear).trans
    (add_le_add le_rfl (budget_le_elementaryBudget (ha 0) k hx ρ.1.im))

/-- Retaining more negative logarithmic depth improves the complete
signed arithmetic budget even after all countably many channels are summed. -/
theorem exactBudget_antitone_depth {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 1 ≤ k) {x t M N : ℝ} (hx : 0 < x)
    (hscale : 1 ≤ scale t) (hM : 0 ≤ M) (hMN : M ≤ N) :
    exactBudget k N x t a ω ≤ exactBudget k M x t a ω := by
  have h := (ZetaClippedEulerFamily.summable_means ha hs hω hlog k hk (hM.trans hMN)
    (verticalScale k x) hscale).tsum_le_tsum (fun n =>
      mul_le_mul_of_nonneg_left
        (ZetaClippedEulerMean.mean_antitone_depth k hk hM hMN (ω n * t) (verticalScale k x))
        (tail_nonneg ha n))
      (ZetaClippedEulerFamily.summable_means ha hs hω hlog k hk hM (verticalScale k x) hscale)
  unfold exactBudget ZetaClippedEulerFamily.totalMean
  gcongr
  linarith [halfWidth_pos k hx]

end
end RiemannGaussian.ZetaStripPhaseFamily
