/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripDisc
import RiemannGaussian.ZetaEulerLogProfile
import RiemannGaussian.ZetaSignedPoleControl

/-!
# The complete strip-disc divisor of actual zeta

The original pole-cleared zeta function is represented in the entire
unit disc of strip coordinates. Every finite window retains the exact
complex boundary moment, rational pole correction and complete divisor.
Each actual zero has its original multiplicity, and every unselected
divisor contribution has nonnegative real part. The boundary limit has
not been asserted.
-/

namespace RiemannGaussian.ZetaStripDisc
noncomputable section
open Complex Filter Metric Set MeromorphicOn
open ZetaGaussianLocalizer AnalyticStripDisc AnalyticDiscSignedDerivative AnalyticDiscBoundaryMoment
open AnalyticDiscCanonicalBounds
open scoped Topology

/-- The pole-cleared carrier is analytic at every point in the open
right half-plane, including the filled zeta pole. -/
theorem analyticAt_regularized {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ regularized s :=
  (differentiable_riemannZeta₁.analyticAt s).div (analyticAt_id.add analyticAt_const)
    (add_one_ne_zero hs.le)

/-- The filled zeta pole introduces no spurious zero on the closed
safe half-plane. -/
theorem regularized_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : regularized s ≠ 0 :=
  div_ne_zero (riemannZeta₁_ne_zero_of_one_le_re hs) (add_one_ne_zero (by linarith))

/-- The complete physical strip lies in the analytic domain of the
actual carrier when its left edge is positive. -/
theorem analyticOnNhd_strip {c : ℂ} {η : ℝ} (hleft : η < c.re) :
    AnalyticOnNhd ℂ regularized (strip c η) := by
  intro s hs
  apply analyticAt_regularized
  have h := (abs_lt.mp (show |s.re - c.re| < η from hs)).1
  linarith

/-- The actual zeta carrier in unit-disc strip coordinates. -/
def carrier (c : ℂ) (η : ℝ) : ℂ → ℂ := pullback regularized c η

/-- Every finite coordinate disc has the actual analytic zeta carrier,
with no exclusion of physical zero points. -/
theorem analyticOnNhd_carrier {c : ℂ} {η r : ℝ} (hη : 0 < η) (hleft : η < c.re)
    (hr : r < 1) : AnalyticOnNhd ℂ (carrier c η) (closedBall 0 r) :=
  analyticOnNhd_pullback hη (analyticOnNhd_strip hleft) hr

/-- A safe physical center is nonzero in the represented carrier. -/
theorem carrier_zero_ne {c : ℂ} (hc : 1 < c.re) (η : ℝ) : carrier c η 0 ≠ 0 := by
  rw [carrier, pullback_zero]
  exact regularized_ne_zero hc.le

/-- The precise logarithmic correction undoing the pole removal and
the normalization denominator at a safe center. -/
theorem logDeriv_regularized {c : ℂ} (hc : 1 < c.re) :
    logDeriv regularized c = logDeriv riemannZeta c + 1 / (c - 1) - 1 / (c + 1) := by
  have hn := riemannZeta₁_ne_zero_of_one_le_re hc.le
  have hd := add_one_ne_zero (s := c) (by linarith)
  have hc1 : c ≠ 1 := by intro h; rw [h] at hc; norm_num at hc
  have hp := neg_logDeriv_riemannZeta_eq_pole_sub hc1 (riemannZeta_ne_zero_of_one_le_re hc.le)
  have h := logDeriv_div (f := riemannZeta₁) (g := fun z : ℂ => z + 1) c hn hd
    (differentiable_riemannZeta₁ c) (by fun_prop)
  change logDeriv regularized c = _ at h
  rw [h]
  have he : logDeriv (fun z : ℂ => z + 1) c = 1 / (c + 1) := by
    simp [logDeriv_apply]
  rw [he]
  linear_combination hp

/-- The physical carrier retains the full multiplicity of every
nontrivial zeta zero after both rational normalizations. -/
theorem meromorphicOrderAt_regularized_zero (ρ : NontrivialZetaZero) :
    meromorphicOrderAt regularized ρ.1 = (analyticZetaZeroMultiplicity ρ : ℤ) := by
  have ha : AnalyticAt ℂ (fun s : ℂ => s + 1) ρ.1 := by fun_prop
  have hn : ρ.1 + 1 ≠ 0 := add_one_ne_zero (NontrivialZetaZero.zero_lt_re ρ).le
  have ho := ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
  change meromorphicOrderAt (riemannZeta₁ / fun s : ℂ => s + 1) ρ.1 = _
  rw [meromorphicOrderAt_div (differentiable_riemannZeta₁.analyticAt ρ.1).meromorphicAt
    ha.meromorphicAt, meromorphicOrderAt_riemannZeta₁_nontrivialZero, ho, sub_zero]

/-- The exact disc coordinate of a physical point, retaining height
and real displacement through the complex tangent. -/
def coordinate (c : ℂ) (η : ℝ) (z : ℂ) : ℂ := Complex.tan (Real.pi * (z - c) / (4 * η))

/-- Every enclosed actual zero has its original analytic multiplicity
in the complete finite coordinate divisor. -/
theorem divisor_at_zero (ρ : NontrivialZetaZero) {c : ℂ} {η r : ℝ}
    (hη : 0 < η) (hleft : η < c.re) (hr1 : r < 1) (hρ : ρ.1 ∈ strip c η)
    (hmem : coordinate c η ρ.1 ∈ ball 0 r) :
    divisor (carrier c η) (ball 0 r) (coordinate c η ρ.1) =
      (analyticZetaZeroMultiplicity ρ : ℤ) := by
  rw [carrier, divisor_pullback hη (analyticOnNhd_strip hleft) hr1 hmem]
  rw [coordinate, AnalyticStripMap.map_tan c hη hρ,
    (analyticOnNhd_strip hleft).meromorphicOn.divisor_apply hρ,
    meromorphicOrderAt_regularized_zero]
  simp

/-- The complete finite complex zero contribution, before projection
or selection of any individual zero. -/
def source (c : ℂ) (η r : ℝ) : ℂ :=
  ∑ᶠ w, divisor (carrier c η) (ball 0 r) w • kernel r w

/-- The full real projection still contains every multiplicity-weighted
coupled zero term. -/
theorem source_re {c : ℂ} {η r : ℝ} (hη : 0 < η) (hleft : η < c.re) (hr1 : r < 1) :
    (source c η r).re = ∑ᶠ w, (divisor (carrier c η) (ball 0 r) w : ℝ) * (kernel r w).re := by
  have hf := analyticOnNhd_carrier hη hleft hr1
  have hd := hf.meromorphicOn.divisor_ball_support_finite
  have hs : (fun w => divisor (carrier c η) (ball 0 r) w • kernel r w).HasFiniteSupport :=
    hd.subset (by intro w hw hdw; exact hw (by simp [hdw]))
  change Complex.reAddGroupHom (∑ᶠ w, divisor (carrier c η) (ball 0 r) w • kernel r w) = _
  rw [map_finsum Complex.reAddGroupHom hs]
  apply finsum_congr
  intro w
  simp [zsmul_eq_mul]

/-- Every nonzero term of the complete actual divisor lies left of
the disc center, by the proved sign-preserving strip map. -/
theorem divisor_re_neg {c : ℂ} {η r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hleft : η < c.re) (hr1 : r < 1) {w : ℂ}
    (hw : divisor (carrier c η) (ball 0 r) w ≠ 0) : w.re < 0 := by
  have hf := analyticOnNhd_carrier hη hleft hr1
  have hzero := zero_of_divisor_ne_zero hf hw
  have hm := (divisor (carrier c η) (ball 0 r)).supportWithinDomain hw
  have hn : ‖w‖ < 1 := (show ‖w‖ < r by simpa only [mem_ball, dist_zero_right] using hm).trans hr1
  apply (AnalyticStripMap.map_re_lt_center_iff c hη hn).mp
  by_contra! h
  exact regularized_ne_zero (s := AnalyticStripMap.map c η w) (by linarith) hzero

/-- Every complete actual zero term is favorable. No absolute-value
estimate or omitted-zero allowance is used here. -/
theorem term_nonneg {c : ℂ} {η r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1) (w : ℂ) :
    0 ≤ (divisor (carrier c η) (ball 0 r) w : ℝ) * (kernel r w).re := by
  by_cases hw : divisor (carrier c η) (ball 0 r) w = 0
  · simp [hw]
  · have hf := analyticOnNhd_carrier hη hleft hr1
    have hneg := divisor_re_neg hc hη hleft hr1 hw
    have hw0 : w ≠ 0 := by intro h; subst w; simp at hneg
    exact mul_nonneg (by exact_mod_cast (hf.mono ball_subset_closedBall).divisor_nonneg w)
      (kernel_re_nonneg hr ((divisor (carrier c η) (ball 0 r)).supportWithinDomain hw) hw0 hneg.le)

/-- The entire complete finite source has nonnegative real part. -/
theorem source_nonneg {c : ℂ} {η r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1) : 0 ≤ (source c η r).re := by
  rw [source_re hη hleft hr1]
  exact finsum_nonneg (term_nonneg hc hη hleft hr hr1)

/-- Any selected actual zero gives its complete signed contribution
with the full multiplicity, while every other zero retains favorable sign. -/
theorem selected_source_le (ρ : NontrivialZetaZero) {c : ℂ} {η r : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1)
    (hρ : ρ.1 ∈ strip c η) (hmem : coordinate c η ρ.1 ∈ ball 0 r) :
    (analyticZetaZeroMultiplicity ρ : ℝ) * (kernel r (coordinate c η ρ.1)).re ≤ (source c η r).re := by
  have hf := analyticOnNhd_carrier hη hleft hr1
  have hd := hf.meromorphicOn.divisor_ball_support_finite
  have hs : (fun w => (divisor (carrier c η) (ball 0 r) w : ℝ) * (kernel r w).re).HasFiniteSupport :=
    hd.subset (by intro w hw hdw; exact hw (by simp [hdw]))
  have h := single_le_finsum (coordinate c η ρ.1) hs (term_nonneg hc hη hleft hr hr1)
  rw [divisor_at_zero ρ hη hleft hr1 hρ hmem, Int.cast_natCast,
    ← source_re hη hleft hr1] at h
  exact h

/-- The complete original complex zeta logarithmic derivative, pole
correction, boundary moment and finite divisor are exactly coupled. -/
theorem logarithmic_identity {c : ℂ} {η r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0) :
    (4 * (η : ℂ) / Real.pi) *
      (logDeriv riemannZeta c + 1 / (c - 1) - 1 / (c + 1)) =
      moment (carrier c η) r + source c η r := by
  have h := AnalyticStripDisc.logDeriv_eq_moment_add_divisor hη (analyticOnNhd_strip hleft)
    (regularized_ne_zero hc.le) hr hr1 hs
  rw [logDeriv_regularized hc] at h
  exact h

/-- The actual selected-zero inequality keeps the signed complex boundary
moment and exact rational pole correction. Every other zero has already
been accounted for with favorable sign. -/
theorem selected_source_constraint (ρ : NontrivialZetaZero) {c : ℂ} {η r : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0)
    (hρ : ρ.1 ∈ strip c η) (hmem : coordinate c η ρ.1 ∈ ball 0 r) :
    (4 * η / Real.pi) * (-logDeriv riemannZeta c).re +
      (analyticZetaZeroMultiplicity ρ : ℝ) * (kernel r (coordinate c η ρ.1)).re ≤
      (-moment (carrier c η) r).re +
        (4 * η / Real.pi) * (1 / (c - 1) - 1 / (c + 1)).re := by
  have h := congrArg Complex.re (logarithmic_identity hc hη hleft hr hr1 hs)
  have hzero := selected_source_le ρ hc hη hleft hr hr1 hρ hmem
  have he : 4 * (η : ℂ) / Real.pi = ((4 * η / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [he] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.sub_re, Complex.neg_re] at h ⊢
  nlinarith

/-- Every actual zero in the physical strip enters every sufficiently
large finite coordinate window, with no imaginary-height restriction. -/
theorem eventually_coordinate_mem (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) :
    ∀ᶠ n in atTop, coordinate c η ρ.1 ∈ ball 0 (r n) :=
  eventually_inverse_mem hη hρ hr

/-- Actual zero-free coordinate circles approach the full strip radius.
This theorem does not assume or assert convergence of their boundary moments. -/
theorem exists_sphere_tendsto {c : ℂ} {η : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hleft : η < c.re) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 1) ∧
      ∀ n, 0 < r n ∧ r n < 1 ∧ ∀ w : ℂ, ‖w‖ = r n → carrier c η w ≠ 0 :=
  AnalyticStripDisc.exists_sphere_tendsto hη (analyticOnNhd_strip hleft) (regularized_ne_zero hc.le)

end
end RiemannGaussian.ZetaStripDisc
