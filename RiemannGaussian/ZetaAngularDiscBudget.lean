/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovAngularBudget

/-!
# A signed local zeta detector for arbitrary proved disc bounds

The exact boundary moment, favorable unselected divisor, actual zero
multiplicity and radial correction are independent of the method used
to bound zeta on the disc. This interface takes those analytic bounds
explicitly. The numerical three-height budget is unchanged; applications
must supply the actual disc estimates, not assume their payment.
-/

namespace RiemannGaussian.ZetaAngularDiscBudget
noncomputable section
open Complex Metric Set Filter
open ZetaNearOneLocalDisc (center)
open ZetaNearOneCanonical (translated translated_zero)
open ZetaNearOneJensen (center_ne_zero)
open ZetaNearOneSignedBound (coupledSum coupledSum_nonneg source_le_sum)
open AnalyticDiscBoundaryMoment
open scoped Topology

/-- Translation preserves the logarithmic derivative at every actual
Euler-side center, without a degree or height restriction. -/
theorem logDeriv_translated {x : ℝ} (hx : 0 < x) (t : ℝ) :
    logDeriv (translated x t) 0 = logDeriv riemannZeta (center x t) := by
  have hs : center x t ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp [ZetaNearOneLocalDisc.center] at he
    linarith
  have hd := (analyticOn_riemannZeta (center x t) hs).differentiableAt
  change logDeriv (riemannZeta ∘ (· + center x t)) 0 = _
  rw [logDeriv_comp (by simpa using hd) (by fun_prop)]
  simp

/-- The whole complex identity keeps the complete coupled divisor on
each eligible circle inside an arbitrary analytic disc. -/
theorem logDeriv_eq_boundary_moment_add_sum {R x t r : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 R))
    (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    logDeriv riemannZeta (center x t) = moment (translated x t) r + coupledSum x t r := by
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  have h := logDeriv_eq_moment_add_divisor hr
    (hf.mono (closedBall_subset_closedBall hrR)) hzero hs
  rwa [logDeriv_translated hx t] at h

/-- Signed angular control uses the supplied upper bound only on the
left and the actual Euler reciprocal lower bound on the right. -/
theorem boundary_moment_le {R x t r P : ℝ} (hx : 0 < x) (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 R))
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated x t z‖ ≤ Real.exp P)
    (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-moment (translated x t) r).re ≤ 2 * (P + Real.log (1 + 1 / x)) / (Real.pi * r) := by
  apply AnalyticDiscSignedBoundary.neg_moment_re_le hr
    ((hf.mono (closedBall_subset_closedBall hrR)).continuousOn.mono sphere_subset_closedBall)
    (fun z hz ↦ hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
  · intro z hz _
    have hn := hb z (closedBall_subset_closedBall hrR (sphere_subset_closedBall hz))
    have hpos : 0 < ‖translated x t z‖ := norm_pos_iff.mpr
      (hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
    simpa only [Real.log_exp] using Real.log_le_log hpos hn
  · intro z _ hz
    exact ZetaNearOneAngularBound.right_arc_lower t hx hz

/-- All unselected divisor terms keep their favorable sign at the
original radius, whose boundary may itself contain zeta zeros. -/
theorem neg_logDeriv_re_le {R x t P : ℝ} (hR : 0 < R) (hx : 0 < x)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 R))
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated x t z‖ ≤ Real.exp P) :
    (-logDeriv riemannZeta (center x t)).re ≤
      2 * (P + Real.log (1 + 1 / x)) / (Real.pi * R) := by
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hR hf hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * (P + Real.log (1 + 1 / x)) / (Real.pi * r n)) atTop
      (𝓝 (2 * (P + Real.log (1 + 1 / x)) / (Real.pi * R))) :=
    tendsto_const_nhds.div (hlim.const_mul Real.pi) (mul_pos Real.pi_pos hR).ne'
  apply ge_of_tendsto' hl
  intro n
  have hm := boundary_moment_le hx (hr n).1 (hr n).2.1.le hf hb (hr n).2.2
  have hsum := coupledSum_nonneg hx (hr n).1 (hf.mono (closedBall_subset_closedBall (hr n).2.1.le))
  rw [logDeriv_eq_boundary_moment_add_sum hx (hr n).1 (hr n).2.1.le hf (hr n).2.2,
    neg_add, Complex.add_re, Complex.neg_re]
  simp only [Complex.neg_re] at hm ⊢
  linarith

/-- The selected genuine zero retains its full multiplicity and exact
radial correction when the signed bound passes to the full radius. -/
theorem neg_logDeriv_re_le_sub_zero (ρ : NontrivialZetaZero) {R x P : ℝ}
    (hR : 0 < R) (hx : 0 < x)
    (hf : AnalyticOnNhd ℂ (translated x ρ.1.im) (closedBall 0 R))
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated x ρ.1.im z‖ ≤ Real.exp P)
    (hnear : x + 1 - ρ.1.re < R) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤
      2 * (P + Real.log (1 + 1 / x)) / (Real.pi * R) -
        (analyticZetaZeroMultiplicity ρ : ℝ) *
          (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / R ^ 2) := by
  have hzero : translated x ρ.1.im 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero ρ.1.im hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hR hf hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * (P + Real.log (1 + 1 / x)) / (Real.pi * r n) -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (r n) ^ 2)) atTop
      (𝓝 (2 * (P + Real.log (1 + 1 / x)) / (Real.pi * R) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / R ^ 2))) :=
    (tendsto_const_nhds.div (hlim.const_mul Real.pi) (mul_pos Real.pi_pos hR).ne').sub
      ((tendsto_const_nhds.sub (tendsto_const_nhds.div (hlim.pow 2)
        (pow_ne_zero 2 hR.ne'))).const_mul _)
  apply ge_of_tendsto hl
  filter_upwards [hlim.eventually (lt_mem_nhds hnear)] with n hn
  have hm := boundary_moment_le hx (hr n).1 (hr n).2.1.le hf hb (hr n).2.2
  have hsource := source_le_sum ρ hx (hr n).1
    (hf.mono (closedBall_subset_closedBall (hr n).2.1.le)) hn
  rw [logDeriv_eq_boundary_moment_add_sum hx (hr n).1 (hr n).2.1.le hf (hr n).2.2,
    neg_add, Complex.add_re, Complex.neg_re]
  simp only [Complex.neg_re] at hm ⊢
  linarith

/-- The full numerical budget of the actual three-height prime inequality. -/
def budget (R P Q x : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 +
    (8 * (P + Real.log (1 + 1 / x)) + 2 * (Q + Real.log (1 + 1 / x))) / (Real.pi * R)

/-- The actual prime inequality bounds a selected zero by the two
explicit disc profiles, with no norm taken across its signed source. -/
theorem source_le_budget (ρ : NontrivialZetaZero) {R x P Q : ℝ}
    (hR : 0 < R) (hx : 0 < x) (hxsmall : x ≤ 1 / 4)
    (hf : AnalyticOnNhd ℂ (translated x ρ.1.im) (closedBall 0 R))
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated x ρ.1.im z‖ ≤ Real.exp P)
    (hf₂ : AnalyticOnNhd ℂ (translated x (2 * ρ.1.im)) (closedBall 0 R))
    (hb₂ : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated x (2 * ρ.1.im) z‖ ≤ Real.exp Q)
    (hnear : x + 1 - ρ.1.re < R) :
    4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / R ^ 2) ≤
      3 / x + budget R P Q x := by
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg
    (a := 1 + x) (by linarith) ρ.1.im
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hxsmall
  have hzero := neg_logDeriv_re_le_sub_zero ρ hR hx hf hb hnear
  have hdouble := neg_logDeriv_re_le hR hx hf₂ hb₂
  change 0 ≤ 3 * (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re +
    4 * (-logDeriv riemannZeta (center x ρ.1.im)).re +
    (-logDeriv riemannZeta (center x (2 * ρ.1.im))).re at hprime
  unfold budget
  simp only [div_eq_mul_inv] at hreal hzero hdouble ⊢
  nlinarith

/-- A numerical payment of the displayed budget gives a strict actual
zero gap. The horizontal shift is fixed by the proposed margin, not by
an unknown smaller gap of the selected zero. -/
theorem margin_of_budget (ρ : NontrivialZetaZero) {R P Q d : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1) (hd : 0 < d) (hdsmall : d < R / 28)
    (hf : AnalyticOnNhd ℂ (translated (6 * d) ρ.1.im) (closedBall 0 R))
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated (6 * d) ρ.1.im z‖ ≤ Real.exp P)
    (hf₂ : AnalyticOnNhd ℂ (translated (6 * d) (2 * ρ.1.im)) (closedBall 0 R))
    (hb₂ : ∀ z ∈ closedBall (0 : ℂ) R, ‖translated (6 * d) (2 * ρ.1.im) z‖ ≤ Real.exp Q)
    (hpay : 14 * d * budget R P Q (6 * d) + 392 * d ^ 2 / R ^ 2 < 1) :
    d < 1 - ρ.1.re := by
  by_contra! hgap
  let v := 6 * d + 1 - ρ.1.re
  have hv : 0 < v := by dsimp only [v]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have hvup : v ≤ 7 * d := by dsimp only [v]; linarith
  have hsource := source_le_budget ρ hR (by positivity : 0 < 6 * d)
    (by linarith : 6 * d ≤ 1 / 4) hf hb hf₂ hb₂
    (by linarith : 6 * d + 1 - ρ.1.re < R)
  have hinv : 1 / (7 * d) ≤ 1 / v := one_div_le_one_div_of_le hv hvup
  have hcorr : v / R ^ 2 ≤ 7 * d / R ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hbase : 0 ≤ 1 / (7 * d) - 7 * d / R ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < R ^ 2)
      (by positivity : 0 < 7 * d)).mpr
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 28 * d) hR.le).mpr
      (by linarith : 28 * d ≤ R)
    nlinarith
  have hmult : (1 : ℝ) ≤ analyticZetaZeroMultiplicity ρ := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hlower : 1 / (7 * d) - 7 * d / R ^ 2 ≤
      (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / v - v / R ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hmult hbase
    have h' := mul_le_mul_of_nonneg_left (show 1 / (7 * d) - 7 * d / R ^ 2 ≤
      1 / v - v / R ^ 2 by linarith)
      (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
    linarith
  have hs : 4 * (1 / (7 * d) - 7 * d / R ^ 2) ≤
      3 / (6 * d) + budget R P Q (6 * d) := by
    change 4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / v - v / R ^ 2) ≤ _ at hsource
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 14 * d)
  have hleft : 14 * d * (4 * (1 / (7 * d) - 7 * d / R ^ 2)) =
      8 - 392 * d ^ 2 / R ^ 2 := by field_simp; ring
  have hright : 14 * d * (3 / (6 * d) + budget R P Q (6 * d)) =
      7 + 14 * d * budget R P Q (6 * d) := by field_simp; ring
  rw [hleft, hright] at hm
  linarith


end
end RiemannGaussian.ZetaAngularDiscBudget
