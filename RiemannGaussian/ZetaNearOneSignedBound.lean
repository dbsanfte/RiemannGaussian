/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneCanonical
import RiemannGaussian.ZetaMoebiusWronskian

/-!
# Signed shrinking-disc bounds for the actual zeta logarithmic derivative

Every enclosed zero lies to the left of the Euler-side center. Keeping
its canonical correction coupled to the pole preserves nonnegativity.
Only the complete analytic residual is norm-bounded. A selected genuine
zero contributes its full multiplicity divided by its horizontal distance,
with an explicit radial correction and all analytic premises discharged.
-/

namespace RiemannGaussian.ZetaNearOneSignedBound
noncomputable section
open Complex Metric Set MeromorphicOn ZetaNearOneLocalDisc ZetaNearOneLogProfile
open DirichletPowerParameters DerivativeOrderComparison ZetaNearOneJensen
open ZetaNearOneCanonical AnalyticDiscSignedDerivative
open scoped Classical

/-- The complete signed complex divisor contribution at the actual center. -/
def coupledSum (x t r : ℝ) : ℂ :=
  ∑ᶠ a, divisor (translated x t) (ball 0 r) a • kernel r a

/-- Taking real parts preserves every coupled divisor term. -/
theorem coupledSum_re (x t r : ℝ)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 r)) :
    (coupledSum x t r).re = ∑ᶠ a,
      (divisor (translated x t) (ball 0 r) a : ℝ) * (kernel r a).re := by
  have hd := hf.meromorphicOn.divisor_ball_support_finite
  have hs : (fun a ↦ divisor (translated x t) (ball 0 r) a • kernel r a).HasFiniteSupport :=
    hd.subset (by intro a ha hda; exact ha (by simp [hda]))
  change Complex.reAddGroupHom (∑ᶠ a, divisor (translated x t) (ball 0 r) a • kernel r a) = _
  rw [map_finsum Complex.reAddGroupHom hs]
  apply finsum_congr
  intro a
  simp [zsmul_eq_mul]

/-- Every nonzero actual divisor term lies strictly left of the center. -/
theorem divisor_re_neg {x t r : ℝ} (hx : 0 < x)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 r)) {a : ℂ}
    (ha : divisor (translated x t) (ball 0 r) a ≠ 0) : a.re < 0 := by
  have hz := zero_of_divisor_ne_zero hf ha
  by_contra! hleft
  apply riemannZeta_ne_zero_of_one_lt_re (s := a + center x t) _ hz
  simp only [Complex.add_re, ZetaNearOneLocalDisc.center, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  linarith

/-- Each complete multiplicity-weighted coupled kernel has nonnegative
real part. No zero count or zero-separation allowance is used. -/
theorem term_nonneg {x t r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 r)) (a : ℂ) :
    0 ≤ (divisor (translated x t) (ball 0 r) a : ℝ) * (kernel r a).re := by
  by_cases ha : divisor (translated x t) (ball 0 r) a = 0
  · simp [ha]
  · have hleft := divisor_re_neg hx hf ha
    have ha0 : a ≠ 0 := by intro he; simp [he] at hleft
    exact mul_nonneg (by exact_mod_cast (hf.mono ball_subset_closedBall).divisor_nonneg a)
      (kernel_re_nonneg hr ((divisor (translated x t) (ball 0 r)).supportWithinDomain ha)
        ha0 hleft.le)

/-- The entire coupled zero sum has nonnegative real part. -/
theorem coupledSum_nonneg {x t r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ (translated x t) (closedBall 0 r)) :
    0 ≤ (coupledSum x t r).re := by
  rw [coupledSum_re x t r hf]
  exact finsum_nonneg (term_nonneg hx hr hf)

/-- Translation preserves the full actual multiplicity of a selected
zeta zero in the local divisor. -/
theorem divisor_at_zero (ρ : NontrivialZetaZero) (x r : ℝ)
    (hf : AnalyticOnNhd ℂ (translated x ρ.1.im) (closedBall 0 r))
    (hρ : ρ.1 - center x ρ.1.im ∈ ball 0 r) :
    divisor (translated x ρ.1.im) (ball 0 r) (ρ.1 - center x ρ.1.im) =
      (analyticZetaZeroMultiplicity ρ : ℤ) := by
  rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hρ]
  change (meromorphicOrderAt (riemannZeta ∘ (· + center x ρ.1.im))
    (ρ.1 - center x ρ.1.im)).untop₀ = _
  rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, sub_add_cancel,
    meromorphicOrderAt_riemannZeta_nontrivialZero]
  simp

/-- The selected zero retains its exact reciprocal-distance source and
radial correction, while all other zeros keep a favorable sign. -/
theorem source_le_sum (ρ : NontrivialZetaZero) {x r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ (translated x ρ.1.im) (closedBall 0 r))
    (hnear : x + 1 - ρ.1.re < r) :
    (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / r ^ 2) ≤
      (coupledSum x ρ.1.im r).re := by
  let a : ℂ := ρ.1 - center x ρ.1.im
  have hd : 0 < x + 1 - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have ha : a = -((x + 1 - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [a, ZetaNearOneLocalDisc.center]
    ring
  have hm : a ∈ ball 0 r := by
    rw [mem_ball, dist_zero_right, ha, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd]
    exact hnear
  have hdFinite := hf.meromorphicOn.divisor_ball_support_finite
  have hterms : (fun z ↦ (divisor (translated x ρ.1.im) (ball 0 r) z : ℝ) *
      (kernel r z).re).HasFiniteSupport :=
    hdFinite.subset (by intro z hz hdz; exact hz (by simp [hdz]))
  have hs := single_le_finsum a hterms (term_nonneg hx hr hf)
  rw [← coupledSum_re x ρ.1.im r hf] at hs
  have hmultiplicity := divisor_at_zero ρ x r hf hm
  change divisor (translated x ρ.1.im) (ball 0 r) a = _ at hmultiplicity
  rw [hmultiplicity, Int.cast_natCast, ha, kernel_neg_real] at hs
  exact hs

/-- Every admissible height and derivative order has an actual signed
upper bound for the zeta logarithmic derivative at its Euler-side center. -/
theorem neg_logDeriv_re_le (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    (-logDeriv riemannZeta (center x t)).re ≤ 8 * allowance k x t / delta k := by
  obtain ⟨r, hrlo, hrhi, g, D, _, hb, he⟩ := exists_controlled_decomp k hk ht hx hx'
  have hδ := delta_pos k
  have hr : 0 < r := by linarith
  have hf := (analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall (by linarith : r ≤ delta k / 2))
  have hs := coupledSum_nonneg hx hr hf
  have hg : (-logDeriv g 0).re ≤ ‖logDeriv g 0‖ := by
    simpa only [norm_neg] using Complex.re_le_norm (-logDeriv g 0)
  change logDeriv riemannZeta (center x t) = logDeriv g 0 + coupledSum x t r at he
  rw [he, neg_add, Complex.add_re]
  simp only [Complex.neg_re] at hg hs ⊢
  linarith

/-- A selected genuine right-half zero forces the full negative
multiplicity source. The remainder and radial correction are explicit
uniform functions of the order, height, and horizontal shift. -/
theorem neg_logDeriv_re_le_sub_zero (k : ℕ) (hk : 1 ≤ k) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : 2 ≤ |ρ.1.im|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : x + 1 - ρ.1.re < delta k / 4) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤ 8 * allowance k x ρ.1.im / delta k -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - 16 * (x + 1 - ρ.1.re) / (delta k) ^ 2) := by
  obtain ⟨r, hrlo, hrhi, g, D, _, hb, he⟩ := exists_controlled_decomp k hk ht hx hx'
  have hδ := delta_pos k
  have hr : 0 < r := by linarith
  have hd : 0 < x + 1 - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have hf := (analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall (by linarith : r ≤ delta k / 2))
  have hs := source_le_sum ρ hx hr hf (hnear.trans hrlo)
  have hcorrect : (x + 1 - ρ.1.re) / r ^ 2 ≤
      16 * (x + 1 - ρ.1.re) / (delta k) ^ 2 := by
    have hh := div_le_div_of_nonneg_left hd.le
      (by positivity : 0 < (delta k) ^ 2 / 16)
      (by nlinarith : (delta k) ^ 2 / 16 ≤ r ^ 2)
    exact hh.trans_eq (by ring)
  have hmul := mul_le_mul_of_nonneg_left hcorrect
    (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
  have hg : (-logDeriv g 0).re ≤ ‖logDeriv g 0‖ := by
    simpa only [norm_neg] using Complex.re_le_norm (-logDeriv g 0)
  change logDeriv riemannZeta (center x ρ.1.im) =
    logDeriv g 0 + coupledSum x ρ.1.im r at he
  rw [he, neg_add, Complex.add_re]
  simp only [Complex.neg_re] at hg ⊢
  nlinarith

end
end RiemannGaussian.ZetaNearOneSignedBound
