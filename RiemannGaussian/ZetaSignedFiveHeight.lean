/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaReciprocalGeometry

/-!
# Five prime phases and a wider proved zero-free region

The exact fourth power `8 * (1 + cos t)^4` couples the five heights
`0, y, 2*y, 3*y, 4*y` before taking any estimate of the logarithmic
derivatives. Its coefficients are `35, 56, 28, 8, 1`.

The complete local pole sums remain in a simultaneous inequality. Selecting
one actual zero then gives a multiplicity-sensitive quadratic constraint.
Above absolute height one, this proves a strict margin
`1 / (28000 * log (abs y + 22))` from both edges of the critical strip.
This more than doubles the previous uniform reciprocal-logarithm margin.

These are unconditional bounds for the literal zeta zeros. The central
part of the strip and the independent signed Suzuki-work bound remain open.
The trigonometric-polynomial method is classical; no novelty is claimed.
-/

open Complex
open scoped Classical ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- The five signed phase coefficients are the exact expansion of a fourth
power; no separate bound on any cosine is used. -/
theorem zetaPrimePhaseFourthPower_identity (t : ℝ) :
    35 + 56 * Real.cos t + 28 * Real.cos (2 * t) +
      8 * Real.cos (3 * t) + Real.cos (4 * t) =
        8 * (1 + Real.cos t) ^ 4 := by
  rw [show 4 * t = 2 * (2 * t) by ring]
  simp only [Real.cos_two_mul, Real.cos_three_mul]
  ring

/-- Positivity of the actual prime-power amplitudes turns the retained
fourth-power phase into a five-height zeta inequality on `re s > 1`. -/
theorem neg_logDeriv_riemannZeta_five_height_nonneg {a : ℝ} (ha : 1 < a) (y : ℝ) :
    0 ≤ 35 * (-logDeriv riemannZeta (a : ℂ)).re +
      56 * (-logDeriv riemannZeta ((a : ℂ) + I * y)).re +
      28 * (-logDeriv riemannZeta ((a : ℂ) + I * (2 * y : ℝ))).re +
      8 * (-logDeriv riemannZeta ((a : ℂ) + I * (3 * y : ℝ))).re +
      (-logDeriv riemannZeta ((a : ℂ) + I * (4 * y : ℝ))).re := by
  let f : ℝ → ℕ → ℂ := fun t ↦ LSeries.term
    (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * t)
  have hs (t : ℝ) : Summable (f t) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using ha)
  have hre (t : ℝ) : HasSum (fun n ↦ (f t n).re)
      (-logDeriv riemannZeta ((a : ℂ) + I * t)).re := by
    rw [neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using ha),
      Complex.re_tsum (hs t)]
    exact (Complex.reCLM.summable (hs t)).hasSum
  have hsum := ((((hre 0).mul_left 35).add ((hre y).mul_left 56)).add
    ((hre (2 * y)).mul_left 28)).add ((hre (3 * y)).mul_left 8) |>.add (hre (4 * y))
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hsum
  rw [← hsum.tsum_eq]
  apply tsum_nonneg
  intro n
  dsimp only [f]
  simp only [vonMangoldt_LSeries_term_re, zero_mul, Real.cos_zero, mul_one]
  have he := zetaPrimePhaseFourthPower_identity (y * Real.log n)
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  have hp := mul_nonneg hw (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
    (by positivity : 0 ≤ (1 + Real.cos (y * Real.log n)) ^ 4))
  simp only [mul_assoc] at he hp ⊢
  nlinarith

/-- The local logarithmic height of a scaled ordinate pays only the
logarithm of the scale, retaining the common ordinate contribution. -/
theorem localZetaLogHeight_mul_le_add_log {k : ℝ} (hk : 1 ≤ k) (y : ℝ) :
    localZetaLogHeight (k * y) ≤ localZetaLogHeight y + Real.log k := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  unfold localZetaLogHeight
  rw [abs_mul, abs_of_pos hkpos]
  calc
    Real.log (k * |y| + 22) ≤ Real.log (k * (|y| + 22)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log (|y| + 22) + Real.log k := by
      rw [Real.log_mul hkpos.ne' (by positivity)]
      ring

private theorem five_height_log_budget (y : ℝ) :
    448 * (35 * localZetaLogHeight 0 + 56 * localZetaLogHeight y +
      28 * localZetaLogHeight (2 * y) + 8 * localZetaLogHeight (3 * y) +
      localZetaLogHeight (4 * y)) ≤ 68096 * localZetaLogHeight y := by
  have h0 := localZetaLogHeight_zero_le y
  have h2 := localZetaLogHeight_mul_le_add_log (by norm_num : (1 : ℝ) ≤ 2) y
  have h3 := localZetaLogHeight_mul_le_add_log (by norm_num : (1 : ℝ) ≤ 3) y
  have h4 := localZetaLogHeight_mul_le_add_log (by norm_num : (1 : ℝ) ≤ 4) y
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith [two_lt_localZetaLogHeight y]

/-- The independent five-height prime inequality controls all five complete
local zero sums together. The pole at one is evaluated before estimating its
nonzero-height contributions. -/
theorem five_height_localZetaPoleSum_re_le {y x : ℝ} (hy : y ≠ 0)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    35 * (localZetaPoleSum 0 ((x - 1 / 2 : ℝ) : ℂ)).re +
      56 * (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re +
      28 * (localZetaPoleSum (2 * y) ((x - 1 / 2 : ℝ) : ℂ)).re +
      8 * (localZetaPoleSum (3 * y) ((x - 1 / 2 : ℝ) : ℂ)).re +
      (localZetaPoleSum (4 * y) ((x - 1 / 2 : ℝ) : ℂ)).re ≤
        35 / x + 68096 * localZetaLogHeight y + 9209 * x / (144 * y ^ 2) := by
  have hprime := neg_logDeriv_riemannZeta_five_height_nonneg (by linarith : 1 < 1 + x) y
  have h0 := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum 0 hx hxsmall
  have h1 := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum y hx hxsmall
  have h2 := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (2 * y) hx hxsmall
  have h3 := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (3 * y) hx hxsmall
  have h4 := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (4 * y) hx hxsmall
  have hp (t : ℝ) (ht : t ≠ 0) : x / (x ^ 2 + t ^ 2) ≤ x / t ^ 2 :=
    div_le_div_of_nonneg_left hx.le (sq_pos_of_ne_zero ht) (by nlinarith [sq_nonneg x])
  have hp1 := hp y hy
  have hp2 := hp (2 * y) (mul_ne_zero (by norm_num) hy)
  have hp3 := hp (3 * y) (mul_ne_zero (by norm_num) hy)
  have hp4 := hp (4 * y) (mul_ne_zero (by norm_num) hy)
  have he0 : x / (x ^ 2 + (0 : ℝ) ^ 2) = 1 / x := by field_simp; ring
  have he2 : x / (2 * y) ^ 2 = (x / y ^ 2) / 4 := by ring
  have he3 : x / (3 * y) ^ 2 = (x / y ^ 2) / 9 := by ring
  have he4 : x / (4 * y) ^ 2 = (x / y ^ 2) / 16 := by ring
  rw [he0] at h0
  rw [he2] at hp2
  rw [he3] at hp3
  rw [he4] at hp4
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at h0
  have hlog := five_height_log_budget y
  simp only [Complex.neg_re, div_eq_mul_inv, mul_inv_rev] at hprime h0 h1 h2 h3 h4 hp1 hp2 hp3 hp4 ⊢
  nlinarith

/-- Selecting one actual zero from the complete five-height inequality keeps
its full analytic multiplicity. All other pole contributions have their
proved nonnegative signs. -/
theorem fiftySix_mul_multiplicity_div_gap_le_fiveHeight (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    56 * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      35 / x + 68096 * localZetaLogHeight rho.1.im +
        9209 * x / (144 * rho.1.im ^ 2) := by
  have h := five_height_localZetaPoleSum_re_le
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) hx hxsmall
  have hs := multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx
  have h0 := localZetaPoleSum_re_nonneg 0 hx
  have h2 := localZetaPoleSum_re_nonneg (2 * rho.1.im) hx
  have h3 := localZetaPoleSum_re_nonneg (3 * rho.1.im) hx
  have h4 := localZetaPoleSum_re_nonneg (4 * rho.1.im) hx
  rw [mul_div_assoc]
  linarith

/-- At four times the actual boundary gap, the five signed prime phases
give a stronger quadratic inequality with every multiplicity retained. -/
theorem multiplicity_le_fiveHeight_signed_zero_gap (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    2016 * (analyticZetaZeroMultiplicity rho : ℝ) - 1575 ≤
      12257280 * localZetaLogHeight rho.1.im * (1 - rho.1.re) +
        46045 * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have h := fiftySix_mul_multiplicity_div_gap_le_fiveHeight rho
    (by linarith : 3 / 4 ≤ rho.1.re) (by positivity : 0 < 4 * d)
    (by dsimp [d]; linarith : 4 * d ≤ 1 / 4)
  rw [show 4 * d + 1 - rho.1.re = 5 * d by dsimp [d]; ring] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 180 * d by positivity)
  have he : 180 * d * (56 * (analyticZetaZeroMultiplicity rho : ℝ) / (5 * d)) =
      2016 * (analyticZetaZeroMultiplicity rho : ℝ) := by field_simp; ring
  have he' : 180 * d * (35 / (4 * d) + 68096 * localZetaLogHeight rho.1.im +
      9209 * (4 * d) / (144 * rho.1.im ^ 2)) =
      1575 + 12257280 * localZetaLogHeight rho.1.im * d + 46045 * d ^ 2 / rho.1.im ^ 2 := by
    field_simp
    ring
  rw [he, he'] at hmul
  dsimp only [d] at hmul
  linarith

private theorem five_height_margin_small (y : ℝ) :
    1 / (28000 * localZetaLogHeight y) < (1 / 16 : ℝ) := by
  have hL := two_lt_localZetaLogHeight y
  exact (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) (by linarith))

/-- Every actual zero above absolute height one stays strictly beyond the
new explicit right-edge margin; no arithmetic premise remains. -/
theorem fiveHeight_margin_lt_one_sub_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    1 / (28000 * localZetaLogHeight rho.1.im) < 1 - rho.1.re := by
  by_cases hrho : 15 / 16 ≤ rho.1.re
  · let d := 1 - rho.1.re
    let L := localZetaLogHeight rho.1.im
    have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
    have hdsmall : d ≤ 1 / 16 := by dsimp [d]; linarith
    have hL : 2 < L := two_lt_localZetaLogHeight rho.1.im
    have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
      exact_mod_cast analyticZetaZeroMultiplicity_positive rho
    have hgap := multiplicity_le_fiveHeight_signed_zero_gap rho hrho
    change 2016 * (analyticZetaZeroMultiplicity rho : ℝ) - 1575 ≤
      12257280 * L * d + 46045 * d ^ 2 / rho.1.im ^ 2 at hgap
    have hy2 : 1 ≤ rho.1.im ^ 2 := by nlinarith [sq_abs rho.1.im]
    have hquad : d ^ 2 / rho.1.im ^ 2 ≤ L * d / 32 := by
      have hdiv : d ^ 2 / rho.1.im ^ 2 ≤ d ^ 2 := div_le_self (sq_nonneg d) hy2
      nlinarith [mul_nonneg hd.le (show 0 ≤ L - 2 by linarith)]
    by_contra hn
    have hdm : d ≤ 1 / (28000 * L) := le_of_not_gt hn
    have hprod := (le_div_iff₀ (show 0 < 28000 * L by positivity)).mp hdm
    have hquad' := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 46045)
    rw [mul_div_assoc] at hgap
    nlinarith only [hgap, hm, hquad', hprod]
  · exact (five_height_margin_small rho.1.im).trans_le (by linarith)

/-- Completion reflection transfers the same strict margin to the left
edge at the unchanged absolute ordinate. -/
theorem fiveHeight_margin_lt_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    1 / (28000 * localZetaLogHeight rho.1.im) < rho.1.re := by
  have h := fiveHeight_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im,
      Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add] using hy)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im,
    sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- A literal zeta-zero bound: every nontrivial zero at absolute height at
least one belongs to this strictly narrower critical strip. -/
theorem nontrivialZetaZero_mem_fiveHeight_reciprocal_log_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Set.Ioo (1 / (28000 * localZetaLogHeight rho.1.im))
      (1 - 1 / (28000 * localZetaLogHeight rho.1.im)) := by
  exact ⟨fiveHeight_margin_lt_re rho hy, by linarith [fiveHeight_margin_lt_one_sub_re rho hy]⟩

/-- The actual zeta function is nonzero on the whole closed right-edge
region supplied by the strict five-height margin. -/
theorem riemannZeta_ne_zero_of_fiveHeight_margin {s : ℂ} (hy : 1 ≤ |s.im|)
    (hs : 1 - 1 / (28000 * localZetaLogHeight s.im) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [five_height_margin_small s.im]
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have hgap := fiveHeight_margin_lt_one_sub_re rho hy
  change 1 / (28000 * localZetaLogHeight s.im) < 1 - s.re at hgap
  linarith

/-- The new uniform margin is strictly more than twice the previously
proved uniform `1/(56458*log-height)` margin. -/
theorem two_mul_quadratic_uniform_margin_lt_fiveHeight (y : ℝ) :
    2 * (1 / (56458 * localZetaLogHeight y)) < 1 / (28000 * localZetaLogHeight y) := by
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end

end RiemannGaussian
