/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCompletionHalfLogBound
import RiemannGaussian.ZetaStechkinZeroFree

/-!
# A wider actual zero-free strip from the half-logarithm completion bound

The new completion estimate applies to all phase families. Instantiating
it with the already proved classical square gives a genuine independent
contradiction in the closed edge region of width `1/(24*log(abs(t)+22))`.
The full multiplicity source and signed prime work are kept before the
nonnegative square supplies the arithmetic floor.

This improves the repository's width by the factor `8/3`. It is not a
claim of a best classical zero-free region or a proof of RH.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical Topology

private theorem family_hasSum_mul (f : ℕ → ℝ) :
    HasSum (fun n => zetaThreePhaseFamily n * f n) (3 * f 0 + 4 * f 1 + f 2) := by
  have h := ((hasSum_ite_eq (0 : ℕ) (3 * f 0)).add
    (hasSum_ite_eq (1 : ℕ) (4 * f 1))).add (hasSum_ite_eq (2 : ℕ) (f 2))
  apply h.congr_fun
  intro n
  by_cases h0 : n = 0
  · subst n
    norm_num [zetaThreePhaseFamily]
  by_cases h1 : n = 1
  · subst n
    norm_num [zetaThreePhaseFamily]
  by_cases h2 : n = 2
  · subst n
    norm_num [zetaThreePhaseFamily]
  simp [zetaThreePhaseFamily, h0, h1, h2]

private theorem family_summable : Summable zetaThreePhaseFamily := by
  simpa using (family_hasSum_mul (fun _ => 1)).summable

private theorem family_log_summable :
    Summable (fun n : ℕ => zetaThreePhaseFamily n * Real.log n) :=
  (family_hasSum_mul (fun n => Real.log n)).summable

private theorem family_oscillatoryMass : phaseOscillatoryMass zetaThreePhaseFamily = 5 := by
  have h := (family_hasSum_mul (fun _ => 1)).tsum_eq
  simp only [mul_one] at h
  rw [family_summable.tsum_eq_zero_add] at h
  change 3 + phaseOscillatoryMass zetaThreePhaseFamily = 3 + 4 + 1 at h
  linarith

private theorem family_logMass : phaseLogFrequencyMass zetaThreePhaseFamily = Real.log 2 := by
  have h := (family_hasSum_mul (fun n => Real.log n)).tsum_eq
  rw [family_log_summable.tsum_eq_zero_add] at h
  simpa [zetaThreePhaseFamily, phaseLogFrequencyMass] using h

/-- The same exact three-height square now pays only half the growing
logarithm and no additive completion mass. Analytic multiplicity and the
full nonnegative prime-power work are retained explicitly. -/
theorem zetaThreePhase_half_log_source_add_primeWork_le
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) :
    4 * (analyticZetaZeroMultiplicity rho : ℝ) / 7 - 1 / 2 +
      (1 - rho.1.re) * (∑' m : ℕ, zetaStechkinPrimeWeight (1 + 6 * (1 - rho.1.re)) m *
        phaseContactKernel zetaThreePhaseFamily (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + 6 * (1 - rho.1.re))) *
        ((3 * Real.log (1 + 6 * (1 - rho.1.re)) +
          5 * Real.log (1 + 6 * (1 - rho.1.re) + |rho.1.im|) + Real.log 2) / 2) +
        30 * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phase_shifted_source_add_primeWork_le_stechkin_half_log
    zetaThreePhaseFamily_nonneg family_summable family_log_summable rho hρ
    (κ := 6) (by norm_num)
  rw [family_oscillatoryMass, family_logMass] at h
  norm_num [phaseShiftSource, zetaThreePhaseFamily] at h
  convert h using 1

/-- The wider literal zero-free edge margin supplied by the half-log
completion estimate. -/
def zetaHalfLogZeroMargin (t : ℝ) : ℝ := 1 / (24 * localZetaLogHeight t)

/-- The improved edge width is positive at every real ordinate. -/
theorem zetaHalfLogZeroMargin_pos (t : ℝ) : 0 < zetaHalfLogZeroMargin t := by
  have h := three_lt_localZetaLogHeight t
  unfold zetaHalfLogZeroMargin
  positivity

/-- An actual zero above absolute height one cannot lie in the wider
closed right-edge region. The independent signed budget beats its full
source there using only proved arithmetic and completion bounds. -/
theorem zetaHalfLog_margin_lt_one_sub_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) : zetaHalfLogZeroMargin rho.1.im < 1 - rho.1.re := by
  let d := 1 - rho.1.re
  let L := localZetaLogHeight rho.1.im
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hL : 3 < L := three_lt_localZetaLogHeight rho.1.im
  by_contra hn
  have hdm : d ≤ 1 / (24 * L) := le_of_not_gt hn
  have hprod : d * (24 * L) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 24 * L)).mp hdm
  have hdL : d * L ≤ 1 / 24 := by nlinarith
  have hdsmall : d ≤ 1 / 72 := by nlinarith [mul_pos hd (by linarith : 0 < L - 3)]
  have hρ : 1 / 2 < rho.1.re := by dsimp [d] at hdsmall; linarith
  have hσ : 1 ≤ 1 + 6 * d := by linarith
  have hgap := zetaThreePhase_half_log_source_add_primeWork_le rho hρ
  change 4 * (analyticZetaZeroMultiplicity rho : ℝ) / 7 - 1 / 2 +
    d * (∑' m : ℕ, zetaStechkinPrimeWeight (1 + 6 * d) m *
      phaseContactKernel zetaThreePhaseFamily (rho.1.im * Real.log m)) ≤
    d * (1 - zetaStechkinWeight (1 + 6 * d)) *
      ((3 * Real.log (1 + 6 * d) +
        5 * Real.log (1 + 6 * d + |rho.1.im|) + Real.log 2) / 2) +
      30 * d ^ 2 / rho.1.im ^ 2 at hgap
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hwork : 0 ≤ d * (∑' m : ℕ, zetaStechkinPrimeWeight (1 + 6 * d) m *
      phaseContactKernel zetaThreePhaseFamily (rho.1.im * Real.log m)) := by
    apply mul_nonneg hd.le
    apply tsum_nonneg
    intro m
    rw [zetaThreePhaseFamily_kernel]
    exact mul_nonneg (zetaStechkinPrimeWeight_nonneg hσ m) (by positivity)
  have hc := four_ninths_le_zetaStechkinWeight hσ
  have hc1 := (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hlogσ : Real.log (1 + 6 * d) ≤ 1 / 12 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + 6 * d)
    linarith
  have hlogy : Real.log (1 + 6 * d + |rho.1.im|) ≤ L := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hheight : (3 * Real.log (1 + 6 * d) +
      5 * Real.log (1 + 6 * d + |rho.1.im|) + Real.log 2) / 2 ≤
        (65 / 24 : ℝ) * L := by linarith
  have hheight' := mul_le_mul_of_nonneg_left hheight (mul_nonneg hd.le (sub_nonneg.mpr hc1))
  have hgamma : d * (1 - zetaStechkinWeight (1 + 6 * d)) *
      ((3 * Real.log (1 + 6 * d) +
        5 * Real.log (1 + 6 * d + |rho.1.im|) + Real.log 2) / 2) ≤
        (325 / 216 : ℝ) * (d * L) := by
    have hh := mul_le_mul_of_nonneg_right (show 1 - zetaStechkinWeight (1 + 6 * d) ≤ 5 / 9 by linarith)
      (show 0 ≤ d * ((65 / 24 : ℝ) * L) by positivity)
    nlinarith only [hheight', hh]
  have hy2 : 1 ≤ rho.1.im ^ 2 := by nlinarith [sq_abs rho.1.im]
  have hquad : 30 * d ^ 2 / rho.1.im ^ 2 ≤ (5 / 36 : ℝ) * (d * L) := by
    have hdiv := div_le_self (sq_nonneg d) hy2
    have hsmall := mul_le_mul_of_nonneg_left hdsmall hd.le
    have hLL := mul_le_mul_of_nonneg_left hL.le hd.le
    rw [mul_div_assoc]
    nlinarith
  nlinarith only [hgap, hm, hwork, hgamma, hquad, hdL]

/-- The genuine critical reflection gives the same exclusion width from
the left edge, preserving the ordinate and analytic multiplicity. -/
theorem zetaHalfLog_margin_lt_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) : zetaHalfLogZeroMargin rho.1.im < rho.1.re := by
  have h := zetaHalfLog_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im,
      Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add] using hy)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im,
    sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every genuine nontrivial zero above absolute height one lies inside
the wider two-sided reciprocal-logarithm strip. -/
theorem nontrivialZetaZero_mem_half_log_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Set.Ioo (zetaHalfLogZeroMargin rho.1.im) (1 - zetaHalfLogZeroMargin rho.1.im) :=
  ⟨zetaHalfLog_margin_lt_re rho hy, by linarith [zetaHalfLog_margin_lt_one_sub_re rho hy]⟩

/-- The width is uniformly small, keeping the new right-edge region in
the positive half-plane where the literal zeta-zero bridge applies. -/
theorem zetaHalfLogZeroMargin_lt (t : ℝ) : zetaHalfLogZeroMargin t < 1 / 72 := by
  have hL := three_lt_localZetaLogHeight t
  unfold zetaHalfLogZeroMargin
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- The literal Riemann zeta function is nonzero throughout the wider
closed right-edge region at every absolute ordinate at least one. -/
theorem riemannZeta_ne_zero_of_half_log_margin {s : ℂ} (hy : 1 ≤ |s.im|)
    (hs : 1 - zetaHalfLogZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [zetaHalfLogZeroMargin_lt s.im]
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have hgap := zetaHalfLog_margin_lt_one_sub_re rho hy
  change zetaHalfLogZeroMargin s.im < 1 - s.re at hgap
  linarith

/-- The new exclusion width is exactly eight thirds of the preceding
Stechkin width, at every real ordinate. -/
theorem zetaHalfLogZeroMargin_eq_mul_stechkin (t : ℝ) :
    zetaHalfLogZeroMargin t = (8 / 3 : ℝ) * zetaStechkinZeroMargin t := by
  unfold zetaHalfLogZeroMargin zetaStechkinZeroMargin
  ring

/-- The improvement of the actual zero-free width is strict everywhere. -/
theorem zetaStechkinZeroMargin_lt_half_log (t : ℝ) :
    zetaStechkinZeroMargin t < zetaHalfLogZeroMargin t := by
  rw [zetaHalfLogZeroMargin_eq_mul_stechkin]
  linarith [zetaStechkinZeroMargin_pos t]

end
end RiemannGaussian
