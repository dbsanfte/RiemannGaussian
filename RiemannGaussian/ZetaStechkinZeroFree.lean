/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinPhaseBudget
import RiemannGaussian.ZetaPhaseExactZeroBound

/-!
# An explicit zero-free strip from the complete Stechkin budget

The elementary three-height square supplies an actual nonnegative prime
work, while the complete reflected comparison retains the full selected
zero source. The global Gamma bound then excludes the closed edge region
of width `1/(64*log(abs(t)+22))` above absolute height one.

This is a concrete improvement of the repository's previously proved
reciprocal-logarithm strip, using a classical trigonometric test. It is
not a proof of RH or a claim of a new best zero-free region in the literature.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical Topology

/-- The exact coefficients of `2*(1+cos(t))^2`. They are used to
prove an actual zero exclusion, without a numerical coefficient search. -/
def zetaThreePhaseFamily (n : ℕ) : ℝ :=
  if n = 0 then 3 else if n = 1 then 4 else if n = 2 then 1 else 0

/-- The classical three-height family has nonnegative coefficients. -/
theorem zetaThreePhaseFamily_nonneg (n : ℕ) : 0 ≤ zetaThreePhaseFamily n := by
  unfold zetaThreePhaseFamily
  split_ifs <;> norm_num

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

/-- The complete kernel is an exact nonnegative square; its sign is
proved before it is applied to any prime-power amplitude. -/
theorem zetaThreePhaseFamily_kernel (t : ℝ) :
    phaseContactKernel zetaThreePhaseFamily t = 2 * (1 + Real.cos t) ^ 2 := by
  rw [phaseContactKernel, (family_hasSum_mul (fun n => Real.cos ((n : ℝ) * t))).tsum_eq]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, Real.cos_zero]
  rw [Real.cos_two_mul]
  ring

/-- The source and complete arithmetic work at shift six obey the
reduced Gamma budget, with analytic multiplicity retained explicitly. -/
theorem zetaThreePhase_stechkin_source_add_primeWork_le
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) :
    4 * (analyticZetaZeroMultiplicity rho : ℝ) / 7 - 1 / 2 +
      (1 - rho.1.re) * (∑' m : ℕ, zetaStechkinPrimeWeight (1 + 6 * (1 - rho.1.re)) m *
        phaseContactKernel zetaThreePhaseFamily (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + 6 * (1 - rho.1.re))) *
        (3 * (1 + Real.log (1 + 6 * (1 - rho.1.re))) +
          5 * (1 + Real.log (1 + 6 * (1 - rho.1.re) + |rho.1.im|)) + Real.log 2) +
        30 * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phase_shifted_source_add_primeWork_le_stechkin_split
    zetaThreePhaseFamily_nonneg family_summable family_log_summable rho hρ
    (κ := 6) (by norm_num)
  rw [family_oscillatoryMass, family_logMass] at h
  norm_num [phaseShiftSource, zetaThreePhaseFamily] at h
  convert h using 1

/-- A simple rational lower bound on the retained Stechkin coefficient
is uniform on every closed Euler sampling line. -/
theorem four_ninths_le_zetaStechkinWeight {σ : ℝ} (hσ : 1 ≤ σ) :
    (4 / 9 : ℝ) ≤ zetaStechkinWeight σ := by
  have h5 : 0 < Real.sqrt 5 := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hroot : Real.sqrt 5 ≤ 9 / 4 := by nlinarith
  have h : (4 / 9 : ℝ) ≤ 1 / Real.sqrt 5 := (le_div_iff₀ h5).mpr (by nlinarith)
  exact h.trans (classical_le_zetaStechkinWeight hσ)

/-- The explicit edge margin certified by the three-height Stechkin
contradiction. -/
def zetaStechkinZeroMargin (t : ℝ) : ℝ := 1 / (64 * localZetaLogHeight t)

/-- The certified margin is strictly positive at every real height. -/
theorem zetaStechkinZeroMargin_pos (t : ℝ) : 0 < zetaStechkinZeroMargin t := by
  have h := three_lt_localZetaLogHeight t
  unfold zetaStechkinZeroMargin
  positivity

/-- Every genuine zero above absolute height one stays strictly farther
from one than the displayed reciprocal-logarithm margin. All arithmetic
and analytic premises of the source inequality are discharged. -/
theorem zetaStechkin_margin_lt_one_sub_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) : zetaStechkinZeroMargin rho.1.im < 1 - rho.1.re := by
  let d := 1 - rho.1.re
  let L := localZetaLogHeight rho.1.im
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hL : 3 < L := three_lt_localZetaLogHeight rho.1.im
  by_contra hn
  have hdm : d ≤ 1 / (64 * L) := le_of_not_gt hn
  have hprod : d * (64 * L) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 64 * L)).mp hdm
  have hdL : d * L ≤ 1 / 64 := by nlinarith
  have hdsmall : d ≤ 1 / 192 := by nlinarith [mul_pos hd (by linarith : 0 < L - 3)]
  have hρ : 1 / 2 < rho.1.re := by dsimp [d] at hdsmall; linarith
  have hσ : 1 ≤ 1 + 6 * d := by linarith
  have hσsmall : 1 + 6 * d ≤ 33 / 32 := by linarith
  have hgap := zetaThreePhase_stechkin_source_add_primeWork_le rho hρ
  change 4 * (analyticZetaZeroMultiplicity rho : ℝ) / 7 - 1 / 2 +
    d * (∑' m : ℕ, zetaStechkinPrimeWeight (1 + 6 * d) m *
      phaseContactKernel zetaThreePhaseFamily (rho.1.im * Real.log m)) ≤
    d * (1 - zetaStechkinWeight (1 + 6 * d)) *
      (3 * (1 + Real.log (1 + 6 * d)) +
        5 * (1 + Real.log (1 + 6 * d + |rho.1.im|)) + Real.log 2) +
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
  have hlogσ : Real.log (1 + 6 * d) ≤ 1 / 32 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + 6 * d)
    linarith
  have hlogy : Real.log (1 + 6 * d + |rho.1.im|) ≤ L := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hheight : 3 * (1 + Real.log (1 + 6 * d)) +
      5 * (1 + Real.log (1 + 6 * d + |rho.1.im|)) + Real.log 2 ≤
        (257 / 32 : ℝ) * L := by linarith
  have hheight' := mul_le_mul_of_nonneg_left hheight (mul_nonneg hd.le (sub_nonneg.mpr hc1))
  have hgamma : d * (1 - zetaStechkinWeight (1 + 6 * d)) *
      (3 * (1 + Real.log (1 + 6 * d)) +
        5 * (1 + Real.log (1 + 6 * d + |rho.1.im|)) + Real.log 2) ≤
        (1285 / 288 : ℝ) * (d * L) := by
    have hh := mul_le_mul_of_nonneg_right (show 1 - zetaStechkinWeight (1 + 6 * d) ≤ 5 / 9 by linarith)
      (show 0 ≤ d * ((257 / 32 : ℝ) * L) by positivity)
    nlinarith only [hheight', hh]
  have hy2 : 1 ≤ rho.1.im ^ 2 := by nlinarith [sq_abs rho.1.im]
  have hquad : 30 * d ^ 2 / rho.1.im ^ 2 ≤ (5 / 96 : ℝ) * (d * L) := by
    have hdiv := div_le_self (sq_nonneg d) hy2
    have hsmall := mul_le_mul_of_nonneg_left hdsmall hd.le
    have hLL := mul_le_mul_of_nonneg_left hL.le hd.le
    rw [mul_div_assoc]
    nlinarith
  nlinarith only [hgap, hm, hwork, hgamma, hquad, hdL]

/-- Genuine completion reflection gives the same margin from zero,
without changing the ordinate or analytic multiplicity. -/
theorem zetaStechkin_margin_lt_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) : zetaStechkinZeroMargin rho.1.im < rho.1.re := by
  have h := zetaStechkin_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im,
      Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add] using hy)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im,
    sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- The actual nontrivial zero lies strictly inside the improved
two-sided strip at every ordinate of absolute value at least one. -/
theorem nontrivialZetaZero_mem_stechkin_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Set.Ioo (zetaStechkinZeroMargin rho.1.im) (1 - zetaStechkinZeroMargin rho.1.im) :=
  ⟨zetaStechkin_margin_lt_re rho hy, by linarith [zetaStechkin_margin_lt_one_sub_re rho hy]⟩

/-- The certified margin is uniformly small, so its right-edge region
lies inside the positive half-plane. -/
theorem zetaStechkinZeroMargin_lt (t : ℝ) : zetaStechkinZeroMargin t < 1 / 192 := by
  have hL := three_lt_localZetaLogHeight t
  unfold zetaStechkinZeroMargin
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- The literal zeta function is nonzero throughout the new closed
right-edge region, at every absolute height at least one. -/
theorem riemannZeta_ne_zero_of_stechkin_margin {s : ℂ} (hy : 1 ≤ |s.im|)
    (hs : 1 - zetaStechkinZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [zetaStechkinZeroMargin_lt s.im]
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have hgap := zetaStechkin_margin_lt_one_sub_re rho hy
  change zetaStechkinZeroMargin s.im < 1 - s.re at hgap
  linarith

/-- The new explicit margin is strictly larger than the full previous
phase-contact margin at every height, not just its simpler corollary. -/
theorem phaseContactZeroMargin_lt_stechkin (t : ℝ) :
    phaseContactZeroMargin t < zetaStechkinZeroMargin t := by
  have hL := three_lt_localZetaLogHeight t
  unfold phaseContactZeroMargin zetaStechkinZeroMargin
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

end
end RiemannGaussian
