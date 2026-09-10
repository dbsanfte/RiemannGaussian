/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCenteredEulerZeroFree
import RiemannGaussian.ZetaPhaseBinomialScale

/-!+# The exact phase family with the global half-logarithm allowance

The existing exact optimizer and the full Stechkin comparison give a
source-beating inequality on the closed edge region of width
`1/(12*log(abs(t)+22))`. This doubles the preceding proved width at every
height. The exact signed prime work, all phase coefficients and the full
analytic multiplicity remain available before the independent arithmetic
floor is used. No new coefficients are selected or fitted.

The interior right-half-strip bound remains open. This is an actual partial
zero exclusion, not an RH proof or a claim of a best published region.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical Topology

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

private theorem exact_log_summable :
    Summable (fun n : ℕ => phaseContactExactFamily n * Real.log n) :=
  (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
    (fun n => Real.log n)).summable

private theorem exact_zero_le_one : phaseContactExactFamily 0 ≤ 1 := by
  have h := phaseContactExactFamily_hasSum_budget.summable.le_tsum 0
    (fun n _ => mul_nonneg (by unfold phaseContactCost; split_ifs <;> positivity)
      (phaseContactExactFamily_nonneg n))
  rw [phaseContactExactFamily_hasSum_budget.tsum_eq] at h
  simpa [phaseContactCost] using h

/-- The exact optimizer pays the smaller global completion allowance,
with its full signed prime work and excess analytic multiplicity retained. -/
theorem phaseContactExact_half_log_source_add_primeWork_le
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) :
    phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
          phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((phaseContactExactFamily 0 * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) +
          phaseOscillatoryMass phaseContactExactFamily *
            Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) +
          phaseLogFrequencyMass phaseContactExactFamily) / 2) +
      (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
        (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phase_shifted_source_add_primeWork_le_stechkin_half_log
    phaseContactExactFamily_nonneg exact_summable exact_log_summable rho hρ
    (κ := 13 / 4) (by norm_num)
  have he : phaseShiftSource (phaseContactExactFamily 0)
      (phaseContactExactFamily 1 * (analyticZetaZeroMultiplicity rho : ℝ)) (13 / 4) =
      phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) := by
    rw [← phaseContactExactFamily_source]
    unfold phaseShiftSource phaseContactSource
    ring
  rwa [he] at h

/-- Rational bounds for the exact family's source and complete frequency
cost give a global budget; the signed arithmetic work is still present. -/
theorem phaseContactExact_half_log_zero_budget
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) * (∑' m : ℕ,
      zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) +
          (61 / 100 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) +
          1 / 4) / 2) + (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hσ : 1 ≤ 1 + (13 / 4 : ℝ) * (1 - rho.1.re) := by linarith
  have hlogσ := Real.log_nonneg hσ
  have hlogy : 0 ≤ Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg rho.1.im])
  have h0 := mul_le_mul_of_nonneg_right exact_zero_le_one hlogσ
  have hA := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le hlogy
  have hB := phaseContactExactFamily_logFrequencyMass_le
  have hc : 0 ≤ 1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) :=
    sub_nonneg.mpr (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hH := mul_le_mul_of_nonneg_left
    (show (phaseContactExactFamily 0 * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) +
      phaseOscillatoryMass phaseContactExactFamily *
        Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) +
      phaseLogFrequencyMass phaseContactExactFamily) / 2 ≤
      (Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) +
        (61 / 100 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) + 1 / 4) / 2
      by linarith) (mul_nonneg hd.le hc)
  have hP := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 by positivity)
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hmult : 0 ≤ (4 / 17 : ℝ) * phaseContactExactFamily 1 *
      ((analyticZetaZeroMultiplicity rho : ℝ) - 1) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (phaseContactExactFamily_nonneg 1)) (by linarith)
  have h := phaseContactExact_half_log_source_add_primeWork_le rho hρ
  simp only [div_eq_mul_inv] at hP h ⊢
  nlinarith only [h, hH, hP, hmult, phaseContactExactRoot_source_lower]

/-- The existing binomial prime-power reserve transfers to the complete
Stechkin work with its exact factor and sampling scale. -/
theorem phaseContactExact_stechkin_binomial_floor {σ : ℝ}
    (hσ : 1 < σ) (hσu : σ ≤ 5 / 4) (y : ℝ) :
    (1 - zetaStechkinWeight σ) * ((1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2)) ≤
      ∑' m : ℕ, zetaStechkinPrimeWeight σ m *
        phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  have hf := phaseContactExact_binomial_scaled_arithmetic_floor hσ hσu y
  have ht := (zetaPhase_stechkin_primeWork_bounds (ω := fun n => (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable
    (fun t => by simpa only [zetaPhaseKernel_natCast] using phaseContactExactFamily_kernel_nonneg t)
    hσ y).1
  simp only [zetaPhaseKernel_natCast] at ht
  exact (mul_le_mul_of_nonneg_left hf
    (sub_nonneg.mpr (zetaStechkinWeight_mem_Ioo hσ.le).2.le)).trans ht

/-- The actual source keeps a strictly positive arithmetic reserve on
the full range where the previously proved binomial scale is available. -/
theorem phaseContactExact_half_log_scaled_zero_source
    (rho : NontrivialZetaZero) (hρ : 12 / 13 ≤ rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) *
      (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((1 / 40 : ℝ) * Real.exp (-13 * (1 - rho.1.re) * Real.log 2)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) +
          (61 / 100 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) +
          1 / 4) / 2) + (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hf := phaseContactExact_stechkin_binomial_floor
    (by linarith : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re))
    (by linarith : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4) rho.1.im
  rw [show -4 * (1 + (13 / 4 : ℝ) * (1 - rho.1.re) - 1) * Real.log 2 =
    -13 * (1 - rho.1.re) * Real.log 2 by ring] at hf
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  have h := phaseContactExact_half_log_zero_budget rho (by linarith)
  nlinarith only [hm, h]

/-- The new all-height edge width supplied by the exact phase family. -/
def zetaPhaseHalfLogZeroMargin (t : ℝ) : ℝ := 1 / (12 * localZetaLogHeight t)

/-- The phase-family margin is strictly positive at every ordinate. -/
theorem zetaPhaseHalfLogZeroMargin_pos (t : ℝ) : 0 < zetaPhaseHalfLogZeroMargin t := by
  have h := three_lt_localZetaLogHeight t
  unfold zetaPhaseHalfLogZeroMargin
  positivity

/-- Every actual zero stays strictly outside the wider right-edge region.
The exact positive phase kernel gives the independent arithmetic sign and
the complete analytic allowance is strictly below the retained source. -/
theorem zetaPhaseHalfLog_margin_lt_one_sub_re (rho : NontrivialZetaZero) :
    zetaPhaseHalfLogZeroMargin rho.1.im < 1 - rho.1.re := by
  let d := 1 - rho.1.re
  let L := localZetaLogHeight rho.1.im
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hL : 3 < L := three_lt_localZetaLogHeight rho.1.im
  by_contra hn
  have hdm : d ≤ 1 / (12 * L) := le_of_not_gt hn
  have hp : d * (12 * L) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 12 * L)).mp hdm
  have hdL : d * L ≤ 1 / 12 := by nlinarith
  have hdsmall : d ≤ 1 / 36 := by nlinarith [mul_pos hd (by linarith : 0 < L - 3)]
  have hρ : 1 / 2 < rho.1.re := by dsimp [d] at hdsmall; linarith
  have hσ : 1 ≤ 1 + (13 / 4 : ℝ) * d := by linarith
  have h := phaseContactExact_half_log_zero_budget rho hρ
  change (11 / 625 : ℝ) + d * (∑' m : ℕ,
    zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * d) m *
      phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) ≤
    d * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * d)) *
      ((Real.log (1 + (13 / 4 : ℝ) * d) +
        (61 / 100 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) + 1 / 4) / 2) +
      (793 / 400 : ℝ) * d ^ 2 / rho.1.im ^ 2 at h
  have hwork : 0 ≤ d * (∑' m : ℕ,
      zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * d) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) := by
    apply mul_nonneg hd.le
    exact tsum_nonneg (fun m => mul_nonneg (zetaStechkinPrimeWeight_nonneg hσ m)
      (phaseContactExactFamily_kernel_nonneg _))
  have hlogσ : Real.log (1 + (13 / 4 : ℝ) * d) ≤ 13 / 144 := by
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (13 / 4 : ℝ) * d)
    linarith
  have hlogy : Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) ≤ L := by
    apply Real.log_le_log (by positivity)
    linarith
  have hH : (Real.log (1 + (13 / 4 : ℝ) * d) +
      (61 / 100 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) + 1 / 4) / 2 ≤
      (181 / 500 : ℝ) * L := by linarith
  have hc := four_ninths_le_zetaStechkinWeight hσ
  have hc1 := (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hHm := mul_le_mul_of_nonneg_left hH (mul_nonneg hd.le (sub_nonneg.mpr hc1))
  have hcm := mul_le_mul_of_nonneg_right
    (show 1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * d) ≤ 5 / 9 by linarith)
    (show 0 ≤ d * ((181 / 500 : ℝ) * L) by positivity)
  have hgamma : d * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * d)) *
      ((Real.log (1 + (13 / 4 : ℝ) * d) +
        (61 / 100 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) + 1 / 4) / 2) ≤
      (181 / 900 : ℝ) * (d * L) := by nlinarith only [hHm, hcm]
  have hy2 : 3 ≤ rho.1.im ^ 2 := (nontrivialZetaZero_im_sq_gt_three rho).le
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg d) (by norm_num : (0 : ℝ) < 3) hy2
  have hsmall := mul_le_mul_of_nonneg_left hdsmall hd.le
  have hLL := mul_le_mul_of_nonneg_left hL.le hd.le
  have hquad : (793 / 400 : ℝ) * d ^ 2 / rho.1.im ^ 2 ≤
      (793 / 129600 : ℝ) * (d * L) := by
    rw [mul_div_assoc]
    nlinarith only [hdiv, hsmall, hLL]
  nlinarith only [h, hwork, hgamma, hquad, hdL]

/-- Critical reflection supplies the matching left-edge margin at the
same ordinate, with no height restriction. -/
theorem zetaPhaseHalfLog_margin_lt_re (rho : NontrivialZetaZero) :
    zetaPhaseHalfLogZeroMargin rho.1.im < rho.1.re := by
  have h := zetaPhaseHalfLog_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every actual nontrivial zero lies strictly inside the stronger
two-sided strip, at every ordinate and with no open arithmetic premise. -/
theorem nontrivialZetaZero_mem_phase_half_log_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Set.Ioo (zetaPhaseHalfLogZeroMargin rho.1.im)
      (1 - zetaPhaseHalfLogZeroMargin rho.1.im) :=
  ⟨zetaPhaseHalfLog_margin_lt_re rho, by linarith [zetaPhaseHalfLog_margin_lt_one_sub_re rho]⟩

/-- The margin stays inside the positive half-plane at every real height. -/
theorem zetaPhaseHalfLogZeroMargin_lt (t : ℝ) : zetaPhaseHalfLogZeroMargin t < 1 / 36 := by
  have hL := three_lt_localZetaLogHeight t
  unfold zetaPhaseHalfLogZeroMargin
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- Literal zeta is nonzero throughout the new closed right-edge region,
at all heights; the pole is explicitly excluded. -/
theorem riemannZeta_ne_zero_of_phase_half_log_margin {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - zetaPhaseHalfLogZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [zetaPhaseHalfLogZeroMargin_lt s.im]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := (nontrivialZetaZero_mem_phase_half_log_strip rho).2
  change s.re < 1 - zetaPhaseHalfLogZeroMargin s.im at h
  linarith

/-- The exact phase family doubles the preceding half-logarithm margin
uniformly over all real heights. -/
theorem zetaPhaseHalfLogZeroMargin_eq_twice (t : ℝ) :
    zetaPhaseHalfLogZeroMargin t = 2 * zetaHalfLogZeroMargin t := by
  unfold zetaPhaseHalfLogZeroMargin zetaHalfLogZeroMargin
  ring

/-- The additional excluded edge width is strictly positive everywhere. -/
theorem zetaHalfLogZeroMargin_lt_phase (t : ℝ) :
    zetaHalfLogZeroMargin t < zetaPhaseHalfLogZeroMargin t := by
  rw [zetaPhaseHalfLogZeroMargin_eq_twice]
  linarith [zetaHalfLogZeroMargin_pos t]

end
end RiemannGaussian
