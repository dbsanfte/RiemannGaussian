/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianBandBudget
import RiemannGaussian.ZetaExactPhaseAngularExclusion
import RiemannGaussian.GaussianFermiProfileSurplus

/-!
# Actual zero exclusion on an explicit Gaussian height band

The entire Gaussian source exceeds the complete cost by a rational margin.
The result first applies to every admissible countable phase family with
the coarse coefficient enclosures, then to the existing exact contact
family with all hypotheses discharged. It excludes literal zeta zeros;
no numerical experiment, boundary limit or prime-sum premise is assumed.
-/

namespace RiemannGaussian.ZetaGaussianBandExclusion
noncomputable section
open GaussianStripProfile GaussianFermiLaplaceOrder ZetaGaussianBandBudget
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)

/-- Any zero within the proposed width contributes at least 48000,
including its true multiplicity and its favorable Poisson reserve. -/
theorem selected_source_lower {a₁ : ℝ} (ha₁ : 79 / 250 ≤ a₁)
    (ρ : NontrivialZetaZero) (hnear : 1 - ρ.1.re ≤ width) :
    48000 ≤ a₁ * ((analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian gaussianScale (1 + shift - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift - ρ.1.re) / (8 * halfWidth 9 shift ^ 2)) +
      factor 9 gaussianScale shift * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift + halfWidth 9 shift - ρ.1.re))) := by
  have hx : 0 < shift := by norm_num [shift, width]
  have hB : 0 < gaussianScale := by norm_num [gaussianScale, width]
  have hη := halfWidth_pos 9 hx
  have hηl : 1 / 200 ≤ halfWidth 9 shift := by
    norm_num [halfWidth, delta, DerivativePowerExponents.alpha, shift, width]
  have hd : 0 < 1 + shift - ρ.1.re := by linarith [ρ.re_lt_one]
  have hdu : 1 + shift - ρ.1.re ≤ shift + width := by linarith
  have hG : 152000 ≤ halfGaussian gaussianScale (1 + shift - ρ.1.re) :=
    source_lower.trans (halfGaussian_antitone (by norm_num [gaussianScale, width]) hdu)
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcot : Real.pi ^ 2 * (1 + shift - ρ.1.re) / (8 * halfWidth 9 shift ^ 2) ≤ 1 := by
    calc
      _ ≤ 16 * (shift + width) / (8 * (1 / 200 : ℝ) ^ 2) := by gcongr; norm_num [shift, width]
      _ ≤ 1 := by norm_num [shift, width]
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hbase : 151999 ≤ halfGaussian gaussianScale (1 + shift - ρ.1.re) -
      Real.pi ^ 2 * (1 + shift - ρ.1.re) / (8 * halfWidth 9 shift ^ 2) := by linarith
  have hweighted := mul_le_mul hm hbase (by norm_num : (0 : ℝ) ≤ 151999) (by linarith)
  have hreserve : 0 ≤ factor 9 gaussianScale shift * ((analyticZetaZeroMultiplicity ρ : ℝ) /
      (1 + shift + halfWidth 9 shift - ρ.1.re)) := by
    have hden : 0 < 1 + shift + halfWidth 9 shift - ρ.1.re := by linarith
    unfold factor
    positivity
  have htotal : 151999 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian gaussianScale (1 + shift - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift - ρ.1.re) / (8 * halfWidth 9 shift ^ 2)) +
      factor 9 gaussianScale shift * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift + halfWidth 9 shift - ρ.1.re)) := by nlinarith only [hweighted, hreserve]
  have h := mul_le_mul ha₁ htotal (by norm_num : (0 : ℝ) ≤ 151999) (by linarith)
  linarith

/-- The full arithmetic and analytic cost is strictly too small for an
actual zero within the target width, for every family in the coarse class. -/
theorem family_margin {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (ha0 : a 0 ≤ 37 / 200) (ha1 : 79 / 250 ≤ a 1)
    (hW : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) (hL : scale ρ.1.im ≤ 320000) :
    width < 1 - ρ.1.re := by
  by_contra! hnear
  have hx : 0 < shift := by norm_num [shift, width]
  have hx' : shift ≤ delta 9 / 4 := by norm_num [shift, width, delta, DerivativePowerExponents.alpha]
  have hline : DirichletPowerParameters.line 9 < ρ.1.re := by
    have hu : width < delta 9 := by norm_num [width, delta, DerivativePowerExponents.alpha]
    rw [delta_eq_one_sub_line] at hu
    linarith
  have h := gaussian_source_le_budget ha hs hp hω0 hω1 hω hlog 9 (by norm_num)
    (by norm_num [gaussianScale, width] : 0 < gaussianScale) hx hx' ρ (by linarith)
    (scale_lower ht) hline
  have hb := budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha)) hW hF ht hL
  have hl := selected_source_lower ha1 ρ hnear
  linarith

/-- The existing exact contact family has the needed logarithmic cost
in the general frequency convention, retaining every high frequency. -/
theorem exact_frequency_cost : frequencyCost phaseContactExactFamily (fun n => (n : ℝ)) ≤ 1 / 4 := by
  unfold frequencyCost
  rw [ZetaExactPhaseAngularExclusion.exact_log_summable.tsum_eq_zero_add]
  simpa [tail, phaseLogFrequencyMass] using phaseContactExactFamily_logFrequencyMass_le

/-- Every actual nontrivial zero in the explicit height band is strictly
farther than 1/450000 from the right edge, with all family premises proved. -/
theorem exact_margin (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hL : scale ρ.1.im ≤ 320000) : (1 / 450000 : ℝ) < 1 - ρ.1.re := by
  have h0 : phaseContactExactFamily 0 = phaseContactExactCoefficients 0 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
  have h1 : phaseContactExactFamily 1 = phaseContactExactCoefficients 1 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 1
  exact family_margin phaseContactExactFamily_nonneg ZetaExactPhaseAngularExclusion.exact_summable
    phaseContactExactFamily_kernel_nonneg (by norm_num) (by norm_num)
    (fun n hn => by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    ZetaExactPhaseAngularExclusion.exact_log_summable
    (by rw [h0]; exact GaussianFermiProfileSurplus.exact_constant_upper)
    (by rw [h1]; exact GaussianFermiProfileSurplus.exact_first_lower)
    ZetaExactPhaseAngularExclusion.mass_bounds.2 exact_frequency_cost ρ ht hL

/-- Literal zeta nonvanishing on the closed right edge of the band,
including every exceptional-point and actual-zero membership check. -/
theorem nonvanishing (s : ℂ) (ht : 1000000 ≤ |s.im|) (hL : scale s.im ≤ 320000)
    (hσ : 1 - 1 / 450000 ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num at ht
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht
  let ρ : NontrivialZetaZero := ⟨s, hz, hn, hs1⟩
  have h := exact_margin ρ ht hL
  change (1 / 450000 : ℝ) < 1 - s.re at h
  linarith

/-- Reflection transports the explicit band to both genuine strip edges
without changing its height interval or strict endpoint convention. -/
theorem exact_strip (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hL : scale ρ.1.im ≤ 320000) :
    (1 / 450000 : ℝ) < ρ.1.re ∧ ρ.1.re < 1 - 1 / 450000 := by
  have hr := exact_margin ρ ht hL
  have hl := exact_margin (NontrivialZetaZero.conjugatePartner ρ)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using ht)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using hL)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

end
end RiemannGaussian.ZetaGaussianBandExclusion
