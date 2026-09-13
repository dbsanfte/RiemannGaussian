/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianScaledBandBudget
import RiemannGaussian.ZetaGaussianBandExclusion
import RiemannGaussian.ZetaLogLogZeroFree

/-!
# Explicit Gaussian zero exclusion with no upper height ceiling

Exact Gaussian scaling preserves the source-cost surplus for every positive
dilation `q ≥ 1`. Choosing the dilation from the actual enlarged logarithmic
height yields the explicit width `min (1/450000) (32/(45*log(|t|+2)))` for
all `|t| ≥ 1000000`. The complete prime responses and analytic costs remain
in the chain; the interior strip and RH remain open.
-/

namespace RiemannGaussian.ZetaGaussianAllHeight
noncomputable section
open ZetaGaussianScaledBandBudget GaussianFermiLaplaceOrder
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)

/-- A selected zero within the scaled width retains the complete source
at least `48000*q`, including multiplicity and the Poisson reserve. -/
theorem selected_source_lower {a₁ q : ℝ} (ha₁ : 79 / 250 ≤ a₁) (hq : 1 ≤ q)
    (ρ : NontrivialZetaZero) (hnear : 1 - ρ.1.re ≤ width q) :
    48000 * q ≤ a₁ * ((analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) +
      factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift q + halfWidth 9 (shift q) - ρ.1.re))) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  obtain ⟨hu, huu⟩ := width_bounds hq
  have hB := (gaussianScale_bounds hq).1
  have hη := halfWidth_pos 9 hx
  have hηl := (geometry hq).1
  have hd : 0 < 1 + shift q - ρ.1.re := by linarith [ρ.re_lt_one]
  have hdu : 1 + shift q - ρ.1.re ≤ shift q + width q := by linarith
  have hG : 152000 * q ≤ halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) :=
    (source_lower hq).trans (halfGaussian_antitone hB hdu)
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcot : Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2) ≤ 1 := by
    calc
      _ ≤ 16 * (GaussianStripProfile.shift + GaussianStripProfile.width) / (8 * (1 / 200 : ℝ) ^ 2) := by
        gcongr
        · linarith
        · norm_num [GaussianStripProfile.shift, GaussianStripProfile.width] at hxu huu ⊢
          linarith
      _ ≤ 1 := by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hbase : 151999 * q ≤ halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
      Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2) := by linarith
  have hweighted := mul_le_mul hm hbase (by positivity : (0 : ℝ) ≤ 151999 * q) (by linarith)
  have hreserve : 0 ≤ factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
      (1 + shift q + halfWidth 9 (shift q) - ρ.1.re)) := by
    have hden : 0 < 1 + shift q + halfWidth 9 (shift q) - ρ.1.re := by linarith
    unfold factor
    positivity
  have htotal : 151999 * q ≤ (analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) +
      factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift q + halfWidth 9 (shift q) - ρ.1.re)) := by nlinarith only [hweighted, hreserve]
  have h := mul_le_mul ha₁ htotal (by positivity : (0 : ℝ) ≤ 151999 * q) (by linarith)
  nlinarith only [h, hq]

/-- The full family cost is too small for a zero in the scaled strip,
at every dilation and every height satisfying its explicit linear constraint. -/
theorem family_margin {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (ha0 : a 0 ≤ 37 / 200) (ha1 : 79 / 250 ≤ a 1)
    (hW : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {q : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) (hL : scale ρ.1.im ≤ 320000 * q) :
    width q < 1 - ρ.1.re := by
  by_contra! hnear
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  have hx' : shift q ≤ delta 9 / 4 := hxu.trans
    (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width, delta, DerivativePowerExponents.alpha])
  have hline : DirichletPowerParameters.line 9 < ρ.1.re := by
    have hu : width q < delta 9 := (width_bounds hq).2.trans_lt
      (by norm_num [GaussianStripProfile.width, delta, DerivativePowerExponents.alpha])
    rw [delta_eq_one_sub_line] at hu
    linarith
  have h := gaussian_source_le_budget ha hs hp hω0 hω1 hω hlog 9 (by norm_num)
    (gaussianScale_bounds hq).1 hx hx' ρ (by linarith)
    (ZetaGaussianBandBudget.scale_lower ht) hline
  have hb := budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha)) hW hF hq ht hL
  have hl := selected_source_lower ha1 hq ρ hnear
  linarith

/-- The exact contact family supplies every premise of the scaled
zero exclusion theorem, independently of the dilation. -/
theorem scaled_margin {q : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) (hL : scale ρ.1.im ≤ 320000 * q) :
    width q < 1 - ρ.1.re := by
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
    ZetaExactPhaseAngularExclusion.mass_bounds.2 ZetaGaussianBandExclusion.exact_frequency_cost
    hq ρ ht hL

/-- A concrete dilation evaluated from the actual enlarged logarithmic height. -/
def dilation (t : ℝ) : ℝ := max 1 (scale t / 320000)

/-- The moving explicit width, with no upper height ceiling. -/
def explicitWidth (t : ℝ) : ℝ := width (dilation t)

/-- The actual height always meets the scaled theorem's precise constraint. -/
theorem scale_le_dilation (t : ℝ) : scale t ≤ 320000 * dilation t := by
  have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 320000)).mp
    (le_max_right 1 (scale t / 320000))
  simpa only [mul_comm, dilation] using h

/-- The complete dilation family excludes each actual zero above the
explicit starting height, with no unevaluated threshold. -/
theorem exact_margin (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    explicitWidth ρ.1.im < 1 - ρ.1.re :=
  scaled_margin (le_max_left _ _) ρ ht (scale_le_dilation ρ.1.im)

/-- Every explicit adaptive width is positive. -/
theorem explicitWidth_pos (t : ℝ) : 0 < explicitWidth t :=
  (width_bounds (le_max_left _ _)).1

/-- The adaptive width is an elementary explicit function at every
real ordinate, including the exact plateau-to-decay transition. -/
theorem explicitWidth_eq_min (t : ℝ) :
    explicitWidth t = min (1 / 450000) (32 / (45 * scale t)) := by
  have hL : 0 < scale t := Real.log_pos (by
    unfold ZetaNearOneLogProfile.height
    linarith [abs_nonneg t])
  by_cases hb : scale t ≤ 320000
  · have hq : scale t / 320000 ≤ 1 := (div_le_one (by norm_num)).mpr hb
    have hmin : (1 / 450000 : ℝ) ≤ 32 / (45 * scale t) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    rw [min_eq_left hmin]
    simp [explicitWidth, dilation, max_eq_left hq, width, GaussianStripProfile.width]
  · have hq : 1 ≤ scale t / 320000 := (le_div_iff₀ (by norm_num)).mpr (by linarith)
    have hmin : 32 / (45 * scale t) ≤ (1 / 450000 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    rw [explicitWidth, dilation, max_eq_right hq, min_eq_right hmin]
    unfold width GaussianStripProfile.width
    field_simp
    ring

/-- The previous full-width band is contained with precisely its
original width, including its logarithmic upper endpoint. -/
theorem explicitWidth_eq_plateau {t : ℝ} (hL : scale t ≤ 320000) :
    explicitWidth t = 1 / 450000 := by
  have hq : scale t / 320000 ≤ 1 := (div_le_one (by norm_num)).mpr hL
  simp [explicitWidth, dilation, max_eq_left hq, width, GaussianStripProfile.width]

/-- Literal zeta nonvanishing holds on the adaptive closed right edge
at every height above one million. -/
theorem nonvanishing (s : ℂ) (ht : 1000000 ≤ |s.im|)
    (hσ : 1 - explicitWidth s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num at ht
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht
  let ρ : NontrivialZetaZero := ⟨s, hz, hn, hs1⟩
  have h := exact_margin ρ ht
  change explicitWidth s.im < 1 - s.re at h
  linarith

/-- Reflection yields both strict edges of the adaptive zero-free strip. -/
theorem exact_strip (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    explicitWidth ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - explicitWidth ρ.1.im := by
  have hr := exact_margin ρ ht
  have hl := exact_margin (NontrivialZetaZero.conjugatePartner ρ)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using ht)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im, sub_neg_eq_add,
    zero_add] at hl
  constructor <;> linarith

/-- Every genuine nontrivial zero above the explicit starting height
lies in the stated elementary strip, with no upper height restriction. -/
theorem exact_strip_min (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    min (1 / 450000) (32 / (45 * scale ρ.1.im)) < ρ.1.re ∧
      ρ.1.re < 1 - min (1 / 450000) (32 / (45 * scale ρ.1.im)) := by
  simpa only [explicitWidth_eq_min] using exact_strip ρ ht

/-- The explicit unbounded-height curve and the existing eventual
region give their larger width on every overlap. The latter threshold
retains its coefficient dependence and is not numerically evaluated. -/
theorem union_with_eventual {A : ℝ} (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      1000000 ≤ |ρ.1.im| →
      max (ZetaLogLogWidth.width A |ρ.1.im|) (explicitWidth ρ.1.im) < ρ.1.re ∧
        ρ.1.re < 1 - max (ZetaLogLogWidth.width A |ρ.1.im|) (explicitWidth ρ.1.im) := by
  obtain ⟨T, hT, hz⟩ := ZetaLogLogZeroFree.exists_eventual_strip hA hAlim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ ht
  obtain ⟨ha, hb⟩ := hz ρ hρ
  obtain ⟨hc, hd⟩ := exact_strip ρ ht
  refine ⟨max_lt ha hc, ?_⟩
  have hm : max (ZetaLogLogWidth.width A |ρ.1.im|) (explicitWidth ρ.1.im) <
      1 - ρ.1.re := max_lt (by linarith) (by linarith)
  linarith

end
end RiemannGaussian.ZetaGaussianAllHeight
