/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianRetainedCost
import RiemannGaussian.ZetaGaussianAllHeight

/-!
# A wider explicit Gaussian region from the complete retained cost

The original Gaussian source and exact phase family are unchanged. Keeping
the fixed and log-log costs separate gives width
`min (1/450000) (221/(250*(L + 2052*log L + 30240)))`, where
`L = log(abs(t)+2)`, for every `abs(t) >= 1000000`.

This contains the previous explicit curve and is strictly wider when
`L > 320000`. It retains the existing eventual log-log component. The
interior signed arithmetic bound and RH remain open.
-/

namespace RiemannGaussian.ZetaGaussianRetainedRegion
noncomputable section
open Complex ZetaGaussianScaledBandBudget GaussianFermiLaplaceOrder
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)

/-- The complete non-Gaussian cost in logarithmic-height coordinates. -/
def heightCost (L : ℝ) : ℝ := L + 2052 * Real.log L + 30240

/-- The retained cost is strictly positive throughout the working domain. -/
theorem heightCost_pos {L : ℝ} (hL : 1 ≤ L) : 0 < heightCost L := by
  have hl := Real.log_nonneg hL
  unfold heightCost
  positivity

/-- The retained cost increases with logarithmic height on its working domain. -/
theorem heightCost_mono {L H : ℝ} (hL : 1 ≤ L) (hLH : L ≤ H) :
    heightCost L ≤ heightCost H := by
  have hl := Real.log_le_log (by linarith : 0 < L) hLH
  unfold heightCost
  linarith

/-- Every eligible family excludes a zero whenever the complete retained
cost fits the dilation, with all prime and analytic premises discharged. -/
theorem family_margin {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (ha0 : a 0 ≤ 37 / 200) (ha1 : 79 / 250 ≤ a 1)
    (hW : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {q : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) (hcost : heightCost (scale ρ.1.im) ≤ 397800 * q) :
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
  have hb := ZetaGaussianRetainedCost.budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha)) hW hF hq ht
  have hl := ZetaGaussianAllHeight.selected_source_lower ha1 hq ρ hnear
  unfold heightCost at hcost
  linarith

/-- The existing exact family supplies the new cost test without any
coefficient search or change of its phase positivity theorem. -/
theorem scaled_margin {q : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) (hcost : heightCost (scale ρ.1.im) ≤ 397800 * q) :
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
    hq ρ ht hcost

/-- The dilation pays the actual fixed and logarithmic costs at each height. -/
def dilation (t : ℝ) : ℝ := max 1 (heightCost (scale t) / 397800)

/-- The improved explicit physical width. -/
def explicitWidth (t : ℝ) : ℝ := width (dilation t)

/-- The chosen dilation meets the full cost constraint at every height. -/
theorem cost_le_dilation (t : ℝ) : heightCost (scale t) ≤ 397800 * dilation t := by
  have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 397800)).mp
    (le_max_right 1 (heightCost (scale t) / 397800))
  simpa only [mul_comm, dilation] using h

/-- The entire explicit curve excludes every actual zero in its right band. -/
theorem exact_margin (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    explicitWidth ρ.1.im < 1 - ρ.1.re :=
  scaled_margin (le_max_left _ _) ρ ht (cost_le_dilation ρ.1.im)

/-- The improved width remains positive at every real height. -/
theorem explicitWidth_pos (t : ℝ) : 0 < explicitWidth t :=
  (width_bounds (le_max_left _ _)).1

/-- The elementary formula keeps the complete non-Gaussian denominator. -/
theorem explicitWidth_eq_min {t : ℝ} (hL : 1 ≤ scale t) :
    explicitWidth t = min (1 / 450000) (221 / (250 * heightCost (scale t))) := by
  have hC := heightCost_pos hL
  by_cases hb : heightCost (scale t) ≤ 397800
  · have hq : heightCost (scale t) / 397800 ≤ 1 := (div_le_one (by norm_num)).mpr hb
    have hmin : (1 / 450000 : ℝ) ≤ 221 / (250 * heightCost (scale t)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    rw [min_eq_left hmin]
    simp [explicitWidth, dilation, max_eq_left hq, width, GaussianStripProfile.width]
  · have hq : 1 ≤ heightCost (scale t) / 397800 := (le_div_iff₀ (by norm_num)).mpr (by linarith)
    have hmin : 221 / (250 * heightCost (scale t)) ≤ (1 / 450000 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    rw [explicitWidth, dilation, max_eq_right hq, min_eq_right hmin]
    unfold width GaussianStripProfile.width
    field_simp
    ring

private theorem log_le_thirteen {L : ℝ} (hL : 0 < L) (hLu : L ≤ 340000) : Real.log L ≤ 13 := by
  apply (Real.log_le_iff_le_exp hL).mpr
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
    (show (27 / 10 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 13
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

/-- The full-width plateau now includes enlarged logarithmic height 340000. -/
theorem explicitWidth_eq_plateau {t : ℝ} (hL : 1 ≤ scale t) (hLu : scale t ≤ 340000) :
    explicitWidth t = 1 / 450000 := by
  have hl := log_le_thirteen (by linarith : 0 < scale t) hLu
  have hc : heightCost (scale t) ≤ 397800 := by unfold heightCost; linarith
  have hq : heightCost (scale t) / 397800 ≤ 1 := (div_le_one (by norm_num)).mpr hc
  simp [explicitWidth, dilation, max_eq_left hq, width, GaussianStripProfile.width]

/-- Beyond the former transition, the full retained cost is below six
fifths of logarithmic height; no asymptotic threshold is hidden. -/
theorem heightCost_le_six_fifths {L : ℝ} (hL : 320000 ≤ L) : heightCost L ≤ (6 / 5) * L := by
  have hLp : 0 < L := by linarith
  have hl := Real.log_le_sub_one_of_pos (show 0 < L / 320000 by positivity)
  rw [Real.log_div hLp.ne' (by norm_num : (320000 : ℝ) ≠ 0)] at hl
  have hc := log_le_thirteen (by norm_num : (0 : ℝ) < 320000) (by norm_num : (320000 : ℝ) ≤ 340000)
  unfold heightCost
  linarith

/-- The required dilation is strictly smaller above the old transition. -/
theorem dilation_lt_previous {t : ℝ} (hL : 320000 < scale t) :
    dilation t < ZetaGaussianAllHeight.dilation t := by
  have hq : 1 < scale t / 320000 := (lt_div_iff₀ (by norm_num)).mpr (by simpa only [one_mul] using hL)
  rw [ZetaGaussianAllHeight.dilation, max_eq_right hq.le, dilation]
  apply max_lt hq
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 397800) (by norm_num : (0 : ℝ) < 320000)).mpr
  have hc := heightCost_le_six_fifths hL.le
  linarith

/-- The new explicit width is strictly larger above the former transition. -/
theorem previous_width_lt {t : ℝ} (hL : 320000 < scale t) :
    ZetaGaussianAllHeight.explicitWidth t < explicitWidth t := by
  have hq := dilation_lt_previous hL
  have hqp : 0 < dilation t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  unfold explicitWidth ZetaGaussianAllHeight.explicitWidth width
  exact div_lt_div_of_pos_left (by norm_num [GaussianStripProfile.width]) hqp hq

/-- The complete previous explicit region is contained in the new one. -/
theorem previous_width_le {t : ℝ} (hL : 1 ≤ scale t) :
    ZetaGaussianAllHeight.explicitWidth t ≤ explicitWidth t := by
  by_cases hb : scale t ≤ 320000
  · rw [ZetaGaussianAllHeight.explicitWidth_eq_plateau hb,
      explicitWidth_eq_plateau hL (by linarith)]
  · exact (previous_width_lt (by linarith)).le

/-- Literal zeta nonvanishing includes the closed improved right edge. -/
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

/-- Reflection retains both strict edges of the improved zero-free strip. -/
theorem exact_strip (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    explicitWidth ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - explicitWidth ρ.1.im := by
  have hr := exact_margin ρ ht
  have hl := exact_margin (NontrivialZetaZero.conjugatePartner ρ)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using ht)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im, sub_neg_eq_add,
    zero_add] at hl
  constructor <;> linarith

/-- The genuine zeta zeros lie in the stated explicit elementary strip. -/
theorem exact_strip_min (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    min (1 / 450000) (221 / (250 * heightCost (scale ρ.1.im))) < ρ.1.re ∧
      ρ.1.re < 1 - min (1 / 450000) (221 / (250 * heightCost (scale ρ.1.im))) := by
  simpa only [explicitWidth_eq_min (ZetaGaussianBandBudget.scale_lower ht)] using exact_strip ρ ht

/-- The existing eventual log-log region combines with the improved
explicit curve by the larger width, preserving both height conditions. -/
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
end RiemannGaussian.ZetaGaussianRetainedRegion
