/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianAllHeight
import RiemannGaussian.ZetaSignedZeroSeparation

/-!
# Retaining multiplicity in the explicit Gaussian exclusion

The complete source contains the actual zero multiplicity. Keeping that
factor gives a larger excluded boundary layer for multiple zeros, with
the same explicit height range and complete arithmetic budget. The
unconditional region for all zeros is unchanged; the signed prime-tail
bound needed for RH remains open.
-/

namespace RiemannGaussian.ZetaGaussianMultiplicityDepth
noncomputable section
open ZetaGaussianScaledBandBudget GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)

/-- A linear lower bound for the complete scaled Gaussian transform,
valid at every real normalized damping. -/
theorem scaled_tangent_lower {q : ℝ} (hq : 1 ≤ q) (z : ℝ) :
    q * (199350 - 56250 * z) ≤ halfGaussian (gaussianScale q) (width q * z) := by
  have hq0 : 0 < q := by linarith
  have hw := (width_bounds hq).1
  have hs : (443 / 1000 : ℝ) ≤ Real.sqrt (Real.pi / 4) / 2 := by
    have he := Real.sq_sqrt (show 0 ≤ Real.pi / 4 by positivity)
    nlinarith [Real.pi_gt_d2, Real.sqrt_nonneg (Real.pi / 4)]
  have ht := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 4) z
  have hscale := halfGaussian_scale hw 4 z
  have hB : 4 * width q ^ 2 = gaussianScale q := by
    unfold width gaussianScale GaussianStripProfile.gaussianScale
    ring
  rw [hB, mul_comm z] at hscale
  have he : width q * (q * (199350 - 56250 * z)) = 443 / 1000 - z / 8 := by
    unfold width GaussianStripProfile.width
    field_simp
    ring
  have hl : width q * (q * (199350 - 56250 * z)) ≤
      width q * halfGaussian (gaussianScale q) (width q * z) := by
    rw [he, hscale]
    norm_num only at ht
    linarith
  exact (mul_le_mul_iff_right₀ hw).mp hl

/-- The full source still exceeds the old cost after the selected
depth is enlarged using its actual multiplicity. -/
theorem selected_source_lower {a₁ q : ℝ} (ha₁ : 79 / 250 ≤ a₁) (hq : 1 ≤ q)
    (ρ : NontrivialZetaZero)
    (hnear : 1 - ρ.1.re ≤
      (7 / 2 - 8 / (3 * (analyticZetaZeroMultiplicity ρ : ℝ))) * width q) :
    48000 * q ≤ a₁ * ((analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) +
      factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift q + halfWidth 9 (shift q) - ρ.1.re))) := by
  let m : ℝ := analyticZetaZeroMultiplicity ρ
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hm0 : 0 < m := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  obtain ⟨hw, hwu⟩ := width_bounds hq
  have hB := (gaussianScale_bounds hq).1
  have hη := halfWidth_pos 9 hx
  have hd : 0 < 1 + shift q - ρ.1.re := by linarith [ρ.re_lt_one]
  have hraw : 7 / 2 - 8 / (3 * m) ≤ (7 / 2 : ℝ) := sub_le_self _ (by positivity)
  have hshift : shift q = width q / 1000 := by
    unfold shift width GaussianStripProfile.shift
    ring
  have hdu : 1 + shift q - ρ.1.re ≤
      width q * (1 / 1000 + 7 / 2 - 8 / (3 * m)) := by
    change 1 - ρ.1.re ≤ (7 / 2 - 8 / (3 * m)) * width q at hnear
    rw [hshift]
    nlinarith only [hnear]
  have hG := (scaled_tangent_lower hq (1 / 1000 + 7 / 2 - 8 / (3 * m))).trans
    (halfGaussian_antitone hB hdu)
  have hGm := mul_le_mul_of_nonneg_left hG hm0.le
  have he : m * (q * (199350 - 56250 * (1 / 1000 + 7 / 2 - 8 / (3 * m)))) =
      q * ((9675 / 4 : ℝ) * m + 150000) := by
    field_simp
    ring
  rw [he] at hGm
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hdot : 1 + shift q - ρ.1.re ≤
      GaussianStripProfile.shift + 7 / 2 * GaussianStripProfile.width := by
    have hr := mul_le_mul_of_nonneg_right hraw hw.le
    change 1 - ρ.1.re ≤ (7 / 2 - 8 / (3 * m)) * width q at hnear
    nlinarith only [hnear, hr, hxu, hwu]
  have hcot : Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2) ≤ 1 := by
    calc
      _ ≤ 16 * (GaussianStripProfile.shift + 7 / 2 * GaussianStripProfile.width) /
          (8 * (1 / 200 : ℝ) ^ 2) := by
        gcongr
        · norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]
        · exact (geometry hq).1
      _ ≤ 1 := by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]
  have hc := mul_le_mul_of_nonneg_left hcot hm0.le
  have hmq : m ≤ q * m := by nlinarith only [mul_nonneg (sub_nonneg.mpr hq) hm0.le]
  have hbase : (152417 : ℝ) * q ≤ m *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) := by
    have hqm := mul_le_mul_of_nonneg_left hm hq0.le
    nlinarith only [hGm, hc, hmq, hqm, hq]
  have hreserve : 0 ≤ factor 9 (gaussianScale q) (shift q) * (m /
      (1 + shift q + halfWidth 9 (shift q) - ρ.1.re)) := by
    have hden : 0 < 1 + shift q + halfWidth 9 (shift q) - ρ.1.re := by linarith
    unfold factor
    positivity
  have htotal : (152417 : ℝ) * q ≤ m *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) +
      factor 9 (gaussianScale q) (shift q) * (m /
        (1 + shift q + halfWidth 9 (shift q) - ρ.1.re)) := by linarith
  have h := mul_le_mul ha₁ htotal (by positivity : (0 : ℝ) ≤ 152417 * q) (by linarith)
  change 48000 * q ≤ a₁ * (m * _ + _)
  nlinarith only [h, hq]

/-- The same complete phase-family budget excludes a multiplicity-dependent
boundary layer. No new arithmetic estimate is assumed. -/
theorem family_margin {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (ha0 : a 0 ≤ 37 / 200) (ha1 : 79 / 250 ≤ a 1)
    (hW : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {q : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) (hL : scale ρ.1.im ≤ 320000 * q) :
    (7 / 2 - 8 / (3 * (analyticZetaZeroMultiplicity ρ : ℝ))) * width q < 1 - ρ.1.re := by
  by_contra! hnear
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  have hx' : shift q ≤ delta 9 / 4 := hxu.trans
    (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width, delta, DerivativePowerExponents.alpha])
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity ρ := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hraw : 7 / 2 - 8 / (3 * (analyticZetaZeroMultiplicity ρ : ℝ)) ≤ (7 / 2 : ℝ) :=
    sub_le_self _ (by positivity)
  have hline : DirichletPowerParameters.line 9 < ρ.1.re := by
    have hmul := mul_le_mul_of_nonneg_right hraw (width_bounds hq).1.le
    have hw := (width_bounds hq).2
    have hgap : 7 / 2 * GaussianStripProfile.width < delta 9 := by
      norm_num [GaussianStripProfile.width, delta, DerivativePowerExponents.alpha]
    rw [delta_eq_one_sub_line] at hgap
    nlinarith only [hnear, hmul, hw, hgap]
  have h := gaussian_source_le_budget ha hs hp hω0 hω1 hω hlog 9 (by norm_num)
    (gaussianScale_bounds hq).1 hx hx' ρ (by linarith)
    (ZetaGaussianBandBudget.scale_lower ht) hline
  have hb := budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha)) hW hF hq ht hL
  have hl := selected_source_lower ha1 hq ρ hnear
  linarith

/-- The mathematically defined exact contact family discharges every
phase and arithmetic premise of the multiplicity-dependent exclusion. -/
theorem scaled_margin {q : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) (hL : scale ρ.1.im ≤ 320000 * q) :
    (7 / 2 - 8 / (3 * (analyticZetaZeroMultiplicity ρ : ℝ))) * width q < 1 - ρ.1.re := by
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

/-- Multiplicity enlarges the boundary exclusion while preserving the
entire previously proved width at multiplicity one. Only positive orders
are used for actual zeros. -/
def multiplicityFactor (m : ℕ) : ℝ := max 1 (7 / 2 - 8 / (3 * (m : ℝ)))

/-- The actual simple-zero case keeps the full previous Gaussian width. -/
theorem multiplicityFactor_one : multiplicityFactor 1 = 1 := by
  norm_num [multiplicityFactor]

/-- The first multiple-zero case already gives a factor greater than two. -/
theorem multiplicityFactor_two : multiplicityFactor 2 = 13 / 6 := by
  norm_num [multiplicityFactor]

/-- Higher positive multiplicity can only increase the excluded depth. -/
theorem multiplicityFactor_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    multiplicityFactor m ≤ multiplicityFactor n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiv : 8 / (3 * (n : ℝ)) ≤ 8 / (3 * (m : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  exact max_le_max le_rfl (by linarith)

/-- Every actual zero obeys the multiplicity-dependent margin throughout
the explicit unbounded height range. -/
theorem exact_margin (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    multiplicityFactor (analyticZetaZeroMultiplicity ρ) *
      ZetaGaussianAllHeight.explicitWidth ρ.1.im < 1 - ρ.1.re := by
  have hraw := scaled_margin (le_max_left _ _) ρ ht
    (ZetaGaussianAllHeight.scale_le_dilation ρ.1.im)
  change (7 / 2 - 8 / (3 * (analyticZetaZeroMultiplicity ρ : ℝ))) *
    ZetaGaussianAllHeight.explicitWidth ρ.1.im < 1 - ρ.1.re at hraw
  unfold multiplicityFactor
  rw [max_mul_of_nonneg _ _ (ZetaGaussianAllHeight.explicitWidth_pos _).le, one_mul]
  exact max_lt (ZetaGaussianAllHeight.exact_margin ρ ht) hraw

/-- Reflection keeps the same ordinate and multiplicity, so both edges
have the same strengthened bound for each actual zero. -/
theorem exact_strip (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    multiplicityFactor (analyticZetaZeroMultiplicity ρ) *
      ZetaGaussianAllHeight.explicitWidth ρ.1.im < ρ.1.re ∧
    ρ.1.re < 1 - multiplicityFactor (analyticZetaZeroMultiplicity ρ) *
      ZetaGaussianAllHeight.explicitWidth ρ.1.im := by
  have hr := exact_margin ρ ht
  have hl := exact_margin (NontrivialZetaZero.conjugatePartner ρ)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using ht)
  simp only [NontrivialZetaZero.conjugatePartner_coe, analyticZetaZeroMultiplicity_conjugatePartner,
    Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add] at hl
  constructor <;> linarith

/-- The multiplicity-dependent exclusion has an elementary width with
the same explicit lower height and no upper ceiling. -/
theorem exact_strip_min (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    multiplicityFactor (analyticZetaZeroMultiplicity ρ) *
      min (1 / 450000) (32 / (45 * scale ρ.1.im)) < ρ.1.re ∧
    ρ.1.re < 1 - multiplicityFactor (analyticZetaZeroMultiplicity ρ) *
      min (1 / 450000) (32 / (45 * scale ρ.1.im)) := by
  simpa only [ZetaGaussianAllHeight.explicitWidth_eq_min] using exact_strip ρ ht

/-- The same theorem supplies an upper bound on multiplicity in every
corresponding boundary layer, with the threshold order arbitrary. -/
theorem multiplicity_lt_of_near_edge (ρ : NontrivialZetaZero)
    (ht : 1000000 ≤ |ρ.1.im|) {k : ℕ} (hk : 1 ≤ k)
    (hnear : min ρ.1.re (1 - ρ.1.re) ≤
      multiplicityFactor k * ZetaGaussianAllHeight.explicitWidth ρ.1.im) :
    analyticZetaZeroMultiplicity ρ < k := by
  by_contra! hmk
  have hmul := mul_le_mul_of_nonneg_right (multiplicityFactor_mono hk hmk)
    (ZetaGaussianAllHeight.explicitWidth_pos ρ.1.im).le
  obtain ⟨hl, hr⟩ := exact_strip ρ ht
  have hdepth : multiplicityFactor (analyticZetaZeroMultiplicity ρ) *
      ZetaGaussianAllHeight.explicitWidth ρ.1.im < min ρ.1.re (1 - ρ.1.re) :=
    lt_min hl (by linarith)
  linarith

/-- Every zero in the larger boundary layer is simple. This excludes
multiple zeros there and does not assert absence of simple zeros. -/
theorem simple_of_near_edge (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hnear : min ρ.1.re (1 - ρ.1.re) ≤
      (13 / 6 : ℝ) * ZetaGaussianAllHeight.explicitWidth ρ.1.im) :
    analyticZetaZeroMultiplicity ρ = 1 := by
  have h := multiplicity_lt_of_near_edge ρ ht (k := 2) (by omega)
    (by simpa only [multiplicityFactor_two] using hnear)
  have hp := analyticZetaZeroMultiplicity_positive ρ
  omega

/-- At enlarged logarithmic height at least one hundred, the new
simplicity layer strictly contains the older explicit simplicity width.
This comparison does not assert superiority at smaller heights. -/
theorem old_simplicity_width_lt {t : ℝ} (hL : 100 ≤ scale t) :
    zetaSignedEdgeWindowWidth t < (13 / 6 : ℝ) * ZetaGaussianAllHeight.explicitWidth t := by
  have hcompare : scale t ≤ localZetaLogHeight t := by
    change Real.log (|t| + 2) ≤ Real.log (|t| + 22)
    apply Real.log_le_log (by positivity)
    linarith
  have hw := zetaSignedEdgeWindowWidth_pos t
  have he := localZetaLogHeight_mul_signedEdgeWindowWidth t
  have hmul := mul_le_mul_of_nonneg_right hcompare hw.le
  have h100 := mul_le_mul_of_nonneg_right (hL.trans hcompare) hw.le
  rw [ZetaGaussianAllHeight.explicitWidth_eq_min,
    mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 13 / 6)]
  apply lt_min
  · nlinarith only [he, h100]
  · have hratio : (13 / 6 : ℝ) * (32 / (45 * scale t)) = 208 / (135 * scale t) := by ring
    rw [hratio]
    apply (lt_div_iff₀ (by linarith : 0 < 135 * scale t)).mpr
    nlinarith only [hmul, he]

/-- The original signed eta current now has its complete simple-zero
head representation throughout the larger Gaussian boundary layer. -/
theorem eta_current_eq_head (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hnear : min ρ.1.re (1 - ρ.1.re) ≤
      (13 / 6 : ℝ) * ZetaGaussianAllHeight.explicitWidth ρ.1.im) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux ρ N =
      2 * (∑ d ∈ Finset.Icc 1 (2 * (N + 2)),
        etaSignedCompletedPair
          (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner ρ) N 0)
          (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner ρ) 0
            (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)
          (pairedEtaHeadCompletedMoment ρ N 0)
          (pairedEtaCompletedMomentInverseTerm ρ 0 (pairedEtaLogTailCutoff (N + 2))
            (2 * (N + 2)) d)).re :=
  pairedEtaLeadingCurrent_eq_momentInverse_head ρ (simple_of_near_edge ρ ht hnear) N

end
end RiemannGaussian.ZetaGaussianMultiplicityDepth
