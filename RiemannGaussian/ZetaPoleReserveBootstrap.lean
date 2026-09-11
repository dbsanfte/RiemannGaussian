/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSignedPoleZeroFree

/-!
# A quantitative zero-free bootstrap from the retained pole reserve

The constant-mode auxiliary pole has a uniform strictly positive reserve
on the existing sampling interval. Retaining this reserve gives an actual
zero-free improvement. Its associated monotone iteration has an explicit
fixed point; the fixed point remains near the strip edge rather than
approaching the critical line.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology

/-- The existing exact family has a positive constant coefficient,
with this rational lower bound obtained from its proved enclosure. -/
theorem phaseContactExactFamily_constant_ge_nine_fiftieths :
    (9 / 50 : ℝ) ≤ phaseContactExactFamily 0 := by
  have he := phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
  change phaseContactExactFamily 0 = phaseContactExactCoefficients 0 at he
  rw [he]
  have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le 0)).1
  norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
  linarith

/-- The constant-pole reserve has a strict numerical floor on the
whole signed-pole sampling interval. Its actual value remains upstream. -/
theorem phaseContactExact_constantPoleReserve_gt {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 4 / 3) :
    (2 / 25 : ℝ) < phaseContactExactFamily 0 * zetaStechkinWeight σ /
      (zetaStechkinAbscissa σ - 1) := by
  have ht := lt_zetaStechkinAbscissa hσ
  have hq := zetaStechkinAbscissa_quadratic σ
  have hσsq : σ ^ 2 ≤ (16 / 9 : ℝ) := by nlinarith
  have ht2 : zetaStechkinAbscissa σ < 2 := by nlinarith
  have hd : 0 < zetaStechkinAbscissa σ - 1 := by linarith
  have hc := four_ninths_le_zetaStechkinWeight hσ
  have ha := phaseContactExactFamily_constant_ge_nine_fiftieths
  have hm : (2 / 25 : ℝ) ≤ phaseContactExactFamily 0 * zetaStechkinWeight σ := by
    have h := mul_le_mul ha hc (by norm_num : (0 : ℝ) ≤ 4 / 9)
      (phaseContactExactFamily_nonneg 0)
    norm_num at h
    exact h
  apply (lt_div_iff₀ hd).mpr
  linarith

/-- The height allowance uses the already proved zero-height floor,
so it is positive even at ordinates with no nontrivial zeros. -/
def zetaPoleReserveAllowance (t : ℝ) : ℝ :=
  (366 * max (13 / 10) (Real.log (|t| + 2)) - 113) / 2160

/-- The allowance is strictly larger than the retained reserve. -/
theorem zetaPoleReserveAllowance_gt (t : ℝ) :
    (2 / 25 : ℝ) < zetaPoleReserveAllowance t := by
  have h := le_max_left (13 / 10 : ℝ) (Real.log (|t| + 2))
  unfold zetaPoleReserveAllowance
  linarith

/-- Every actual zero in the signed-pole sampling range obeys the
strict budget with the constant-pole reserve fully discharged. -/
theorem phaseContactExact_poleReserve_strict_zero_budget
    (rho : NontrivialZetaZero) (hρ : 35 / 39 ≤ rho.1.re) :
    (11 / 625 : ℝ) + (2 / 25 : ℝ) * (1 - rho.1.re) <
      zetaPoleReserveAllowance rho.1.im * (1 - rho.1.re) := by
  let d : ℝ := 1 - rho.1.re
  let σ : ℝ := 1 + (13 / 4 : ℝ) * d
  let L : ℝ := max (13 / 10) (Real.log (|rho.1.im| + 2))
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hdu : d ≤ 4 / 39 := by dsimp [d]; linarith
  have hσ : 1 ≤ σ := by dsimp [σ]; linarith
  have hσu : σ ≤ 4 / 3 := by dsimp [σ]; linarith
  have hL : 13 / 10 ≤ L := le_max_left _ _
  have hlog : Real.log (σ + |rho.1.im|) ≤ L := by
    apply le_trans _ (le_max_right _ _)
    apply Real.log_le_log (by positivity)
    linarith
  have hH : (481 / 1600 : ℝ) * d + (61 / 200 : ℝ) *
      Real.log (σ + |rho.1.im|) - 1 / 8 ≤
        (37 / 1200 : ℝ) + (61 / 200 : ℝ) * L - 1 / 8 := by linarith
  have hH0 : 0 ≤ (37 / 1200 : ℝ) + (61 / 200 : ℝ) * L - 1 / 8 := by linarith
  have hc0 : 0 ≤ 1 - zetaStechkinWeight σ :=
    sub_nonneg.mpr (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hc : 1 - zetaStechkinWeight σ ≤ 5 / 9 := by
    linarith [four_ninths_le_zetaStechkinWeight hσ]
  have hwork : 0 ≤ d * (∑' m : ℕ, zetaStechkinPrimeWeight σ m *
      phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) := by
    apply mul_nonneg hd.le
    exact tsum_nonneg (fun m ↦ mul_nonneg (zetaStechkinPrimeWeight_nonneg hσ m)
      (phaseContactExactFamily_kernel_nonneg _))
  have hreserve := mul_lt_mul_of_pos_left
    (phaseContactExact_constantPoleReserve_gt hσ hσu) hd
  have h := phaseContactExact_signedPole_zero_budget rho hρ
  change (11 / 625 : ℝ) + d * _ + d * _ ≤
    d * (1 - zetaStechkinWeight σ) * _ at h
  have hu := mul_le_mul_of_nonneg_left hH (mul_nonneg hd.le hc0)
  have hv := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc hH0) hd.le
  change (11 / 625 : ℝ) + (2 / 25 : ℝ) * d < _
  unfold zetaPoleReserveAllowance
  change (11 / 625 : ℝ) + (2 / 25 : ℝ) * d < (366 * L - 113) / 2160 * d
  nlinarith only [h, hwork, hreserve, hu, hv]

/-- The explicit fixed point of the retained-reserve improvement,
capped at the range where the signed-pole budget has been proved. -/
def zetaPoleReserveFixedMargin (t : ℝ) : ℝ :=
  min (4 / 39) ((11 / 625) / (zetaPoleReserveAllowance t - 2 / 25))

/-- The fixed margin is positive and remains within its actual
sampling range. No unproved extrapolation toward one half is used. -/
theorem zetaPoleReserveFixedMargin_bounds (t : ℝ) :
    0 < zetaPoleReserveFixedMargin t ∧ zetaPoleReserveFixedMargin t ≤ 4 / 39 := by
  constructor
  · exact lt_min (by norm_num) (div_pos (by norm_num)
      (sub_pos.mpr (zetaPoleReserveAllowance_gt t)))
  · exact min_le_left _ _

/-- The fixed point is an unconditional strict exclusion width for
the actual nontrivial zeros. The positive reserve proves strictness. -/
theorem zetaPoleReserveFixedMargin_lt_one_sub_re (rho : NontrivialZetaZero) :
    zetaPoleReserveFixedMargin rho.1.im < 1 - rho.1.re := by
  by_contra hn
  have hd := le_of_not_gt hn
  have hdu := hd.trans (zetaPoleReserveFixedMargin_bounds rho.1.im).2
  have hρ : 35 / 39 ≤ rho.1.re := by linarith
  have h := phaseContactExact_poleReserve_strict_zero_budget rho hρ
  have hb := hd.trans (min_le_right (4 / 39 : ℝ)
    ((11 / 625) / (zetaPoleReserveAllowance rho.1.im - 2 / 25)))
  have hm := (le_div_iff₀ (sub_pos.mpr (zetaPoleReserveAllowance_gt rho.1.im))).mp hb
  nlinarith

/-- A previously available lower bound on the edge distance feeds
back through the positive constant-pole reserve. -/
def zetaPoleReserveStep (t δ : ℝ) : ℝ :=
  min (4 / 39) (((11 / 625) + (2 / 25) * δ) / zetaPoleReserveAllowance t)

/-- The feedback step increases when its input exclusion increases. -/
theorem zetaPoleReserveStep_mono (t : ℝ) : Monotone (zetaPoleReserveStep t) := by
  intro x y hxy
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ (by linarith [zetaPoleReserveAllowance_gt t])
  linarith

/-- The feedback is an actual zero theorem: its only input is a
previously established bound for that same zero. -/
theorem zetaPoleReserveStep_lt_one_sub_re (rho : NontrivialZetaZero)
    {δ : ℝ} (hδ : δ ≤ 1 - rho.1.re) :
    zetaPoleReserveStep rho.1.im δ < 1 - rho.1.re := by
  by_cases hd : 4 / 39 < 1 - rho.1.re
  · exact (min_le_left _ _).trans_lt hd
  · have hρ : 35 / 39 ≤ rho.1.re := by linarith
    have h := phaseContactExact_poleReserve_strict_zero_budget rho hρ
    apply (min_le_right _ _).trans_lt
    apply (div_lt_iff₀ (by linarith [zetaPoleReserveAllowance_gt rho.1.im])).mpr
    linarith

/-- The explicit endpoint is a fixed point of the actual feedback
map, including the case where the sampling cap is reached. -/
theorem zetaPoleReserveStep_fixed (t : ℝ) :
    zetaPoleReserveStep t (zetaPoleReserveFixedMargin t) = zetaPoleReserveFixedMargin t := by
  let A := zetaPoleReserveAllowance t
  have hA : 0 < A := by dsimp [A]; linarith [zetaPoleReserveAllowance_gt t]
  have hr : 0 < A - 2 / 25 := sub_pos.mpr (zetaPoleReserveAllowance_gt t)
  have he : (11 / 625 : ℝ) / (A - 2 / 25) * (A - 2 / 25) = 11 / 625 :=
    div_mul_cancel₀ _ hr.ne'
  unfold zetaPoleReserveStep zetaPoleReserveFixedMargin
  change min (4 / 39) ((11 / 625 + 2 / 25 * min (4 / 39) (11 / 625 / (A - 2 / 25))) / A) =
    min (4 / 39) (11 / 625 / (A - 2 / 25))
  by_cases hc : (4 / 39 : ℝ) ≤ (11 / 625) / (A - 2 / 25)
  · rw [min_eq_left hc]
    apply min_eq_left
    apply (le_div_iff₀ hA).mpr
    have h := (le_div_iff₀ hr).mp hc
    linarith
  · rw [min_eq_right (le_of_not_ge hc)]
    have hh : ((11 / 625 : ℝ) + 2 / 25 * (11 / 625 / (A - 2 / 25))) / A =
        11 / 625 / (A - 2 / 25) := by
      apply (div_eq_iff hA.ne').mpr
      linarith
    rw [hh, min_eq_right (le_of_not_ge hc)]

/-- The feedback map has only this fixed point. Consequently its
iteration cannot silently yield a wider limiting region. -/
theorem zetaPoleReserveStep_fixed_unique (t : ℝ) {x : ℝ}
    (hx : zetaPoleReserveStep t x = x) : x = zetaPoleReserveFixedMargin t := by
  let A := zetaPoleReserveAllowance t
  have hA : 0 < A := by dsimp [A]; linarith [zetaPoleReserveAllowance_gt t]
  have hr : 0 < A - 2 / 25 := sub_pos.mpr (zetaPoleReserveAllowance_gt t)
  change min (4 / 39) ((11 / 625 + 2 / 25 * x) / A) = x at hx
  unfold zetaPoleReserveFixedMargin
  change x = min (4 / 39) (11 / 625 / (A - 2 / 25))
  by_cases hc : (4 / 39 : ℝ) ≤ (11 / 625 + 2 / 25 * x) / A
  · rw [min_eq_left hc] at hx
    rw [← hx]
    apply (min_eq_left _).symm
    apply (le_div_iff₀ hr).mpr
    have h := (le_div_iff₀ hA).mp hc
    rw [← hx] at h
    linarith
  · have hsmall := le_of_not_ge hc
    rw [min_eq_right hsmall] at hx
    have he := (div_eq_iff hA.ne').mp hx
    have hx' : x = (11 / 625) / (A - 2 / 25) := by
      apply (eq_div_iff hr.ne').mpr
      linarith
    rw [hx, hx'] at hsmall
    exact hx'.trans (min_eq_right hsmall).symm

/-- Any input below the fixed point gains a strictly larger margin
after one application of the reserve map. -/
theorem zetaPoleReserveStep_strict_improvement (t : ℝ) {δ : ℝ}
    (hδ : δ < zetaPoleReserveFixedMargin t) : δ < zetaPoleReserveStep t δ := by
  have hd := lt_of_lt_of_le hδ (min_le_right (4 / 39 : ℝ)
    ((11 / 625) / (zetaPoleReserveAllowance t - 2 / 25)))
  have hm := (lt_div_iff₀ (sub_pos.mpr (zetaPoleReserveAllowance_gt t))).mp hd
  apply lt_min (hδ.trans_le (zetaPoleReserveFixedMargin_bounds t).2)
  apply (lt_div_iff₀ (by linarith [zetaPoleReserveAllowance_gt t])).mpr
  linarith

/-- The successive exclusion bounds generated by the actual reserve
map, starting from the elementary open-strip bound. -/
def zetaPoleReserveIterate (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => zetaPoleReserveStep t (zetaPoleReserveIterate t n)

/-- Every feedback iterate is nonnegative and bounded by the exact
fixed point. This bound also records the limit of this mechanism. -/
theorem zetaPoleReserveIterate_bounds (t : ℝ) (n : ℕ) :
    0 ≤ zetaPoleReserveIterate t n ∧
      zetaPoleReserveIterate t n ≤ zetaPoleReserveFixedMargin t := by
  induction n with
  | zero => exact ⟨le_rfl, (zetaPoleReserveFixedMargin_bounds t).1.le⟩
  | succ n ih =>
    constructor
    · change 0 ≤ min (4 / 39) ((11 / 625 + 2 / 25 * zetaPoleReserveIterate t n) /
        zetaPoleReserveAllowance t)
      apply le_min (by norm_num)
      apply div_nonneg _ (by linarith [zetaPoleReserveAllowance_gt t])
      linarith [ih.1]
    · exact ((zetaPoleReserveStep_mono t) ih.2).trans_eq (zetaPoleReserveStep_fixed t)

/-- Repeatedly feeding the previous region back into the reserve
never decreases the exclusion obtained by this iteration. -/
theorem zetaPoleReserveIterate_mono (t : ℝ) : Monotone (zetaPoleReserveIterate t) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact (zetaPoleReserveIterate_bounds t 1).1
  | succ n ih => exact zetaPoleReserveStep_mono t ih

/-- Every finite stage excludes genuine zeta zeros with no missing
arithmetic premise. The induction uses the previously proved stage. -/
theorem zetaPoleReserveIterate_lt_one_sub_re (rho : NontrivialZetaZero) (n : ℕ) :
    zetaPoleReserveIterate rho.1.im n < 1 - rho.1.re := by
  induction n with
  | zero => exact sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  | succ n ih => exact zetaPoleReserveStep_lt_one_sub_re rho ih.le

/-- The complete increasing sequence converges to the explicit
fixed point, which is at most `4/39`, not to the critical line. -/
theorem tendsto_zetaPoleReserveIterate (t : ℝ) :
    Tendsto (zetaPoleReserveIterate t) atTop (𝓝 (zetaPoleReserveFixedMargin t)) := by
  have hb : BddAbove (Set.range (zetaPoleReserveIterate t)) :=
    ⟨zetaPoleReserveFixedMargin t, by
      rintro _ ⟨n, rfl⟩
      exact (zetaPoleReserveIterate_bounds t n).2⟩
  have ht := tendsto_atTop_ciSup (zetaPoleReserveIterate_mono t) hb
  have hc : Continuous (zetaPoleReserveStep t) := by
    unfold zetaPoleReserveStep
    fun_prop
  have hs := hc.continuousAt.tendsto.comp ht
  have hn := ht.comp (tendsto_add_atTop_nat 1)
  have he : zetaPoleReserveStep t (⨆ n, zetaPoleReserveIterate t n) =
      ⨆ n, zetaPoleReserveIterate t n := by
    apply tendsto_nhds_unique hs
    exact hn
  have hf := zetaPoleReserveStep_fixed_unique t he
  rwa [hf] at ht

/-- On every ordinate allowed by the proved zero-height floor, the
new fixed margin is strictly wider than the preceding signed-pole one. -/
theorem zetaSignedPole_margin_lt_poleReserveFixed {t : ℝ}
    (ht : 13 / 10 ≤ Real.log (|t| + 2)) :
    zetaSignedPoleZeroMargin t < zetaPoleReserveFixedMargin t := by
  have hden := zetaSignedPole_denominator_pos t
  have hm := zetaSignedPoleZeroMargin_pos t
  have he : zetaSignedPoleZeroMargin t * (7625 * Real.log (|t| + 2) - 2000) = 792 :=
    div_mul_cancel₀ _ hden.ne'
  apply lt_min
  · unfold zetaSignedPoleZeroMargin
    apply (div_lt_iff₀ hden).mpr
    linarith
  · apply (lt_div_iff₀ (sub_pos.mpr (zetaPoleReserveAllowance_gt t))).mpr
    unfold zetaPoleReserveAllowance
    rw [max_eq_right ht]
    nlinarith

/-- Feeding the preceding proved region into the actual reserve map
strictly enlarges it at every admissible zero ordinate. -/
theorem zetaSignedPole_margin_lt_reserveStep {t : ℝ}
    (ht : 13 / 10 ≤ Real.log (|t| + 2)) :
    zetaSignedPoleZeroMargin t < zetaPoleReserveStep t (zetaSignedPoleZeroMargin t) :=
  zetaPoleReserveStep_strict_improvement t (zetaSignedPole_margin_lt_poleReserveFixed ht)

/-- An elementary closed form of the iterated exclusion endpoint.
The height floor and the finite sampling cap remain explicit. -/
theorem zetaPoleReserveFixedMargin_eq (t : ℝ) :
    zetaPoleReserveFixedMargin t = min (4 / 39)
      (4752 / (45750 * max (13 / 10) (Real.log (|t| + 2)) - 35725)) := by
  have hp := sub_pos.mpr (zetaPoleReserveAllowance_gt t)
  have he : 45750 * max (13 / 10) (Real.log (|t| + 2)) - 35725 =
      270000 * (zetaPoleReserveAllowance t - 2 / 25) := by
    unfold zetaPoleReserveAllowance
    ring
  unfold zetaPoleReserveFixedMargin
  rw [he]
  congr 1
  field_simp
  ring

/-- The global width retains the previous theorem at low ordinates
and uses the improved reserve margin wherever it is larger. -/
def zetaPoleReserveZeroMargin (t : ℝ) : ℝ :=
  max (zetaSignedPoleZeroMargin t) (zetaPoleReserveFixedMargin t)

/-- The global reserve width never weakens the previous exclusion. -/
theorem zetaSignedPole_margin_le_poleReserve (t : ℝ) :
    zetaSignedPoleZeroMargin t ≤ zetaPoleReserveZeroMargin t := le_max_left _ _

/-- The retained global width stays positive and below one quarter,
so the original literal-zeta nonvanishing bridge remains applicable. -/
theorem zetaPoleReserveZeroMargin_bounds (t : ℝ) :
    0 < zetaPoleReserveZeroMargin t ∧ zetaPoleReserveZeroMargin t < 1 / 4 := by
  constructor
  · exact (zetaSignedPoleZeroMargin_pos t).trans_le (le_max_left _ _)
  · apply max_lt (zetaSignedPoleZeroMargin_lt_one_quarter t)
    linarith [(zetaPoleReserveFixedMargin_bounds t).2]

/-- The improved global width decreases with the absolute ordinate,
including both its sampling cap and its inherited low-height region. -/
theorem zetaPoleReserveZeroMargin_antitone_abs {a b : ℝ} (h : |a| ≤ |b|) :
    zetaPoleReserveZeroMargin b ≤ zetaPoleReserveZeroMargin a := by
  have hlog := Real.log_le_log (by positivity : 0 < |a| + 2)
    (by linarith : |a| + 2 ≤ |b| + 2)
  have hmax := max_le_max_left (13 / 10 : ℝ) hlog
  have hA : zetaPoleReserveAllowance a ≤ zetaPoleReserveAllowance b := by
    unfold zetaPoleReserveAllowance
    linarith
  have hold : zetaSignedPoleZeroMargin b ≤ zetaSignedPoleZeroMargin a := by
    exact div_le_div_of_nonneg_left (by norm_num) (zetaSignedPole_denominator_pos a)
      (by linarith)
  apply max_le_max hold
  apply min_le_min_left
  exact div_le_div_of_nonneg_left (by norm_num)
    (sub_pos.mpr (zetaPoleReserveAllowance_gt a)) (by linarith)

/-- Both proved exclusions apply to each genuine zero, so their
maximum is still a strict unconditional exclusion width. -/
theorem zetaPoleReserve_margin_lt_one_sub_re (rho : NontrivialZetaZero) :
    zetaPoleReserveZeroMargin rho.1.im < 1 - rho.1.re :=
  max_lt (zetaSignedPole_margin_lt_one_sub_re rho) (zetaPoleReserveFixedMargin_lt_one_sub_re rho)

/-- Critical reflection transports the complete improved margin to
the left side of the actual zero strip. -/
theorem zetaPoleReserve_margin_lt_re (rho : NontrivialZetaZero) :
    zetaPoleReserveZeroMargin rho.1.im < rho.1.re := by
  have h := zetaPoleReserve_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- The literal nontrivial zeros lie in the improved reflected strip. -/
theorem nontrivialZetaZero_mem_poleReserve_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Set.Ioo (zetaPoleReserveZeroMargin rho.1.im)
      (1 - zetaPoleReserveZeroMargin rho.1.im) :=
  ⟨zetaPoleReserve_margin_lt_re rho,
    by linarith [zetaPoleReserve_margin_lt_one_sub_re rho]⟩

/-- The actual zeta function is nonzero on the wider closed right
edge region, explicitly away from its pole. -/
theorem riemannZeta_ne_zero_of_poleReserve_margin {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - zetaPoleReserveZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [(zetaPoleReserveZeroMargin_bounds s.im).2]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := (nontrivialZetaZero_mem_poleReserve_strip rho).2
  change s.re < 1 - zetaPoleReserveZeroMargin s.im at h
  linarith

end
end RiemannGaussian
