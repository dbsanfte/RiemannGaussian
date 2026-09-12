/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPoleRemainder
import RiemannGaussian.ZetaCompletionHalfLogBound

/-!
# A logarithmic allowance for the complete outside-distance Gaussian remainder

An exact horizontal Poisson comparison controls every zero outside a
distance cutoff by the complete xi mass at one shifted point. Combined
with cubic Gaussian decay, its cost is `24*B/η^2`, including at `Re s = 1`.
The original complex remainder and complete near/far decomposition are
retained. A genuine elementary logarithmic bound discharges the shifted
xi value on the boundary line; no unknown divisor constant remains there.
-/

namespace RiemannGaussian.ZetaGaussianDistanceRemainder
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical

/-- The original complex remainder outside a closed distance cutoff. -/
def farTerm (B η : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) : ℂ :=
  if η ≤ ‖s - ρ.1‖ then ZetaGaussianPoleRemainder.term B s ρ else 0

/-- The original complex remainder in the complementary open distance ball. -/
def nearTerm (B η : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) : ℂ :=
  if ‖s - ρ.1‖ < η then ZetaGaussianPoleRemainder.term B s ρ else 0

/-- The exact shifted Poisson mass of the nearby zeros already retained in the source. -/
def nearPoisson (η : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) : ℝ :=
  if ‖s - ρ.1‖ < η then zetaGlobalPoissonSummand (s + (η : ℂ)) ρ else 0

/-- Outside a radius, one horizontal shift dominates the entire inverse-square
kernel by a positive Poisson kernel. The comparison includes the boundary `Re z = 0`. -/
theorem inverse_square_le_shifted_poisson {η : ℝ} (hη : 0 < η)
    {z : ℂ} (hz : 0 ≤ z.re) (hd : η ≤ ‖z‖) :
    1 / ‖z‖ ^ 2 ≤ (2 / η) * ((z.re + η) / Complex.normSq (z + (η : ℂ))) := by
  have hq : 0 < ‖z‖ := hη.trans_le hd
  have hr : 0 < (z + (η : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hD := Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hr)
  have hsq : η ^ 2 ≤ ‖z‖ ^ 2 := (sq_le_sq₀ hη.le (norm_nonneg _)).mpr hd
  have he : Complex.normSq (z + (η : ℂ)) = ‖z‖ ^ 2 + 2 * z.re * η + η ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    ring
  have hcomp : η * Complex.normSq (z + (η : ℂ)) ≤ 2 * (z.re + η) * ‖z‖ ^ 2 := by
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ 2 * z.re + η by positivity) (sub_nonneg.mpr hsq)]
  rw [div_mul_div_comm]
  exact (div_le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2) (mul_pos hη hD)).mpr
    (by simpa only [one_mul] using hcomp)

/-- Every actual Gaussian remainder outside the distance ball has a
positive shifted-Poisson majorant with its complete analytic multiplicity. -/
theorem norm_term_le_shifted_poisson {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) (hd : η ≤ ‖s - ρ.1‖) :
    ‖ZetaGaussianPoleRemainder.term B s ρ‖ ≤ (24 * B / η ^ 2) *
      zetaGlobalPoissonSummand (s + (η : ℂ)) ρ := by
  have hr := (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ).le
  have hb := GaussianLaplacePoleRemainder.norm_remainder_le_inverse_square hB hη hr hd
  have hp := inverse_square_le_shifted_poisson hη hr hd
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 12 * B / η by positivity)
  have hbound : ‖GaussianLaplacePoleRemainder.remainder B (s - ρ.1)‖ ≤
      (24 * B / η ^ 2) * ((s.re - ρ.1.re + η) /
        Complex.normSq (s + (η : ℂ) - ρ.1)) := by
    have he : s - ρ.1 + (η : ℂ) = s + (η : ℂ) - ρ.1 := by ring
    simp only [Complex.sub_re, he] at hmul
    have hmul' : (12 * B / η) / ‖s - ρ.1‖ ^ 2 ≤
        (24 * B / η ^ 2) * ((s.re - ρ.1.re + η) /
          Complex.normSq (s + (η : ℂ) - ρ.1)) := by
      convert! hmul using 1 <;> ring
    exact hb.trans hmul'
  rw [ZetaGaussianPoleRemainder.term, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (analyticZetaZeroMultiplicity ρ : ℝ) *
        ((24 * B / η ^ 2) * ((s.re - ρ.1.re + η) /
          Complex.normSq (s + (η : ℂ) - ρ.1))) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by
      simp only [zetaGlobalPoissonSummand, Complex.add_re, Complex.ofReal_re]
      ring

/-- The complete outside-distance series has one summable Poisson majorant. -/
theorem norm_farTerm_le {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) :
    ‖farTerm B η s ρ‖ ≤ (24 * B / η ^ 2) * zetaGlobalPoissonSummand (s + (η : ℂ)) ρ := by
  unfold farTerm
  split_ifs with hd
  · exact norm_term_le_shifted_poisson hB hη hs ρ hd
  · simpa only [norm_zero] using mul_nonneg (show 0 ≤ 24 * B / η ^ 2 by positivity)
      (zetaGlobalPoissonSummand_nonneg (by simp only [Complex.add_re, Complex.ofReal_re]; linarith) ρ)

/-- The outside estimate retains the full positive Poisson reserve of
every nearby zero rather than charging that zero to the tail. -/
theorem norm_farTerm_le_reserve {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) :
    ‖farTerm B η s ρ‖ ≤ (24 * B / η ^ 2) *
      (zetaGlobalPoissonSummand (s + (η : ℂ)) ρ - nearPoisson η s ρ) := by
  by_cases hd : ‖s - ρ.1‖ < η
  · simp [farTerm, nearPoisson, hd, not_le.mpr hd]
  · simpa only [nearPoisson, hd, if_false, sub_zero] using norm_farTerm_le hB hη hs ρ

/-- The genuine nearby Poisson reserve is summable as part of the same
complete positive xi mass, with its original distance cutoff unchanged. -/
theorem summable_nearPoisson {η : ℝ} (hη : 0 < η) {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (nearPoisson η s) := by
  have hs' : 1 ≤ (s + (η : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  apply (summable_zetaGlobalPoissonSummand hs').of_nonneg_of_le
  · intro ρ
    unfold nearPoisson
    split_ifs <;> simp [zetaGlobalPoissonSummand_nonneg hs']
  · intro ρ
    unfold nearPoisson
    split_ifs <;> simp [zetaGlobalPoissonSummand_nonneg hs']

/-- The genuine complex outside-distance remainder is absolutely summable. -/
theorem summable_farTerm {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) : Summable (farTerm B η s) := by
  have hs' : 1 ≤ (s + (η : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  exact ((summable_zetaGlobalPoissonSummand hs').mul_left (24 * B / η ^ 2)).of_norm_bounded
    (norm_farTerm_le hB hη hs)

/-- The complete complex outside-distance remainder costs only the
original shifted xi Poisson mass times `24*B/η^2`, with no height truncation. -/
theorem norm_tsum_farTerm_le {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑' ρ : NontrivialZetaZero, farTerm B η s ρ‖ ≤
      (24 * B / η ^ 2) * (logDeriv riemannXi (s + (η : ℂ))).re := by
  have hs' : 1 ≤ (s + (η : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hsum := summable_farTerm hB hη hs
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero, ‖farTerm B η s ρ‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' ρ : NontrivialZetaZero,
        (24 * B / η ^ 2) * zetaGlobalPoissonSummand (s + (η : ℂ)) ρ :=
      hsum.norm.tsum_le_tsum (norm_farTerm_le hB hη hs)
        ((summable_zetaGlobalPoissonSummand hs').mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_zetaGlobalPoissonSummand hs']

/-- The full complex tail allowance subtracts the exact mass of every
nearby zero. This reserve is available to pay for the cotangent correction
when the complete smoothed strip comparison is assembled. -/
theorem norm_tsum_farTerm_le_reserve {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑' ρ : NontrivialZetaZero, farTerm B η s ρ‖ ≤ (24 * B / η ^ 2) *
      ((logDeriv riemannXi (s + (η : ℂ))).re -
        ∑' ρ : NontrivialZetaZero, nearPoisson η s ρ) := by
  have hs' : 1 ≤ (s + (η : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hp := summable_zetaGlobalPoissonSummand hs'
  have hn := summable_nearPoisson hη hs
  have hsum := summable_farTerm hB hη hs
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero, ‖farTerm B η s ρ‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' ρ : NontrivialZetaZero, (24 * B / η ^ 2) *
        (zetaGlobalPoissonSummand (s + (η : ℂ)) ρ - nearPoisson η s ρ) :=
      hsum.norm.tsum_le_tsum (norm_farTerm_le_reserve hB hη hs) ((hp.sub hn).mul_left _)
    _ = _ := by rw [tsum_mul_left, hp.tsum_sub hn, tsum_zetaGlobalPoissonSummand hs']

/-- Inside the distance ball the same shifted Poisson kernel has an
explicit lower bound; the near and far comparisons share one physical scale. -/
theorem shifted_poisson_lower {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : 0 ≤ z.re) (hd : ‖z‖ ≤ η) :
    1 / (2 * η) ≤ (z.re + η) / Complex.normSq (z + (η : ℂ)) := by
  have hr : 0 < (z + (η : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hD := Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hr)
  have hsq : ‖z‖ ^ 2 ≤ η ^ 2 := (sq_le_sq₀ (norm_nonneg _) hη.le).mpr hd
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * η) hD).mpr
  rw [Complex.sq_norm] at hsq
  rw [one_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, add_zero] at hsq ⊢
  nlinarith

/-- Every nearby actual zero contributes at least its full multiplicity
divided by `2*eta` to the retained reserve, without a simplicity assumption. -/
theorem nearPoisson_lower {η : ℝ} (hη : 0 < η) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) (hd : ‖s - ρ.1‖ < η) :
    (analyticZetaZeroMultiplicity ρ : ℝ) / (2 * η) ≤ nearPoisson η s ρ := by
  have hp := shifted_poisson_lower hη (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ).le hd.le
  have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
  have he : s - ρ.1 + (η : ℂ) = s + (η : ℂ) - ρ.1 := by ring
  simp only [Complex.sub_re, he] at hh
  rw [nearPoisson, if_pos hd]
  convert! hh using 1
  · ring
  · simp only [zetaGlobalPoissonSummand, Complex.add_re, Complex.ofReal_re]
    ring

/-- The original near-distance remainder is supported on a genuinely finite
complete subset of the zeta divisor, including at a boundary evaluation point. -/
theorem finite_support_nearTerm (B η : ℝ) (s : ℂ) :
    (Function.support (nearTerm B η s)).Finite := by
  have hf : {ρ : NontrivialZetaZero | |ρ.1.im| ≤ |s.im| + |η|}.Finite := by
    simpa only [zetaSpectralCoordinate_re] using
      spectralZetaZeroWindowSet_finite (by positivity : 0 ≤ |s.im| + |η|)
  apply hf.subset
  intro ρ hρ
  have hd : ‖s - ρ.1‖ < η := by
    by_contra hn
    exact hρ (by simp [nearTerm, hn])
  have hi : |s.im - ρ.1.im| ≤ ‖s - ρ.1‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s - ρ.1)
  have htriangle : |ρ.1.im| ≤ |s.im - ρ.1.im| + |s.im| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (ρ.1.im - s.im) s.im
  change |ρ.1.im| ≤ |s.im| + |η|
  linarith [le_abs_self η]

/-- The finite near ball and complete far complement reconstruct the
original complex remainder without any sign or multiplicity loss. -/
theorem tsum_eq_near_add_far {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) :
    (∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B s ρ) =
      (∑' ρ : NontrivialZetaZero, nearTerm B η s ρ) +
      ∑' ρ : NontrivialZetaZero, farTerm B η s ρ := by
  have hn : Summable (nearTerm B η s) := summable_of_hasFiniteSupport (finite_support_nearTerm B η s)
  rw [← hn.tsum_add (summable_farTerm hB hη hs)]
  apply tsum_congr
  intro ρ
  by_cases hd : ‖s - ρ.1‖ < η
  · simp [nearTerm, farTerm, hd, not_le.mpr hd]
  · simp [nearTerm, farTerm, hd, le_of_not_gt hd]

/-- An elementary upper allowance for the original shifted xi Poisson mass. -/
def poissonAllowance (η t : ℝ) : ℝ :=
  η / (η ^ 2 + t ^ 2) + 1 / η + 448 * localZetaLogHeight 0 +
    Real.log (1 + η + |t|) / 2

/-- The actual shifted xi mass is bounded by a fully elementary
half-logarithmic expression, retaining its exact nonreal pole. -/
theorem re_logDeriv_shift_le {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 4) (t : ℝ) :
    (logDeriv riemannXi (((1 + η : ℝ) : ℂ) + I * t)).re ≤ poissonAllowance η t := by
  have hσ : 1 < 1 + η := by linarith
  have hs : 1 < (((1 + η : ℝ) : ℂ) + I * t).re := by simpa using hσ
  have he := congrArg Complex.re (zeta_global_complex_budget hs)
  have hp : (1 / ((((1 + η : ℝ) : ℂ) + I * t) - 1) : ℂ).re = η / (η ^ 2 + t ^ 2) := by
    have hc : (((1 + η : ℝ) : ℂ) + I * t) - 1 = (η : ℂ) + I * t := by push_cast; ring
    rw [hc, zetaPole_real_part]
  simp only [Complex.add_re, hp] at he
  have hc := re_zetaGlobalRegularCorrection_le_half_log hσ.le t
  have hn := norm_neg_logDeriv_riemannZeta_re_le_real_axis hσ t
  rw [Real.norm_eq_abs] at hn
  have hr := neg_logDeriv_riemannZeta_real_le_local hη hηsmall
  unfold poissonAllowance
  linarith [neg_le_abs (-logDeriv riemannZeta (((1 + η : ℝ) : ℂ) + I * t)).re]

/-- On `Re s = 1`, every omitted Gaussian remainder is paid for by a
proved elementary allowance. This bound has no unspecified zero sum or xi value. -/
theorem norm_tsum_farTerm_le_elementary {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 4) (t : ℝ) :
    ‖∑' ρ : NontrivialZetaZero, farTerm B η (1 + I * t) ρ‖ ≤
      (24 * B / η ^ 2) * poissonAllowance η t := by
  have hs : 1 ≤ (1 + I * (t : ℂ)).re := by simp
  have h := norm_tsum_farTerm_le hB hη hs
  have he : 1 + I * (t : ℂ) + (η : ℂ) = ((1 + η : ℝ) : ℂ) + I * t := by push_cast; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (re_logDeriv_shift_le hη hηsmall t) (by positivity))

/-- The elementary boundary allowance keeps the entire signed nearby
reserve. The coarser scalar bound is not substituted for this source of cancellation. -/
theorem norm_tsum_farTerm_le_elementary_reserve {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 4) (t : ℝ) :
    ‖∑' ρ : NontrivialZetaZero, farTerm B η (1 + I * t) ρ‖ ≤ (24 * B / η ^ 2) *
      (poissonAllowance η t - ∑' ρ : NontrivialZetaZero, nearPoisson η (1 + I * t) ρ) := by
  have hs : 1 ≤ (1 + I * (t : ℂ)).re := by simp
  have h := norm_tsum_farTerm_le_reserve hB hη hs
  have he : 1 + I * (t : ℂ) + (η : ℂ) = ((1 + η : ℝ) : ℂ) + I * t := by push_cast; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (re_logDeriv_shift_le hη hηsmall t) _) (by positivity))

end
end RiemannGaussian.ZetaGaussianDistanceRemainder
