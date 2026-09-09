/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaCarrier

/-!
# Signed control of the dyadic eta completion by phase

The dyadic term `w = 2 * 2^(-s)` retains both its amplitude and phase.
When `cos(Im(s) * log 2) ≤ 0`, the denominator `1-w` stays uniformly
away from zero. On the closed half strip `1/2 ≤ Re(s) ≤ 1`, its
negative logarithmic derivative has real part between `log 2 / 2`
and `2 * log 2 / 3`. These are independent estimates for the literal
completion term, not a bound for the complete Suzuki carrier.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- The full complex dyadic term in the eta completion factor. -/
def pairedEtaDyadicTerm (s : ℂ) : ℂ := 2 * (2 : ℂ) ^ (-s)

private lemma log_two_complex : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm

/-- The dyadic amplitude and cosine are retained in the exact real part. -/
theorem pairedEtaDyadicTerm_re (s : ℂ) :
    (pairedEtaDyadicTerm s).re =
      2 * Real.exp (-s.re * Real.log 2) * Real.cos (s.im * Real.log 2) := by
  unfold pairedEtaDyadicTerm
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), log_two_complex]
  simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, Complex.exp_re,
    ofReal_re, neg_re, ofReal_im, neg_im, mul_im, add_zero]
  rw [show Real.log 2 * -s.im = -(s.im * Real.log 2) by ring, Real.cos_neg]
  rw [show Real.log 2 * -s.re = -s.re * Real.log 2 by ring]
  ring

/-- The dyadic amplitude is exact at every complex argument. -/
theorem normSq_pairedEtaDyadicTerm (s : ℂ) :
    normSq (pairedEtaDyadicTerm s) = 4 * Real.exp (-2 * s.re * Real.log 2) := by
  unfold pairedEtaDyadicTerm
  rw [normSq_mul, Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    log_two_complex, ← Complex.sq_norm (Complex.exp _), Complex.norm_exp]
  norm_num only [normSq_ofNat, mul_re, ofReal_re, neg_re, ofReal_im, neg_im,
    zero_mul, sub_zero]
  rw [← Real.exp_nat_mul _ 2]
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

/-- The logarithmic derivative keeps its complex dyadic quotient. -/
theorem pairedEtaFactorLogDerivative_eq_dyadic (s : ℂ) :
    pairedEtaFactorLogDerivative s =
      (Real.log 2 : ℂ) * (pairedEtaDyadicTerm s / (1 - pairedEtaDyadicTerm s)) := by
  unfold pairedEtaFactorLogDerivative pairedEtaFactor pairedEtaDyadicTerm
  rw [log_two_complex]
  ring

private lemma normSq_one_sub (w : ℂ) :
    normSq (1 - w) = 1 + normSq w - 2 * w.re := by
  simp [Complex.normSq_sub]

private lemma re_div_one_sub (w : ℂ) :
    (w / (1 - w)).re = (w.re - normSq w) / normSq (1 - w) := by
  simp only [Complex.div_re, sub_re, one_re, sub_im, one_im, normSq_apply]
  ring

/-- A nonpositive dyadic cosine provides a uniform squared denominator
lower bound at every real part, including the completion boundary. -/
theorem normSq_pairedEtaFactor_phase_lower {s : ℂ}
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    1 + normSq (pairedEtaDyadicTerm s) ≤ normSq (pairedEtaFactor s) := by
  have hw : (pairedEtaDyadicTerm s).re ≤ 0 := by
    rw [pairedEtaDyadicTerm_re]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hphase
  change 1 + normSq (pairedEtaDyadicTerm s) ≤ normSq (1 - pairedEtaDyadicTerm s)
  rw [normSq_one_sub]
  linarith

/-- The phase condition excludes every dyadic completion zero without
an exceptional-height assumption. -/
theorem pairedEtaFactor_ne_zero_of_nonpos_cos {s : ℂ}
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) : pairedEtaFactor s ≠ 0 := by
  apply Complex.normSq_pos.mp
  have := normSq_pairedEtaFactor_phase_lower hphase
  linarith [normSq_nonneg (pairedEtaDyadicTerm s)]

/-- Exact strip amplitudes trap the squared dyadic radius between one
and two, independently of the imaginary coordinate. -/
theorem normSq_pairedEtaDyadicTerm_strip_bounds {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1) :
    1 ≤ normSq (pairedEtaDyadicTerm s) ∧ normSq (pairedEtaDyadicTerm s) ≤ 2 := by
  rw [normSq_pairedEtaDyadicTerm]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := Real.exp_le_exp.mpr (show -2 * Real.log 2 ≤ -2 * s.re * Real.log 2 by
    nlinarith)
  have hupp := Real.exp_le_exp.mpr (show -2 * s.re * Real.log 2 ≤ -Real.log 2 by
    nlinarith)
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have he2 : Real.exp (-2 * Real.log 2) = 1 / 4 := by
    rw [show -2 * Real.log 2 = -Real.log 2 + -Real.log 2 by ring, Real.exp_add, he]
    norm_num
  rw [he2] at hlow
  rw [he] at hupp
  constructor <;> linarith

/-- The dyadic completion logarithmic derivative has a uniform signed
strip enclosure. The sign is kept rather than replaced by its norm. -/
theorem pairedEtaFactorLogDerivative_re_phase_strip_bounds {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    Real.log 2 / 2 ≤ -(pairedEtaFactorLogDerivative s).re ∧
      -(pairedEtaFactorLogDerivative s).re ≤ 2 * Real.log 2 / 3 := by
  let w := pairedEtaDyadicTerm s
  have hw : w.re ≤ 0 := by
    dsimp [w]
    rw [pairedEtaDyadicTerm_re]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hphase
  obtain ⟨hql, hqu⟩ := normSq_pairedEtaDyadicTerm_strip_bounds hlo hhi
  change 1 ≤ normSq w at hql
  change normSq w ≤ 2 at hqu
  have hd : 0 < normSq (1 - w) := by rw [normSq_one_sub]; linarith
  have hr : -(2 / 3 : ℝ) ≤ (w / (1 - w)).re ∧
      (w / (1 - w)).re ≤ -(1 / 2 : ℝ) := by
    rw [re_div_one_sub]
    constructor
    · apply (le_div_iff₀ hd).mpr
      rw [normSq_one_sub]
      linarith
    · apply (div_le_iff₀ hd).mpr
      rw [normSq_one_sub]
      linarith
  rw [pairedEtaFactorLogDerivative_eq_dyadic]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change Real.log 2 / 2 ≤ -(Real.log 2 * (w / (1 - w)).re) ∧
    -(Real.log 2 * (w / (1 - w)).re) ≤ 2 * Real.log 2 / 3
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hr.1 hl.le,
    mul_le_mul_of_nonneg_left hr.2 hl.le]

/-- The complete complex logarithmic derivative lies in a fixed disk
on a favorable phase. This retains a usable bound for arbitrary complex
tests, not just their real coefficients. -/
theorem norm_pairedEtaFactorLogDerivative_add_half_le {s : ℂ}
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    ‖pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2‖ ≤ Real.log 2 / 2 := by
  let w := pairedEtaDyadicTerm s
  have hw : w.re ≤ 0 := by
    dsimp [w]
    rw [pairedEtaDyadicTerm_re]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hphase
  have hn : 1 - w ≠ 0 := pairedEtaFactor_ne_zero_of_nonpos_cos hphase
  have hd : 0 < normSq (1 - w) := Complex.normSq_pos.mpr hn
  have he : w / (1 - w) + 1 / 2 = (1 + w) / (2 * (1 - w)) := by
    field_simp
    ring
  have hq : normSq (w / (1 - w) + 1 / 2) ≤ 1 / 4 := by
    rw [he, normSq_div, normSq_mul]
    norm_num only [normSq_ofNat]
    apply (div_le_iff₀ (by positivity)).mpr
    rw [normSq_one_sub, Complex.normSq_add]
    simp only [normSq_one, one_mul, conj_re]
    linarith
  have hf : pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2 =
      (Real.log 2 : ℂ) * (w / (1 - w) + 1 / 2) := by
    rw [pairedEtaFactorLogDerivative_eq_dyadic]
    dsimp [w]
    ring
  have hsq : normSq (pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2) ≤
      (Real.log 2) ^ 2 / 4 := by
    rw [hf, normSq_mul, normSq_ofReal]
    nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg (Real.log 2))]
  rw [← Complex.sq_norm] at hsq
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [norm_nonneg (pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2)]

/-- Every complex weighted dyadic contribution has a centered real
enclosure. Its exact phase remains in the expression being bounded. -/
theorem abs_re_mul_pairedEtaFactorLogDerivative_add_half_le (B : ℂ) {s : ℂ}
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    |(B * (pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2)).re| ≤
      ‖B‖ * (Real.log 2 / 2) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_pairedEtaFactorLogDerivative_add_half_le hphase)
    (norm_nonneg B)

end
end RiemannGaussian
