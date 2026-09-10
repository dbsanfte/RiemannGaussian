/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCompletionReserve
import RiemannGaussian.ZetaPhaseHalfLogZeroFree

/-!
# A wider literal zero exclusion from the retained completion reserve

The all-family completion reserve pays the existing exact family's fixed
frequency cost and its quadratic pole allowance in the new edge region.
No coefficients are changed or searched for. Every genuine nontrivial
zero has distance greater than `1/(10*log(abs(t)+2))` from both edges.
The interior right-half signed inequality remains open; this is a proved
partial exclusion and does not assert RH or a best published region.
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

/-- The existing exact family has this constant-mode upper bound.
Its coefficients remain the previously proved algebraic optimizer. -/
theorem phaseContactExactFamily_zero_le : phaseContactExactFamily 0 ≤ (37 / 200 : ℝ) := by
  have he := phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
  change phaseContactExactFamily 0 = phaseContactExactCoefficients 0 at he
  rw [he]
  have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le 0)).2
  norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
  linarith

/-- The whole exact family has at least three quarters of a unit of
mass. This lower bound controls a favorable signed completion term. -/
theorem three_quarters_le_phaseContactExactFamily_mass :
    (3 / 4 : ℝ) ≤ ∑' n, phaseContactExactFamily n := by
  have he := (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
    (fun _ ↦ 1)).tsum_eq
  simp only [mul_one] at he
  change (∑' n, phaseContactExactFamily n) = _ at he
  rw [he]
  calc
    (3 / 4 : ℝ) ≤ ∑ i : Fin 9, (phaseContactPrimalCenter i - 1 / 10 ^ 15) := by
      norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ, Fin.sum_univ_succ]
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ by
      linarith [(abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le i)).1])

/-- The recovered completion reserve of the actual family is at least
one quarter. It comes from the true signed completion, independently of
the arithmetic sum and of the location of a selected zero. -/
theorem phaseContactExactFamily_completionReserve_ge :
    (1 / 4 : ℝ) ≤ (Real.log 2 / 2) * (∑' n, phaseContactExactFamily n) := by
  have hlog : (1 / 3 : ℝ) ≤ Real.log 2 / 2 := by linarith [Real.log_two_gt_d9]
  have h := mul_le_mul hlog three_quarters_le_phaseContactExactFamily_mass
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by positivity : 0 ≤ Real.log 2 / 2)
  norm_num at h
  exact h

/-- Retaining the favorable constant gives this smaller actual zero
budget. The original phase kernel, sampling line, signed prime work,
source efficiency, and quadratic pole term remain explicit. -/
theorem phaseContactExact_completionReserve_zero_budget
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) * (∑' m : ℕ,
      zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((481 / 1600 : ℝ) * (1 - rho.1.re) +
          (61 / 200 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) - 1 / 8) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hσ : 1 ≤ 1 + (13 / 4 : ℝ) * d := by linarith
  have hlogσ := Real.log_nonneg hσ
  have hlogy : 0 ≤ Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg rho.1.im])
  have hlogσu := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (13 / 4 : ℝ) * d)
  have h0 := mul_le_mul_of_nonneg_right phaseContactExactFamily_zero_le hlogσ
  have hA := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le hlogy
  have hc : 0 ≤ d * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * d)) :=
    mul_nonneg hd.le (sub_nonneg.mpr (zetaStechkinWeight_mem_Ioo hσ).2.le)
  have hH : (phaseContactExactFamily 0 * Real.log (1 + (13 / 4 : ℝ) * d) +
      phaseOscillatoryMass phaseContactExactFamily *
        Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) +
      phaseLogFrequencyMass phaseContactExactFamily) / 2 -
      (Real.log 2 / 2) * (∑' n, phaseContactExactFamily n) ≤
      (481 / 1600 : ℝ) * d +
        (61 / 200 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) - 1 / 8 := by
    nlinarith only [h0, hA, hlogσu, phaseContactExactFamily_logFrequencyMass_le,
      phaseContactExactFamily_completionReserve_ge]
  have hHm := mul_le_mul_of_nonneg_left hH hc
  have hP := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * d ^ 2 / rho.1.im ^ 2 by positivity)
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hmult : 0 ≤ (4 / 17 : ℝ) * phaseContactExactFamily 1 *
      ((analyticZetaZeroMultiplicity rho : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (phaseContactExactFamily_nonneg 1)) (by linarith)
  have he : phaseShiftSource (phaseContactExactFamily 0)
      (phaseContactExactFamily 1 * (analyticZetaZeroMultiplicity rho : ℝ)) (13 / 4) =
      phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) := by
    rw [← phaseContactExactFamily_source]
    unfold phaseShiftSource phaseContactSource
    ring
  have h := phase_shifted_source_add_primeWork_add_completionReserve_le
    phaseContactExactFamily_nonneg exact_summable exact_log_summable rho hρ
    (κ := 13 / 4) (by norm_num)
  rw [he] at h
  dsimp only [d] at hHm hP
  simp only [div_eq_mul_inv] at hP h ⊢
  nlinarith only [h, hHm, hP, hmult, phaseContactExactRoot_source_lower]

/-- The eta exclusion at low height implies a useful lower bound for
the smaller logarithmic height at every genuine nontrivial zero. -/
theorem six_fifths_lt_log_abs_im_add_two (rho : NontrivialZetaZero) :
    (6 / 5 : ℝ) < Real.log (|rho.1.im| + 2) := by
  have hy : (3 / 2 : ℝ) < |rho.1.im| := by
    nlinarith [nontrivialZetaZero_im_sq_gt_three rho, sq_abs rho.1.im,
      abs_nonneg rho.1.im]
  have hlow := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 7 / 8)
  have hlog : Real.log (7 / 2 : ℝ) = 2 * Real.log 2 + Real.log (7 / 8 : ℝ) := by
    rw [show 2 * Real.log 2 = Real.log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      ← Real.log_mul (by norm_num : (2 : ℝ) ^ 2 ≠ 0)
      (by norm_num : (7 / 8 : ℝ) ≠ 0)]
    norm_num
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 7 / 2)
    (by linarith : (7 / 2 : ℝ) ≤ |rho.1.im| + 2)
  rw [hlog] at hmono
  norm_num at hlow
  linarith [Real.log_two_gt_d9]

/-- The new explicit width uses the retained completion constant and
the smaller logarithmic height. -/
def zetaCompletionReserveZeroMargin (t : ℝ) : ℝ := 1 / (10 * Real.log (|t| + 2))

/-- The new edge margin is positive at every real height. -/
theorem zetaCompletionReserveZeroMargin_pos (t : ℝ) :
    0 < zetaCompletionReserveZeroMargin t := by
  have hlog : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  unfold zetaCompletionReserveZeroMargin
  positivity

/-- The explicit completion and pole allowance is strictly below the
retained source throughout the new edge region. This numerical margin
is proved from the actual analytic bounds, without any arithmetic premise. -/
theorem zetaCompletionReserve_allowance_le {d L y c : ℝ}
    (hd : 0 ≤ d) (hL : 6 / 5 ≤ L) (hdL : d * L ≤ 1 / 10)
    (hy : 3 ≤ y ^ 2) (hc : 4 / 9 ≤ c) :
    d * (1 - c) * ((481 / 1600 : ℝ) * d + (61 / 200 : ℝ) * L - 1 / 8) +
      (793 / 400 : ℝ) * d ^ 2 / y ^ 2 ≤
      (61 / 360 : ℝ) * (d * L) - (79 / 172800 : ℝ) * d := by
  have hsmall : d ≤ 1 / 12 := by nlinarith
  have hB : 0 ≤ (481 / 1600 : ℝ) * d + (61 / 200 : ℝ) * L - 1 / 8 := by linarith
  have hm := mul_le_mul_of_nonneg_right (show 1 - c ≤ 5 / 9 by linarith)
    (mul_nonneg hd hB)
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg d) (by norm_num : (0 : ℝ) < 3) hy
  have hsq := mul_le_mul_of_nonneg_left hsmall hd
  rw [mul_div_assoc]
  nlinarith only [hm, hdiv, hsq, hd]

/-- After all the explicit completion and pole errors, the whole edge
allowance is below the original source by the fixed positive gap
`59/90000`. This is the quantitative inequality used in the contradiction. -/
theorem zetaCompletionReserve_allowance_add_gap_le {d L y c : ℝ}
    (hd : 0 ≤ d) (hL : 6 / 5 ≤ L) (hdL : d * L ≤ 1 / 10)
    (hy : 3 ≤ y ^ 2) (hc : 4 / 9 ≤ c) :
    d * (1 - c) * ((481 / 1600 : ℝ) * d + (61 / 200 : ℝ) * L - 1 / 8) +
      (793 / 400 : ℝ) * d ^ 2 / y ^ 2 + 59 / 90000 ≤ (11 / 625 : ℝ) := by
  have h := zetaCompletionReserve_allowance_le hd hL hdL hy hc
  nlinarith only [h, hdL, hd]

/-- Every actual zero stays strictly outside the new right-edge
region. The independent signed allowance leaves at least `59/90000`
below the source after all completion and quadratic pole costs. -/
theorem zetaCompletionReserve_margin_lt_one_sub_re (rho : NontrivialZetaZero) :
    zetaCompletionReserveZeroMargin rho.1.im < 1 - rho.1.re := by
  let d := 1 - rho.1.re
  let L := Real.log (|rho.1.im| + 2)
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hL : 6 / 5 < L := six_fifths_lt_log_abs_im_add_two rho
  by_contra hn
  have hdm : d ≤ 1 / (10 * L) := le_of_not_gt hn
  have hp := (le_div_iff₀ (by positivity : 0 < 10 * L)).mp hdm
  have hdL : d * L ≤ 1 / 10 := by nlinarith
  have hdsmall : d ≤ 1 / 12 := by nlinarith [mul_le_mul_of_nonneg_left hL.le hd.le]
  have hρ : 1 / 2 < rho.1.re := by dsimp [d] at hdsmall; linarith
  have hσ : 1 ≤ 1 + (13 / 4 : ℝ) * d := by linarith
  have h := phaseContactExact_completionReserve_zero_budget rho hρ
  have hwork : 0 ≤ d * (∑' m : ℕ,
      zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * d) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) := by
    apply mul_nonneg hd.le
    exact tsum_nonneg (fun m => mul_nonneg (zetaStechkinPrimeWeight_nonneg hσ m)
      (phaseContactExactFamily_kernel_nonneg _))
  have hlogy : Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) ≤ L := by
    apply Real.log_le_log (by positivity)
    linarith
  have hc := four_ninths_le_zetaStechkinWeight hσ
  have hc0 := sub_nonneg.mpr (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hH := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hlogy (by norm_num : (0 : ℝ) ≤ 61 / 200))
    (mul_nonneg hd.le hc0)
  have hb := zetaCompletionReserve_allowance_add_gap_le hd.le hL.le hdL
    (nontrivialZetaZero_im_sq_gt_three rho).le hc
  change (11 / 625 : ℝ) + d * _ ≤ _ at h
  nlinarith only [h, hwork, hH, hb]

/-- Critical reflection supplies the same improved edge distance on
the left, preserving the actual ordinate. -/
theorem zetaCompletionReserve_margin_lt_re (rho : NontrivialZetaZero) :
    zetaCompletionReserveZeroMargin rho.1.im < rho.1.re := by
  have h := zetaCompletionReserve_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every genuine nontrivial zero lies in this narrower two-sided
strip at every ordinate, with no unproved arithmetic antecedent. -/
theorem nontrivialZetaZero_mem_completionReserve_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Set.Ioo (zetaCompletionReserveZeroMargin rho.1.im)
      (1 - zetaCompletionReserveZeroMargin rho.1.im) :=
  ⟨zetaCompletionReserve_margin_lt_re rho,
    by linarith [zetaCompletionReserve_margin_lt_one_sub_re rho]⟩

/-- The width is uniformly small, so the literal nonvanishing bridge
stays in the positive half-plane at every real ordinate. -/
theorem zetaCompletionReserveZeroMargin_lt (t : ℝ) :
    zetaCompletionReserveZeroMargin t < 3 / 20 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
  have h : (2 / 3 : ℝ) < Real.log (|t| + 2) := by linarith [Real.log_two_gt_d9]
  unfold zetaCompletionReserveZeroMargin
  apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.log (|t| + 2))).mpr
  linarith

/-- The literal Riemann zeta function is nonzero throughout the wider
closed right-edge region, at all heights and explicitly away from its pole. -/
theorem riemannZeta_ne_zero_of_completionReserve_margin {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - zetaCompletionReserveZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [zetaCompletionReserveZeroMargin_lt s.im]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := (nontrivialZetaZero_mem_completionReserve_strip rho).2
  change s.re < 1 - zetaCompletionReserveZeroMargin s.im at h
  linarith

/-- The new exclusion width is strictly more than six fifths of the
previous strongest width at every real ordinate. -/
theorem six_fifths_phaseHalfLog_margin_lt_completionReserve (t : ℝ) :
    (6 / 5 : ℝ) * zetaPhaseHalfLogZeroMargin t < zetaCompletionReserveZeroMargin t := by
  have hsmall : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  have hlog : Real.log (|t| + 2) < Real.log (|t| + 22) :=
    Real.log_lt_log (by positivity) (by linarith)
  unfold zetaPhaseHalfLogZeroMargin zetaCompletionReserveZeroMargin localZetaLogHeight
  rw [show (6 / 5 : ℝ) * (1 / (12 * Real.log (|t| + 22))) =
    1 / (10 * Real.log (|t| + 22)) by ring]
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

end
end RiemannGaussian
