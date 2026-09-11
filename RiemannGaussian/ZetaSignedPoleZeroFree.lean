/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCompletionSupportBudget

/-!
# Retaining the signed pole subtraction in the phase zero budget

The nonconstant pole terms are negative on the near-edge sampling range.
Their complete sum therefore has no positive quadratic pole cost. The
constant mode also retains its favorable auxiliary-pole subtraction.
These facts apply to every admissible coefficient family, before the
existing exact family is used to obtain a literal zero-free region.
The independent arithmetic bound throughout the interior strip remains open.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical Topology

/-- The comparison coefficient stays below this rational upper bound
on the sampling interval used in the signed pole estimate. -/
theorem zetaStechkinWeight_le_eight_seventeenths {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 4 / 3) :
    zetaStechkinWeight σ ≤ (8 / 17 : ℝ) := by
  have hs : 0 < Real.sqrt (1 + 4 * σ ^ 2) := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + 4 * σ ^ 2 by positivity)
  have hσsq : σ ^ 2 ≤ (16 / 9 : ℝ) := by nlinarith
  have he : zetaStechkinWeight σ = σ / Real.sqrt (1 + 4 * σ ^ 2) := by
    unfold zetaStechkinWeight zetaStechkinAbscissa
    congr 1
    ring
  rw [he]
  apply (div_le_iff₀ hs).mpr
  nlinarith

/-- Both squared pole distances and the signed leading difference are
controlled together. The subtraction has a positive gap before it is
multiplied by the squared ordinate. -/
theorem zetaStechkinPole_parameters {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 4 / 3) :
    (zetaStechkinAbscissa σ - 1) ^ 2 ≤ (7 / 8 : ℝ) ∧
      (5 / 51 : ℝ) ≤ zetaStechkinWeight σ * (zetaStechkinAbscissa σ - 1) -
        (σ - 1) := by
  have ht := lt_zetaStechkinAbscissa hσ
  have hq := zetaStechkinAbscissa_quadratic σ
  have hm := zetaStechkinWeight_mul hσ
  have hc := zetaStechkinWeight_le_eight_seventeenths hσ hσu
  have hσsq : σ ^ 2 ≤ (16 / 9 : ℝ) := by nlinarith
  have ha : zetaStechkinAbscissa σ - 1 ≤ (14 / 15 : ℝ) := by nlinarith
  constructor
  · nlinarith
  · nlinarith only [hm, hc, hσu]

/-- The full signed pole term is strictly negative away from its
constant phase on this interval. Replacing it by the first positive
summand would introduce an unnecessary quadratic pole error. -/
theorem zetaStechkinPoleBudget_neg {σ y : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 4 / 3) (hy : 3 ≤ y ^ 2) :
    zetaStechkinPoleBudget σ y < 0 := by
  let x := σ - 1
  let b := zetaStechkinAbscissa σ - 1
  let c := zetaStechkinWeight σ
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxu : x ≤ (1 / 3 : ℝ) := by dsimp [x]; linarith
  have hb : 0 < b := by dsimp [b]; linarith [lt_zetaStechkinAbscissa hσ]
  have hc : 0 < c := (zetaStechkinWeight_mem_Ioo hσ).1
  obtain ⟨hb2, hgap⟩ := zetaStechkinPole_parameters hσ hσu
  change b ^ 2 ≤ (7 / 8 : ℝ) at hb2
  change (5 / 51 : ℝ) ≤ c * b - x at hgap
  have hfirst : x * b ^ 2 ≤ (7 / 24 : ℝ) := by
    calc
      _ ≤ x * (7 / 8) := mul_le_mul_of_nonneg_left hb2 hx
      _ ≤ _ := by linarith
  have hsecond : (5 / 17 : ℝ) ≤ (c * b - x) * y ^ 2 := by
    have h := mul_le_mul hgap hy (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith : 0 ≤ c * b - x)
    norm_num at h
    exact h
  have hdrop : 0 ≤ c * b * x ^ 2 := by positivity
  have hden1 : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x]
  have hden2 : 0 < b ^ 2 + y ^ 2 := by nlinarith [sq_nonneg b]
  change x / (x ^ 2 + y ^ 2) - c * (b / (b ^ 2 + y ^ 2)) < 0
  rw [sub_neg, ← mul_div_assoc]
  apply (div_lt_div_iff₀ hden1 hden2).mpr
  nlinarith only [hfirst, hsecond, hdrop]

/-- The zero-frequency pole keeps its exact auxiliary subtraction. -/
theorem zetaStechkinPoleBudget_zero {σ : ℝ} (hσ : 1 < σ) :
    zetaStechkinPoleBudget σ 0 = 1 / (σ - 1) -
      zetaStechkinWeight σ / (zetaStechkinAbscissa σ - 1) := by
  have hx : σ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hσ)
  have ht : zetaStechkinAbscissa σ - 1 ≠ 0 := by
    have h := lt_zetaStechkinAbscissa hσ.le
    linarith
  unfold zetaStechkinPoleBudget
  simp only [sq, zero_mul, add_zero]
  field_simp

/-- Every summable nonnegative real-frequency family with a separated
nonconstant spectrum has a pole budget supported only at its constant
mode. The complete countable signed sum and the constant subtraction
are retained; the gap is imposed on the actual sampled ordinates. -/
theorem zetaPhase_stechkinPole_le_constant {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ y : ℝ}
    (hσ : 1 < σ) (hσu : σ ≤ 4 / 3) (hω0 : ω 0 = 0)
    (hω : ∀ n, 3 ≤ (ω (n + 1) * y) ^ 2) :
    (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)) ≤
      a 0 / (σ - 1) - a 0 * zetaStechkinWeight σ / (zetaStechkinAbscissa σ - 1) := by
  have hp := summable_zetaPhase_stechkin_pole (ω := ω) ha hs hσ y
  rw [hp.tsum_eq_zero_add]
  have htail : (∑' n : ℕ, a (n + 1) *
      zetaStechkinPoleBudget σ (ω (n + 1) * y)) ≤ 0 := by
    apply tsum_nonpos
    intro n
    apply mul_nonpos_of_nonneg_of_nonpos (ha (n + 1))
    exact (zetaStechkinPoleBudget_neg hσ.le hσu (hω n)).le
  simp only [hω0, zero_mul, zetaStechkinPoleBudget_zero hσ]
  simp only [div_eq_mul_inv]
  nlinarith only [htail]

/-- Every nonconstant integer frequency satisfies the separation
condition at an actual zero ordinate. No frequency count or particular
coefficient family is prescribed. -/
theorem phase_stechkinPole_le_constant {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ y : ℝ}
    (hσ : 1 < σ) (hσu : σ ≤ 4 / 3) (hy : 3 ≤ y ^ 2) :
    (∑' n : ℕ, a n * zetaStechkinPoleBudget σ ((n : ℝ) * y)) ≤
      a 0 / (σ - 1) - a 0 * zetaStechkinWeight σ / (zetaStechkinAbscissa σ - 1) := by
  apply zetaPhase_stechkinPole_le_constant ha hs hσ hσu (by norm_num)
  intro n
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hsq : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg y)
  rw [mul_pow]
  nlinarith only [hm, hy]

/-- Every admissible phase family retains its full source, arithmetic
work, negative completion constant and constant-pole reserve together.
There is no positive quadratic pole cost on this sampling interval. -/
theorem phase_shifted_source_add_primeWork_add_signedPoleReserve_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {κ : ℝ} (hκ : 0 < κ)
    (hκd : κ * (1 - rho.1.re) ≤ 1 / 3) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaStechkinPrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) +
      (1 - rho.1.re) * (a 0 * zetaStechkinWeight (1 + κ * (1 - rho.1.re)) /
        (zetaStechkinAbscissa (1 + κ * (1 - rho.1.re)) - 1)) +
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + κ * (1 - rho.1.re))) *
        (Real.log 2 / 2) * (∑' n, a n) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + κ * (1 - rho.1.re))) *
        ((a 0 * Real.log (1 + κ * (1 - rho.1.re)) +
          phaseOscillatoryMass a * Real.log (1 + κ * (1 - rho.1.re) + |rho.1.im|) +
            phaseLogFrequencyMass a) / 2) := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < κ * d := mul_pos hκ hd
  have hσ : 1 < 1 + κ * d := by linarith
  have hσu : 1 + κ * d ≤ 4 / 3 := by dsimp [d]; linarith
  have hH := summable_phase_globalHeight_of_logFrequency ha hs hlog hσ rho.1.im
  have hmain := zetaPhase_stechkin_source_add_primeWork_add_completionReserve_le
    (ω := fun n ↦ (n : ℝ)) ha hs 1 (by norm_num) rho hρ hσ hH
  have hpole := phase_stechkinPole_le_constant ha hs hσ hσu
    (nontrivialZetaZero_im_sq_gt_three rho).le
  have hcost := mul_le_mul_of_nonneg_left
    (phase_global_half_log_le_split_budget ha hs hlog hσ rho.1.im)
    (show 0 ≤ 1 - zetaStechkinWeight (1 + κ * d) by
      linarith [(zetaStechkinWeight_mem_Ioo hσ.le).2])
  rw [show 1 + κ * d - rho.1.re = κ * d + d by dsimp [d]; ring] at hmain
  simp only [zetaPhaseKernel_natCast] at hmain
  rw [add_sub_cancel_left] at hpole
  have hsum : a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d) +
      (∑' m : ℕ, zetaStechkinPrimeWeight (1 + κ * d) m *
        phaseContactKernel a (rho.1.im * Real.log m)) +
      a 0 * zetaStechkinWeight (1 + κ * d) / (zetaStechkinAbscissa (1 + κ * d) - 1) +
      (1 - zetaStechkinWeight (1 + κ * d)) * (Real.log 2 / 2) * (∑' n, a n) ≤
      a 0 / (κ * d) + (1 - zetaStechkinWeight (1 + κ * d)) *
        ((a 0 * Real.log (1 + κ * d) +
          phaseOscillatoryMass a * Real.log (1 + κ * d + |rho.1.im|) +
            phaseLogFrequencyMass a) / 2) := by linarith
  have hm := mul_le_mul_of_nonneg_left hsum hd.le
  have he1 : d * (a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d)) =
      a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ + 1) := by
    have hk1 : κ + 1 ≠ 0 := by positivity
    field_simp
  have he0 : d * (a 0 / (κ * d)) = a 0 / κ := by field_simp
  simp only [mul_add] at hm
  rw [he1, he0] at hm
  unfold phaseShiftSource
  dsimp only [d] at hm ⊢
  linear_combination hm

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

private theorem exact_log_summable :
    Summable (fun n : ℕ => phaseContactExactFamily n * Real.log n) :=
  (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
    (fun n => Real.log n)).summable

/-- The unchanged exact family obeys this stronger necessary zero
inequality. The whole prime work and the constant-pole reserve remain
on the source side; the former quadratic pole allowance has disappeared. -/
theorem phaseContactExact_signedPole_zero_budget
    (rho : NontrivialZetaZero) (hρ : 35 / 39 ≤ rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) * (∑' m : ℕ,
      zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) +
      (1 - rho.1.re) *
        (phaseContactExactFamily 0 * zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) /
          (zetaStechkinAbscissa (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) - 1)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((481 / 1600 : ℝ) * (1 - rho.1.re) +
          (61 / 200 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) - 1 / 8) := by
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
  have h := phase_shifted_source_add_primeWork_add_signedPoleReserve_le
    phaseContactExactFamily_nonneg exact_summable exact_log_summable rho (by linarith)
    (κ := 13 / 4) (by norm_num) (by linarith)
  rw [he] at h
  dsimp only [d] at hHm
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h, hHm, hmult, phaseContactExactRoot_source_lower]

/-- The previously proved eta height exclusion gives this sharper
logarithmic height floor, without a numerical zeta-zero certificate. -/
theorem thirteen_tenths_lt_log_abs_im_add_two (rho : NontrivialZetaZero) :
    (13 / 10 : ℝ) < Real.log (|rho.1.im| + 2) := by
  have hy : (17 / 10 : ℝ) < |rho.1.im| := by
    nlinarith [nontrivialZetaZero_im_sq_gt_three rho, sq_abs rho.1.im,
      abs_nonneg rho.1.im]
  have hlow := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 37 / 40)
  have hlog : Real.log (37 / 10 : ℝ) = 2 * Real.log 2 + Real.log (37 / 40 : ℝ) := by
    rw [show 2 * Real.log 2 = Real.log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      ← Real.log_mul (by norm_num : (2 : ℝ) ^ 2 ≠ 0)
        (by norm_num : (37 / 40 : ℝ) ≠ 0)]
    norm_num
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 37 / 10)
    (by linarith : (37 / 10 : ℝ) ≤ |rho.1.im| + 2)
  rw [hlog] at hmono
  norm_num at hlow
  linarith [Real.log_two_gt_d9]

/-- The signed pole improvement yields a height-dependent edge width.
Its leading constant uses the existing source and oscillatory mass bounds. -/
def zetaSignedPoleZeroMargin (t : ℝ) : ℝ :=
  792 / (7625 * Real.log (|t| + 2) - 2000)

/-- The new denominator is positive at every ordinate, including zero. -/
theorem zetaSignedPole_denominator_pos (t : ℝ) :
    0 < 7625 * Real.log (|t| + 2) - 2000 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
  linarith [Real.log_two_gt_d9]

/-- The signed pole exclusion has positive width at every height. -/
theorem zetaSignedPoleZeroMargin_pos (t : ℝ) : 0 < zetaSignedPoleZeroMargin t :=
  div_pos (by norm_num) (zetaSignedPole_denominator_pos t)

/-- After retaining the signed pole cancellation, the explicit
allowance is below the source by a positive multiple of the edge distance.
No estimate for a zeta-dependent arithmetic sum is assumed. -/
theorem zetaSignedPole_allowance_le {d L c : ℝ}
    (hd : 0 ≤ d) (hL : 13 / 10 ≤ L)
    (hdL : d * (7625 * L - 2000) ≤ 792) (hc : 4 / 9 ≤ c) :
    d * (1 - c) * ((481 / 1600 : ℝ) * d + (61 / 200 : ℝ) * L - 1 / 8) ≤
      (11 / 625 : ℝ) - (221 / 28080 : ℝ) * d := by
  have hdsmall : d ≤ 4 / 39 := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hL)]
  have hB : 0 ≤ (481 / 1600 : ℝ) * d + (61 / 200 : ℝ) * L - 1 / 8 := by linarith
  have hm := mul_le_mul_of_nonneg_right (show 1 - c ≤ 5 / 9 by linarith)
    (mul_nonneg hd hB)
  have hsq := mul_le_mul_of_nonneg_left hdsmall hd
  nlinarith only [hm, hsq, hdL]

/-- Every genuine nontrivial zero lies strictly beyond the wider
right-edge margin. The arithmetic and constant-pole reserves have proved
nonnegative sign, and the complete remaining allowance is too small. -/
theorem zetaSignedPole_margin_lt_one_sub_re (rho : NontrivialZetaZero) :
    zetaSignedPoleZeroMargin rho.1.im < 1 - rho.1.re := by
  let d := 1 - rho.1.re
  let L := Real.log (|rho.1.im| + 2)
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hL : 13 / 10 < L := thirteen_tenths_lt_log_abs_im_add_two rho
  by_contra hn
  have hdm : d ≤ 792 / (7625 * L - 2000) := le_of_not_gt hn
  have hdL := (le_div_iff₀ (zetaSignedPole_denominator_pos rho.1.im)).mp hdm
  have hdsmall : d ≤ 4 / 39 := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hL.le)]
  have hρ : 35 / 39 ≤ rho.1.re := by dsimp [d] at hdsmall; linarith
  have hσ : 1 ≤ 1 + (13 / 4 : ℝ) * d := by linarith
  have h := phaseContactExact_signedPole_zero_budget rho hρ
  have hwork : 0 ≤ d * (∑' m : ℕ,
      zetaStechkinPrimeWeight (1 + (13 / 4 : ℝ) * d) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) := by
    apply mul_nonneg hd.le
    exact tsum_nonneg (fun m => mul_nonneg (zetaStechkinPrimeWeight_nonneg hσ m)
      (phaseContactExactFamily_kernel_nonneg _))
  have hconst : 0 ≤ d *
      (phaseContactExactFamily 0 * zetaStechkinWeight (1 + (13 / 4 : ℝ) * d) /
        (zetaStechkinAbscissa (1 + (13 / 4 : ℝ) * d) - 1)) := by
    have ha := phaseContactExactFamily_nonneg 0
    have hc := (zetaStechkinWeight_mem_Ioo hσ).1.le
    have ht : 0 < zetaStechkinAbscissa (1 + (13 / 4 : ℝ) * d) - 1 := by
      linarith [lt_zetaStechkinAbscissa hσ]
    positivity
  have hlogy : Real.log (1 + (13 / 4 : ℝ) * d + |rho.1.im|) ≤ L := by
    apply Real.log_le_log (by positivity)
    linarith
  have hc := four_ninths_le_zetaStechkinWeight hσ
  have hc0 := sub_nonneg.mpr (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hH := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hlogy (by norm_num : (0 : ℝ) ≤ 61 / 200))
    (mul_nonneg hd.le hc0)
  have hb := zetaSignedPole_allowance_le hd.le hL.le hdL hc
  change (11 / 625 : ℝ) + d * _ + d * _ ≤ _ at h
  nlinarith only [h, hwork, hconst, hH, hb, hd]

/-- Critical reflection preserves the ordinate and supplies the same
improved margin at the left edge. -/
theorem zetaSignedPole_margin_lt_re (rho : NontrivialZetaZero) :
    zetaSignedPoleZeroMargin rho.1.im < rho.1.re := by
  have h := zetaSignedPole_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- The literal nontrivial zeros obey this narrower strip at every
ordinate, with every analytic and arithmetic assumption discharged. -/
theorem nontrivialZetaZero_mem_signedPole_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Set.Ioo (zetaSignedPoleZeroMargin rho.1.im)
      (1 - zetaSignedPoleZeroMargin rho.1.im) :=
  ⟨zetaSignedPole_margin_lt_re rho,
    by linarith [zetaSignedPole_margin_lt_one_sub_re rho]⟩

/-- The explicit width is uniformly below one quarter, including at
low heights. This keeps the literal nonvanishing bridge in the positive
half-plane without introducing a height restriction. -/
theorem zetaSignedPoleZeroMargin_lt_one_quarter (t : ℝ) :
    zetaSignedPoleZeroMargin t < 1 / 4 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
  unfold zetaSignedPoleZeroMargin
  apply (div_lt_iff₀ (zetaSignedPole_denominator_pos t)).mpr
  linarith [Real.log_two_gt_d9]

/-- The literal Riemann zeta function is nonzero on the wider closed
right-edge region, at every height and explicitly away from its pole. -/
theorem riemannZeta_ne_zero_of_signedPole_margin {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - zetaSignedPoleZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [zetaSignedPoleZeroMargin_lt_one_quarter s.im]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := (nontrivialZetaZero_mem_signedPole_strip rho).2
  change s.re < 1 - zetaSignedPoleZeroMargin s.im at h
  linarith

/-- The new exclusion is strictly wider than this fixed multiple of
the preceding strongest project width, at every real ordinate. -/
theorem completionReserve_margin_scaled_lt_signedPole (t : ℝ) :
    (1584 / 1525 : ℝ) * zetaCompletionReserveZeroMargin t < zetaSignedPoleZeroMargin t := by
  have hL : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  unfold zetaCompletionReserveZeroMargin zetaSignedPoleZeroMargin
  rw [show (1584 / 1525 : ℝ) * (1 / (10 * Real.log (|t| + 2))) =
    792 / (7625 * Real.log (|t| + 2)) by ring]
  exact div_lt_div_of_pos_left (by norm_num) (zetaSignedPole_denominator_pos t) (by linarith)

end
end RiemannGaussian
