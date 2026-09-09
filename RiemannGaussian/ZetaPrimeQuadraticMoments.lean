/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeColourCancellation

/-!
# Separation of the complete prime quadratic and mixed product

The prime square has a double pole at every zeta zero, whereas its
product with the complete prime-divisor response has at most a simple
pole. A common finite weight clears both actual divisors except at the
selected zero. The whole mixed product then has a uniform bound at the
geometric scale, below the linear source of the prime square. The exact
quadratic identity is kept alongside that estimate.

This weight is constructed for these two responses: a weight that clears
the derivative-based Wronskians need not clear a logarithmic derivative
at zeros of higher multiplicity.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The actual prime square with the common quartic pole factor. -/
def zetaPrimeSquareResponse (s : ℂ) : ℂ :=
  (s - 1) ^ 4 * (logDeriv riemannZeta s) ^ 2

/-- The whole mixed product retains the complete divisor response
in its second factor, before estimating any individual moments. -/
def zetaPrimeMixedProductResponse (s : ℂ) : ℂ :=
  (s - 1) ^ 4 * (-logDeriv riemannZeta s) * zetaPrimeDivisorResponse s

private theorem selected_ne_one (rho : NontrivialZetaZero) : rho.1 ≠ 1 := by
  intro h
  have hr := NontrivialZetaZero.re_lt_one rho
  simp [h] at hr

private theorem analytic_quartic (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ (z - 1) ^ 4) s :=
  (analyticAt_id.sub analyticAt_const).pow 4

private theorem meromorphic_log (s : ℂ) : MeromorphicAt (logDeriv riemannZeta) s :=
  (meromorphicAt_riemannZeta s).deriv.div (meromorphicAt_riemannZeta s)

private theorem analytic_log {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (logDeriv riemannZeta) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact hz.deriv.div hz (riemannZeta_ne_zero_of_one_lt_re hs)

/-- The prime square is meromorphic everywhere, including all
multiple zeta zeros. -/
theorem meromorphicAt_zetaPrimeSquareResponse (s : ℂ) :
    MeromorphicAt zetaPrimeSquareResponse s :=
  (analytic_quartic s).meromorphicAt.mul ((meromorphic_log s).pow 2)

/-- The mixed product is meromorphic on the complete correction
half-plane; no zero-free assumption enters this continuation. -/
theorem meromorphicAt_zetaPrimeMixedProductResponse {s : ℂ} (hs : 1 / 2 < s.re) :
    MeromorphicAt zetaPrimeMixedProductResponse s := by
  have hz := meromorphicAt_riemannZeta s
  exact ((analytic_quartic s).meromorphicAt.mul (meromorphic_log s).neg).mul
    (hz.deriv.neg.sub (hz.mul (analyticAt_zetaProperPrimePowerSeries hs).meromorphicAt))

private theorem order_log (rho : NontrivialZetaZero) :
    meromorphicOrderAt (logDeriv riemannZeta) rho.1 = -1 := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_riemannZeta rho.1)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    have hm := analyticZetaZeroMultiplicity_positive rho
    exact_mod_cast (show (analyticZetaZeroMultiplicity rho : ℤ) ≠ 0 by omega)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    exact WithTop.coe_ne_top

private theorem order_quartic (rho : NontrivialZetaZero) :
    meromorphicOrderAt (fun z : ℂ ↦ (z - 1) ^ 4) rho.1 = 0 := by
  have ha := analytic_quartic rho.1
  rw [ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_zero.mpr (pow_ne_zero 4 (sub_ne_zero.mpr (selected_ne_one rho)))]
  simp

/-- Every nontrivial zero gives the prime square an exact double
pole, independently of the zero's multiplicity. -/
theorem meromorphicOrderAt_zetaPrimeSquareResponse (rho : NontrivialZetaZero) :
    meromorphicOrderAt zetaPrimeSquareResponse rho.1 = -2 := by
  change meromorphicOrderAt ((fun z : ℂ ↦ (z - 1) ^ 4) * (logDeriv riemannZeta) ^ 2) rho.1 = _
  rw [meromorphicOrderAt_mul (analytic_quartic _).meromorphicAt ((meromorphic_log _).pow 2),
    order_quartic, zero_add, meromorphicOrderAt_pow (meromorphic_log _), order_log]
  change ((2 : ℤ) : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_mul, WithTop.coe_inj]
  norm_num

/-- The source of the prime square retains the actual multiplicity
but contains no unknown leading derivative phase of zeta. -/
theorem meromorphicTrailingCoeffAt_zetaPrimeSquareResponse (rho : NontrivialZetaZero) :
    meromorphicTrailingCoeffAt zetaPrimeSquareResponse rho.1 =
      (rho.1 - 1) ^ 4 * (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 := by
  have hm : ((analyticZetaZeroMultiplicity rho : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))
  change meromorphicTrailingCoeffAt
    ((fun z : ℂ ↦ (z - 1) ^ 4) * (logDeriv riemannZeta) ^ 2) rho.1 = _
  rw [(analytic_quartic _).meromorphicAt.meromorphicTrailingCoeffAt_mul
      ((meromorphic_log _).pow 2),
    (analytic_quartic _).meromorphicTrailingCoeffAt_of_ne_zero
      (pow_ne_zero 4 (sub_ne_zero.mpr (selected_ne_one rho))),
    (meromorphic_log _).meromorphicTrailingCoeffAt_pow,
    meromorphicTrailingCoeffAt_logDeriv_of_order (meromorphicAt_riemannZeta _) hm
      (meromorphicOrderAt_riemannZeta_nontrivialZero rho)]
  norm_cast

/-- The whole mixed product has a strictly weaker selected pole.
The common response is kept intact, including all its cancellations. -/
theorem meromorphicOrderAt_zetaPrimeMixedProductResponse_gt (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    (-2 : WithTop ℤ) < meromorphicOrderAt zetaPrimeMixedProductResponse rho.1 := by
  have hh := analyticAt_zetaPrimeDivisorResponse hrho (selected_ne_one rho)
  change (-2 : WithTop ℤ) < meromorphicOrderAt
    (((fun z : ℂ ↦ (z - 1) ^ 4) * -(logDeriv riemannZeta)) * zetaPrimeDivisorResponse) rho.1
  rw [meromorphicOrderAt_mul ((analytic_quartic _).meromorphicAt.mul (meromorphic_log _).neg)
      hh.meromorphicAt,
    meromorphicOrderAt_mul (analytic_quartic _).meromorphicAt (meromorphic_log _).neg,
    order_quartic, zero_add, ← meromorphicOrderAt_neg, order_log]
  apply lt_of_lt_of_le (b := (-1 : WithTop ℤ))
  · change ((-2 : ℤ) : WithTop ℤ) < ((-1 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  · simpa only [add_zero] using add_le_add_right hh.meromorphicOrderAt_nonneg (-1 : WithTop ℤ)

/-- The full positive composite response is exactly mixed product
minus prime square; the zeta denominator is explicitly nonzero. -/
theorem zetaPrimeQuadraticResponse_identity {s : ℂ} (hs : riemannZeta s ≠ 0) :
    (s - 1) ^ 4 * zetaPositiveCompositeResponse s =
      zetaPrimeMixedProductResponse s - zetaPrimeSquareResponse s := by
  rw [zetaPositiveCompositeResponse_eq_prime_mul_mixed hs,
    zetaPrimeMixedProductResponse, zetaPrimeSquareResponse, ← zetaPrimeColourResponse_sum]
  ring

/-- One fixed finite weight clears both actual quadratic responses
throughout the selected closed disc, leaving the selected zero visible. -/
def zetaPrimeQuadraticWeight (rho : NontrivialZetaZero) : ℂ → ℂ :=
  meromorphicPairClearingWeight zetaPrimeSquareResponse zetaPrimeMixedProductResponse
    (zetaWronskianMomentDomain rho) rho.1

/-- The pure prime-pair moment with the actual common pole weight. -/
def zetaPrimeQuadraticMoment (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  signedTaylorMoment N (zetaPrimeQuadraticWeight rho * zetaPrimeSquareResponse)
    (zetaWronskianMomentCenter rho)

/-- The whole mixed moment with exactly the same pole weight. -/
def zetaPrimeMixedProductMoment (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  signedTaylorMoment N (zetaPrimeQuadraticWeight rho * zetaPrimeMixedProductResponse)
    (zetaWronskianMomentCenter rho)

/-- The selected complex source, including the retained common weight. -/
def zetaPrimeQuadraticSource (rho : NontrivialZetaZero) : ℂ :=
  zetaPrimeQuadraticWeight rho rho.1 *
    ((rho.1 - 1) ^ 4 * (analyticZetaZeroMultiplicity rho : ℂ) ^ 2)

/-- The actual quadratic weight is entire. -/
theorem analyticAt_zetaPrimeQuadraticWeight (rho : NontrivialZetaZero) (s : ℂ) :
    AnalyticAt ℂ (zetaPrimeQuadraticWeight rho) s := analyticAt_meromorphicPairClearingWeight ..

/-- The common weight cannot erase the selected source. -/
theorem zetaPrimeQuadraticSource_ne_zero (rho : NontrivialZetaZero) :
    zetaPrimeQuadraticSource rho ≠ 0 := by
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))
  exact mul_ne_zero (meromorphicPairClearingWeight_ne_zero zetaPrimeSquareResponse
    zetaPrimeMixedProductResponse (zetaWronskianMomentDomain rho) rho.1)
    (mul_ne_zero (pow_ne_zero 4 (sub_ne_zero.mpr (selected_ne_one rho))) (pow_ne_zero 2 hm))

private theorem domain_re_gt_half (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {s : ℂ} (hs : s ∈ zetaWronskianMomentDomain rho) : 1 / 2 < s.re := by
  have hn : ‖s - zetaWronskianMomentCenter rho‖ ≤ zetaWronskianMomentRadius rho := by
    simpa [zetaWronskianMomentDomain, mem_closedBall, dist_eq_norm] using hs
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (s - zetaWronskianMomentCenter rho)).trans hn)).1
  have hc : (zetaWronskianMomentCenter rho).re = 3 / 2 := by simp [zetaWronskianMomentCenter]
  rw [Complex.sub_re, hc] at hr
  have hR := (zetaWronskianMomentRadius_spec rho hrho).2.2
  linarith

private theorem selected_mem_domain (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    rho.1 ∈ zetaWronskianMomentDomain rho := by
  simpa [zetaWronskianMomentDomain, mem_closedBall, dist_eq_norm, norm_sub_rev] using
    (zetaWronskianMomentRadius_spec rho hrho).2.1.le

private theorem square_analytic_euler {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ zetaPrimeSquareResponse s :=
  (analytic_quartic s).mul ((analytic_log hs).pow 2)

private theorem mixed_analytic_euler {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ zetaPrimeMixedProductResponse s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  exact ((analytic_quartic s).mul (analytic_log hs).neg).mul
    (analyticAt_zetaPrimeDivisorResponse (by linarith) hs1)

/-- After all other poles are cleared, the complete prime quadratic
has its exact linear source and a uniformly bounded geometric error. -/
theorem exists_zetaPrimeQuadraticMoment_error (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeQuadraticMoment rho N -
        ((N + 1 : ℕ) : ℂ) * zetaPrimeQuadraticSource rho‖ ≤ C := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hm : MeromorphicOn zetaPrimeSquareResponse (zetaWronskianMomentDomain rho) :=
    fun s _ ↦ meromorphicAt_zetaPrimeSquareResponse s
  have he := meromorphicPairQuadraticRegular_apply (g := zetaPrimeMixedProductResponse)
    (isCompact_closedBall _ _) hm (selected_mem_domain rho hrho)
    (meromorphicOrderAt_zetaPrimeSquareResponse rho)
  rw [meromorphicTrailingCoeffAt_zetaPrimeSquareResponse] at he
  obtain ⟨C, hC, hb⟩ := exists_meromorphicPairClearedMoment_error (g := zetaPrimeMixedProductResponse)
    hm (square_analytic_euler (by norm_num [zetaWronskianMomentCenter])) hspec.2.1
    (sub_ne_zero.mp (norm_pos_iff.mp hspec.1)) (by rw [meromorphicOrderAt_zetaPrimeSquareResponse])
  refine ⟨C, hC, fun N ↦ ?_⟩
  simpa only [he, zetaPrimeQuadraticMoment, zetaPrimeQuadraticSource, zetaPrimeQuadraticWeight,
    zetaWronskianMomentDomain] using hb N

/-- An independent bound for the entire mixed product. It includes
every convolution cross term and every nonselected pole; no bound for
the remaining prime square is assumed. -/
theorem exists_zetaPrimeMixedProductMoment_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeMixedProductMoment rho N‖ ≤ C := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hm : MeromorphicOn zetaPrimeMixedProductResponse (zetaWronskianMomentDomain rho) :=
    fun _ hs ↦ meromorphicAt_zetaPrimeMixedProductResponse (domain_re_gt_half rho hrho hs)
  have ho := meromorphicOrderAt_zetaPrimeMixedProductResponse_gt rho hrho
  have he := meromorphicPairQuadraticRegular_eq_zero (g := zetaPrimeSquareResponse)
    (isCompact_closedBall _ _) hm (selected_mem_domain rho hrho) ho
  obtain ⟨C, hC, hb⟩ := exists_meromorphicPairClearedMoment_error (g := zetaPrimeSquareResponse)
    hm (mixed_analytic_euler (by norm_num [zetaWronskianMomentCenter])) hspec.2.1
    (sub_ne_zero.mp (norm_pos_iff.mp hspec.1)) ho.le
  refine ⟨C, hC, fun N ↦ ?_⟩
  simpa only [he, mul_zero, sub_zero, zetaPrimeMixedProductMoment, zetaPrimeQuadraticWeight,
    zetaWronskianMomentDomain,
    meromorphicPairClearingWeight_comm zetaPrimeMixedProductResponse zetaPrimeSquareResponse] using hb N

/-- At the normalized linear-source scale, the entire mixed product
has the quantitative error allowance `C/(N+1)`. -/
theorem exists_zetaPrimeMixedProductMoment_decay_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeMixedProductMoment rho N) /
        ((N + 1 : ℕ) : ℂ)‖ ≤ C / ((N + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_zetaPrimeMixedProductMoment_bound rho hrho
  refine ⟨C, hC, fun N ↦ ?_⟩
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg _)

/-- The normalized prime quadratic approaches the exact selected
source with the quantitative error allowance `C/(N+1)`. -/
theorem exists_zetaPrimeQuadraticMoment_decay_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeQuadraticMoment rho N) /
        ((N + 1 : ℕ) : ℂ) - zetaPrimeQuadraticSource rho‖ ≤ C / ((N + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_zetaPrimeQuadraticMoment_error rho hrho
  refine ⟨C, hC, fun N ↦ ?_⟩
  have hn : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
  rw [show ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeQuadraticMoment rho N) /
      ((N + 1 : ℕ) : ℂ) - zetaPrimeQuadraticSource rho =
      ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeQuadraticMoment rho N -
        ((N + 1 : ℕ) : ℂ) * zetaPrimeQuadraticSource rho) / ((N + 1 : ℕ) : ℂ) by field_simp,
    norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg _)

private theorem tendsto_div_nat_succ (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)).const_div_atTop C

/-- The complete mixed product vanishes at the linear-source scale. -/
theorem tendsto_zetaPrimeMixedProductMoment (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦
      ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeMixedProductMoment rho N) /
        ((N + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaPrimeMixedProductMoment_decay_bound rho hrho
  exact squeeze_zero_norm hb (tendsto_div_nat_succ C)

/-- The surviving pure quadratic has a nonzero complex limit; the
preceding mixed-product estimate does not bound this source away. -/
theorem tendsto_zetaPrimeQuadraticMoment (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦
      ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeQuadraticMoment rho N) /
        ((N + 1 : ℕ) : ℂ)) atTop (𝓝 (zetaPrimeQuadraticSource rho)) := by
  obtain ⟨C, _, hb⟩ := exists_zetaPrimeQuadraticMoment_decay_bound rho hrho
  have h := squeeze_zero_norm hb (tendsto_div_nat_succ C)
  exact (tendsto_sub_nhds_zero_iff).mp h

/-- The pure quadratic is the complete convolution of prime moments,
including every pair of derivative orders. The common weight is kept
on the first factor without estimating the factors separately. -/
theorem zetaPrimeQuadraticMoment_eq_full_cross (rho : NontrivialZetaZero) (N : ℕ) :
    zetaPrimeQuadraticMoment rho N =
      ∑ k ∈ Finset.range (N + 1),
        signedTaylorMoment k (fun z ↦ zetaPrimeQuadraticWeight rho z *
          (z - 1) ^ 2 * (-logDeriv riemannZeta z)) (zetaWronskianMomentCenter rho) *
        zetaPoleClearedPrimeMoment (N - k) (zetaWronskianMomentCenter rho) := by
  have hs : 1 < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ (z - 1) ^ 2 * (-logDeriv riemannZeta z))
      (zetaWronskianMomentCenter rho) :=
    (analyticAt_id.sub analyticAt_const).pow 2 |>.mul (analytic_log hs).neg
  have hw : AnalyticAt ℂ (fun z ↦ zetaPrimeQuadraticWeight rho z *
      (z - 1) ^ 2 * (-logDeriv riemannZeta z)) (zetaWronskianMomentCenter rho) :=
    ((analyticAt_zetaPrimeQuadraticWeight rho _).mul
      ((analyticAt_id.sub analyticAt_const).pow 2)).mul (analytic_log hs).neg
  have he : zetaPrimeQuadraticWeight rho * zetaPrimeSquareResponse =
      (fun z ↦ zetaPrimeQuadraticWeight rho z * (z - 1) ^ 2 * (-logDeriv riemannZeta z)) *
        (fun z ↦ (z - 1) ^ 2 * (-logDeriv riemannZeta z)) := by
    funext z
    simp only [Pi.mul_apply, zetaPrimeSquareResponse]
    ring
  rw [zetaPrimeQuadraticMoment, he]
  exact signedTaylorMoment_mul hw hp N

/-- The estimated mixed product is the complete convolution with the
analytic common response. This identity preserves the cross terms
whose separate absolute bounds would lose the cancellation. -/
theorem zetaPrimeMixedProductMoment_eq_full_cross (rho : NontrivialZetaZero) (N : ℕ) :
    zetaPrimeMixedProductMoment rho N =
      ∑ k ∈ Finset.range (N + 1),
        signedTaylorMoment k (fun z ↦ zetaPrimeQuadraticWeight rho z *
          (z - 1) ^ 2 * (-logDeriv riemannZeta z)) (zetaWronskianMomentCenter rho) *
        signedTaylorMoment (N - k) zetaPrimeDivisorRegular (zetaWronskianMomentCenter rho) := by
  have hs : 1 < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have hs1 : zetaWronskianMomentCenter rho ≠ 1 := by intro h; simp [h] at hs
  have hw : AnalyticAt ℂ (fun z ↦ zetaPrimeQuadraticWeight rho z *
      (z - 1) ^ 2 * (-logDeriv riemannZeta z)) (zetaWronskianMomentCenter rho) :=
    ((analyticAt_zetaPrimeQuadraticWeight rho _).mul
      ((analyticAt_id.sub analyticAt_const).pow 2)).mul (analytic_log hs).neg
  have he : zetaPrimeQuadraticWeight rho * zetaPrimeMixedProductResponse =ᶠ[𝓝 (zetaWronskianMomentCenter rho)]
      (fun z ↦ zetaPrimeQuadraticWeight rho z * (z - 1) ^ 2 * (-logDeriv riemannZeta z)) *
        zetaPrimeDivisorRegular := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    simp only [Pi.mul_apply, zetaPrimeMixedProductResponse, zetaPrimeDivisorRegular_eq hz]
    ring
  rw [zetaPrimeMixedProductMoment, signedTaylorMoment_congr N he]
  exact signedTaylorMoment_mul hw (analyticAt_zetaPrimeDivisorRegular (by linarith)) N

end

end RiemannGaussian
