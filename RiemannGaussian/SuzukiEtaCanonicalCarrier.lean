/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaCanonicalLog
import RiemannGaussian.SuzukiEtaContourGeometry

/-!
# The actual carrier with its local poles kept explicit

The exact canonical pole product and the bounded analytic unit
reconstruct the full eta carrier, with the numerator and all complex
phases retained. The downstream norm bound charges only the proved
analytic unit and leaves the entire pole product visible.
-/

open Complex Filter MeromorphicOn Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- The complete local canonical pole product, with the actual cleared
denominator's integer divisor and every dyadic factor retained. -/
def suzukiEtaCanonicalPoleProduct (t : {T : ℝ // 2 ≤ T}) (w : ℂ) : ℂ :=
  ∏ᶠ i, Complex.canonicalFactor (suzukiEtaCanonicalRadius t) i w ^
    divisor (suzukiEtaLocalClearedDenominator t.1) (ball 0 (suzukiEtaCanonicalRadius t)) i

/-- Multiplying by the full local pole product gives exactly the
analytic unit at every regular point of the disk. -/
theorem suzukiEtaCanonicalUnit_eq_poleProduct_mul (t : {T : ℝ // 2 ≤ T}) {w : ℂ}
    (hw : w ∈ closedBall 0 (suzukiEtaCanonicalRadius t))
    (hf : suzukiEtaLocalClearedDenominator t.1 w ≠ 0) :
    suzukiEtaCanonicalUnit t w =
      suzukiEtaCanonicalPoleProduct t w * suzukiEtaLocalClearedDenominator t.1 w := by
  have ha : AnalyticAt ℂ (suzukiEtaLocalClearedDenominator t.1) w := by
    apply analyticOnNhd_suzukiEtaLocalClearedDenominator t.property
    exact (closedBall_subset_closedBall (by linarith [(suzukiEtaCanonicalRadius_spec t).2.1])) hw
  have ho : meromorphicOrderAt (suzukiEtaLocalClearedDenominator t.1) w = 0 :=
    ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf
  have he := (suzukiEtaCanonicalUnit_decomp t).eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
    hw ho (suzukiEtaCanonicalRadius_pos t)
  simpa [suzukiEtaCanonicalPoleProduct, divisor_suzukiEtaCleared_sphere_canonicalRadius_eq_zero t,
    ha.meromorphicTrailingCoeffAt_of_ne_zero hf, smul_eq_mul] using he

private lemma local_domain (t : {T : ℝ // 2 ≤ T}) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 < (staticContourSafeEndpoint t.1 + w).re ∧ staticContourSafeEndpoint t.1 + w ≠ 1 := by
  have hr := (abs_le.mp (Complex.abs_re_le_norm w)).1
  have hi := (abs_le.mp (Complex.abs_im_le_norm w)).1
  constructor
  · simp only [staticContourSafeEndpoint, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
    linarith
  · intro he
    have him := congrArg Complex.im he
    simp [staticContourSafeEndpoint] at him
    linarith [t.property]

private lemma local_completionDomain (t : {T : ℝ // 2 ≤ T}) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hf : suzukiEtaLocalClearedDenominator t.1 w ≠ 0) :
    staticContourSafeEndpoint t.1 + w ∈ pairedEtaCompletionDomain := by
  obtain ⟨hs, h1⟩ := local_domain t hw
  refine ⟨hs, h1, ?_⟩
  intro hF
  have he := pairedEtaXiCompletionNumerator_mul_clearedCarrierDenominator hs h1
  rw [hF, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at he
  exact (mul_ne_zero (pairedEtaXiCompletionNumerator_ne_zero_of_re_pos hs h1) hf) he

private lemma inverse_coordinate (s : ℂ) :
    suzukiArithmeticZetaArgument (I * (s - 1 / 2)) = s := by
  unfold suzukiArithmeticZetaArgument
  simp only [mul_sub, ← mul_assoc, I_mul_I]
  ring

/-- The complete actual carrier factors into its literal eta numerator,
full pole product and normalized analytic phase. -/
theorem suzukiXiZeroCarrier_eq_canonicalPoleProduct (t : {T : ℝ // 2 ≤ T}) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hf : suzukiEtaLocalClearedDenominator t.1 w ≠ 0) :
    suzukiXiZeroCarrier (I * (staticContourSafeEndpoint t.1 + w - 1 / 2)) =
      I * pairedEtaFactor (staticContourSafeEndpoint t.1 + w) *
        pairedEtaCore (staticContourSafeEndpoint t.1 + w) * suzukiEtaCanonicalPoleProduct t w *
          Complex.exp (-suzukiEtaCanonicalLog t w) / suzukiEtaCanonicalUnit t 0 := by
  let s := staticContourSafeEndpoint t.1 + w
  have hs := local_completionDomain t hw hf
  have hd : suzukiEtaCarrierDenominator s ≠ 0 := by
    have hJ := suzukiEtaClearedCarrierDenominator_eq_factor_mul hs.2.2
    have hne : pairedEtaFactor s * suzukiEtaCarrierDenominator s ≠ 0 := by rwa [← hJ]
    exact (mul_ne_zero_iff.mp hne).2
  have hz : suzukiArithmeticZetaArgument (I * (s - 1 / 2)) ∈ pairedEtaCompletionDomain := by
    rwa [inverse_coordinate]
  have hE : suzukiXiEValue (I * (s - 1 / 2)) ≠ 0 :=
    (suzukiEtaCarrierDenominator_ne_zero_iff_on_completionDomain hz).mp (by rwa [inverse_coordinate])
  have hb : w ∈ ball 0 (suzukiEtaCanonicalRadius t) := by
    rw [mem_ball, dist_zero_right]
    linarith [(suzukiEtaCanonicalRadius_spec t).1]
  have hp := suzukiEtaCanonicalUnit_eq_poleProduct_mul t (ball_subset_closedBall hb) hf
  have hg := exp_suzukiEtaCanonicalLog_mul_zero_eq t hb
  have hg0 := (suzukiEtaCanonicalUnit_decomp t).ne_zero 0
    (mem_closedBall_self (suzukiEtaCanonicalRadius_pos t).le)
  have hc : suzukiEtaCanonicalUnit t 0 =
      Complex.exp (-suzukiEtaCanonicalLog t w) * suzukiEtaCanonicalPoleProduct t w *
        pairedEtaFactor s * suzukiEtaCarrierDenominator s := by
    calc
      _ = Complex.exp (-suzukiEtaCanonicalLog t w) * suzukiEtaCanonicalUnit t w := by
        rw [← hg, ← mul_assoc, ← Complex.exp_add]
        simp
      _ = _ := by
        rw [hp, suzukiEtaLocalClearedDenominator, suzukiEtaClearedCarrierDenominator_eq_factor_mul hs.2.2]
        dsimp [s]
        ring
  change suzukiXiZeroCarrier (I * (s - 1 / 2)) = _
  rw [suzukiXiZeroCarrier_eq_etaCarrier_on_completionDomain hz hE, inverse_coordinate, suzukiEtaCarrier]
  field_simp
  rw [hc]
  ring

/-- The proved analytic unit contributes an explicit envelope. All
remaining local pole dependence stays in the exact canonical product. -/
theorem norm_suzukiXiZeroCarrier_le_canonicalPoleProduct (t : {T : ℝ // 2 ≤ T}) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hf : suzukiEtaLocalClearedDenominator t.1 w ≠ 0) :
    ‖suzukiXiZeroCarrier (I * (staticContourSafeEndpoint t.1 + w - 1 / 2))‖ ≤
      (3 * staticContourLocalEtaMass * (t.1 + 4) /
        (staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass)) *
          Real.exp (64 * suzukiEtaCanonicalLogMajorant t) * ‖suzukiEtaCanonicalPoleProduct t w‖ := by
  have ht := t.property
  have hmass := one_le_staticContourLocalEtaMass
  have hs := (local_domain t hw).1
  have hF := (pairedEtaFactor_and_deriv_norm_bounds hs.le).1
  have hEta := norm_staticContourLocalEta_le (by linarith [t.property] : 0 ≤ t.1)
    (z := w) (by rw [mem_closedBall, dist_zero_right]; dsimp [staticContourLocalEtaOuterRadius]; linarith)
  have hL := norm_suzukiEtaCanonicalLog_le_unit t hw
  have hRe : -(suzukiEtaCanonicalLog t w).re ≤ 64 * suzukiEtaCanonicalLogMajorant t := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm (suzukiEtaCanonicalLog t w))).1
    linarith
  have hfloor := suzukiEtaClearedFloor_le_norm_canonicalUnit_zero t
  have hexp := Real.exp_le_exp.mpr hRe
  have hp : 0 < staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass := by
    positivity [staticContourSafeEtaFactorFloor_pos, one_le_staticContourSafeZetaDirichletMass]
  rw [suzukiXiZeroCarrier_eq_canonicalPoleProduct t hw hf, norm_div, norm_mul, norm_mul,
    norm_mul, norm_mul, norm_I, one_mul, Complex.norm_exp, neg_re]
  calc
    _ ≤ (3 * (staticContourLocalEtaMass * (t.1 + 4)) * ‖suzukiEtaCanonicalPoleProduct t w‖ *
          Real.exp (64 * suzukiEtaCanonicalLogMajorant t)) /
        (staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass) := by
      apply div_le_div₀ (by positivity) ?_ hp hfloor
      gcongr
      exact hEta
    _ = _ := by ring

/-- The previously constructed admissible vertical sides supply
nonvanishing of the cleared denominator on the complete strip segment. -/
theorem suzukiEtaLocalClearedDenominator_ne_zero_on_admissible_strip
    (t : {T : ℝ // 2 ≤ T}) (ht : SuzukiXiEtaVerticalAdmissible (-t.1))
    {y : ℝ} (hy : y ∈ Icc 0 (1 / 2)) :
    suzukiEtaLocalClearedDenominator t.1 ((y - 1 : ℝ) : ℂ) ≠ 0 := by
  have hdomain := mem_suzukiXiEtaExtendedCarrierDomain_vertical (y := y) ht
    (by linarith [hy.1])
  have harg : suzukiArithmeticZetaArgument ((-t.1 : ℂ) + (y : ℂ) * I) =
      staticContourSafeEndpoint t.1 + ((y - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [suzukiArithmeticZetaArgument, staticContourSafeEndpoint]
    ring
  have hd := (suzukiEtaCarrierDenominator_ne_zero_iff_on_completionDomain hdomain.1).mpr hdomain.2
  have hF := hdomain.1.2.2
  rw [Complex.ofReal_neg, harg] at hd hF
  rw [suzukiEtaLocalClearedDenominator, suzukiEtaClearedCarrierDenominator_eq_factor_mul hF]
  exact mul_ne_zero hF hd

/-- The full unit estimate applies along the actual admissible strip,
with only the complete canonical pole product left in the bound. -/
theorem norm_suzukiXiZeroCarrier_admissible_strip_le_canonicalPoleProduct
    (t : {T : ℝ // 2 ≤ T}) (ht : SuzukiXiEtaVerticalAdmissible (-t.1))
    {y : ℝ} (hy : y ∈ Icc 0 (1 / 2)) :
    ‖suzukiXiZeroCarrier ((-t.1 : ℂ) + (y : ℂ) * I)‖ ≤
      (3 * staticContourLocalEtaMass * (t.1 + 4) /
        (staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass)) *
          Real.exp (64 * suzukiEtaCanonicalLogMajorant t) *
            ‖suzukiEtaCanonicalPoleProduct t ((y - 1 : ℝ) : ℂ)‖ := by
  have hw : ‖((y - 1 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have he := norm_suzukiXiZeroCarrier_le_canonicalPoleProduct t hw
    (suzukiEtaLocalClearedDenominator_ne_zero_on_admissible_strip t ht hy)
  have hcoord : I * (staticContourSafeEndpoint t.1 + ((y - 1 : ℝ) : ℂ) - 1 / 2) =
      (-t.1 : ℂ) + (y : ℂ) * I := by
    apply Complex.ext <;> simp [staticContourSafeEndpoint]
    ring
  rwa [hcoord] at he

end
end RiemannGaussian
