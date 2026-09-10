/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaQuarticGaussian
import RiemannGaussian.EtaThinStripPrefix

/-!
# Decay of the independent eta quartic upper allowance

The literal height-adapted eta estimate controls the completed-square
allowance after exact Gaussian rescaling. Its positive power tends to
zero on every fixed vertical line to the right of three quarters. This
is a signed upper bound, not a bound for the absolute quartic integral
or for the completed normalized reflection source.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

private lemma gaussian_allowance_rescale (F : ℝ → ℝ) {tau : ℝ}
    (htau : 0 < tau) (c : ℝ) :
    tau ^ 2 / 4 * (∫ t : ℝ, (t - c) ^ 2 * translatedGaussian tau c t * F t) =
      Real.sqrt tau / 4 * (∫ y : ℝ, y ^ 2 * Real.exp (-y ^ 2) * F (c + y / Real.sqrt tau)) := by
  let q := Real.sqrt tau
  have hq : 0 < q := Real.sqrt_pos.mpr htau
  have hq2 : q ^ 2 = tau := Real.sq_sqrt htau.le
  let G (y : ℝ) := y ^ 2 * Real.exp (-y ^ 2) * F (c + y / q)
  have he (u : ℝ) : G (q * u) = tau * (u ^ 2 * Real.exp (-tau * u ^ 2) * F (u + c)) := by
    dsimp [G]
    rw [mul_div_cancel_left₀ _ hq.ne', mul_pow, hq2]
    simp only [add_comm c u, neg_mul]
    ring
  have hs := Measure.integral_comp_mul_left G q
  simp_rw [he] at hs
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hq), smul_eq_mul] at hs
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => (t - c) ^ 2 * translatedGaussian tau c t * F t) c
  simp only [add_sub_cancel_right, translatedGaussian] at hshift
  rw [hshift] at hs
  change tau ^ 2 / 4 * (∫ t : ℝ, (t - c) ^ 2 * Real.exp (-tau * (t - c) ^ 2) * F t) =
    q / 4 * (∫ y : ℝ, G y)
  have heq := congrArg (fun x : ℝ => q * x) hs
  simp only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at heq
  rw [← heq]
  rw [← hq2]
  ring

private lemma eta_quartic_rescaled_bound {sigma epsilon tau : ℝ}
    (he : 0 < epsilon) (hehi : epsilon < 1 / 4) (hsigma : 1 - epsilon ≤ sigma)
    (htau : 0 < tau) (htime : tau ≤ 1) (c y : ℝ) :
    normSq (pairedEtaCore (pairedEtaVerticalArgument sigma (c + y / Real.sqrt tau))) ^ 2 ≤
      (6 / epsilon) ^ 4 * (Real.sqrt tau) ^ (-4 * epsilon) *
        (3 + |sigma| + |c| + |y|) := by
  let q := Real.sqrt tau
  let A := 3 + |sigma| + |c|
  let T := A + |y| / q
  have hq : 0 < q := Real.sqrt_pos.mpr htau
  have hq1 : q ≤ 1 := (Real.sqrt_le_one).mpr htime
  have hA : 3 ≤ A := by dsimp [A]; linarith [abs_nonneg sigma, abs_nonneg c]
  have hT : 3 ≤ T := by dsimp [T]; linarith [div_nonneg (abs_nonneg y) hq.le]
  have hnorm : ‖pairedEtaVerticalArgument sigma (c + y / q)‖ ≤ T := by
    have hn := norm_add_le (sigma : ℂ) (((c + y / q : ℝ) : ℂ) * I)
    have ht := abs_add_le c (y / q)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one] at hn
    rw [abs_div, abs_of_pos hq] at ht
    dsimp [pairedEtaVerticalArgument, T, A] at *
    linarith
  have heta := norm_pairedEtaCore_le_thinStrip_height he (by linarith : epsilon ≤ 1 / 2)
    (s := pairedEtaVerticalArgument sigma (c + y / q))
    (by simpa [pairedEtaVerticalArgument] using hsigma) hT hnorm
  have hTupper : T ≤ (A + |y|) / q := by
    apply (le_div_iff₀ hq).mpr
    dsimp [T]
    rw [add_mul, div_mul_cancel₀ _ hq.ne']
    nlinarith [mul_le_mul_of_nonneg_left hq1 (show 0 ≤ A by linarith)]
  have he4 : (T ^ epsilon) ^ 4 = T ^ (4 * epsilon) := by
    rw [← Real.rpow_natCast (T ^ epsilon) 4, ← Real.rpow_mul (by linarith : 0 ≤ T)]
    congr 1
    ring
  have hmass : normSq (pairedEtaCore (pairedEtaVerticalArgument sigma (c + y / q))) ^ 2 ≤
      (6 / epsilon) ^ 4 * T ^ (4 * epsilon) := by
    rw [Complex.normSq_eq_norm_sq, ← pow_mul]
    have hpow := pow_le_pow_left₀ (norm_nonneg _) heta 4
    exact hpow.trans_eq (by
      rw [show 6 * T ^ epsilon / epsilon = (6 / epsilon) * T ^ epsilon by ring, mul_pow, he4])
  have hb : 1 ≤ A + |y| := by linarith [abs_nonneg y]
  calc
    _ ≤ (6 / epsilon) ^ 4 * T ^ (4 * epsilon) := hmass
    _ ≤ (6 / epsilon) ^ 4 * (((A + |y|) / q) ^ (4 * epsilon)) := by
      gcongr
    _ = (6 / epsilon) ^ 4 * q ^ (-4 * epsilon) * (A + |y|) ^ (4 * epsilon) := by
      rw [Real.div_rpow (by linarith : 0 ≤ A + |y|) hq.le,
        show -4 * epsilon = -(4 * epsilon) by ring, Real.rpow_neg hq.le]
      ring
    _ ≤ (6 / epsilon) ^ 4 * q ^ (-4 * epsilon) * (A + |y|) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hb (by linarith))
      positivity
    _ = _ := rfl

/-- A uniform positive-power bound for the actual quartic allowance.
It holds for all vertical lines and centers in the stated bounded
region, with no zero hypothesis and no choice of Dirichlet coefficients. -/
theorem exists_pairedEta_quartic_gaussian_allowance_bound {epsilon M : ℝ}
    (he : 0 < epsilon) (hehi : epsilon < 1 / 4) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (sigma c tau : ℝ),
      1 - epsilon ≤ sigma → |sigma| + |c| ≤ M → 0 < tau → tau ≤ 1 →
        tau ^ 2 / 4 * (∫ t : ℝ, (t - c) ^ 2 * translatedGaussian tau c t *
          normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2) ≤
          C * (Real.sqrt tau) ^ (1 - 4 * epsilon) := by
  let J : ℝ := ∫ y : ℝ, Real.exp (-y ^ 2) * (1 + |y|) ^ 3
  have hJ : Integrable (fun y : ℝ => Real.exp (-y ^ 2) * (1 + |y|) ^ 3) := by
    have hi := integrable_translatedGaussian_mul_of_polynomial_bound (f := fun y : ℝ => (1 + |y|) ^ 3)
      (by norm_num : (0 : ℝ) < 1) 0 (by fun_prop) (C := 1) (by norm_num) 3
      (fun y => by simp [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + |y|)])
    simpa only [smul_eq_mul, translatedGaussian, sub_zero, neg_mul, one_mul] using! hi
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  let C := (6 / epsilon) ^ 4 * (4 + M) * J / 4
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro sigma c tau hsigma hregion htau htime
  let q := Real.sqrt tau
  let f (y : ℝ) := pairedEtaCore (pairedEtaVerticalArgument sigma (c + y / q))
  let G (y : ℝ) := y ^ 2 * Real.exp (-y ^ 2) * normSq (f y) ^ 2
  let K := (6 / epsilon) ^ 4 * q ^ (-4 * epsilon) * (4 + M)
  have hq : 0 < q := Real.sqrt_pos.mpr htau
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hspos : 0 < sigma := by linarith
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hs : 0 < (pairedEtaVerticalArgument sigma (c + y / q)).re := by
      simpa [pairedEtaVerticalArgument] using hspos
    change ContinuousAt (pairedEtaCore ∘ fun u : ℝ => pairedEtaVerticalArgument sigma (c + u / q)) y
    apply (analyticOnNhd_pairedEtaCore _ hs).continuousAt.comp
      (f := fun u : ℝ => pairedEtaVerticalArgument sigma (c + u / q))
    unfold pairedEtaVerticalArgument
    fun_prop
  have hGcont : Continuous G := by dsimp [G]; fun_prop
  have hG0 (y : ℝ) : 0 ≤ G y := by dsimp [G]; positivity
  have hb (y : ℝ) : G y ≤ K * (Real.exp (-y ^ 2) * (1 + |y|) ^ 3) := by
    have hp := eta_quartic_rescaled_bound he hehi hsigma htau htime c y
    have hu : 0 ≤ 1 + |y| := by positivity
    have hy : y ^ 2 ≤ (1 + |y|) ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have hr : 3 + |sigma| + |c| + |y| ≤ (4 + M) * (1 + |y|) := by
      have hm := mul_nonneg (show 0 ≤ 3 + M by linarith) (abs_nonneg y)
      nlinarith
    have ha : 0 ≤ (6 / epsilon) ^ 4 * q ^ (-4 * epsilon) := by positivity
    calc
      G y ≤ y ^ 2 * Real.exp (-y ^ 2) *
          ((6 / epsilon) ^ 4 * q ^ (-4 * epsilon) * (3 + |sigma| + |c| + |y|)) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ ≤ (1 + |y|) ^ 2 * Real.exp (-y ^ 2) *
          ((6 / epsilon) ^ 4 * q ^ (-4 * epsilon) * ((4 + M) * (1 + |y|))) := by
        gcongr
      _ = _ := by dsimp [K]; ring
  have hG : Integrable G :=
    (hJ.const_mul K).mono' hGcont.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hG0 y)] using hb y)
  have hint : (∫ y : ℝ, G y) ≤ K * J := by
    have hi := integral_mono hG (hJ.const_mul K) hb
    simpa only [integral_const_mul, J] using hi
  rw [gaussian_allowance_rescale _ htau c]
  change q / 4 * (∫ y : ℝ, G y) ≤ C * q ^ (1 - 4 * epsilon)
  calc
    _ ≤ q / 4 * (K * J) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = C * q ^ (1 - 4 * epsilon) := by
      rw [show 1 - 4 * epsilon = 1 + (-4 * epsilon) by ring,
        Real.rpow_add hq, Real.rpow_one]
      dsimp [C, K]
      ring

/-- The signed quartic integral has a vanishing positive-power upper
bound, uniformly over each bounded region to the right of `1-epsilon`.
The negative part and all phase correlations remain unrestricted. -/
theorem exists_pairedEta_quartic_gaussian_signed_bound {epsilon M : ℝ}
    (he : 0 < epsilon) (hehi : epsilon < 1 / 4) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (sigma c tau : ℝ),
      1 - epsilon ≤ sigma → |sigma| + |c| ≤ M → 0 < tau → tau ≤ 1 →
        max 0 (∫ t : ℝ, (translatedGaussian tau c t : ℂ) *
          pairedEtaVerticalQuarticCurvature sigma t).re ≤
          C * (Real.sqrt tau) ^ (1 - 4 * epsilon) := by
  obtain ⟨C, hC, hb⟩ := exists_pairedEta_quartic_gaussian_allowance_bound he hehi hM
  refine ⟨C, hC, ?_⟩
  intro sigma c tau hsigma hregion htau htime
  apply max_le (by positivity)
  exact (pairedEta_quartic_gaussian_upper (by linarith : 0 < sigma) htau c).trans
    (hb sigma c tau hsigma hregion htau htime)

/-- The positive part of the complete quartic eta integral tends to
zero along every bounded moving family of lines staying strictly to
the right of three quarters. No infinite-prefix exchange is assumed. -/
theorem tendsto_pairedEta_quartic_gaussian_positivePart_moving
    {epsilon M : ℝ} (he : 0 < epsilon) (hehi : epsilon < 1 / 4) (hM : 0 ≤ M)
    (sigma center : ℝ → ℝ)
    (hsigma : ∀ᶠ tau in 𝓝[>] (0 : ℝ), 1 - epsilon ≤ sigma tau)
    (hregion : ∀ᶠ tau in 𝓝[>] (0 : ℝ), |sigma tau| + |center tau| ≤ M) :
    Tendsto (fun tau : ℝ => max 0 (∫ t : ℝ, (translatedGaussian tau (center tau) t : ℂ) *
      pairedEtaVerticalQuarticCurvature (sigma tau) t).re) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_pairedEta_quartic_gaussian_signed_bound he hehi hM
  have hp : 0 < 1 - 4 * epsilon := by linarith
  have hlim : Tendsto (fun tau : ℝ => C * (Real.sqrt tau) ^ (1 - 4 * epsilon))
      (𝓝[>] 0) (𝓝 0) := by
    have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have h := ((Real.continuousAt_rpow_const 0 (1 - 4 * epsilon) (Or.inr hp.le)).tendsto.comp
      hsqrt).const_mul C
    simpa only [Real.sqrt_zero, Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using! h
  apply squeeze_zero' (Eventually.of_forall fun tau => le_max_left _ _) _ hlim
  filter_upwards [hsigma, hregion, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with tau hs hr ht hu
  exact hb (sigma tau) (center tau) tau hs hr ht hu.le

/-- Every fixed positive vertical line to the right of three quarters
has an unconditional vanishing upper allowance for its signed quartic
eta integral, at every fixed Gaussian center. -/
theorem tendsto_pairedEta_quartic_gaussian_positivePart {sigma : ℝ}
    (hsigma : 3 / 4 < sigma) (c : ℝ) :
    Tendsto (fun tau : ℝ => max 0 (∫ t : ℝ, (translatedGaussian tau c t : ℂ) *
      pairedEtaVerticalQuarticCurvature sigma t).re) (𝓝[>] 0) (𝓝 0) := by
  let epsilon := min (1 / 8) ((sigma - 3 / 4) / 2)
  have he : 0 < epsilon := lt_min (by norm_num) (by linarith)
  have hehi : epsilon < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have hleft : 1 - (1 / 4 - epsilon) ≤ sigma := by
    have hh := min_le_right (1 / 8) ((sigma - 3 / 4) / 2)
    dsimp [epsilon] at *
    linarith
  exact tendsto_pairedEta_quartic_gaussian_positivePart_moving
    (epsilon := 1 / 4 - epsilon) (by linarith) (by linarith)
    (M := |sigma| + |c|) (by positivity) (fun _ => sigma) (fun _ => c)
    (Eventually.of_forall fun _ => hleft) (Eventually.of_forall fun _ => le_rfl)

end
end RiemannGaussian
