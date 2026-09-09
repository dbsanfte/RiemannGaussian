/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaClearedDenominator
import RiemannGaussian.DigammaHalfPlaneBound

/-!
# Polynomial growth of the full arithmetic carrier denominator

The dyadic-cleared denominator is analytic in fixed disks translated
with the ordinate. Its size is at most a constant times the square of
the height. The estimate uses the actual eta series, its Cauchy
derivative bound and the full Archimedean correction; no unknown
carrier pole or artificial dyadic zero is deleted from the disk.
-/

open Complex Filter MeasureTheory Metric Set Topology
namespace RiemannGaussian
noncomputable section

private lemma norm_two_cpow_neg_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(2 : ℂ) ^ (-s)‖ ≤ 1 := by
  have h : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s).re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (y := -s) (by norm_num : (0 : ℝ) < 2)
  rw [h, neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hs)

/-- Both elementary factors in the cleared expression are bounded on
the whole closed right half-plane, without any trigonometric restriction. -/
theorem pairedEtaFactor_and_deriv_norm_bounds {s : ℂ} (hs : 0 ≤ s.re) :
    ‖pairedEtaFactor s‖ ≤ 3 ∧ ‖deriv pairedEtaFactor s‖ ≤ 2 * ‖Complex.log 2‖ := by
  have hp := norm_two_cpow_neg_le_one hs
  constructor
  · unfold pairedEtaFactor
    have h := norm_sub_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
    norm_num only [norm_one, norm_mul, norm_ofNat] at h
    linarith
  · rw [(hasDerivAt_pairedEtaFactor s).deriv, norm_mul, norm_mul]
    norm_num only [norm_ofNat]
    exact mul_le_of_le_one_right (by positivity) hp

/-- The full Archimedean correction has a polynomial bound on a
fixed right half-plane separated from its pole at one. -/
theorem exists_norm_suzukiChebyshevMellinCompletedCorrection_le_linear :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 3 / 8 ≤ s.re → 1 / 2 ≤ |s.im| →
      ‖suzukiChebyshevMellinCompletedCorrection s‖ ≤ K * (1 + ‖s‖) := by
  obtain ⟨G, hG, hg⟩ := exists_norm_digamma_le_linear_of_re_ge (by norm_num : (0 : ℝ) < 1 / 8)
  let K : ℝ := 6 + ‖Complex.log Real.pi‖ + G
  refine ⟨K, by dsimp [K]; linarith [norm_nonneg (Complex.log Real.pi)], ?_⟩
  intro s hs him
  have hn : 1 / 3 ≤ ‖s‖ := (by linarith : (1 : ℝ) / 3 ≤ s.re).trans (Complex.re_le_norm s)
  have hn1 : 1 / 2 ≤ ‖s - 1‖ := by
    exact him.trans (by simpa using Complex.abs_im_le_norm (s - 1))
  have h0 : ‖1 / s‖ ≤ 3 := by
    rw [norm_div, norm_one]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 3) hn
    norm_num at h
    simpa only [one_div] using h
  have h1 : ‖1 / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hn1
    norm_num at h
    simpa only [one_div] using h
  have hgs := hg (s / 2) (by simp only [div_ofNat_re]; linarith)
  have hnormhalf : ‖s / 2‖ ≤ ‖s‖ := by simp only [norm_div, norm_ofNat]; linarith [norm_nonneg s]
  have hgs' : ‖Complex.digamma (s / 2)‖ ≤ G * (1 + ‖s‖) :=
    hgs.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have hraw : ‖suzukiChebyshevMellinCompletedCorrection s‖ ≤
      3 + 2 + ‖Complex.log Real.pi‖ / 2 + G * (1 + ‖s‖) / 2 := by
    unfold suzukiChebyshevMellinCompletedCorrection
    calc
      _ ≤ ‖1 / s + 1 / (s - 1) - Complex.log Real.pi / 2‖ + ‖Complex.digamma (s / 2) / 2‖ :=
        norm_add_le _ _
      _ ≤ (‖1 / s‖ + ‖1 / (s - 1)‖) + ‖Complex.log Real.pi / 2‖ +
          ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [norm_div, norm_one, norm_ofNat] at h0 h1 ⊢
        gcongr
  exact hraw.trans (by dsimp [K]; nlinarith [norm_nonneg s, norm_nonneg (Complex.log Real.pi)])

private lemma translated_disk_norm {T : ℝ} (hT : 0 ≤ T) {w : ℂ} (hw : ‖w‖ ≤ 9 / 8) :
    ‖staticContourSafeEndpoint T + w‖ ≤ T + 3 := by
  have hs : ‖staticContourSafeEndpoint T‖ ≤ 3 / 2 + T := by
    unfold staticContourSafeEndpoint
    simpa [abs_of_nonneg hT] using norm_add_le ((3 / 2 : ℝ) : ℂ) ((T : ℂ) * I)
  exact (norm_add_le _ _).trans (by linarith)

/-- Cauchy's estimate bounds the actual eta derivative on the inner
moving disk by the same linear ordinate scale as eta itself. -/
theorem norm_pairedEtaArithmeticDerivativeValue_local_disk_le {T : ℝ} (hT : 0 ≤ T)
    {w : ℂ} (hw : ‖w‖ ≤ 9 / 8) :
    ‖pairedEtaArithmeticDerivativeValue (staticContourSafeEndpoint T + w)‖ ≤
      8 * staticContourLocalEtaMass * (T + 4) := by
  let s := staticContourSafeEndpoint T + w
  have hs : 3 / 8 ≤ s.re := by
    have hwr := (abs_le.mp (Complex.abs_re_le_norm w)).1
    rw [show s.re = 3 / 2 + w.re by simp [s, staticContourSafeEndpoint]]
    linarith
  have hq (q : ℂ) (hq : q ∈ closedBall s (1 / 8)) :
      q - staticContourSafeEndpoint T ∈ closedBall 0 staticContourLocalEtaOuterRadius := by
    have hd : ‖q - s‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hq
    have he : q - staticContourSafeEndpoint T = (q - s) + w := by dsimp [s]; ring
    rw [mem_closedBall, dist_zero_right, he]
    exact (norm_add_le _ _).trans (by dsimp [staticContourLocalEtaOuterRadius]; linarith)
  have ha : AnalyticOnNhd ℂ pairedEtaCore (closedBall s (1 / 8)) := by
    intro q hqs
    have hr := (abs_le.mp (Complex.abs_re_le_norm (q - s))).1
    have hn : ‖q - s‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hqs
    apply analyticOnNhd_pairedEtaCore
    change 0 < q.re
    simp only [sub_re] at hr
    linarith
  have hd : DiffContOnCl ℂ pairedEtaCore (ball s (1 / 8)) := by
    refine ⟨ha.differentiableOn.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball s (by norm_num : (1 / 8 : ℝ) ≠ 0)]
    exact ha.continuousOn
  have hb (q : ℂ) (hqs : q ∈ sphere s (1 / 8)) :
      ‖pairedEtaCore q‖ ≤ staticContourLocalEtaMass * (T + 4) := by
    have h := norm_staticContourLocalEta_le hT (hq q (sphere_subset_closedBall hqs))
    simpa only [staticContourLocalEta, add_sub_cancel] using h
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 8) hd hb
  rw [(hasDerivAt_pairedEtaCore_arithmeticDerivativeValue (by linarith : 0 < s.re)).deriv] at h
  convert h using 1
  ring

/-- The dyadic-cleared denominator in a fixed disk centered at
`3/2+i*T`. This retains its actual higher-order zeros. -/
def suzukiEtaLocalClearedDenominator (T : ℝ) (w : ℂ) : ℂ :=
  suzukiEtaClearedCarrierDenominator (staticContourSafeEndpoint T + w)

/-- The full moving disk has genuine analyticity, including every
dyadic exception, when its ordinate is at least two. -/
theorem analyticOnNhd_suzukiEtaLocalClearedDenominator {T : ℝ} (hT : 2 ≤ T) :
    AnalyticOnNhd ℂ (suzukiEtaLocalClearedDenominator T) (closedBall 0 (9 / 8)) := by
  intro w hw
  have hn : ‖w‖ ≤ 9 / 8 := by simpa only [mem_closedBall, dist_zero_right] using hw
  have hre := (abs_le.mp (Complex.abs_re_le_norm w)).1
  have him := (abs_le.mp (Complex.abs_im_le_norm w)).1
  have hs : 0 < (staticContourSafeEndpoint T + w).re := by
    simp [staticContourSafeEndpoint]
    linarith
  have h1 : staticContourSafeEndpoint T + w ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp [staticContourSafeEndpoint] at hi
    linarith
  exact (analyticAt_suzukiEtaClearedCarrierDenominator hs h1).comp
    (analyticAt_const.add analyticAt_id)

/-- One fixed quadratic polynomial bounds the complete cleared
denominator on every moving disk. All constants are independent of
the ordinate and no zero-free interior is assumed. -/
theorem exists_norm_suzukiEtaLocalClearedDenominator_le_quadratic :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ w ∈ closedBall (0 : ℂ) (9 / 8),
      ‖suzukiEtaLocalClearedDenominator T w‖ ≤ C * (T + 4) ^ 2 := by
  obtain ⟨K, hK, hcor⟩ := exists_norm_suzukiChebyshevMellinCompletedCorrection_le_linear
  let M := staticContourLocalEtaMass
  let L := ‖Complex.log 2‖
  let C : ℝ := 1 + M * (27 + 2 * L + 3 * K)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_staticContourLocalEtaMass
  have hL : 0 ≤ L := norm_nonneg _
  have hK0 : 0 ≤ K := by linarith
  refine ⟨C, by dsimp [C]; exact le_add_of_nonneg_right (by positivity), ?_⟩
  intro T hT w hw
  let s := staticContourSafeEndpoint T + w
  have hn : ‖w‖ ≤ 9 / 8 := by simpa only [mem_closedBall, dist_zero_right] using hw
  have hwr := (abs_le.mp (Complex.abs_re_le_norm w)).1
  have hwi := (abs_le.mp (Complex.abs_im_le_norm w)).1
  have hsre : 3 / 8 ≤ s.re := by
    rw [show s.re = 3 / 2 + w.re by simp [s, staticContourSafeEndpoint]]
    linarith
  have hsim : 1 / 2 ≤ |s.im| := by
    have hi : 1 / 2 ≤ s.im := by
      rw [show s.im = T + w.im by simp [s, staticContourSafeEndpoint]]
      linarith
    exact hi.trans (le_abs_self _)
  have hsnorm := translated_disk_norm (by linarith : 0 ≤ T) hn
  have hX : 1 ≤ T + 4 := by linarith
  have heta : ‖pairedEtaCore s‖ ≤ M * (T + 4) := by
    have hw' : w ∈ closedBall 0 staticContourLocalEtaOuterRadius := by
      rw [mem_closedBall, dist_zero_right]
      dsimp [staticContourLocalEtaOuterRadius]
      linarith
    exact norm_staticContourLocalEta_le (by linarith) hw'
  have hetad := norm_pairedEtaArithmeticDerivativeValue_local_disk_le (by linarith : 0 ≤ T) hn
  have hR : ‖suzukiChebyshevMellinCompletedCorrection s‖ ≤ K * (T + 4) :=
    (hcor s hsre hsim).trans (mul_le_mul_of_nonneg_left (by linarith) hK0)
  obtain ⟨hF, hdF⟩ := pairedEtaFactor_and_deriv_norm_bounds (by linarith : 0 ≤ s.re)
  have hraw : ‖suzukiEtaClearedCarrierDenominator s‖ ≤
      ‖pairedEtaFactor s‖ * ‖pairedEtaArithmeticDerivativeValue s‖ +
      ((1 + ‖suzukiChebyshevMellinCompletedCorrection s‖) * ‖pairedEtaFactor s‖ +
        ‖deriv pairedEtaFactor s‖) * ‖pairedEtaCore s‖ := by
    unfold suzukiEtaClearedCarrierDenominator
    calc
      _ ≤ ‖pairedEtaFactor s * pairedEtaArithmeticDerivativeValue s‖ +
          ‖((1 + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaFactor s -
            deriv pairedEtaFactor s) * pairedEtaCore s‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul]
        gcongr
        calc
          _ ≤ ‖(1 + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaFactor s‖ +
              ‖deriv pairedEtaFactor s‖ := norm_sub_le _ _
          _ ≤ _ := by
            simp only [norm_mul]
            gcongr
            simpa only [norm_one] using norm_add_le (1 : ℂ) (suzukiChebyshevMellinCompletedCorrection s)
  change ‖suzukiEtaClearedCarrierDenominator s‖ ≤ C * (T + 4) ^ 2
  calc
    _ ≤ 3 * (8 * M * (T + 4)) + ((1 + K * (T + 4)) * 3 + 2 * L) * (M * (T + 4)) :=
      hraw.trans (by gcongr)
    _ = M * (27 + 2 * L) * (T + 4) + 3 * K * M * (T + 4) ^ 2 := by ring
    _ ≤ M * (27 + 2 * L) * (T + 4) ^ 2 + 3 * K * M * (T + 4) ^ 2 := by
      gcongr
      nlinarith
    _ ≤ C * (T + 4) ^ 2 := by dsimp [C]; nlinarith [sq_nonneg (T + 4)]

end
end RiemannGaussian
