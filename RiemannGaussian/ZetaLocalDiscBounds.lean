import RiemannGaussian.EtaThinStripFactor
import RiemannGaussian.EtaZetaMultiplicitySchwarz
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeZeta

/-!
# Actual zeta bounds on discs centered on the safe line

The entire pole-removed function is translated about `3/2+i*y`. The
existing eta rectangle estimate controls the left half of its unit disc;
the dyadic factor controls the right half. The actual Möbius Dirichlet
series supplies a positive lower bound at the center. These estimates are
the analytic inputs for a local signed zero-pole decomposition.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The safe-line Dirichlet mass is the actual positive real zeta value. -/
theorem staticContourSafeZetaDirichletMass_eq_zeta :
    (staticContourSafeZetaDirichletMass : ℂ) = riemannZeta (3 / 2) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num : 1 < (3 / 2 : ℂ).re)]
  unfold staticContourSafeZetaDirichletMass
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  norm_num [one_div]

/-- The existing safe-line Möbius and zeta mass has an explicit
numerical upper bound from the original real eta estimate. -/
theorem staticContourSafeZetaDirichletMass_le_eight : staticContourSafeZetaDirichletMass ≤ 8 := by
  have h := norm_riemannZeta_one_add_le_four_div
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  norm_num at h
  rw [← staticContourSafeZetaDirichletMass_eq_zeta] at h
  simpa [abs_of_nonneg (zero_le_one.trans one_le_staticContourSafeZetaDirichletMass)] using h

/-- To the right of the safe line the dyadic factor has the same
quarter lower bound as at the boundary of the earlier eta strip. -/
theorem quarter_le_norm_etaFactor_of_three_halves_le_re {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
  rw [norm_one, norm_two_mul_two_cpow_neg] at h
  have hp : (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hsqrt]
    nlinarith
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow] at hp
  linarith

/-- Pole-removed zeta translated to the actual safe-line center. -/
def localZetaPoleRemoved (y : ℝ) (z : ℂ) : ℂ := riemannZeta₁ (3 / 2 + I * y + z)

/-- The translated pole-removed zeta function is entire. -/
theorem differentiable_localZetaPoleRemoved (y : ℝ) : Differentiable ℂ (localZetaPoleRemoved y) := by
  unfold localZetaPoleRemoved
  exact differentiable_riemannZeta₁.comp (by fun_prop)

/-- The literal eta support bounds the entire translated unit disc. -/
theorem norm_localZetaPoleRemoved_le (y : ℝ) {z : ℂ} (hz : z ∈ closedBall 0 (1 : ℝ)) :
    ‖localZetaPoleRemoved y z‖ ≤ 8 * (|y| + 22) ^ 2 := by
  have hzn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hzre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hzn
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hzn
  let s : ℂ := 3 / 2 + I * y + z
  have hsre : s.re = 3 / 2 + z.re := by simp [s]
  have hsim : s.im = y + z.im := by simp [s]
  have hslo : 1 / 2 ≤ s.re := by rw [hsre]; linarith [(abs_le.mp hzre).1]
  have hshi : s.re ≤ 5 / 2 := by rw [hsre]; linarith [(abs_le.mp hzre).2]
  have him : |s.im| ≤ |y| + 1 := by rw [hsim]; exact (abs_add_le _ _).trans (by linarith)
  change ‖riemannZeta₁ s‖ ≤ _
  by_cases hs : s.re ≤ 3 / 2
  · exact (norm_riemannZeta₁_le_etaStrip hslo hs).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |s.im| + 20) (by linarith) 2) (by norm_num))
  · have hspos : 0 < s.re := by linarith
    have hre : |s.re| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, hshi⟩
    have hre1 : |s.re - 1| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hn : ‖s‖ ≤ |y| + 22 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      linarith
    have hn1 : ‖s - 1‖ ≤ |y| + 22 := by
      have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
      linarith
    have hp : ‖s - 1‖ * ‖s‖ ≤ (|y| + 22) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hn1 hn (norm_nonneg s) (by positivity)
    refine (norm_riemannZeta₁_le_of_etaFactor_lower hspos
      (quarter_le_norm_etaFactor_of_three_halves_le_re (by linarith))).trans ?_
    rw [div_le_iff₀ hspos]
    nlinarith [sq_nonneg (|y| + 22)]

/-- The actual Möbius reciprocal bound gives a uniform positive floor
for pole-removed zeta at every translated center. -/
theorem sixteenth_le_norm_localZetaPoleRemoved_zero (y : ℝ) :
    (1 / 16 : ℝ) ≤ ‖localZetaPoleRemoved y 0‖ := by
  let s : ℂ := 3 / 2 + I * y
  have hs : s.re = 3 / 2 := by simp [s]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs]; norm_num)
  have hinv : ‖(riemannZeta s)⁻¹‖ ≤ 8 :=
    (norm_inv_riemannZeta_safeLine_le_mass hs).trans staticContourSafeZetaDirichletMass_le_eight
  have hlower : (1 / 8 : ℝ) ≤ ‖riemannZeta s‖ := by
    have hprod := mul_le_mul_of_nonneg_right hinv (norm_nonneg (riemannZeta s))
    rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzne)] at hprod
    linarith
  have hn : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re, hs] at h
    linarith
  change (1 / 16 : ℝ) ≤ ‖riemannZeta₁ (s + 0)‖
  rw [add_zero, riemannZeta₁_eq_sub_one_mul hs1, norm_mul]
  nlinarith [mul_le_mul hn hlower (by norm_num : (0 : ℝ) ≤ 1 / 8) (norm_nonneg (s - 1))]

end

end RiemannGaussian
