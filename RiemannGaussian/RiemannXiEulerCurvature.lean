/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiGlobalLogDerivative
import RiemannGaussian.ZetaStechkinZeroFree

/-!
# Logarithmic curvature on the closed Euler half-plane

The proved reciprocal-logarithmic zero-free strip gives a polynomial
lower bound for the distance from every point of `Re s >= 1` to every
genuine xi zero. The finite low-height divisor is included explicitly.
The full paired logarithmic-derivative expansion then bounds curvature
on this closed half-plane, including its boundary.

The signed, absolutely convergent expansion remains the upstream
identity; its norm is taken only to construct a Gaussian-integrable
majorant for the normalized arithmetic source.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- A single polynomial edge bound includes every genuine zero, including
the finite low-height divisor not covered by the explicit Stechkin theorem. -/
theorem exists_zetaZero_polynomial_edge_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ rho : NontrivialZetaZero,
      1 ≤ C * (1 + |rho.1.im|) * (1 - rho.1.re) := by
  classical
  let S : ℝ := ∑ rho ∈ spectralZetaZeroWindow 1, 1 / (1 - rho.1.re)
  have hS : 0 ≤ S := Finset.sum_nonneg fun rho _ =>
    div_nonneg zero_le_one (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le
  refine ⟨1408 + S, by linarith, ?_⟩
  intro rho
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  by_cases hy : 1 ≤ |rho.1.im|
  · have hL := three_lt_localZetaLogHeight rho.1.im
    have hgap := zetaStechkin_margin_lt_one_sub_re rho hy
    unfold zetaStechkinZeroMargin at hgap
    have hp : 1 ≤ 64 * localZetaLogHeight rho.1.im * (1 - rho.1.re) := by
      have := (div_lt_iff₀ (by positivity : 0 < 64 * localZetaLogHeight rho.1.im)).mp hgap
      nlinarith
    have hlog : localZetaLogHeight rho.1.im ≤ |rho.1.im| + 22 :=
      Real.log_le_self (by positivity)
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ hd.le
    nlinarith [mul_nonneg hS (abs_nonneg rho.1.im), abs_nonneg rho.1.im]
  · have hmem : rho ∈ spectralZetaZeroWindow 1 := by
      rw [mem_spectralZetaZeroWindow (by norm_num), zetaSpectralCoordinate_re]
      exact (lt_of_not_ge hy).le
    have hterm : 1 / (1 - rho.1.re) ≤ S :=
      Finset.single_le_sum (fun sigma _ =>
        div_nonneg zero_le_one (sub_pos.mpr (NontrivialZetaZero.re_lt_one sigma)).le) hmem
    have hone : 1 ≤ S * (1 - rho.1.re) := (div_le_iff₀ hd).mp hterm
    apply hone.trans
    apply mul_le_mul_of_nonneg_right _ hd.le
    nlinarith [mul_nonneg hS (abs_nonneg rho.1.im), abs_nonneg rho.1.im]

/-- The entire closed Euler half-plane has a common polynomial distance
bound from the complete genuine zero divisor. No fixed horizontal buffer
or zero-height cutoff is required. -/
theorem exists_riemannXi_euler_zero_distance_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re → ∀ rho : NontrivialZetaZero,
      1 ≤ C * (1 + ‖s‖) * ‖s - rho.1‖ := by
  obtain ⟨C, hC, hgap⟩ := exists_zetaZero_polynomial_edge_constant
  refine ⟨2 * C, by linarith, ?_⟩
  intro s hs rho
  have hC0 : 0 ≤ C := by linarith
  have hd : 0 ≤ ‖s - rho.1‖ := norm_nonneg _
  have hs0 := norm_nonneg s
  by_cases hd1 : 1 ≤ ‖s - rho.1‖
  · have hp : 1 ≤ 2 * C * (1 + ‖s‖) := by nlinarith
    exact hp.trans (le_mul_of_one_le_right (by positivity) hd1)
  · have hdist : ‖s - rho.1‖ < 1 := lt_of_not_ge hd1
    have hordinate : |rho.1.im| ≤ ‖s‖ + ‖s - rho.1‖ := by
      calc
        |rho.1.im| ≤ ‖(rho.1 : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ ‖s‖ + ‖s - rho.1‖ := by
          have := norm_sub_le s (s - rho.1)
          simpa only [sub_sub_cancel] using this
    have hed : 1 - rho.1.re ≤ ‖s - rho.1‖ := by
      have := Complex.re_le_norm (s - rho.1)
      simp only [sub_re] at this
      linarith
    calc
      1 ≤ C * (1 + |rho.1.im|) * (1 - rho.1.re) := hgap rho
      _ ≤ C * (2 * (1 + ‖s‖)) * ‖s - rho.1‖ := by
        apply mul_le_mul _ hed (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le
          (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hC0
      _ = _ := by ring

private lemma divisor_weight_le {s a : ℂ} {P : ℝ}
    (hgap : 1 ≤ P * ‖s - a‖) :
    1 + ‖a‖ ^ 2 ≤ (2 + (1 + 2 * ‖s‖ ^ 2) * P ^ 2) * ‖s - a‖ ^ 2 := by
  have hn : ‖a‖ ≤ ‖s‖ + ‖s - a‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le s (s - a)
  have hn2 : ‖a‖ ^ 2 ≤ 2 * ‖s‖ ^ 2 + 2 * ‖s - a‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg a) hn
    nlinarith [sq_nonneg (‖s‖ - ‖s - a‖)]
  have hp : 1 ≤ P ^ 2 * ‖s - a‖ ^ 2 := by
    have hh := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hgap
    nlinarith
  calc
    1 + ‖a‖ ^ 2 ≤ 2 * ‖s - a‖ ^ 2 + (1 + 2 * ‖s‖ ^ 2) := by linarith
    _ ≤ 2 * ‖s - a‖ ^ 2 + (1 + 2 * ‖s‖ ^ 2) * (P ^ 2 * ‖s - a‖ ^ 2) := by
      gcongr
      exact le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring

/-- The full xi curvature is controlled by zero distance and the already
summable multiplicity-weighted divisor. This estimate is deduced from the
exact paired expansion, without differentiating an unproved infinite sum. -/
theorem norm_deriv_logDeriv_riemannXi_le_of_zero_distance {s : ℂ}
    (hxi : riemannXi s ≠ 0) {P : ℝ} (hP : 0 < P)
    (hgap : ∀ rho : NontrivialZetaZero, 1 ≤ P * ‖s - rho.1‖) :
    ‖deriv (logDeriv riemannXi) s‖ ≤
      2 * (2 + (1 + 2 * ‖s‖ ^ 2) * P ^ 2) *
        ∑' rho : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity rho : ℝ) / (1 + ‖(rho.1 : ℂ)‖ ^ 2) := by
  let K := 2 + (1 + 2 * ‖s‖ ^ 2) * P ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : 0 ≤ ∑' rho : NontrivialZetaZero,
      (analyticZetaZeroMultiplicity rho : ℝ) / (1 + ‖(rho.1 : ℂ)‖ ^ 2) :=
    tsum_nonneg fun _ => by positivity
  apply norm_deriv_le_of_lip' (by positivity)
  have hnear := (analyticOnNhd_riemannXi s (mem_univ s)).continuousAt.eventually_ne hxi
  filter_upwards [ball_mem_nhds s (by positivity : 0 < 1 / (2 * P)), hnear] with v hv hvi
  have hvs : ‖v - s‖ < 1 / (2 * P) := mem_ball_iff_norm.mp hv
  rw [← tsum_zetaLogDerivDifference hvi hxi]
  have hb := tsum_of_norm_bounded
    (summable_distinct_zetaZeroInverseSquareNorm.hasSum.mul_left (2 * K * ‖v - s‖))
      (f := zetaLogDerivDifferenceSummand v s) (fun rho => ?_)
  · convert hb using 1
    ring
  have hgs := hgap rho
  have hds : 0 < ‖s - rho.1‖ := by
    by_contra hn
    have he : ‖s - rho.1‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    simp only [he, mul_zero] at hgs
    norm_num at hgs
  have hsmall : ‖v - s‖ < ‖s - rho.1‖ / 2 := by
    have hh : 1 / P ≤ ‖s - rho.1‖ := (div_le_iff₀ hP).mpr (by nlinarith)
    rw [show 1 / (2 * P) = (1 / P) / 2 by ring] at hvs
    linarith
  have htri : ‖s - rho.1‖ ≤ ‖v - s‖ + ‖v - rho.1‖ := by
    have hh := norm_sub_le (v - rho.1) (v - s)
    rw [show v - rho.1 - (v - s) = s - rho.1 by ring] at hh
    linarith
  have hvd : ‖s - rho.1‖ / 2 ≤ ‖v - rho.1‖ := by linarith
  have hsne : s - rho.1 ≠ 0 := norm_pos_iff.mp hds
  have hvne : v - rho.1 ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖v - rho.1‖)
  have he : 1 / (v - rho.1) - 1 / (s - rho.1) =
      (s - v) / ((v - rho.1) * (s - rho.1)) := by field_simp; ring
  have hw := divisor_weight_le hgs
  have hrecip : 1 / (‖v - rho.1‖ * ‖s - rho.1‖) ≤
      2 * K / (1 + ‖(rho.1 : ℂ)‖ ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod : ‖s - rho.1‖ ^ 2 ≤ 2 * (‖v - rho.1‖ * ‖s - rho.1‖) := by
      nlinarith
    calc
      1 * (1 + ‖(rho.1 : ℂ)‖ ^ 2) = 1 + ‖(rho.1 : ℂ)‖ ^ 2 := one_mul _
      _ ≤ K * ‖s - rho.1‖ ^ 2 := hw
      _ ≤ K * (2 * (‖v - rho.1‖ * ‖s - rho.1‖)) := mul_le_mul_of_nonneg_left hprod hK
      _ = _ := by ring
  rw [zetaLogDerivDifferenceSummand, he, norm_mul, Complex.norm_natCast,
    norm_div, norm_mul, norm_sub_rev s v]
  calc
    _ = (analyticZetaZeroMultiplicity rho : ℝ) * ‖v - s‖ *
        (1 / (‖v - rho.1‖ * ‖s - rho.1‖)) := by ring
    _ ≤ (analyticZetaZeroMultiplicity rho : ℝ) * ‖v - s‖ *
        (2 * K / (1 + ‖(rho.1 : ℂ)‖ ^ 2)) := by gcongr
    _ = _ := by ring

/-- The actual xi logarithmic curvature has polynomial growth on the
entire closed Euler half-plane. Every zero-distance and summability
hypothesis has been discharged for the genuine zeta divisor. -/
theorem exists_norm_deriv_logDeriv_riemannXi_euler_polynomial_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re →
      ‖deriv (logDeriv riemannXi) s‖ ≤ C * (1 + ‖s‖) ^ 4 := by
  obtain ⟨C, hC, hdist⟩ := exists_riemannXi_euler_zero_distance_constant
  let S := ∑' rho : NontrivialZetaZero,
    (analyticZetaZeroMultiplicity rho : ℝ) / (1 + ‖(rho.1 : ℂ)‖ ^ 2)
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  refine ⟨2 * (2 + 2 * C ^ 2) * S, by positivity, ?_⟩
  intro s hs
  have hxi : riemannXi s ≠ 0 := by
    intro hz
    let rho : NontrivialZetaZero := ⟨s, (riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp hz⟩
    exact not_lt_of_ge hs (NontrivialZetaZero.re_lt_one rho)
  have hp : 0 < C * (1 + ‖s‖) := mul_pos (by linarith) (by positivity)
  have h := norm_deriv_logDeriv_riemannXi_le_of_zero_distance hxi hp (hdist s hs)
  have hpoly : 2 + (1 + 2 * ‖s‖ ^ 2) * (C * (1 + ‖s‖)) ^ 2 ≤
      (2 + 2 * C ^ 2) * (1 + ‖s‖) ^ 4 := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  calc
    _ ≤ 2 * (2 + (1 + 2 * ‖s‖ ^ 2) * (C * (1 + ‖s‖)) ^ 2) * S := h
    _ ≤ 2 * ((2 + 2 * C ^ 2) * (1 + ‖s‖) ^ 4) * S := by gcongr
    _ = _ := by ring

end
end RiemannGaussian
