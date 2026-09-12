/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeHeatNeighbourBound
import RiemannGaussian.GaussianPoleHeatBand

/-!
# The source retained by a complete band of recurrence corrections

The actual cleared residual tends to zero uniformly for all moment orders
between `N` and `2N+2`, at the original `N`-th quadratic width. This controls
the complete weighted band of residuals. The corresponding band of actual
prime heat retains a fixed negative multiplicity source. Thus the upper
neighbour cannot be discarded when the recurrence is iterated over a
growing band, despite its proved decay at each fixed neighbouring order.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open GaussianSimplePoleHeat GaussianCentralTailBound

/-- The complete residual heat tends uniformly to zero over a growing
band of orders at one shared quadratic width. Both frequency ranges use
one bound independent of the selected order within the band. -/
theorem eventually_norm_clearedPrimeRemainderHeat_band_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ k → k ≤ 2 * N + 2 →
      ‖normalizedClearedPrimeRemainderHeat D S rho k
        (quadraticWidth c (clearedPrimeSourceDistance rho) N)‖ ≤ ε := by
  obtain ⟨C, hC, A, hA, hbound⟩ := exists_normalizedClearedPrimeRemainderHeat_bound hD S hS rho hrho
  have hu := clearedPrimeSourceDistance_pos rho
  have hg := clearedPrimeCentralGeometry rho hrho
  have hr : 0 < clearedPrimeCentralRadius rho := hu.trans hg.2.1
  have hratio : clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho < 1 :=
    (div_lt_one hr).mpr hg.2.1
  have hG : 1 ≤ 4 * clearedPrimeSourceDistance rho := by
    unfold clearedPrimeSourceDistance
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hcentral := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity :
    0 ≤ clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) hratio).const_mul C
  have houter := (tendsto_pow_mul_tailAllowance_quadraticWidth hg.1 hc hu
    (by positivity : 0 < (4 * clearedPrimeSourceDistance rho) ^ 2)
    (normalizedPrimeTailClearingPolynomial D S rho).natDegree).const_mul
      (A * (4 * clearedPrimeSourceDistance rho) ^ 2)
  have hlim : Tendsto (fun N : ℕ ↦ C * (clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) ^ N +
      A * (4 * clearedPrimeSourceDistance rho) ^ (2 * N + 2) *
        tailAllowance (clearedPrimeCentralWindow rho)
          (normalizedPrimeTailClearingPolynomial D S rho).natDegree
          (quadraticWidth c (clearedPrimeSourceDistance rho) N)) atTop (𝓝 0) := by
    have h := hcentral.add houter
    simp only [mul_zero, add_zero] at h
    convert h using 1
    ext N
    rw [pow_add, pow_mul]
    ring
  filter_upwards [hlim.eventually (gt_mem_nhds hε),
    (tendsto_quadraticWidth c (clearedPrimeSourceDistance rho)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hsmall hwidth
  intro k hNk hk
  apply (hbound k _ (quadraticWidth_pos hc hu N) hwidth.le).trans
  apply le_trans _ hsmall.le
  exact add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hratio.le hNk) hC.le)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG hk) hA.le)
      (tailAllowance_nonneg _ _ (quadraticWidth_pos hc hu N)))

/-- The complete band of actual upper-order recurrence contributions,
with the original prime phases and the common width retained. -/
def clearedPrimeHeatBand (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero) (c : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (quadraticBandWeight c N j : ℂ) *
    normalizedClearedPrimeHeat D S rho (N + j + 2) (quadraticWidth c (clearedPrimeSourceDistance rho) N)

/-- The corresponding complete residual band uses exactly the same
weights, orders and width as the actual prime band. -/
def clearedPrimeRemainderHeatBand (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero)
    (c : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (quadraticBandWeight c N j : ℂ) *
    normalizedClearedPrimeRemainderHeat D S rho (N + j + 2)
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)

/-- The entire weighted residual band tends to zero. Its growing number
of orders is paid for by the exact bounded sum of recurrence weights. -/
theorem tendsto_clearedPrimeRemainderHeatBand {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (clearedPrimeRemainderHeatBand D S rho c) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_norm_clearedPrimeRemainderHeat_band_le hD S hS rho hrho hc
    (show 0 < ε / (6 * c) by positivity), eventually_ge_atTop 1] with N hsmall hN
  rw [dist_zero_right]
  have hsum : ‖clearedPrimeRemainderHeatBand D S rho c N‖ ≤
      (∑ j ∈ Finset.range N, quadraticBandWeight c N j) * (ε / (6 * c)) := by
    unfold clearedPrimeRemainderHeatBand
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (quadraticBandWeight_nonneg hc.le N j)]
    apply mul_le_mul_of_nonneg_left _ (quadraticBandWeight_nonneg hc.le N j)
    exact hsmall (N + j + 2) (by omega) (by have := Finset.mem_range.mp hj; omega)
  have htotal := (sum_quadraticBandWeight_bounds hc.le hN).2
  have hlt : (3 * c) * (ε / (6 * c)) < ε := by
    have he : (3 * c) * (ε / (6 * c)) = ε / 2 := by field_simp; ring
    rw [he]
    linarith
  exact hsum.trans_lt ((mul_le_mul_of_nonneg_right htotal (by positivity)).trans_lt hlt)

/-- The complete upper-order band splits into its exact real pole
contribution and its entire complex residual. No sign or phase is erased. -/
theorem clearedPrimeHeatBand_eq_source_add_remainder {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    clearedPrimeHeatBand D S rho c N = -(analyticZetaZeroMultiplicity rho : ℂ) *
      ((∑ j ∈ Finset.range N, quadraticBandWeight c N j *
        attenuation (N + j + 2) (clearedPrimeSourceDistance rho)
          (quadraticWidth c (clearedPrimeSourceDistance rho) N) : ℝ) : ℂ) +
      clearedPrimeRemainderHeatBand D S rho c N := by
  unfold clearedPrimeHeatBand clearedPrimeRemainderHeatBand
  simp_rw [normalizedClearedPrimeHeat_eq_source_add_remainder hD S hS rho _
    (quadraticWidth_pos hc (clearedPrimeSourceDistance_pos rho) N), mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- At every nonempty band the negative source has a fixed floor in
magnitude, with the full residual still explicit. -/
theorem clearedPrimeHeatBand_re_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    (clearedPrimeHeatBand D S rho c N).re ≤
      -(analyticZetaZeroMultiplicity rho : ℝ) * c * Real.exp (-4 * c) +
        ‖clearedPrimeRemainderHeatBand D S rho c N‖ := by
  rw [clearedPrimeHeatBand_eq_source_add_remainder hD S hS rho hc]
  simp only [add_re, neg_mul, neg_re, mul_re, natCast_re, ofReal_re, natCast_im,
    ofReal_im, zero_mul, sub_zero]
  have hsource := weighted_attenuation_band_lower hc (clearedPrimeSourceDistance_pos rho) hN
  simp only [neg_mul] at hsource
  have hm : 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) := Nat.cast_nonneg _
  have hr := re_le_norm (clearedPrimeRemainderHeatBand D S rho c N)
  nlinarith [mul_le_mul_of_nonneg_left hsource hm]

/-- Although each fixed upper neighbour vanishes, their complete
growing band retains a strictly negative source. Hence iterating the
recurrence cannot discard the accumulated correction. -/
theorem eventually_clearedPrimeHeatBand_re_le_negative {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N in atTop, (clearedPrimeHeatBand D S rho c N).re ≤
      -(analyticZetaZeroMultiplicity rho : ℝ) * c * Real.exp (-4 * c) / 2 := by
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) :=
    Nat.cast_pos.mpr (analyticZetaZeroMultiplicity_positive rho)
  have hε : 0 < (analyticZetaZeroMultiplicity rho : ℝ) * c * Real.exp (-4 * c) / 2 := by positivity
  have hlim := (tendsto_clearedPrimeRemainderHeatBand hD S hS rho hrho hc).norm
  filter_upwards [hlim.eventually (gt_mem_nhds (by simpa only [norm_zero] using hε)),
    eventually_ge_atTop 1] with N hsmall hN
  have h := clearedPrimeHeatBand_re_le hD S hS rho hc hN
  linarith

private theorem quadraticBandWeight_eq_coefficient {u : ℝ} (hu : 0 < u) (c : ℝ) (N j : ℕ) :
    2 * (quadraticWidth c u N : ℂ) * (((N + j : ℕ) : ℂ) + 2) / (u : ℂ) ^ 2 =
      (quadraticBandWeight c N j : ℂ) := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hN2 : (N : ℂ) + 2 ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
  unfold quadraticWidth quadraticBandWeight
  push_cast
  field_simp

/-- Iterating the actual recurrence over a complete band retains both
endpoint heats and the entire accumulated upper-order correction. Every
term has the same original width, cutoff, sieve and prime phases. -/
theorem clearedPrimeHeat_extraFactor_band {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∑ j ∈ Finset.range N, (clearedPrimeSourceDistance rho : ℂ) ^ (N + j + 1) *
      clearedHeatPrimeResponse (quadraticWidth c (clearedPrimeSourceDistance rho) N)
        ((Polynomial.X - Polynomial.C rho.1) * normalizedPrimeTailClearingPolynomial D S rho)
        D S (N + j + 1) (zetaWronskianMomentCenter rho)) =
      normalizedClearedPrimeHeat D S rho (2 * N) (quadraticWidth c (clearedPrimeSourceDistance rho) N) -
        normalizedClearedPrimeHeat D S rho N (quadraticWidth c (clearedPrimeSourceDistance rho) N) +
        clearedPrimeHeatBand D S rho c N := by
  have hu := clearedPrimeSourceDistance_pos rho
  simp_rw [normalizedClearedPrimeHeat_three_order (quadraticWidth_pos hc hu N) hD S hS rho,
    quadraticBandWeight_eq_coefficient hu]
  rw [Finset.sum_add_distrib]
  congr 1
  simpa only [Nat.add_assoc, Nat.add_zero, ← two_mul] using Finset.sum_range_sub
    (fun j ↦ normalizedClearedPrimeHeat D S rho (N + j)
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)) N

end
end RiemannGaussian.SquarefreeEulerQuadratic
