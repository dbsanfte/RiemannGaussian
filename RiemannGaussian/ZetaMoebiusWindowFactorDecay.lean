/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusLcmBound
import RiemannGaussian.ZetaAveragedWindowSource

/-!
# Uniform arithmetic control of large factors in the actual source window

Every factor in the retained physical window exceeds the squared original
divisor cutoff. The joint lcm estimate therefore removes all power growth
in that cutoff. Whole moving complex families can have coefficient mass
`D^3 * sqrt(D)` while retaining independently vanishing normalized response.
Their unions and overlaps are not identified with the remaining source
without a separate exact representation and a proved coefficient budget.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- Every finite complex family of mixed-prime factors in the actual
physical window has only a linear moment-order cost times coefficient mass.
The bound is on the full genuine series for each factor, including all multiples. -/
theorem exists_zetaRightHalfWindowFactorFamily_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ), 1 ≤ N →
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P ∧ P ∈ zetaLogWindow N) →
      ‖∑ P ∈ S, w P * ∑' n,
        zetaMoebiusMultipleCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n‖ ≤
        C * (1 + 8 * (N : ℝ)) * ∑ P ∈ S, ‖w P‖ := by
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_large_factor_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N S w hN hS
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ S, ‖w P‖ * (C * (1 + 8 * (N : ℝ)) * B) := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hP0, hP1, hmix, hwindow⟩ := hS P hP
      have hlarge : D ^ 2 ≤ P := (zetaLogWindow_gt_moebiusCutoff_sq rho hN hwindow).le
      rw [(hasSum_zetaMoebiusMultipleFilter p D N hP0 hP1 hmix (by norm_num)).tsum_eq, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (hb p D P N hP0 hlarge).trans
      gcongr
      exact hwindow.2
    _ = (C * B) * (1 + 8 * (N : ℝ)) * ∑ P ∈ S, ‖w P‖ := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by gcongr; linarith

/-- The enlarged coefficient budget has an explicit source-normalized
bound for every actual window-factor family. All common-divisor and
factor-size estimates are discharged, leaving no cancellation assumption. -/
theorem exists_zetaRightHalfWindowFactorFamily_budget_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ), 1 ≤ N →
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P ∧ P ∈ zetaLogWindow N) →
      (∑ P ∈ S, ‖w P‖) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 3 *
          Real.sqrt (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑ P ∈ S, w P * ∑' n,
        zetaMoebiusMultipleCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n‖ ≤
        C * (1 + 8 * (N : ℝ)) * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 0 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le.trans' zero_le_one
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfWindowFactorFamily_bound rho hrho
  refine ⟨C * u + 1, by positivity, ?_⟩
  intro N S w hN hS hw
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq N)
  have he : ((Real.sqrt q) ^ N) ^ 2 = q ^ N := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul, Real.sq_sqrt hq]
  have hsqrt : Real.sqrt (D : ℝ) ≤ (Real.sqrt q) ^ N :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by rwa [he]⟩
  have hw' : (∑ P ∈ S, ‖w P‖) ≤ (q ^ N) ^ 3 * (Real.sqrt q) ^ N := by
    apply hw.trans
    gcongr
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * (1 + 8 * (N : ℝ)) * ∑ P ∈ S, ‖w P‖) :=
      mul_le_mul_of_nonneg_left (hb N S w hN hS) (by positivity)
    _ ≤ u ^ (N + 1) * (C * (1 + 8 * (N : ℝ)) * ((q ^ N) ^ 3 * (Real.sqrt q) ^ N)) := by
      gcongr
    _ = (C * u) * (1 + 8 * (N : ℝ)) * (u * Real.sqrt q * q ^ 3) ^ N := by
      rw [mul_pow, mul_pow, pow_succ, show (q ^ 3) ^ N = (q ^ N) ^ 3 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u) * (1 + 8 * (N : ℝ)) * zetaMoebiusCubicRate u ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
    _ ≤ _ := by
      gcongr
      · exact pow_nonneg (zetaMoebiusCubicRate_pos hu).le N
      · linarith

/-- The complete enlarged-family error vanishes despite its linear
moment factor; every right-half source distance gives a strict geometric rate. -/
theorem tendsto_zetaRightHalfWindowFactorAllowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C * (1 + 8 * (N : ℝ)) *
      zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N) atTop (𝓝 0) := by
  have h0 := (zetaMoebiusCubicRate_pos (u := 3 / 2 - rho.1.re)
    (by linarith [NontrivialZetaZero.re_lt_one rho])).le
  have h1 := zetaMoebiusCubicRate_lt_one (u := 3 / 2 - rho.1.re) (by linarith)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hn := tendsto_self_mul_const_pow_of_lt_one h0 h1
  have h := (hp.add (hn.const_mul 8)).const_mul C
  convert h using 1
  · funext N
    ring
  · simp

/-- Arbitrary moving complex families with the enlarged budget have
independently vanishing full arithmetic response at the actual source scale.
Their coefficients are unrestricted apart from the explicit mass budget. -/
theorem tendsto_zetaRightHalfWindowFactorFamily (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hS : ∀ᶠ N in atTop,
      (∀ P ∈ S N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P ∧ P ∈ zetaLogWindow N) ∧
        (∑ P ∈ S N, ‖w N P‖) ≤
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 3 *
            Real.sqrt (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑ P ∈ S N, w N P * ∑' n,
      zetaMoebiusMultipleCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfWindowFactorFamily_budget_bound rho hrho
  apply squeeze_zero_norm' _ (tendsto_zetaRightHalfWindowFactorAllowance rho hrho C)
  filter_upwards [hS, Filter.eventually_ge_atTop 1] with N hN hN1
  exact hb N (S N) (w N) hN1 hN.1 hN.2

end
end RiemannGaussian
