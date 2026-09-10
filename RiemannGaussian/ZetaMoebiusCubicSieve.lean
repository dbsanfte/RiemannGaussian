/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusScaleBound
import RiemannGaussian.ZetaSievedLogWindow

/-!
# A larger simultaneous sieve from the retained divisor scale

The square-root multiplier cost allows every actual complex factor family
whose total absolute weight is at most the cube of the original cutoff.
Its normalized error has the explicit eighth-root rate. Applying the bound
to all grouped sieve overlaps removes every mixed-prime divisor below the
binary logarithm of that cube, with the original zero source retained.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The explicit geometric rate for the full cubic overlap budget. -/
def zetaMoebiusCubicRate (u : ℝ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt u))

/-- The new rate is positive at every positive source distance. -/
theorem zetaMoebiusCubicRate_pos {u : ℝ} (hu : 0 < u) : 0 < zetaMoebiusCubicRate u := by
  unfold zetaMoebiusCubicRate
  positivity

/-- Every right-half source distance has a strictly decaying rate. -/
theorem zetaMoebiusCubicRate_lt_one {u : ℝ} (hu : u < 1) : zetaMoebiusCubicRate u < 1 := by
  simpa only [zetaMoebiusCubicRate, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1), one_pow] using hu

/-- The exact exponent audit: source normalization pays for the
square-root head cost and the complete cubic overlap cost together. -/
theorem zetaMoebiusHeadGrowth_sqrt_cubic_rate {u : ℝ} (hu : 0 < u) :
    u * Real.sqrt (zetaMoebiusHeadGrowth u) * zetaMoebiusHeadGrowth u ^ 3 =
      zetaMoebiusCubicRate u := by
  have hr : Real.sqrt (Real.sqrt (Real.sqrt u)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu))).ne'
  calc
    _ = (u * zetaMoebiusHeadGrowth u ^ 3) * Real.sqrt (zetaMoebiusHeadGrowth u) := by ring
    _ = Real.sqrt (Real.sqrt u) / Real.sqrt (Real.sqrt (Real.sqrt u)) := by
      rw [zetaMoebiusHeadGrowth_cubic_rate hu, zetaMoebiusHeadGrowth, Real.sqrt_inv]
      rfl
    _ = _ := (div_eq_iff hr).mpr (by
      simpa only [zetaMoebiusCubicRate, pow_two] using
        (Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt u))).symm)

/-- Uniform independent decay for every actual finite complex factor
family with cubic coefficient mass. Neither factor sizes nor overlaps are
restricted, and the signed arithmetic sum remains explicit. -/
theorem exists_zetaRightHalfMoebiusMultipleFamily_cubic_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      (∑ P ∈ S, ‖w P‖) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 3 →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑ P ∈ S, w P * ∑' n,
        zetaMoebiusMultipleCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n‖ ≤
        C * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 0 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le.trans' zero_le_one
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFamily_sqrt_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨C * u * B + 1, by positivity, ?_⟩
  intro N S w hS hw
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq N)
  have he : ((Real.sqrt q) ^ N) ^ 2 = q ^ N := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul, Real.sq_sqrt hq]
  have hsqrt : Real.sqrt (D : ℝ) ≤ (Real.sqrt q) ^ N :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by rwa [he]⟩
  have hw' : (∑ P ∈ S, ‖w P‖) ≤ (q ^ N) ^ 3 :=
    hw.trans (pow_le_pow_left₀ (by positivity) hD 3)
  have hbound := hb p D N S w hS
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * Real.sqrt D * B * ∑ P ∈ S, ‖w P‖) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * (Real.sqrt q) ^ N * B * (q ^ N) ^ 3) := by gcongr
    _ = (C * u * B) * (u * Real.sqrt q * q ^ 3) ^ N := by
      rw [mul_pow, mul_pow, pow_succ, show (q ^ 3) ^ N = (q ^ N) ^ 3 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u * B) * zetaMoebiusCubicRate u ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (pow_nonneg (zetaMoebiusCubicRate_pos hu).le N)

/-- The complete sieve union inherits the cubic budget, charging its
actual grouped overlap coefficients before estimating their total mass. -/
theorem exists_zetaRightHalfMoebiusSieve_cubic_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset ℕ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      divisibilitySieveCost S ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 3 →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMoebiusSieveFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) S N
          (3 / 2 + I * rho.1.im)‖ ≤
        C * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfMoebiusMultipleFamily_cubic_bound rho hrho
  refine ⟨C, hC, fun N S hS hcost ↦ ?_⟩
  rw [zetaMoebiusSieveFilter_eq_grouped _ _ N S hS (by norm_num)]
  exact hb N (divisibilitySieveSupport S) (divisibilitySieveCoefficient S)
    (fun _ hP ↦ divisibilitySieveSupport_eligible S hS hP) hcost

/-- The larger explicit sieve at the unchanged divisor cutoff. -/
def zetaRightHalfCubicSieve (rho : NontrivialZetaZero) (N : ℕ) : Finset ℕ :=
  zetaMoebiusSieveHead (Nat.log 2
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3))

/-- Eligibility and the entire cubic overlap cost are discharged at
every order for the actual enlarged sieve. -/
theorem zetaRightHalfCubicSieve_budget (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (∀ P ∈ zetaRightHalfCubicSieve rho N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) ∧
      divisibilitySieveCost (zetaRightHalfCubicSieve rho N) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 3 := by
  refine ⟨zetaMoebiusSieveHead_eligible _, ?_⟩
  have h := divisibilitySieveCost_zetaMoebiusSieveHead_log_le
    (Nat.pow_pos (n := 3) (zetaRightHalfPoleJetCutoff_pos rho hrho N))
  exact_mod_cast h

/-- The enlarged threshold is at least three times the preceding
binary-logarithmic threshold, with the integer rounding kept exactly. -/
theorem three_mul_natLog_le_natLog_cube {D : ℕ} (hD : 0 < D) :
    3 * Nat.log 2 D ≤ Nat.log 2 (D ^ 3) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [Nat.mul_comm 3, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hD.ne') 3

/-- The larger actual sieve deletes an independently negligible union,
with every inclusion-exclusion overlap and source-scale cost paid. -/
theorem tendsto_zetaRightHalfCubicSieve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSieveFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfCubicSieve rho N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfMoebiusSieve_cubic_bound rho hrho
  apply squeeze_zero_norm (fun N ↦ hb N (zetaRightHalfCubicSieve rho N)
    (zetaRightHalfCubicSieve_budget rho hrho N).1 (zetaRightHalfCubicSieve_budget rho hrho N).2)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (zetaMoebiusCubicRate_pos (by linarith [NontrivialZetaZero.re_lt_one rho])).le
      (zetaMoebiusCubicRate_lt_one (by linarith))).const_mul C

/-- The full actual source survives the larger sieve on distinct-prime
integers. This conclusion has no undisclosed arithmetic estimate as a premise. -/
theorem tendsto_zetaRightHalfCubicSievedPrimeTail (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSievedPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfCubicSieve rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfDistinctPrimeTail rho hrho).sub
    (tendsto_zetaRightHalfCubicSieve rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaMoebiusSievedPrimeFilter,
    (hasSum_zetaMoebiusSievedPrimeFilter _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (zetaRightHalfCubicSieve_budget rho hrho N).1 (by norm_num)).tsum_eq, mul_sub]

end
end RiemannGaussian
