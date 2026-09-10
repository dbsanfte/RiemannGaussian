/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaDominatedResonanceDecay
import RiemannGaussian.ZetaMoebiusSievedPrimeTail
import RiemannGaussian.ZetaMoebiusDivisorFourier

/-!
# The sieved distinct-prime source in a smaller centered Fourier region

The arithmetic sieve and the improved Fourier localization apply to the
same original complex sum. The final finite carrier retains the whole
negative multiplicity source. Its physical expansion keeps the exact sieve,
every coefficient sign, and every centered phase inside the Fourier products.
All discarded terms have a proved vanishing allowance; the signed bound on
this retained carrier remains open.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every finite sieve preserves the original divisor majorant,
regardless of which sectors it selects. -/
theorem norm_zetaMoebiusSievedPrimeCoefficient_le (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    ‖zetaMoebiusSievedPrimeCoefficient D S n‖ ≤ zetaMoebiusLogMajorant n := by
  unfold zetaMoebiusSievedPrimeCoefficient zetaMoebiusDistinctPrimeCoefficient
  split_ifs <;> first
    | exact norm_zetaMoebiusLogTailCoefficient_le D n
    | simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n

/-- Every complex arithmetic family has the same exact physical
reconstruction of its full centered Fourier interaction. -/
theorem zetaArithmeticCenteredPart_eq_physical (a : ℕ → ℂ)
    (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    zetaArithmeticCenteredPart a p N y S =
      ∑ n ∈ zetaPrimeLogBand N, a n * zetaMoebiusCenteredPhysicalWeight p N y S n := by
  unfold zetaArithmeticCenteredPart centeredFourierPart zetaMoebiusCenteredPhysicalWeight
  simp_rw [zetaArithmeticWeightedDFT_sub_zero_eq]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The complete sieved arithmetic coefficient paired with the smaller
centered frequency region; neither the sieve nor the phase is averaged out. -/
def zetaMoebiusSievedFourierCarrier (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (y : ℝ) : ℂ :=
  zetaArithmeticCenteredPart (zetaMoebiusSievedPrimeCoefficient D S) p N y
    (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))

/-- The final finite carrier uses exactly the surviving distinct-prime
products, with the entire centered Fourier weight still attached. -/
theorem zetaMoebiusSievedFourierCarrier_eq_physical (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (y : ℝ) :
    zetaMoebiusSievedFourierCarrier p D S N y =
      ∑ n ∈ (zetaPrimeLogBand N).filter
        (fun n ↦ n.primeFactors.Nontrivial ∧ ¬∃ P ∈ S, P ∣ n),
        zetaMoebiusLogTailCoefficient D n * zetaMoebiusCenteredPhysicalWeight p N y
          (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) n := by
  rw [zetaMoebiusSievedFourierCarrier, zetaArithmeticCenteredPart_eq_physical, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hP : n.primeFactors.Nontrivial <;> by_cases hS : ∃ P ∈ S, P ∣ n <;>
    simp [zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient, hP, hS]

/-- The smaller Fourier carrier approximates the genuine sieved
infinite series with an explicit error independent of every sieve choice. -/
theorem norm_zetaMoebiusSievedPrimeFilter_sub_fourier_le (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    ‖zetaMoebiusSievedPrimeFilter p D S N (3 / 2 + I * y) -
      zetaMoebiusSievedFourierCarrier p D S N y‖ ≤
      (1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant p +
        2 * zetaMoebiusLogMajorantMass (9 / 8) *
          zetaQuarterGapError p N y (48 / 49) (14 / 15) :=
  norm_zetaArithmeticFilter_sub_narrow_le _ (norm_zetaMoebiusSievedPrimeCoefficient_le D S)
    p N y hN

/-- Arbitrarily moving sieves and divisor cutoffs share a vanishing
band-and-frequency error, even without source normalization. -/
theorem tendsto_zetaMoebiusSievedPrimeFilter_sub_fourier (p : Polynomial ℂ)
    (D : ℕ → ℕ) (S : ℕ → Finset ℕ) (y : ℝ) :
    Tendsto (fun N ↦ zetaMoebiusSievedPrimeFilter p (D N) (S N) N (3 / 2 + I * y) -
      zetaMoebiusSievedFourierCarrier p (D N) (S N) N y) atTop (𝓝 0) :=
  tendsto_zetaArithmeticFilter_sub_narrow _
    (fun N ↦ norm_zetaMoebiusSievedPrimeCoefficient_le (D N) (S N)) p y

/-- The actual selected-zero carrier, with its original jet filter,
geometric divisor schedule, cofinal sieve, and narrower frequency threshold. -/
def zetaRightHalfSievedFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaMoebiusSievedFourierCarrier (zetaRightHalfPoleJetFilter rho hrho)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfMoebiusSieve rho N) N rho.1.im

/-- The full negative multiplicity source survives simultaneous
arithmetic sieving and the independently justified smaller frequency region. -/
theorem tendsto_zetaRightHalfSievedFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfSievedFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).mul_const (3 / 2 - rho.1.re)
  simp only [← pow_succ, zero_mul] at hp
  have hpc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  simp only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero] at hpc
  have he := tendsto_zetaMoebiusSievedPrimeFilter_sub_fourier
    (zetaRightHalfPoleJetFilter rho hrho)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)))
    (zetaRightHalfMoebiusSieve rho) rho.1.im
  have h := (tendsto_zetaRightHalfSievedPrimeTail rho hrho).sub (hpc.mul he)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold zetaRightHalfSievedFourierCarrier
  ring

/-- Every symbol rate in the analytic admissible range preserves the
entire selected-zero source on the same cofinal arithmetic sieve. The
statement covers all such rates without choosing or optimizing coefficients. -/
theorem tendsto_zetaRightHalfSievedFourier_band_rate (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {r : ℝ} (hr : 0 < r)
    (hgap : Real.exp (-Real.log 2 / 16) * (8 / 9) < r ^ 2) :
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaArithmeticCenteredPart
        (zetaMoebiusSievedPrimeCoefficient (D N) (zetaRightHalfMoebiusSieve rho N))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im (zetaMoebiusResonantModes N (r ^ N)))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  dsimp only
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).mul_const (3 / 2 - rho.1.re)
  simp only [← pow_succ, zero_mul] at hp
  have hpc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  simp only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero] at hpc
  have he := tendsto_zetaArithmeticFilter_sub_band_rate
    (fun N ↦ zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfMoebiusSieve rho N))
    (fun N ↦ norm_zetaMoebiusSievedPrimeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hr hgap
  have h := (tendsto_zetaRightHalfSievedPrimeTail rho hrho).sub (hpc.mul he)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold zetaMoebiusSievedPrimeFilter zetaArithmeticFilter
  ring

/-- The full original pole-jet response differs from the final finite
carrier by the previously proved sieve error plus explicit geometric band
and Fourier errors. No retained signed interaction is hidden in this allowance. -/
theorem exists_zetaRightHalfSievedFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfSievedFourierCarrier rho hrho N)‖ ≤
        C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          ((1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant (zetaRightHalfPoleJetFilter rho hrho) +
            2 * zetaMoebiusLogMajorantMass (9 / 8) *
              zetaQuarterGapError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
                (48 / 49) (14 / 15)) := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfSievedPrimeTail_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  let S := zetaRightHalfMoebiusSieve rho N
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hu : ‖u‖ ≤ 1 := by
    have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 (by linarith)
  have he : u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
      zetaRightHalfSievedFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaMoebiusSievedPrimeFilter p D S N (3 / 2 + I * rho.1.im)) +
      u * (zetaMoebiusSievedPrimeFilter p D S N (3 / 2 + I * rho.1.im) -
        zetaMoebiusSievedFourierCarrier p D S N rho.1.im) := by
    change _ * (_ - zetaMoebiusSievedFourierCarrier p D S N rho.1.im) = _
    ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfSievedFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul] using norm_zetaMoebiusSievedPrimeFilter_sub_fourier_le p D S N rho.1.im hN

/-- The original product support, exact sieve, and all Fourier phase
products coexist in one finite source theorem at every hypothetical zero. -/
theorem tendsto_zetaRightHalfSievedFourier_physical (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ (zetaPrimeLogBand N).filter
        (fun n ↦ n.primeFactors.Nontrivial ∧ ¬∃ P ∈ zetaRightHalfMoebiusSieve rho N, P ∣ n),
        zetaMoebiusLogTailCoefficient (D N) n *
          zetaMoebiusCenteredPhysicalWeight (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
            (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [zetaRightHalfSievedFourierCarrier, zetaMoebiusSievedFourierCarrier_eq_physical] using
    tendsto_zetaRightHalfSievedFourierCarrier rho hrho

end
end RiemannGaussian
