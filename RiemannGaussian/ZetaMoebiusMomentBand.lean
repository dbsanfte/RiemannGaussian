/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailMoments
import RiemannGaussian.ZetaPrimeFilterCalculus

/-!
# A finite band for the actual moving Möbius tail

A positive divisor majorant controls both omitted logarithmic tails,
uniformly in the Möbius cutoff. The retained finite sum keeps the full
signed coefficients and the selected-zero source. It is suitable for
finite Fourier analysis without an infinite Poisson interchange.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- A cutoff-independent positive majorant for the divisor logarithms. -/
def zetaMoebiusLogMajorant (n : ℕ) : ℝ :=
  ∑ a ∈ n.divisorsAntidiagonal, Real.log a.2

/-- Every term of the divisor majorant is nonnegative. -/
theorem zetaMoebiusLogMajorant_nonneg (n : ℕ) : 0 ≤ zetaMoebiusLogMajorant n :=
  Finset.sum_nonneg (fun a _ ↦ Real.log_natCast_nonneg a.2)

/-- The true signed coefficient is bounded uniformly in its divisor cutoff. -/
theorem norm_zetaMoebiusLogTailCoefficient_le (D n : ℕ) :
    ‖zetaMoebiusLogTailCoefficient D n‖ ≤ zetaMoebiusLogMajorant n := by
  rw [zetaMoebiusLogTailCoefficient_eq, zetaMoebiusLogMajorant]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · rw [norm_mul, Complex.norm_intCast, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
    have hm : (|μ a.1| : ℝ) ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a.1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg a.2)
  · simpa only [norm_zero] using Real.log_natCast_nonneg a.2

private theorem LSeriesSummable_log {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ (Real.log n : ℂ)) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).convolution
    (LSeriesHasSum_one hs).LSeriesSummable
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one] at h
  simpa only [← Complex.natCast_log] using h

/-- The majorant has genuine absolute convergence in the Euler half-plane. -/
theorem LSeriesSummable_zetaMoebiusLogMajorant {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (zetaMoebiusLogMajorant n : ℂ)) s := by
  have h := (LSeriesHasSum_one hs).LSeriesSummable.convolution (LSeriesSummable_log hs)
  have he : (fun n ↦ (zetaMoebiusLogMajorant n : ℂ)) =
      (fun _ : ℕ ↦ (1 : ℂ)) ⍟ (fun n : ℕ ↦ (Real.log n : ℂ)) := by
    funext n
    simp [zetaMoebiusLogMajorant, LSeries.convolution_def]
  rw [he]
  exact h

/-- The real exponential mass of the majorant is summable beyond one. -/
theorem summable_zetaMoebiusLogMajorant {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n ↦ zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n) := by
  exact summable_zetaPrimeExpWeight_mul _ (by simp [zetaMoebiusLogMajorant])
    (LSeriesSummable_zetaMoebiusLogMajorant (by simpa using hσ))

/-- The finite real-axis mass used only for the omitted tails. -/
def zetaMoebiusLogMajorantMass (σ : ℝ) : ℝ :=
  ∑' n, zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n

/-- The tail-control mass is nonnegative. -/
theorem zetaMoebiusLogMajorantMass_nonneg (σ : ℝ) : 0 ≤ zetaMoebiusLogMajorantMass σ :=
  tsum_nonneg (fun n ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)

/-- One actual Möbius-tail moment restricted to the explicit finite band. -/
def zetaMoebiusBandMoment (D N k : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ zetaPrimeLogBand N,
    zetaMoebiusLogTailCoefficient D n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n

/-- The finite Möbius band with the whole complex polynomial filter. -/
def zetaMoebiusBandFilter (p : Polynomial ℂ) (D N : ℕ) (y : ℝ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * zetaMoebiusBandMoment D N k y

/-- The actual filtered band as one signed arithmetic sum. -/
theorem zetaMoebiusBandFilter_eq_sum (p : Polynomial ℂ) (D N : ℕ) (y : ℝ) :
    zetaMoebiusBandFilter p D N y = ∑ n ∈ zetaPrimeLogBand N,
      zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n := by
  simp only [zetaMoebiusBandFilter, zetaMoebiusBandMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [zetaPrimeFilterKernel_nat]
  simp only [Finset.mul_sum, zetaPrimeLogKernel]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem norm_atom_le_outside (D N k n : ℕ) (y : ℝ)
    (hn : n ∉ zetaPrimeLogBand N) :
    ‖zetaMoebiusLogTailCoefficient D n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n) +
          (8 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n)) := by
  have hw (σ : ℝ) : 0 ≤ zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n :=
    mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le
  by_cases hn0 : n = 0
  · subst n
    simp [zetaMoebiusLogTailCoefficient, zetaMoebiusLogMajorant]
  rw [norm_mul]
  rcases zetaPrimeLogBand_complement N hn0 hn with hl | hu
  · have hb := norm_zetaPrimeLogKernel_le_lower_band N k n (3 / 2 + I * y) hl
    have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [hs] at hb
    have h := mul_le_mul (norm_zetaMoebiusLogTailCoefficient_le D n) hb
      (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ N * 8 ^ k by positivity) (hw (5 / 4))]
  · have h := mul_le_mul (norm_zetaMoebiusLogTailCoefficient_le D n)
      (norm_zetaPrimeLogKernel_le_upper_band N k n y hu)
      (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ N * (1 / 4) ^ k by positivity) (hw (3 / 2))]

private theorem tsum_sub_sum_eq_complement {f : ℕ → ℂ} (hf : Summable f) (S : Finset ℕ) :
    (∑' n, f n) - ∑ n ∈ S, f n = ∑' n, if n ∈ S then 0 else f n := by
  have h := hf.sum_add_tsum_compl (s := S)
  rw [tsum_subtype] at h
  have he : ((S : Set ℕ)ᶜ).indicator f = (fun n ↦ if n ∈ S then 0 else f n) := by
    funext n
    by_cases hn : n ∈ S <;> simp [hn]
  rw [he] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

/-- Both arithmetic tails have a geometric bound independent of the
divisor cutoff and the ordinate. The retained finite band stays signed. -/
theorem norm_zetaMoebiusLogTailMoment_sub_band_le (D N k : ℕ) (y : ℝ) :
    ‖zetaMoebiusLogTailMoment D (N + k) (3 / 2 + I * y) - zetaMoebiusBandMoment D N k y‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * zetaMoebiusLogMajorantMass (3 / 2) +
          (8 : ℝ) ^ k * zetaMoebiusLogMajorantMass (5 / 4)) := by
  let f (n : ℕ) : ℂ :=
    zetaMoebiusLogTailCoefficient D n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n
  have hsum : HasSum f (zetaMoebiusLogTailMoment D (N + k) (3 / 2 + I * y)) := by
    apply (hasSum_zetaMoebiusLogTailMoment D (N + k) (by norm_num)).congr_fun
    intro n
    dsimp [f, zetaPrimeLogKernel]
    ring
  have ht : Summable (fun n ↦ if n ∈ zetaPrimeLogBand N then 0 else f n) := by
    apply (hsum.summable.indicator ((zetaPrimeLogBand N : Set ℕ)ᶜ)).congr
    intro n
    by_cases hn : n ∈ zetaPrimeLogBand N <;> simp [hn]
  have h1 := summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 3 / 2)
  have h2 := summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 5 / 4)
  have hmajor := ((h1.mul_left ((1 / 4 : ℝ) ^ k)).add
    (h2.mul_left ((8 : ℝ) ^ k))).mul_left ((1 / 2 : ℝ) ^ N)
  rw [← hsum.tsum_eq]
  change ‖(∑' n, f n) - ∑ n ∈ zetaPrimeLogBand N, f n‖ ≤ _
  rw [tsum_sub_sum_eq_complement hsum.summable]
  calc
    _ ≤ ∑' n, (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n) +
          (8 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n)) := by
      apply (norm_tsum_le_tsum_norm ht.norm).trans
      apply Summable.tsum_le_tsum _ ht.norm hmajor
      intro n
      by_cases hn : n ∈ zetaPrimeLogBand N
      · rw [if_pos hn, norm_zero]
        exact mul_nonneg (by positivity) (add_nonneg
          (mul_nonneg (by positivity) (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le))
          (mul_nonneg (by positivity) (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)))
      · rw [if_neg hn]
        exact norm_atom_le_outside D N k n y hn
    _ = _ := by
      rw [tsum_mul_left, (h1.mul_left _).tsum_add (h2.mul_left _), tsum_mul_left, tsum_mul_left]
      rfl

/-- The fixed constant in the uniform bound for both omitted filtered tails. -/
def zetaMoebiusBandTailConstant (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ *
    ((1 / 4 : ℝ) ^ k * zetaMoebiusLogMajorantMass (3 / 2) +
      (8 : ℝ) ^ k * zetaMoebiusLogMajorantMass (5 / 4))

/-- The full moving tail can be restricted to the explicit finite band
with geometric error uniform over all choices of divisor cutoff. -/
theorem norm_zetaMoebiusLogTailFilter_sub_band_le (p : Polynomial ℂ) (D N : ℕ) (y : ℝ) :
    ‖zetaMoebiusLogTailFilter p D N (3 / 2 + I * y) - zetaMoebiusBandFilter p D N y‖ ≤
      (1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant p := by
  rw [zetaMoebiusLogTailFilter, zetaMoebiusBandFilter]
  simp only [zetaMomentSequenceFilter, Polynomial.sum, ← Finset.sum_sub_distrib, ← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * zetaMoebiusLogMajorantMass (3 / 2) +
          (8 : ℝ) ^ k * zetaMoebiusLogMajorantMass (5 / 4))) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_zetaMoebiusLogTailMoment_sub_band_le D N k y) (norm_nonneg _)
    _ = _ := by
      rw [zetaMoebiusBandTailConstant, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The discarded part tends to zero for every moving divisor schedule. -/
theorem tendsto_zetaMoebiusLogTailFilter_sub_band (p : Polynomial ℂ) (D : ℕ → ℕ) (y : ℝ) :
    Tendsto (fun N ↦ zetaMoebiusLogTailFilter p (D N) N (3 / 2 + I * y) -
      zetaMoebiusBandFilter p (D N) N y) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaMoebiusLogTailFilter_sub_band_le p (D N) N y)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (zetaMoebiusBandTailConstant p)

/-- The finite band retains the full selected-zero multiplicity for
the original exponentially growing divisor schedule. -/
theorem tendsto_zetaRightHalfMoebiusBand (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusBandFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).mul_const (3 / 2 - rho.1.re)
  simp only [← pow_succ, zero_mul] at hp
  have hpc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  simp only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero] at hpc
  have he := hpc.mul (tendsto_zetaMoebiusLogTailFilter_sub_band
    (zetaRightHalfPoleJetFilter rho hrho)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))) rho.1.im)
  have h := (tendsto_zetaRightHalfPoleJetTail rho hrho).sub he
  simp only [mul_sub, sub_sub_cancel, mul_zero, sub_zero] at h
  exact h

end
end RiemannGaussian
