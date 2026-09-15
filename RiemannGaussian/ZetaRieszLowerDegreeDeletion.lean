/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowerDegreeBounds

/-!
# Actual lower-degree deletion with unchanged source and fallback

The complete actual two- and three-extreme-prime classes are removed only
on their proved source intervals. Every earlier support cut survives and
all other scales retain their existing residual. The actual deletion error
vanishes independently, while the whole constant-filter carrier retains
its negative multiplicity source and exact signed cosine representation.
The independent joint cofinal lower bound remains open.
-/

namespace RiemannGaussian.ZetaRieszLowerDegreeDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeCount
open ZetaRieszLowerDegreeBounds

/-- Remove the two- or three-prime class only on its proved source
interval; otherwise retain the entire previous four-prime residual. -/
def degreeResidualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if u < Real.exp (-(2 / 3 : ℝ)) then
    (ZetaRieszFourExtremeDeletion.fourResidualBand u N).filter (fun n => (extremePrimes u N n).card < 2)
  else if u < Real.exp (-(9 / 16 : ℝ)) then
    (ZetaRieszFourExtremeDeletion.fourResidualBand u N).filter (fun n => (extremePrimes u N n).card < 3)
  else ZetaRieszFourExtremeDeletion.fourResidualBand u N

/-- The complete actual signed response on the new adaptive support. -/
def degreeResidualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ degreeResidualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Every previously proved support restriction is retained. -/
theorem degreeResidualBand_subset (u : ℝ) (N : ℕ) :
    degreeResidualBand u N ⊆ ZetaRieszFourExtremeDeletion.fourResidualBand u N := by
  unfold degreeResidualBand
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

/-- The two-prime interval now leaves at most one physical-cutoff prime. -/
theorem surviving_extreme_count_le_one {u : ℝ} {N n : ℕ}
    (hu : u < Real.exp (-(2 / 3 : ℝ))) (hn : n ∈ degreeResidualBand u N) :
    (extremePrimes u N n).card ≤ 1 := by
  rw [degreeResidualBand, if_pos hu] at hn
  have h := (Finset.mem_filter.mp hn).2
  omega

/-- The larger three-prime interval leaves at most two physical-cutoff primes. -/
theorem surviving_extreme_count_le_two {u : ℝ} {N n : ℕ}
    (hu : u < Real.exp (-(9 / 16 : ℝ))) (hn : n ∈ degreeResidualBand u N) :
    (extremePrimes u N n).card ≤ 2 := by
  by_cases htwo : u < Real.exp (-(2 / 3 : ℝ))
  · exact (surviving_extreme_count_le_one htwo hn).trans (by norm_num)
  · rw [degreeResidualBand, if_neg htwo, if_pos hu] at hn
    have h := (Finset.mem_filter.mp hn).2
    omega

/-- The whole additional actual deletion is independently negligible at
source scale, for every fixed filter and ordinate, with all-scale fallback. -/
theorem tendsto_four_sub_degreeResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszFourExtremeDeletion.fourResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u -
        degreeResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u)) atTop (𝓝 0) := by
  by_cases htwo : u < Real.exp (-(2 / 3 : ℝ))
  · have h := tendsto_two_degree_sum
      (fun N => (ZetaRieszFourExtremeDeletion.fourResidualBand u N).filter
        (fun n => 2 ≤ (extremePrimes u N n).card)) P y hu htwo
      (fun _ _ hn => (Finset.mem_filter.mp hn).2)
    apply h.congr'
    filter_upwards [] with N
    have he := Finset.sum_filter_add_sum_filter_not (ZetaRieszFourExtremeDeletion.fourResidualBand u N)
      (fun n => (extremePrimes u N n).card < 2)
      (fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    simp only [not_lt] at he
    dsimp only [ZetaRieszFourExtremeDeletion.fourResidualResponse, degreeResidualResponse, degreeResidualBand]
    rw [if_pos htwo]
    rw [← he]
    ring
  · by_cases hthree : u < Real.exp (-(9 / 16 : ℝ))
    · have h := tendsto_three_degree_sum
        (fun N => (ZetaRieszFourExtremeDeletion.fourResidualBand u N).filter
          (fun n => 3 ≤ (extremePrimes u N n).card)) P y hu hthree
        (fun _ _ hn => (Finset.mem_filter.mp hn).2)
      apply h.congr'
      filter_upwards [] with N
      have he := Finset.sum_filter_add_sum_filter_not (ZetaRieszFourExtremeDeletion.fourResidualBand u N)
        (fun n => (extremePrimes u N n).card < 3)
        (fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
      simp only [not_lt] at he
      dsimp only [ZetaRieszFourExtremeDeletion.fourResidualResponse, degreeResidualResponse, degreeResidualBand]
      rw [if_neg htwo, if_pos hthree]
      rw [← he]
      ring
    · simpa only [degreeResidualResponse, degreeResidualBand, if_neg htwo, if_neg hthree,
        ZetaRieszFourExtremeDeletion.fourResidualResponse, sub_self, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The reduced constant-filter carrier retains the original source normalization. -/
def normalizedDegreeResidual (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    degreeResidualResponse 1 N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
      (3 / 2 - rho.1.re)

/-- The smaller actual carrier retains the complete negative multiplicity
source. The independent signed lower floor is not a consequence of this limit. -/
theorem tendsto_normalizedDegreeResidual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (normalizedDegreeResidual rho) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszFourExtremeDeletion.tendsto_normalizedFourResidual rho hrho hexposed).sub
    (tendsto_four_sub_degreeResidual 1 rho.1.im hu)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedDegreeResidual ZetaRieszFourExtremeDeletion.normalizedFourResidual
  ring

/-- The new whole real residual still retains the actual Riesz sign,
nonnegative factorial envelope and full product cosine phase. -/
theorem re_normalizedDegreeResidual_eq_cosine_sum (rho : NontrivialZetaZero) (N : ℕ) :
    (normalizedDegreeResidual rho N).re =
      (3 / 2 - rho.1.re) ^ (N + 1) *
        ∑ n ∈ degreeResidualBand (3 / 2 - rho.1.re) N,
          (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n).re *
            (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
              Real.cos (rho.1.im * Real.log n) := by
  simp only [normalizedDegreeResidual, degreeResidualResponse, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.re_sum, ZetaRieszCosineCarrier.re_coefficient_filter_one]

end
end RiemannGaussian.ZetaRieszLowerDegreeDeletion
