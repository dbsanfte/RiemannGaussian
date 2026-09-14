/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeRieszWindows

/-!
# Complete cofactor sums and the unchanged original prime correction

A finite physical divisor cutoff gives exact Euler marks and genuine
completion in Re(s)>1, with the original polynomial factorial filter.
Returning to the literal composite carrier keeps the ordinary-prime
correction. The cofinal floor theorem states a sufficient condition only;
its independent arithmetic premise remains open.
-/

namespace RiemannGaussian.ZetaSquarefreeRieszCompletion
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory Set Filter Topology
open ZetaArithmeticAffine
open ZetaArithmeticBandCorrelation
open ZetaSquarefreeRieszWindows
open scoped ArithmeticFunction.Moebius

/-- The actual negative source needs only a fixed one-sided floor
strictly above minus one on a cofinal sequence. No absolute-value decay
or uniform bound at every order is required. The floor is a premise. -/
theorem false_of_cofinal_original_riesz_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop,
      -c ≤ ((3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im).re) : False := by
  have hsource := Complex.continuous_re.continuousAt.tendsto.comp
    (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho)
  have hf := ge_of_tendsto_of_frequently hsource hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- A finite physical divisor cutoff contains every nonzero Riesz ramp.
The cutoff depends on L, not on an internal factorial moment shift. -/
theorem riesz_eq_finite_divisor_cutoff (L : ℝ) {D n : ℕ}
    (hL : L ≤ Real.log (D + 1 : ℕ)) (hn : n ≠ 0) :
    VaughanLogAverage.riesz L n = ∑ d ∈ Finset.Icc 1 D,
      if d ∣ n then (μ d : ℝ) * max 0 (L - Real.log d) else 0 := by
  have hz (d : ℕ) (hd : D < d) : max 0 (L - Real.log d) = 0 := by
    apply max_eq_left
    apply sub_nonpos.mpr
    exact hL.trans (Real.log_le_log (by positivity)
      (by exact_mod_cast (show D + 1 ≤ d by omega)))
  calc
    _ = ∑ d ∈ n.divisors,
        if d ≤ D then (μ d : ℝ) * max 0 (L - Real.log d) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ≤ D
      · rw [if_pos hd]
      · rw [if_neg hd, hz d (by omega), mul_zero]
    _ = _ := by
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · exact fun h ↦ ⟨⟨Nat.pos_of_dvd_of_pos h.1.1
          (Nat.pos_of_ne_zero hn), h.2⟩, h.1.1⟩
      · exact fun h ↦ ⟨⟨h.2, hn⟩, h.1.2⟩

/-- Completing the squarefree support gives an exact finite superposition
of original divisibility marks, including every cofactor of each mark. -/
theorem completed_riesz_eq_finite_marks (L : ℝ) {D : ℕ}
    (hL : L ≤ Real.log (D + 1 : ℕ)) (n : ℕ) :
    (if Squarefree n then (VaughanLogAverage.riesz L n : ℂ) else 0) =
      ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        (((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ) *
          RoughSquarefreeBare.coefficient ∅ d n := by
  rw [Finset.sum_filter]
  by_cases hn : Squarefree n
  · rw [if_pos hn, riesz_eq_finite_divisor_cutoff L hL hn.ne_zero,
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ n
    · simp [RoughSquarefreeBare.coefficient, hn, hd, hn.squarefree_of_dvd hd]
    · by_cases hsf : Squarefree d <;>
        simp [RoughSquarefreeBare.coefficient, hn, hd, hsf]
  · simp [RoughSquarefreeBare.coefficient, hn]

/-- All cofactor correlations of the completed Riesz series are summed
by the exact complex Euler marks. This is genuine convergence in Re(s)>1,
not an assertion about Dirichlet-series convergence after continuation. -/
theorem LSeriesHasSum_completed_riesz (L : ℝ) {D : ℕ}
    (hL : L ≤ Real.log (D + 1 : ℕ)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum
      (fun n ↦ if Squarefree n then (VaughanLogAverage.riesz L n : ℂ) else 0) s
      (squarefreeEulerResponse s *
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ) *
            squarefreeEulerMultiplier ∅ d s) := by
  have h := LSeriesHasSum.sum (S := (Finset.Icc 1 D).filter Squarefree)
    (fun d hd ↦ (LSeriesHasSum_markedSquarefreeEuler ∅ (by simp)
      (Finset.mem_filter.mp hd).2 (by simp) hs).smul
      ((((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ)))
  convert h using 1
  · funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact completed_riesz_eq_finite_marks L hL n
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- Returning from the completed Euler representation to the actual
composite coefficient retains the entire ordinary-prime correction. -/
theorem original_riesz_eq_finite_marks_add_prime (L : ℝ) (hL0 : 0 < L) {D : ℕ}
    (hL : L ≤ Real.log (D + 1 : ℕ)) (n : ℕ) :
    SquarefreeVaughanLogSource.coefficient L n =
      (-(Real.log n : ℂ) / (L : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ) *
            RoughSquarefreeBare.coefficient ∅ d n) +
      (if n.Prime then ((Real.log n * min L (Real.log n) / L : ℝ) : ℂ) else 0) := by
  rw [← completed_riesz_eq_finite_marks L hL n,
    SquarefreeVaughanLogSource.coefficient_eq_completed_with_prime hL0]
  congr 1
  by_cases hn : Squarefree n
  · simp only [if_pos hn, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  · simp [hn]

/-- Every factorial polynomial filter acts on the complete cofactor
sum at the same physical cutoff. All logarithms and phases are retained. -/
theorem hasSum_completed_riesz_log_filter (L : ℝ) {D : ℕ}
    (hL : L ≤ Real.log (D + 1 : ℕ)) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦
      (if Squarefree n then (VaughanLogAverage.riesz L n : ℂ) else 0) *
        (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n)
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        (((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ) *
          SquarefreeEulerLog.response p ∅ d N s) := by
  have h := hasSum_sum (s := (Finset.Icc 1 D).filter Squarefree) (fun d _ ↦
    (SquarefreeEulerLog.summable_response p ∅ (by simp) d N hs).hasSum.mul_left
      ((((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ)))
  apply h.congr_fun
  intro n
  rw [completed_riesz_eq_finite_marks L hL n, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The literal finite carrier has the same cofactor decomposition for
every complex observation. Substituting its original factorial kernel
retains both the original band and its prime endpoint exactly. -/
theorem sum_original_riesz_eq_mark_sums_add_prime (T : Finset ℕ) (f : ℕ → ℂ)
    (L : ℝ) (hL0 : 0 < L) {D : ℕ} (hL : L ≤ Real.log (D + 1 : ℕ)) :
    (∑ n ∈ T, SquarefreeVaughanLogSource.coefficient L n * f n) =
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ) * (-(1 / (L : ℂ)))) *
          ∑ n ∈ T, RoughSquarefreeBare.coefficient ∅ d n * (Real.log n : ℂ) * f n) +
      ∑ n ∈ T,
        (if n.Prime then ((Real.log n * min L (Real.log n) / L : ℝ) : ℂ) else 0) * f n := by
  simp_rw [original_riesz_eq_finite_marks_add_prime L hL0 hL,
    add_mul, Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ n ∈ T, ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((((μ d : ℝ) * max 0 (L - Real.log d) : ℝ) : ℂ) * (-(1 / (L : ℂ)))) *
          (RoughSquarefreeBare.coefficient ∅ d n * (Real.log n : ℂ) * f n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]

end
end RiemannGaussian.ZetaSquarefreeRieszCompletion
