/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAssignedCompanion

/-!
# One finite signed sum with the whole infinite boundary paid

The entire companion outside 7N/4 < log n <= 9N/4 has a geometric bound, uniform in height and radius up to exp(-11/16). Every original finite mask remains in a multiplier between minus one and one. The exact source and reserve survive; the independent arithmetic floor remains open.
-/

namespace RiemannGaussian.ZetaRieszJointAllocation
noncomputable section
open scoped BigOperators Classical

open Filter Topology
open ZetaRieszJointCofactor

/-- The constant polynomial filter is exactly the original factorial logarithmic kernel. -/
theorem filter_one_eq (N : ℕ) (s : ℂ) (n : ℕ) :
    zetaPrimeFilterKernel 1 N s n = zetaPrimeLogKernel N s n := by
  simp only [zetaPrimeFilterKernel, ZetaRieszCosineCarrier.factorialPolynomial_one,
    zetaPrimeLogKernel, zetaPrimeFeature, neg_mul]

/-- The complete infinite outer logarithmic tails have one geometric bound for every dominated coefficient family and height. -/
theorem exists_complete_outer_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧ ∀ (N : ℕ) (a : ℕ → ℂ),
      (∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) →
      (∀ (n : ℕ), (7 / 4 : ℝ) * N < Real.log n → Real.log n ≤ (9 / 4 : ℝ) * N → a n = 0) →
      ∀ (y u : ℝ), 0 ≤ u → u ≤ Real.exp (-(11 / 16 : ℝ)) →
        ‖(u : ℂ) ^ (N + 1) * ∑' n, a n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤ r ^ N * C := by
  obtain ⟨r, C, hr0, hr1, hC, hb⟩ := ZetaArithmeticDeviationBounds.exists_uniform_deviation_bound
    (1 : Polynomial ℂ) (Real.exp_pos (-(11 / 16 : ℝ))) (by norm_num : (0 : ℝ) < 7 / 4)
    (by norm_num : (7 / 4 : ℝ) < 2) (by norm_num : (2 : ℝ) < 9 / 4)
    ZetaRieszHarmonicWindow.reserve_window_costs.1 ZetaRieszHarmonicWindow.reserve_window_costs.2
  refine ⟨r, C, hr0, hr1, hC, ?_⟩
  intro N a ha hz y u hu huU
  have hs := (summable_zetaDominatedMoment a ha N
    (by norm_num : (1 : ℝ) < (3 / 2 + Complex.I * (y : ℂ)).re)).hasSum
  apply le_of_tendsto (hs.mul_left ((u : ℂ) ^ (N + 1))).norm
  apply Eventually.of_forall
  intro S
  have h := hb N S a (fun n _ => ha n) y u hu huU
  have hzero : (∑ n ∈ LogarithmicDeviation.deviationBand S (7 / 4) (9 / 4) N,
      a n * zetaPrimeFilterKernel 1 N (3 / 2 + Complex.I * y) n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have h := (Finset.mem_filter.mp hn).2
    rw [hz n h.1 h.2, zero_mul]
  rw [hzero, sub_zero] at h
  simpa only [filter_one_eq, Finset.mul_sum] using h

/-- The complete finite integer window between the proved reserve-range logarithmic endpoints. -/
def literalWindow (N : ℕ) : Finset ℕ :=
  LogarithmicDeviation.deviationBand (zetaPrimeLogBand N) (7 / 4) (9 / 4) N

/-- The finite window has exactly the desired strict lower and closed upper logarithmic endpoints. -/
theorem mem_literalWindow (N n : ℕ) : n ∈ literalWindow N ↔
    (7 / 4 : ℝ) * N < Real.log n ∧ Real.log n ≤ (9 / 4 : ℝ) * N := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      have := hn.1
      norm_num at this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlog2lo := Real.log_two_gt_d9
    have hlog2hi := Real.log_two_lt_d9
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hupper : n ≤ 2 ^ (32 * N) := by
      have he : Real.log (n : ℝ) ≤ Real.log (2 ^ (32 * N) : ℕ) := by
        simp only [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
        nlinarith [hn.2]
      exact_mod_cast (Real.log_le_log_iff hnpos (by positivity : (0 : ℝ) < (2 ^ (32 * N) : ℕ))).mp he
    have hlower : (N : ℝ) * Real.log 2 / 4 < Real.log n := by nlinarith [hn.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hupper⟩, hlower⟩, hn⟩


/-- The whole companion outside the finite window has a height-uniform geometric source-scale bound. -/
theorem exists_companion_window_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (y u : ℝ), 0 ≤ u → u ≤ Real.exp (-(11 / 16 : ℝ)) →
        ‖(u : ℂ) ^ (N + 1) * (compositeWing u y N -
          ∑ n ∈ literalWindow N, assignedAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) y N n)‖ ≤ r ^ N * C := by
  obtain ⟨r, C, hr0, hr1, hC, hb⟩ := exists_complete_outer_bound
  refine ⟨r, C, hr0, hr1, hC, ?_⟩
  intro N y u hu huU
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let a : ℕ → ℂ := fun n => if n ∈ literalWindow N then 0 else assignedCoefficient A L N n
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n := by
    intro n
    dsimp only [a]
    split_ifs
    · simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n
    · exact norm_assignedCoefficient_le A hL N n
  have hz : ∀ (n : ℕ), (7 / 4 : ℝ) * N < Real.log n → Real.log n ≤ (9 / 4 : ℝ) * N → a n = 0 := by
    intro n hnlo hnhi
    exact if_pos ((mem_literalWindow N n).mpr ⟨hnlo, hnhi⟩)
  have h := hb N a ha hz y u hu huU
  let f : ℕ → ℂ := fun n => assignedAtom A L y N n
  let g : ℕ → ℂ := fun n => if n ∈ literalWindow N then f n else 0
  have hf : HasSum f (compositeWing u y N) := hasSum_assignedAtom u y N
  have hg : Summable g := by
    apply hf.summable.norm.of_norm_bounded
    intro n
    dsimp only [g]
    split_ifs
    · exact le_rfl
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0).trans_le (norm_nonneg _)
  have hgts : (∑' n, g n) = ∑ n ∈ literalWindow N, f n := by
    calc
      _ = ∑ n ∈ literalWindow N, g n := tsum_eq_sum (fun n hn => if_neg hn)
      _ = _ := Finset.sum_congr rfl (fun n hn => if_pos hn)
  have hts : (∑' n, a n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) =
      compositeWing u y N - ∑ n ∈ literalWindow N, f n := by
    rw [← hf.tsum_eq, ← hgts, ← hf.summable.tsum_sub hg]
    apply tsum_congr
    intro n
    by_cases hn : n ∈ literalWindow N
    · simp [a, g, hn]
    · simp only [a, g, if_neg hn, sub_zero]
      dsimp only [f, assignedCoefficient]
      rw [assignedAtom_eq_boundedShare A hL y N n]
      ring
  rw [hts] at h
  exact h

-- Finite signed complement identity; no floor or mask equality is assumed.
/-- An exact finite signed subtraction retains every phase and the complementary allocation fraction. -/
theorem finite_response_sub_companion (S : Finset ℕ) (A : Finset ℕ) {L : ℝ}
    (hL : 0 < L) (y : ℝ) (N : ℕ) :
    (∑ n ∈ S, SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) -
      (∑ n ∈ S, assignedAtom A L y N n) =
    ∑ n ∈ S, residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [assignedAtom_eq_boundedShare A hL y N n, residualCoefficient]
  push_cast
  ring


/-- The actual finite lower-count mask minus the complete assigned fraction; no earlier mask is dropped. -/
def finiteWeight (u : ℝ) (N K n : ℕ) : ℝ :=
  (if n ∈ LogarithmicDeviation.deviationBand (ZetaRieszHarmonicWindow.fewBand u N K)
    (7 / 4) (9 / 4) N then 1 else 0) -
      boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n

/-- The joint finite multiplier lies between minus one and one, including the off-mask correction. -/
theorem finiteWeight_bounds (u : ℝ) (N K n : ℕ) :
    -1 ≤ finiteWeight u N K n ∧ finiteWeight u N K n ≤ 1 := by
  have h := boundedShare_bounds (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n
  unfold finiteWeight
  split_ifs <;> constructor <;> linarith

/-- The full joint finite coefficient, preserving its signed Riesz profile and original masks. -/
def finiteCoefficient (u : ℝ) (N K n : ℕ) : ℂ :=
  (finiteWeight u N K n : ℂ) *
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n

/-- One finite sum representing the remaining count-minus-companion response up to the proved geometric error. -/
def finiteResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ literalWindow N, finiteCoefficient u N K n *
    zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n

/-- The finite response is exactly the old masked response minus the companion inside the complete finite window. -/
theorem finiteResponse_eq (u y : ℝ) (N K : ℕ) :
    finiteResponse u y N K = ZetaRieszHarmonicWindow.windowResponse 1 u y (7 / 4) (9 / 4) N K -
      ∑ n ∈ literalWindow N, assignedAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) y N n := by
  let S := LogarithmicDeviation.deviationBand (ZetaRieszHarmonicWindow.fewBand u N K) (7 / 4) (9 / 4) N
  let f := fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
    zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n
  have hSW : S ⊆ literalWindow N := by
    intro n hn
    exact (mem_literalWindow N n).mpr (Finset.mem_filter.mp hn).2
  have hsum : (∑ n ∈ literalWindow N, if n ∈ S then f n else 0) =
      ZetaRieszHarmonicWindow.windowResponse 1 u y (7 / 4) (9 / 4) N K := by
    calc
      _ = ∑ n ∈ S, if n ∈ S then f n else 0 :=
        (Finset.sum_subset hSW (fun n _ hn => if_neg hn)).symm
      _ = ∑ n ∈ S, f n := Finset.sum_congr rfl (fun n hn => if_pos hn)
      _ = _ := by simp only [ZetaRieszHarmonicWindow.windowResponse, filter_one_eq, S, f]
  rw [← hsum, ← Finset.sum_sub_distrib]
  unfold finiteResponse
  apply Finset.sum_congr rfl
  intro n hn
  rw [assignedAtom_eq_boundedShare _ (SquarefreeVaughanLogSource.length_pos u N) y N n]
  unfold finiteCoefficient finiteWeight
  change (((if n ∈ S then (1 : ℝ) else 0) - boundedShare _ N n : ℝ) : ℂ) * _ * _ = _
  by_cases hnS : n ∈ S
  · simp only [if_pos hnS, Complex.ofReal_sub, Complex.ofReal_one, f]
    ring
  · simp only [if_neg hnS, Complex.ofReal_sub, Complex.ofReal_zero, f]
    ring

/-- The whole arithmetic difference has a single finite representation with a geometric error uniform in height, count threshold and radius. -/
theorem exists_finiteResponse_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ Real.exp (-(11 / 16 : ℝ)) →
        ‖(u : ℂ) ^ (N + 1) *
          (ZetaRieszHarmonicWindow.windowResponse 1 u y (7 / 4) (9 / 4) N K -
            compositeWing u y N - finiteResponse u y N K)‖ ≤ r ^ N * C := by
  obtain ⟨r, C, hr0, hr1, hC, hb⟩ := exists_companion_window_error
  refine ⟨r, C, hr0, hr1, hC, ?_⟩
  intro N K y u hu huU
  rw [finiteResponse_eq]
  have he : (u : ℂ) ^ (N + 1) *
      (ZetaRieszHarmonicWindow.windowResponse 1 u y (7 / 4) (9 / 4) N K - compositeWing u y N -
        (ZetaRieszHarmonicWindow.windowResponse 1 u y (7 / 4) (9 / 4) N K -
          ∑ n ∈ literalWindow N, assignedAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) y N n)) =
      -((u : ℂ) ^ (N + 1) * (compositeWing u y N -
          ∑ n ∈ literalWindow N, assignedAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) y N n)) := by ring
  rw [he, norm_neg]
  exact hb N y u hu huU


open ZetaRieszPrimeCountFrequency

/-- The finite joint arithmetic response on the original dyadic schedule and source normalization. -/
def finiteRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) * finiteResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- The full arithmetic remainder differs from the finite joint response by an independently vanishing error. -/
theorem tendsto_arithmetic_sub_finite (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huh : u ≤ Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j => arithmeticRemainder u y j - finiteRemainder u y j) atTop (𝓝 0) := by
  obtain ⟨r, C, hr0, hr1, _, hb⟩ := exists_finiteResponse_error
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp tendsto_dyadicMomentOrder).mul_const C
  simp only [Function.comp_def, zero_mul] at ht
  apply squeeze_zero_norm (fun j => ?_) ht
  have h := hb (dyadicMomentOrder j) (dyadicPrimeCount j) y u hu huh
  dsimp only [arithmeticRemainder, finiteRemainder]
  simpa only [mul_sub] using h

/-- The exact exposed-zero source and positive reserve survive in one finite signed sum; its independent floor remains open. -/
theorem tendsto_finite_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j : ℕ => finiteRemainder (3 / 2 - rho.1.re) rho.1.im j +
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1) *
        ZetaRieszWingReserve.reserve (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he := tendsto_arithmetic_sub_finite rho.1.im hu huh.le
  have hs := (tendsto_arithmeticRemainder_add_reserve rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall (fun _ => by ring))

/-- The complete finite signed coefficient retains the original divisor majorant without an incidence cost. -/
theorem norm_finiteCoefficient_le (u : ℝ) (N K n : ℕ) :
    ‖finiteCoefficient u N K n‖ ≤ zetaMoebiusLogMajorant n := by
  have h := finiteWeight_bounds u N K n
  rw [finiteCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr h)).trans
    (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)


end
end RiemannGaussian.ZetaRieszJointAllocation
