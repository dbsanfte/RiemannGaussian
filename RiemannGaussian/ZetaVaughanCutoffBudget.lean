/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVaughanReduction
import RiemannGaussian.ZetaMoebiusScaleBound
import Mathlib.Algebra.BigOperators.Module

/-!
# Square-root budgets for the complete Vaughan small-factor response

Chebyshev's bound pays for the actual von Mangoldt prefix, including all
prime powers, before the unit-circle Cauchy estimate is applied. Retaining
the inverse-square-root Dirichlet weights changes the two-prefix cost from
`U * V` to `sqrt U * sqrt V`. The original signed response, factorial filter
and finite band remain those of `ZetaVaughanReduction`.

These independent small-factor bounds do not bound the remaining bilinear
carrier. The prime-density input is the classical Chebyshev bound already
proved in Mathlib; no historical novelty is claimed for partial summation.
-/

open Complex Filter Metric Set Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.ZetaVaughanCutoffBudget
noncomputable section
open ZetaVaughanReduction

private theorem range_succ_eq (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, f (k + 1)) = ∑ k ∈ Finset.Icc 1 N, f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

private theorem weighted_prefix_le (c f : ℕ → ℝ) (C : ℝ)
    (hc : ∀ n, (∑ k ∈ Finset.range n, c k) ≤ C * n)
    (hf : ∀ n, 0 ≤ f n) (hanti : Antitone f) (N : ℕ) :
    (∑ k ∈ Finset.range N, f k * c k) ≤ C * ∑ k ∈ Finset.range N, f k := by
  have hr : C * ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range N, f k * C := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
  rw [hr]
  simp_rw [← smul_eq_mul]
  rw [Finset.sum_range_by_parts f c, Finset.sum_range_by_parts f (fun _ ↦ C)]
  simp only [smul_eq_mul, Finset.sum_const, nsmul_eq_mul]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hc N) (hf _)
  · apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonpos_left (by simpa [mul_comm] using hc (k + 1))
      (sub_nonpos.mpr (hanti (Nat.le_succ k)))

/-- Actual prime-power density pays the logarithmic weight with no extra
logarithm of the cutoff. All von Mangoldt terms are retained. -/
theorem sum_vonMangoldt_inv_sqrt_le (V : ℕ) :
    (∑ n ∈ Finset.Icc 1 V, ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≤
      12 * Real.sqrt V := by
  let c : ℕ → ℝ := fun k ↦ ArithmeticFunction.vonMangoldt (k + 1)
  let f : ℕ → ℝ := fun k ↦ 1 / Real.sqrt (k + 1)
  have hc (n : ℕ) : (∑ k ∈ Finset.range n, c k) ≤ 6 * n := by
    have he : (∑ k ∈ Finset.range n, c k) = Chebyshev.psi n := by
      rw [show c = fun k ↦ ArithmeticFunction.vonMangoldt (k + 1) from rfl,
        range_succ_eq]
      simp only [Chebyshev.psi, Nat.floor_natCast]
      congr 1
    rw [he]
    have hlog : Real.log 4 + 4 ≤ 6 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    exact (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hf (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hanti : Antitone f := by
    intro a b hab
    dsimp [f]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_succ hab))
  have hb := weighted_prefix_le c f 6 hc hf hanti V
  have he : (∑ k ∈ Finset.range V, f k * c k) =
      ∑ n ∈ Finset.Icc 1 V, ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    rw [← range_succ_eq]
    apply Finset.sum_congr rfl
    intro k _
    simp [f, c, div_eq_mul_inv, mul_comm]
  have hf' : (∑ k ∈ Finset.range V, f k) =
      ∑ n ∈ Finset.Icc 1 V, 1 / Real.sqrt n := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      range_succ_eq (fun n : ℕ ↦ 1 / Real.sqrt n) V
  rw [he, hf'] at hb
  exact hb.trans (by nlinarith [sum_inv_sqrt_Icc_le V])

/-- The entire Möbius prefix keeps its inverse-square-root divisor weights. -/
theorem norm_moebiusHead_le_sqrt (U : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖zetaMoebiusDirichletHead U s‖ ≤ 2 * Real.sqrt U := by
  rw [zetaMoebiusDirichletHead]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.range U, 1 / Real.sqrt (n + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro n _
      have he : Complex.exp (-s * (Real.log (n + 1 : ℕ) : ℂ)) =
          zetaPrimeFeature s (n + 1) := by
        unfold zetaPrimeFeature
        simp only [neg_mul]
      rw [he, norm_mul]
      have hm : ‖(μ (n + 1) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
      exact (mul_le_mul hm (norm_zetaPrimeFeature_le_inv_sqrt hs (by omega))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ ≤ _ := by
      rw [range_succ_eq (fun n : ℕ ↦ 1 / Real.sqrt n)]
      exact sum_inv_sqrt_Icc_le U

/-- Chebyshev density improves the entire prime prefix's uniform cutoff cost. -/
theorem norm_primeHead_le_sqrt (V : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖primeHead V s‖ ≤ 12 * Real.sqrt V := by
  rw [primeHead, zetaFiniteDirichletSeries]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 V, ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_div] using
          (norm_zetaPrimeFeature_le_inv_sqrt hs (Finset.mem_Icc.mp hn).1))
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := sum_vonMangoldt_inv_sqrt_le V

private theorem unit_ball_re (y : ℝ) {s : ℂ}
    (hs : s ∈ closedBall (3 / 2 + I * (y : ℂ)) 1) : 1 / 2 ≤ s.re := by
  have hr := (Complex.abs_re_le_norm (s - (3 / 2 + I * (y : ℂ)))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hr
  linarith [(abs_le.mp hr).1]

/-- Every prime-prefix moment inherits the same square-root budget. -/
theorem norm_primeHead_moment_le_sqrt (V N : ℕ) (y : ℝ) :
    ‖signedTaylorMoment N (primeHead V) (3 / 2 + I * y)‖ ≤ 12 * Real.sqrt V := by
  have ha := differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 V)
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hd : DiffContOnCl ℂ (primeHead V) (ball (3 / 2 + I * (y : ℂ)) 1) :=
    ha.differentiableOn.diffContOnCl
  simpa only [one_pow, div_one] using norm_signedTaylorMoment_le (by norm_num) hd
    (fun s hs ↦ norm_primeHead_le_sqrt V (unit_ball_re y (sphere_subset_closedBall hs))) N

/-- The full independent budget keeps the square roots of both cutoffs,
including their product and all three small-factor terms. -/
theorem exists_smallFilter_sqrt_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (U V N : ℕ),
      ‖smallFilter p U V N (3 / 2 + I * y)‖ ≤
        (12 * Real.sqrt V + C * (2 * Real.sqrt U +
          24 * Real.sqrt U * Real.sqrt V)) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_moment_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p U V N
  have hm := differentiable_zetaMoebiusDirichletHead U
  have ha := differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 V)
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hg : Differentiable ℂ (fun s ↦ -(zetaMoebiusDirichletHead U s * primeHead V s)) :=
    (hm.mul ha).neg
  have hbound (k : ℕ) := hb (zetaMoebiusDirichletHead U)
    (fun s ↦ -(zetaMoebiusDirichletHead U s * primeHead V s)) hm hg
    (2 * Real.sqrt U) (24 * Real.sqrt U * Real.sqrt V)
    (by positivity) (by positivity) (fun s hs ↦ norm_moebiusHead_le_sqrt U hs)
    (fun s hs ↦ by
      rw [norm_neg, norm_mul]
      exact (mul_le_mul (norm_moebiusHead_le_sqrt U hs) (norm_primeHead_le_sqrt V hs)
        (norm_nonneg _) (by positivity)).trans_eq (by ring)) k
  have hz : AnalyticAt ℂ riemannZeta (3 / 2 + I * (y : ℂ)) :=
    analyticOn_riemannZeta _ (by intro h; have := congrArg Complex.re h; norm_num at this)
  have hsmall (k : ℕ) :
      ‖signedTaylorMoment k (smallResponse U V) (3 / 2 + I * y)‖ ≤
        12 * Real.sqrt V + C * (2 * Real.sqrt U + 24 * Real.sqrt U * Real.sqrt V) := by
    have ha' : AnalyticAt ℂ (primeHead V) (3 / 2 + I * (y : ℂ)) := ha.analyticAt (z := _)
    have hb' : AnalyticAt ℂ (fun s ↦ zetaMoebiusDirichletHead U s * (-deriv riemannZeta s) +
        (-(zetaMoebiusDirichletHead U s * primeHead V s)) * riemannZeta s)
        (3 / 2 + I * (y : ℂ)) :=
      ((hm.analyticAt (z := _)).mul hz.deriv.neg).add ((hg.analyticAt (z := _)).mul hz)
    unfold smallResponse
    rw [signedTaylorMoment_add k ha' hb']
    exact (norm_add_le _ _).trans (add_le_add (norm_primeHead_moment_le_sqrt V k y) (hbound k))
  rw [smallFilter, zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ *
        (12 * Real.sqrt V + C * (2 * Real.sqrt U + 24 * Real.sqrt U * Real.sqrt V)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hsmall (N + k)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- A symmetric budget that allows arbitrary allocation between the two
factor cutoffs, and includes zero and unit cutoffs without exceptions. -/
def budget (U V : ℕ) : ℝ := Real.sqrt (U + 1 : ℝ) * Real.sqrt (V + 1 : ℝ)

/-- The full cutoff budget is positive. -/
theorem budget_pos (U V : ℕ) : 0 < budget U V := by unfold budget; positivity

private theorem sqrt_le_budget (U V : ℕ) :
    Real.sqrt U ≤ budget U V ∧ Real.sqrt V ≤ budget U V ∧
      Real.sqrt U * Real.sqrt V ≤ budget U V := by
  have hU : 1 ≤ Real.sqrt (U + 1 : ℝ) := Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) U])
  have hV : 1 ≤ Real.sqrt (V + 1 : ℝ) := Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) V])
  have hU' : Real.sqrt U ≤ Real.sqrt (U + 1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hV' : Real.sqrt V ≤ Real.sqrt (V + 1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  unfold budget
  refine ⟨?_, ?_, mul_le_mul hU' hV' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
  · exact hU'.trans (le_mul_of_one_le_right (Real.sqrt_nonneg _) hV)
  · exact hV'.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) hU)

/-- One independent ordinate constant controls every polynomial, moment
and pair of cutoffs through their complete square-root product budget. -/
theorem exists_smallFilter_budget_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (U V N : ℕ),
      ‖smallFilter p U V N (3 / 2 + I * y)‖ ≤
        C * budget U V * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_smallFilter_sqrt_bound y hy
  refine ⟨12 + 26 * C, by positivity, ?_⟩
  intro p U V N
  have ⟨hU, hV, hUV⟩ := sqrt_le_budget U V
  have hinner : 2 * Real.sqrt U + 24 * Real.sqrt U * Real.sqrt V ≤ 26 * budget U V := by
    nlinarith
  apply (hb p U V N).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  have hCinner := mul_le_mul_of_nonneg_left hinner hC.le
  nlinarith

/-- The compact budget is at most `D+1` whenever both cutoffs are at most D. -/
theorem budget_le_of_le {U V D : ℕ} (hU : U ≤ D) (hV : V ≤ D) :
    budget U V ≤ D + 1 := by
  calc
    _ ≤ Real.sqrt (D + 1 : ℝ) * Real.sqrt (D + 1 : ℝ) := by
      unfold budget
      gcongr
    _ = _ := Real.mul_self_sqrt (by positivity)

/-- Any pair of moving cutoffs whose explicit normalized budget vanishes
has independently vanishing small-factor response. -/
theorem tendsto_smallFilter_of_budget (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (U V : ℕ → ℕ)
    (hbudget : Tendsto (fun N ↦ u ^ (N + 1) * budget (U N) (V N)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * smallFilter p (U N) (V N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_smallFilter_budget_bound y hy
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  apply squeeze_zero_norm (fun N ↦ ?_) (by
    simpa only [mul_zero] using hbudget.const_mul (C * S))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  exact (mul_le_mul_of_nonneg_left (hb p (U N) (V N) N) (by positivity)).trans_eq (by ring)

/-- A growing positive denominator may slow the inverse-source exponential
cutoff by any amount. Its full cost is retained in the next bound. -/
def dampedCutoff (u b : ℝ) (N : ℕ) : ℕ := ⌊u⁻¹ ^ N / b⌋₊

/-- The exact independent cutoff allowance, including the integer-floor
correction, holds for every positive damping denominator. -/
theorem normalized_budget_dampedCutoff_le {u b : ℝ} (hu : 0 < u) (hb : 0 < b)
    (N U V : ℕ) (hU : U ≤ dampedCutoff u b N) (hV : V ≤ dampedCutoff u b N) :
    u ^ (N + 1) * budget U V ≤ u / b + u ^ (N + 1) := by
  have hfloor : (dampedCutoff u b N : ℝ) ≤ u⁻¹ ^ N / b := Nat.floor_le (by positivity)
  have hbudget : budget U V ≤ u⁻¹ ^ N / b + 1 := by
    linarith [budget_le_of_le hU hV]
  calc
    _ ≤ u ^ (N + 1) * (u⁻¹ ^ N / b + 1) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by
      rw [pow_succ, inv_pow]
      field_simp

/-- All moving cutoff pairs below the damped ceiling have independent
decay, for every positive denominator tending to infinity. -/
theorem tendsto_smallFilter_dampedCutoff (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (b : ℕ → ℝ)
    (hb : ∀ N, 0 < b N) (hbtop : Tendsto b atTop atTop) (U V : ℕ → ℕ)
    (hU : ∀ N, U N ≤ dampedCutoff u (b N) N)
    (hV : ∀ N, V N ≤ dampedCutoff u (b N) N) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * smallFilter p (U N) (V N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  apply tendsto_smallFilter_of_budget p y hy hu U V
  apply squeeze_zero (fun N ↦ mul_nonneg (by positivity) (budget_pos _ _).le)
    (fun N ↦ normalized_budget_dampedCutoff_le hu (hb N) N (U N) (V N) (hU N) (hV N))
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hu.le hu1).comp (tendsto_add_atTop_nat 1)
  simpa only [zero_add, Function.comp_def] using (hbtop.const_div_atTop u).add hpow

/-- The complete normalized small-factor response has an explicit
allowance for every positive damping denominator and both cutoff choices. -/
theorem exists_smallFilter_damped_bound (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N U V : ℕ) (b : ℝ), 0 < b →
      U ≤ dampedCutoff u b N → V ≤ dampedCutoff u b N →
      ‖(u : ℂ) ^ (N + 1) * smallFilter p U V N (3 / 2 + I * y)‖ ≤
        C * (u / b + u ^ (N + 1)) := by
  obtain ⟨C, hC, hb⟩ := exists_smallFilter_budget_bound y hy
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  refine ⟨C * S + 1, by positivity, ?_⟩
  intro N U V b hb0 hU hV
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * budget U V * S) :=
      mul_le_mul_of_nonneg_left (hb p U V N) (by positivity)
    _ = (C * S) * (u ^ (N + 1) * budget U V) := by ring
    _ ≤ (C * S) * (u / b + u ^ (N + 1)) := mul_le_mul_of_nonneg_left
      (normalized_budget_dampedCutoff_le hu hb0 N U V hU hV) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The complete hypothetical-zero response survives every paid allocation
of the two cutoffs. This limit is conditional, not an independent floor. -/
theorem tendsto_actual_source_of_budget (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (U V : ℕ → ℕ)
    (hbudget : Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      responseFilter (zetaRightHalfPoleJetFilter rho hrho) (U N) (V N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hsmall := tendsto_smallFilter_of_budget (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hu U V hbudget
  have h := (tendsto_zetaRightHalfPoleJetFilter rho hrho).sub hsmall
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  push_cast
  rw [filter_identity _ _ _ N (by norm_num), mul_add, add_sub_cancel_left]

/-- The same paid cutoff allocations retain the original finite band,
product phases, shared primes and negative-multiplicity source. -/
theorem tendsto_actual_band_of_budget (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (U V : ℕ → ℕ)
    (hbudget : Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      zetaArithmeticBand (fun n ↦ (bilinear (U N) (V N) n : ℂ))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u := 3 / 2 - rho.1.re
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have herror := tendsto_zetaDominatedFilter_sub_band
    (fun N n ↦ (bilinear (U N) (V N) n : ℂ)) (fun N ↦ norm_bilinear_le (U N) (V N)) p rho.1.im
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have hsum := (tendsto_actual_source_of_budget rho hrho U V hbudget).congr'
    (Filter.Eventually.of_forall fun N ↦ congrArg
      (fun z : ℂ ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * z)
      (hasSum_responseFilter p (U N) (V N) N (s := 3 / 2 + I * (rho.1.im : ℂ))
        (by norm_num)).tsum_eq.symm)
  have h := hsum.sub (hpow.mul herror)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [zetaArithmeticFilter, u]
  push_cast
  ring

/-- A canonical near-inverse-source cutoff: the positive damping is N+1. -/
def linearDampedCutoff (u : ℝ) (N : ℕ) : ℕ := dampedCutoff u (N + 1) N

/-- The concrete new cutoff has vanishing independent budget, with the
explicit allowance `u/(N+1) + u^(N+1)`. -/
theorem tendsto_budget_linearDampedCutoff {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N ↦ u ^ (N + 1) * budget (linearDampedCutoff u N) (linearDampedCutoff u N))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N : ℕ ↦ mul_nonneg (by positivity) (budget_pos _ _).le)
    (fun N ↦ normalized_budget_dampedCutoff_le hu (by positivity : 0 < (N : ℝ) + 1)
      N _ _ le_rfl le_rfl)
  have hdiv := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul u
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hu.le hu1).comp (tendsto_add_atTop_nat 1)
  simpa only [mul_zero, zero_add, mul_one_div, Function.comp_def] using hdiv.add hpow

/-- The actual complete bilinear band has its source at the larger
cutoff `floor(u^(-N)/(N+1))`. The independent signed lower bound remains open. -/
theorem tendsto_actual_band_linearDampedCutoff (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let D := linearDampedCutoff (3 / 2 - rho.1.re)
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      zetaArithmeticBand (fun n ↦ (bilinear (D N) (D N) n : ℂ))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply tendsto_actual_band_of_budget rho hrho
  exact tendsto_budget_linearDampedCutoff
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)

/-- Every geometric cutoff strictly below inverse-source growth is
eventually smaller than the concrete linearly damped cutoff. -/
theorem eventually_geometricCutoff_lt_linearDampedCutoff {u r : ℝ}
    (hu : 0 < u) (hr : 1 ≤ r) (hur : u * r < 1) :
    ∀ᶠ N : ℕ in atTop, zetaMoebiusGeometricCutoff r N < linearDampedCutoff u N := by
  have hur0 : 0 ≤ u * r := mul_nonneg hu.le (zero_le_one.trans hr)
  have hN := tendsto_self_mul_const_pow_of_lt_one hur0 hur
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hur0 hur
  have hlim : Tendsto (fun N : ℕ ↦ 2 * ((N : ℝ) + 1) * (u * r) ^ N) atTop (𝓝 0) := by
    convert (hN.add hpow).const_mul 2 using 1
    · funext N; ring
    · simp
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN
  have hrN : 1 ≤ r ^ N := one_le_pow₀ hr
  have hpos : 0 < u ^ N := pow_pos hu N
  have hinv : u ^ N * u⁻¹ ^ N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hu.ne', one_pow]
  have hscale : (r ^ N + 1) * ((N : ℝ) + 1) < u⁻¹ ^ N := by
    rw [mul_pow] at hN
    apply (mul_lt_mul_iff_right₀ hpos).mp
    have hcomp := mul_le_mul_of_nonneg_right (by linarith : r ^ N + 1 ≤ 2 * r ^ N)
      (show 0 ≤ ((N : ℝ) + 1) * u ^ N by positivity)
    nlinarith
  have hdiv : r ^ N + 1 < u⁻¹ ^ N / ((N : ℝ) + 1) :=
    (lt_div_iff₀ (by positivity)).mpr hscale
  have hfloor : (zetaMoebiusGeometricCutoff r N : ℝ) ≤ r ^ N := Nat.floor_le (by positivity)
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  apply Nat.le_floor
  push_cast
  linarith

/-- In particular, the new cutoff strictly enlarges the preceding
Vaughan cutoff at every source normalization, after finitely many orders. -/
theorem eventually_previous_cutoff_lt {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N : ℕ in atTop,
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N < linearDampedCutoff u N := by
  have hq := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hs : Real.sqrt u < 1 := by nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
  apply eventually_geometricCutoff_lt_linearDampedCutoff hu hq
  have hq2 : zetaMoebiusHeadGrowth u ≤ zetaMoebiusHeadGrowth u ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hq2 hu.le
  rw [zetaMoebiusHeadGrowth_rate hu] at hmul
  exact hmul.trans_lt hs

end
end RiemannGaussian.ZetaVaughanCutoffBudget
