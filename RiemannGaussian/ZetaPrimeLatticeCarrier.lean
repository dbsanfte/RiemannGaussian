/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeDiscrepancyWork
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The original signed prime carrier on the integer lattice

The lattice/continuous sampling difference has an exact signed sawtooth
formula and an independent geometric bound for the full factorial filter.
Subtracting the complete integer background preserves the selected zero's
original linear source. Every composite coefficient, prime phase, endpoint
and polynomial coefficient remains in the resulting finite arithmetic sum.

The independent cofinal signed lower bound remains open.
-/

namespace RiemannGaussian.PrimeLatticeCarrier
noncomputable section
open Complex Filter MeasureTheory Topology
open scoped Classical

/-- The complete integer sum on the original half-open real interval. -/
def lattice (p : Polynomial ℂ) (N : ℕ) (s : ℂ) (a b : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, zetaPrimeFilterKernel p N s n

/-- The upper sawtooth. At an integer its value is one; those endpoint
values are retained in the exact Abel identity. -/
def saw (x : ℝ) : ℝ := (⌊x⌋₊ : ℝ) + 1 - x

/-- On the nonnegative axis the actual sawtooth lies in `(0,1]`. -/
theorem saw_bounds {x : ℝ} (hx : 0 ≤ x) : 0 < saw x ∧ saw x ≤ 1 := by
  constructor
  · exact sub_pos.mpr (Nat.lt_floor_add_one x)
  · dsimp [saw]
    linarith [Nat.floor_le hx]

private theorem prefix_one (x : ℝ) :
    (∑ _n ∈ Finset.Icc 0 ⌊x⌋₊, (1 : ℂ)) = (⌊x⌋₊ : ℂ) + 1 := by
  simp

/-- Exact Abel summation for every original integer, with the complete
prefix and both unrounded endpoints. -/
theorem lattice_eq_abel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lattice p N s a b =
      zetaPrimeFilterKernel p N s b * ((⌊b⌋₊ : ℂ) + 1) -
        zetaPrimeFilterKernel p N s a * ((⌊a⌋₊ : ℂ) + 1) -
          ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * ((⌊x⌋₊ : ℂ) + 1) := by
  have h := sum_mul_eq_sub_sub_integral_mul (fun _ : ℕ ↦ (1 : ℂ)) ha.le hab
    (fun x hx ↦ (contDiffAt_zetaPrimeFilterKernel p N s (ha.trans_le hx.1)).differentiableAt
      (by norm_num)) (integrableOn_deriv_zetaPrimeFilterKernel p N s ha)
  simpa only [prefix_one, mul_one, lattice] using h

/-- Genuine compact-interval integrability of the full complex derivative
paired with the discontinuous sawtooth. -/
theorem integrableOn_deriv_mul_saw (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x ↦ deriv (zetaPrimeFilterKernel p N s) x * (saw x : ℂ))
      (Set.Icc a b) := by
  have hd := integrableOn_deriv_zetaPrimeFilterKernel p N s (b := b) ha
  have ht := integrableOn_mul_sum_Icc (fun _ : ℕ ↦ (1 : ℂ)) (m := 0) ha.le hd
  simp_rw [prefix_one] at ht
  have hx : IntegrableOn (fun x : ℝ ↦ (x : ℂ) * deriv (zetaPrimeFilterKernel p N s) x)
      (Set.Icc a b) :=
    IntegrableOn.continuousOn_mul Complex.continuous_ofReal.continuousOn hd isCompact_Icc
  convert ht.sub hx using 1
  funext x
  simp only [Pi.sub_apply]
  simp only [saw, ofReal_sub, ofReal_add, ofReal_natCast, ofReal_one]
  ring

/-- Exact lattice sampling error: its complex phase, both boundary
sawtooth values and the entire derivative integral remain available. -/
theorem lattice_sub_integral (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lattice p N s a b - (∫ x in Set.Ioc a b, zetaPrimeFilterKernel p N s x) =
      zetaPrimeFilterKernel p N s b * (saw b : ℂ) -
        zetaPrimeFilterKernel p N s a * (saw a : ℂ) -
          ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (saw x : ℂ) := by
  have hd := integrableOn_deriv_zetaPrimeFilterKernel p N s (b := b) ha
  have ht := integrableOn_mul_sum_Icc (fun _ : ℕ ↦ (1 : ℂ)) (m := 0) ha.le hd
  simp_rw [prefix_one] at ht
  have hx : IntegrableOn (fun x : ℝ ↦ deriv (zetaPrimeFilterKernel p N s) x * (x : ℂ))
      (Set.Icc a b) := by
    simpa only [mul_comm] using
      IntegrableOn.continuousOn_mul Complex.continuous_ofReal.continuousOn hd isCompact_Icc
  have hi : (∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (saw x : ℂ)) =
      (∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * ((⌊x⌋₊ : ℂ) + 1)) -
        ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (x : ℂ) := by
    rw [← integral_sub (ht.mono_set Set.Ioc_subset_Icc_self) (hx.mono_set Set.Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    dsimp only
    simp only [saw, ofReal_sub, ofReal_add, ofReal_natCast, ofReal_one]
    ring
  rw [hi, lattice_eq_abel p N s ha hab, zetaPrimeFilterKernel_integral_Ioc p N s ha hab]
  simp only [saw, ofReal_sub, ofReal_add, ofReal_natCast, ofReal_one]
  ring

/-- The complete coefficient budget for a single fixed exponential tilt. -/
def coefficientBudget (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ * (4 / 5 : ℝ) ^ k

/-- The coefficient budget is nonnegative for every complex filter. -/
theorem coefficientBudget_nonneg (p : Polynomial ℂ) : 0 ≤ coefficientBudget p := by
  unfold coefficientBudget
  exact Finset.sum_nonneg (fun _ _ ↦ by positivity)

/-- The full lowering derivative is an exact parameter-shifted pair;
the ordinate-bearing multiplier is kept before any norm. -/
theorem deriv_kernel_eq_shift (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    deriv (zetaPrimeFilterKernel p (N + 1) s) x =
      zetaPrimeFilterKernel p N (s + 1) x - s * zetaPrimeFilterKernel p (N + 1) (s + 1) x := by
  rw [deriv_zetaPrimeFilterKernel p N s hx, sub_div, mul_div_assoc]
  simpa only [pow_one, Nat.cast_one] using congrArg₂ (fun u v : ℂ ↦ u - s * v)
    (zetaPrimeFilterKernel_div_pow p N 1 s hx)
    (zetaPrimeFilterKernel_div_pow p (N + 1) 1 s hx)

/-- A uniform spatially integrable bound for the entire derivative pair.
The full complex center enters its constant; no height uniformity is asserted. -/
theorem norm_deriv_kernel_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * (y : ℂ))) x‖ ≤
      (5 / 4 + ‖3 / 2 + I * (y : ℂ)‖) * (4 / 5 : ℝ) ^ (N + 1) * coefficientBudget p *
        x ^ (-(5 / 4 : ℝ)) := by
  have hx0 := zero_lt_one.trans_le hx
  have hk (n : ℕ) :
      ‖zetaPrimeFilterKernel p n (3 / 2 + I * (y : ℂ) + 1) x‖ ≤
        (4 / 5 : ℝ) ^ n * x ^ (-(5 / 4 : ℝ)) * coefficientBudget p := by
    have h := norm_zetaPrimeFilterKernel_le_tilt p n (3 / 2 + I * (y : ℂ) + 1)
      hx (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h
    rw [Real.rpow_def_of_pos hx0]
    simpa only [coefficientBudget, mul_comm (Real.log x) (-(5 / 4 : ℝ)), neg_mul] using h
  rw [deriv_kernel_eq_shift p N _ hx0]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact (add_le_add (hk N) (mul_le_mul_of_nonneg_left (hk (N + 1)) (norm_nonneg _))).trans_eq
    (by rw [pow_succ]; ring)

/-- The same tilt bounds every positive-axis boundary kernel, uniformly
over all possible finite sampling endpoints. -/
theorem norm_kernel_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ)) x‖ ≤
      (4 / 5 : ℝ) ^ N * coefficientBudget p := by
  have h := norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * (y : ℂ)) hx
    (by norm_num : (0 : ℝ) < 5 / 4)
  norm_num at h
  have he : Real.exp (-(1 / 4 * Real.log x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.log_nonneg hx])
  apply h.trans
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by positivity)) (coefficientBudget_nonneg p)).trans_eq
      (by simp [coefficientBudget])

/-- The full sawtooth integral has a fixed geometric allowance. Its
spatial majorant is integrated on the whole half-line, not on a truncated
window whose constant could grow with the endpoint. -/
theorem norm_saw_integral_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {a b : ℝ} (ha : 1 ≤ a) :
    ‖∫ x in Set.Ioc a b,
      deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * (y : ℂ))) x * (saw x : ℂ)‖ ≤
        4 * (5 / 4 + ‖3 / 2 + I * (y : ℂ)‖) *
          (4 / 5 : ℝ) ^ (N + 1) * coefficientBudget p := by
  let D := (5 / 4 + ‖3 / 2 + I * (y : ℂ)‖) *
    (4 / 5 : ℝ) ^ (N + 1) * coefficientBudget p
  have hD : 0 ≤ D := by
    have hP := coefficientBudget_nonneg p
    dsimp [D]
    positivity
  have hs : Set.Ioc a b ⊆ Set.Ioi (1 : ℝ) := fun x hx ↦ ha.trans_lt hx.1
  have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(5 / 4 : ℝ)) < -1)
    (by norm_num : (0 : ℝ) < 1)
  have hg := (hp.mono_set hs).const_mul D
  have hf := (integrableOn_deriv_mul_saw p (N + 1) (3 / 2 + I * (y : ℂ))
    (b := b) (zero_lt_one.trans_le ha)).mono_set Set.Ioc_subset_Icc_self
  have hi : (∫ x in Set.Ioc a b, x ^ (-(5 / 4 : ℝ))) ≤ 4 := by
    have h := setIntegral_mono_set hp (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Real.rpow_nonneg (lt_trans zero_lt_one hx).le _) (Filter.Eventually.of_forall hs)
    norm_num [integral_Ioi_rpow_of_lt (by norm_num : (-(5 / 4 : ℝ)) < -1)
      (by norm_num : (0 : ℝ) < 1)] at h
    exact h
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x in Set.Ioc a b, D * x ^ (-(5 / 4 : ℝ)) := by
      apply integral_mono_ae hf.norm hg
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (saw_bounds
        (zero_le_one.trans (ha.trans hx.1.le))).1.le]
      exact (mul_le_of_le_one_right (norm_nonneg _) (saw_bounds
        (zero_le_one.trans (ha.trans hx.1.le))).2).trans
          (norm_deriv_kernel_le p N y (ha.trans hx.1.le))
    _ = D * ∫ x in Set.Ioc a b, x ^ (-(5 / 4 : ℝ)) := integral_const_mul _ _
    _ ≤ D * 4 := mul_le_mul_of_nonneg_left hi hD
    _ = _ := by dsimp [D]; ring

/-- The complete sampling allowance, independent of both real endpoints. -/
def samplingConstant (p : Polynomial ℂ) (y : ℝ) : ℝ :=
  (2 + 4 * (5 / 4 + ‖3 / 2 + I * (y : ℂ)‖)) * coefficientBudget p

/-- The actual lattice/continuous difference decays geometrically for
every fixed full polynomial, with no pole-cancellation or zero hypothesis. -/
theorem norm_lattice_sub_integral_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖lattice p (N + 1) (3 / 2 + I * (y : ℂ)) a b -
      (∫ x in Set.Ioc a b, zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * (y : ℂ)) x)‖ ≤
        (4 / 5 : ℝ) ^ (N + 1) * samplingConstant p y := by
  have hb (x : ℝ) (hx : 1 ≤ x) :
      ‖zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * (y : ℂ)) x * (saw x : ℂ)‖ ≤
        (4 / 5 : ℝ) ^ (N + 1) * coefficientBudget p := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (saw_bounds (zero_le_one.trans hx)).1.le]
    exact (mul_le_of_le_one_right (norm_nonneg _) (saw_bounds (zero_le_one.trans hx)).2).trans
      (norm_kernel_le p (N + 1) y hx)
  rw [lattice_sub_integral p (N + 1) _ (zero_lt_one.trans_le ha) hab]
  apply (norm_sub_le _ _).trans
  exact (add_le_add ((norm_sub_le _ _).trans (add_le_add (hb b (ha.trans hab)) (hb a ha)))
    (norm_saw_integral_le p N y ha)).trans_eq (by dsimp [samplingConstant]; ring)

/-- The sampling error tends to zero for every moving interval on the
positive axis, with the same fixed polynomial and ordinate. -/
theorem tendsto_lattice_sub_integral (p : Polynomial ℂ) (y : ℝ) (a b : ℕ → ℝ)
    (ha : ∀ N, 1 ≤ a N) (hab : ∀ N, a N ≤ b N) :
    Tendsto (fun N ↦ lattice p N (3 / 2 + I * (y : ℂ)) (a N) (b N) -
      (∫ x in Set.Ioc (a N) (b N), zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ)) x))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ ↦ (4 / 5 : ℝ) ^ N * samplingConstant p y) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
        (by norm_num : (4 / 5 : ℝ) < 1)).mul_const (samplingConstant p y)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  simpa only [Nat.sub_add_cancel hN] using
    norm_lattice_sub_integral_le p (N - 1) y (ha N) (hab N)

/-- The original expanding band, now centered by the complete unit integer
lattice. Every composite keeps coefficient minus one, with no phase selection. -/
def centered (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ zetaPrimeLogBand N, ((PrimeDiscrepancyWork.jump n - 1 : ℝ) : ℂ) *
    zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ)) n

/-- The finite lattice carrier is exactly the original ordinary-prime
band minus its complete integer background, with unchanged endpoints. -/
theorem centered_eq_prime_sub_lattice (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    centered p N y = zetaOrdinaryPrimeBandFilter p N y -
      lattice p N (3 / 2 + I * (y : ℂ)) (zetaPrimeBandLower N) (zetaPrimeBandUpper N) := by
  rw [centered, zetaPrimeLogBand_eq_Ioc, zetaOrdinaryPrimeBandFilter_eq_finiteSum,
    zetaPrimeFilterFiniteSum, Finset.sum_filter, lattice, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime <;> simp [PrimeDiscrepancyWork.jump, hn, sub_mul]

/-- The literal lattice carrier pairs the full kernel with first error
increments. No additional preceding discrepancy is inserted, in contrast
to the separate quadratic work identity. -/
theorem centered_eq_error_increments (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    centered p N y = -(∑ n ∈ zetaPrimeLogBand N,
      zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ)) n *
        ((PrimeDiscrepancyWork.error n - PrimeDiscrepancyWork.error (n - 1) : ℝ) : ℂ)) := by
  rw [centered, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := by
    rw [zetaPrimeLogBand_eq_Ioc, Finset.mem_Ioc] at hn
    omega
  have h := PrimeDiscrepancyWork.error_succ (n - 1)
  rw [Nat.sub_add_cancel hn1] at h
  have he : PrimeDiscrepancyWork.jump n - 1 =
      -(PrimeDiscrepancyWork.error n - PrimeDiscrepancyWork.error (n - 1)) := by linarith
  rw [he]
  push_cast
  ring

/-- The new linear carrier differs from the original signed Chebyshev
integral only by the exact old boundary and the exact sampling discrepancy.
This identity imposes no root or normalization condition on the polynomial. -/
theorem centered_sub_carrier (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    centered p N y - zetaPrimeBandChebyshevIntegral p N y =
      zetaPrimeBandChebyshevBoundary p N y -
        (lattice p N (3 / 2 + I * (y : ℂ)) (zetaPrimeBandLower N) (zetaPrimeBandUpper N) -
          (∫ x in Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N),
            zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ)) x)) := by
  rw [centered_eq_prime_sub_lattice]
  linear_combination zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral p N y

private theorem lower_ge_one (N : ℕ) : 1 ≤ zetaPrimeBandLower N := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.log_pos (by norm_num)).le) (by norm_num)

/-- The full comparison has two explicit geometric error terms. Neither
the carrier nor the prime/composite sum is bounded by this estimate. -/
theorem norm_centered_sub_carrier_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    ‖centered p N y - zetaPrimeBandChebyshevIntegral p N y‖ ≤
      (1 / 2 : ℝ) ^ N * ((Real.log 4 + 1) * zetaPrimeBandEndpointConstant p) +
        (4 / 5 : ℝ) ^ N * samplingConstant p y := by
  rw [centered_sub_carrier]
  apply (norm_sub_le _ _).trans
  apply add_le_add (norm_zetaPrimeBandChebyshevBoundary_le p N y)
  simpa only [Nat.sub_add_cancel hN] using
    norm_lattice_sub_integral_le p (N - 1) y (lower_ge_one N) (zetaPrimeBandLower_le_upper N)

/-- The original linear carrier is transported with an independently
vanishing full error for every fixed polynomial and height. -/
theorem tendsto_centered_sub_carrier (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ centered p N y - zetaPrimeBandChebyshevIntegral p N y) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ ↦ zetaPrimeBandChebyshevBoundary p N y) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N ↦ norm_zetaPrimeBandChebyshevBoundary_le p N y)
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          ((Real.log 4 + 1) * zetaPrimeBandEndpointConstant p)
  have h := hb.sub (tendsto_lattice_sub_integral p y zetaPrimeBandLower zetaPrimeBandUpper
    lower_ge_one zetaPrimeBandLower_le_upper)
  simpa only [centered_sub_carrier, sub_self] using h

/-- The independently vanishing transport error remains negligible at
every fixed-zero normalization, including the endpoint value `u=1`. -/
theorem tendsto_scaled_comparison (p : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1) *
      (centered p N y - zetaPrimeBandChebyshevIntegral p N y)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ ↦ ‖centered p N y - zetaPrimeBandChebyshevIntegral p N y‖)
      atTop (𝓝 0) := by simpa using (tendsto_centered_sub_carrier p y).norm
  apply squeeze_zero_norm (fun N ↦ ?_) hlim
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hu hu1)

/-- Every hypothetical right-half zero retains its original negative
multiplicity in the complete linear prime-versus-integer lattice sum.
The transport error above is independent of this zero-source hypothesis. -/
theorem tendsto_actual_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      centered (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im) atTop
        (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have he := tendsto_scaled_comparison (zetaRightHalfZeroModeFilter rho hrho) rho.1.im
    (u := 3 / 2 - rho.1.re) (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)
  have h := (tendsto_zetaRightHalfPrimeBandChebyshevIntegral rho hrho).add he
  simp only [add_zero] at h
  convert h using 1
  funext N
  ring

/-- The complete real channel of the actual lattice sum has the same
source, retaining the original polynomial, ordinate and multiplicity. -/
theorem tendsto_actual_source_re (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      (centered (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im).re) atTop
        (𝓝 (-(analyticZetaZeroMultiplicity rho : ℝ))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_actual_source rho hrho)
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re]
    using h

end
end RiemannGaussian.PrimeLatticeCarrier
