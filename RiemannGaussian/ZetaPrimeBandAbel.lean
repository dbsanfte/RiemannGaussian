/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFilterCalculus
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Signed Abel transport of the actual ordinary-prime band

The complete complex factorial filter can be paired exactly with the
ordinary-prime Chebyshev error. Both finite endpoints and both phase
channels are retained. The final identities apply to the same expanding
band that carries the selected zero's negative multiplicity signal.
No bound on this signed Chebyshev-error pairing is assumed or proved here.
-/

open Complex Filter MeasureTheory Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

private def ordinaryPrimeCoefficient (m : ℕ) : ℂ :=
  if m.Prime then (Real.log m : ℂ) else 0

private theorem ordinaryPrimeCoefficient_sum (x : ℝ) :
    (∑ m ∈ Finset.Icc 0 ⌊x⌋₊, ordinaryPrimeCoefficient m) = (Chebyshev.theta x : ℂ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.Prime <;> simp [ordinaryPrimeCoefficient, hm]

/-- The complete complex filtered sum over ordinary primes in `(a,b]`.
Natural floors specify the endpoints exactly, including a prime endpoint. -/
def zetaPrimeFilterFiniteSum (p : Polynomial ℂ) (N : ℕ) (s : ℂ) (a b : ℝ) : ℂ :=
  ∑ m ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
    (Real.log m : ℂ) * zetaPrimeFilterKernel p N s m

/-- Exact Abel summation for the full complex ordinary-prime filter. -/
theorem zetaPrimeFilterFiniteSum_eq_abel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    zetaPrimeFilterFiniteSum p N s a b =
      zetaPrimeFilterKernel p N s b * (Chebyshev.theta b : ℂ) -
        zetaPrimeFilterKernel p N s a * (Chebyshev.theta a : ℂ) -
          ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (Chebyshev.theta x : ℂ) := by
  have h := sum_mul_eq_sub_sub_integral_mul ordinaryPrimeCoefficient ha.le hab
    (fun x hx ↦ (contDiffAt_zetaPrimeFilterKernel p N s (ha.trans_le hx.1)).differentiableAt
      (by norm_num)) (integrableOn_deriv_zetaPrimeFilterKernel p N s ha)
  simp_rw [ordinaryPrimeCoefficient_sum] at h
  rw [zetaPrimeFilterFiniteSum, Finset.sum_filter]
  convert h using 1
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.Prime <;> simp [ordinaryPrimeCoefficient, hm, mul_comm]

/-- Ordinary integration by parts for exactly the same complex kernel.
The continuous density and both boundary values remain explicit. -/
theorem zetaPrimeFilterKernel_integral_Ioc (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Set.Ioc a b, zetaPrimeFilterKernel p N s x) =
      zetaPrimeFilterKernel p N s b * (b : ℂ) - zetaPrimeFilterKernel p N s a * (a : ℂ) -
        ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (x : ℂ) := by
  have hd : IntervalIntegrable (deriv (zetaPrimeFilterKernel p N s)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_deriv_zetaPrimeFilterKernel p N s ha
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := zetaPrimeFilterKernel p N s)
    (u' := deriv (zetaPrimeFilterKernel p N s))
    (v := fun x : ℝ ↦ (x : ℂ)) (v' := fun _ : ℝ ↦ (1 : ℂ))
    (fun x hx ↦ by
      rw [Set.uIcc_of_le hab] at hx
      exact ((contDiffAt_zetaPrimeFilterKernel p N s (ha.trans_le hx.1)).differentiableAt
        (by norm_num)).hasDerivAt)
    (fun x _ ↦ by simpa only [Complex.ofReal_one, id_eq] using (hasDerivAt_id x).ofReal_comp)
    hd intervalIntegrable_const
  simpa only [mul_one, intervalIntegral.integral_of_le hab] using h

/-- The actual atomic-minus-continuous discrepancy is the signed
Chebyshev-error pairing, with no loss of its complex phase or endpoints. -/
theorem zetaPrimeFilterFiniteSum_sub_integral (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    zetaPrimeFilterFiniteSum p N s a b - (∫ x in Set.Ioc a b, zetaPrimeFilterKernel p N s x) =
      zetaPrimeFilterKernel p N s b * ((Chebyshev.theta b - b : ℝ) : ℂ) -
        zetaPrimeFilterKernel p N s a * ((Chebyshev.theta a - a : ℝ) : ℂ) +
          ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * ((x - Chebyshev.theta x : ℝ) : ℂ) := by
  have hd := integrableOn_deriv_zetaPrimeFilterKernel p N s (b := b) ha
  have htheta := integrableOn_mul_sum_Icc ordinaryPrimeCoefficient (m := 0) ha.le hd
  simp_rw [ordinaryPrimeCoefficient_sum] at htheta
  have htheta' := htheta.mono_set Set.Ioc_subset_Icc_self
  have hxIcc : IntegrableOn (fun x : ℝ ↦ (x : ℂ) * deriv (zetaPrimeFilterKernel p N s) x)
      (Set.Icc a b) :=
    IntegrableOn.continuousOn_mul Complex.continuous_ofReal.continuousOn hd isCompact_Icc
  have hx : IntegrableOn (fun x : ℝ ↦ deriv (zetaPrimeFilterKernel p N s) x * (x : ℂ))
      (Set.Ioc a b) := by
    simpa only [mul_comm] using hxIcc.mono_set Set.Ioc_subset_Icc_self
  have hi :
      (∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (x : ℂ)) -
        (∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * (Chebyshev.theta x : ℂ)) =
          ∫ x in Set.Ioc a b, deriv (zetaPrimeFilterKernel p N s) x * ((x - Chebyshev.theta x : ℝ) : ℂ) := by
    rw [← integral_sub hx htheta']
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    dsimp only
    rw [Complex.ofReal_sub, mul_sub]
  rw [zetaPrimeFilterFiniteSum_eq_abel p N s ha hab, zetaPrimeFilterKernel_integral_Ioc p N s ha hab,
    ← hi, Complex.ofReal_sub, Complex.ofReal_sub]
  ring

/-- The error pairing uses the full lowering operator. In particular its
phase-rotation term is not replaced by an absolute-value bound. -/
theorem zetaPrimeFilterFiniteSum_sub_integral_lowering (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    zetaPrimeFilterFiniteSum p (N + 1) s a b -
        (∫ x in Set.Ioc a b, zetaPrimeFilterKernel p (N + 1) s x) =
      zetaPrimeFilterKernel p (N + 1) s b * ((Chebyshev.theta b - b : ℝ) : ℂ) -
        zetaPrimeFilterKernel p (N + 1) s a * ((Chebyshev.theta a - a : ℝ) : ℂ) +
          ∫ x in Set.Ioc a b,
            (zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ) *
              ((x - Chebyshev.theta x : ℝ) : ℂ) := by
  rw [zetaPrimeFilterFiniteSum_sub_integral p (N + 1) s ha hab]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [deriv_zetaPrimeFilterKernel p N s (ha.trans hx.1)]

/-- The complete complex Chebyshev-error integrand is genuinely
integrable on positive compact intervals, for every moment order. -/
theorem integrableOn_zetaPrimeFilter_chebyshevError (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x ↦ deriv (zetaPrimeFilterKernel p N s) x * ((x - Chebyshev.theta x : ℝ) : ℂ))
      (Set.Icc a b) := by
  have hd := integrableOn_deriv_zetaPrimeFilterKernel p N s (b := b) ha
  have ht := integrableOn_mul_sum_Icc ordinaryPrimeCoefficient (m := 0) ha.le hd
  simp_rw [ordinaryPrimeCoefficient_sum] at ht
  have hx : IntegrableOn (fun x : ℝ ↦ (x : ℂ) * deriv (zetaPrimeFilterKernel p N s) x)
      (Set.Icc a b) :=
    IntegrableOn.continuousOn_mul Complex.continuous_ofReal.continuousOn hd isCompact_Icc
  have he : (fun x : ℝ ↦ (x : ℂ) * deriv (zetaPrimeFilterKernel p N s) x -
      deriv (zetaPrimeFilterKernel p N s) x * (Chebyshev.theta x : ℂ)) =
      (fun x ↦ deriv (zetaPrimeFilterKernel p N s) x * ((x - Chebyshev.theta x : ℝ) : ℂ)) := by
    funext x
    push_cast
    ring
  rw [← he]
  exact hx.sub ht

/-- The exact unrounded lower endpoint of the retained logarithmic band. -/
def zetaPrimeBandLower (N : ℕ) : ℝ := Real.exp ((N : ℝ) * Real.log 2 / 4)

/-- The exact integral upper endpoint of the retained logarithmic band. -/
def zetaPrimeBandUpper (N : ℕ) : ℝ := ((2 ^ (32 * N) : ℕ) : ℝ)

/-- The lower endpoint is positive at every moment order, including zero. -/
theorem zetaPrimeBandLower_pos (N : ℕ) : 0 < zetaPrimeBandLower N := Real.exp_pos _

/-- The two retained-band endpoints are ordered for all moment orders. -/
theorem zetaPrimeBandLower_le_upper (N : ℕ) : zetaPrimeBandLower N ≤ zetaPrimeBandUpper N := by
  have hl : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have he : zetaPrimeBandUpper N = Real.exp ((32 * (N : ℝ)) * Real.log 2) := by
    simp only [zetaPrimeBandUpper, Nat.cast_pow, Nat.cast_ofNat]
    rw [show 32 * (N : ℝ) = ((32 * N : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [he, zetaPrimeBandLower, Real.exp_le_exp]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hl]

/-- The logarithmic selection and the exact floored interval select the
same integers. No lower boundary fibre is silently included or omitted. -/
theorem zetaPrimeLogBand_eq_Ioc (N : ℕ) :
    zetaPrimeLogBand N = Finset.Ioc ⌊zetaPrimeBandLower N⌋₊ ⌊zetaPrimeBandUpper N⌋₊ := by
  ext m
  simp only [zetaPrimeLogBand, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
    zetaPrimeBandUpper, Nat.floor_natCast]
  rw [Nat.floor_lt (zetaPrimeBandLower_pos N).le]
  constructor
  · rintro ⟨⟨hm, hu⟩, hl⟩
    refine ⟨?_, hu⟩
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simpa only [zetaPrimeBandLower, Real.exp_log hmpos] using Real.exp_lt_exp.mpr hl
  · rintro ⟨hl, hu⟩
    have hmpos : (0 : ℝ) < m := (zetaPrimeBandLower_pos N).trans hl
    have hmnat : 0 < m := by exact_mod_cast hmpos
    refine ⟨⟨by omega, hu⟩, ?_⟩
    simpa only [zetaPrimeBandLower, Real.log_exp] using Real.log_lt_log (zetaPrimeBandLower_pos N) hl

/-- The previously isolated arithmetic carrier is precisely the finite
prime filter on these two real endpoints. -/
theorem zetaOrdinaryPrimeBandFilter_eq_finiteSum (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaOrdinaryPrimeBandFilter p N y =
      zetaPrimeFilterFiniteSum p N (3 / 2 + I * y) (zetaPrimeBandLower N) (zetaPrimeBandUpper N) := by
  rw [zetaOrdinaryPrimeBandFilter_eq_prime_sum, zetaPrimeFilterFiniteSum, ← zetaPrimeLogBand_eq_Ioc]
  apply Finset.sum_congr rfl
  intro m _
  rw [zetaPrimeFilterKernel_nat]
  ring

/-- Exact signed Chebyshev-error transport for the actual retained band
that recovers every selected right-half zero's multiplicity. This identity
supplies no independent bound on the displayed error integral. -/
theorem zetaOrdinaryPrimeBandFilter_sub_integral (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaOrdinaryPrimeBandFilter p N y -
        (∫ x in Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N),
          zetaPrimeFilterKernel p N (3 / 2 + I * y) x) =
      zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandUpper N) *
          ((Chebyshev.theta (zetaPrimeBandUpper N) - zetaPrimeBandUpper N : ℝ) : ℂ) -
        zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandLower N) *
          ((Chebyshev.theta (zetaPrimeBandLower N) - zetaPrimeBandLower N : ℝ) : ℂ) +
          ∫ x in Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N),
            deriv (zetaPrimeFilterKernel p N (3 / 2 + I * y)) x * ((x - Chebyshev.theta x : ℝ) : ℂ) := by
  rw [zetaOrdinaryPrimeBandFilter_eq_finiteSum]
  exact zetaPrimeFilterFiniteSum_sub_integral p N _ (zetaPrimeBandLower_pos N)
    (zetaPrimeBandLower_le_upper N)

end

end RiemannGaussian
