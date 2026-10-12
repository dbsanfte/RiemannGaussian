/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorMovingFloorCode
import RiemannGaussian.ArithmeticOperatorLcmCutoffAudit
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Distinct-column successor Gamma gate, with the unpaid commutator retained

Ordinary addition couples `n` and `n+1`, each with its full divisor sum.
The Gamma-compatible cofactor twist has an actual polylogarithmic
centered bound. It is therefore source-blind at every positive power
scale. The prime-leg-only correlation differs by an exact SIGNED
commutator. No estimate for this commutator is asserted or imported.
-/

namespace RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open ArithmeticOperatorFloorInverseAudit
open scoped BigOperators Topology ComplexConjugate

/-- Literal prime-leg-only successor cross-correlation, all powers kept. -/
def primeCross (X : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    primeLegDivisor (primePhase y) n*conj (primeLegDivisor (primePhase y) (n+1))

/-- Gamma-compatible correlation has both cofactor phases, not merely
the original prime phases. It is a genuinely different arithmetic term. -/
def gammaCross (X : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    coupledDivisor (primePhase y) n*conj (coupledDivisor (primePhase y) (n+1))

/-- Untwisted complete ordinary-integer density/reference contribution. -/
def integerReference (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, Real.log n*Real.log ((n+1 : ℕ) : ℝ)

/-- Exact joined two-column discrepancy; full phases and both orders
remain inside, and no component is norm-paid. -/
def signedDiscrepancy (X : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    (twistCommutator (primePhase y) n*conj (primeLegDivisor (primePhase y) (n+1))+
      coupledDivisor (primePhase y) n*conj (twistCommutator (primePhase y) (n+1)))

theorem primeCross_sub_gammaCross (X : ℕ) (y : ℝ) :
    primeCross X y-gammaCross X y = signedDiscrepancy X y := by
  unfold primeCross gammaCross signedDiscrepancy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← primeLegDivisor_sub_coupled, ← primeLegDivisor_sub_coupled, map_sub]
  ring

/-- Actual Gamma evaluation keeps the exact relative successor phase. -/
theorem gammaCross_eq (X : ℕ) (y : ℝ) :
    gammaCross X y = ∑ n ∈ Finset.Icc 1 X,
      (primePhase y n*conj (primePhase y (n+1)))*
        (Real.log n : ℂ)*(Real.log ((n+1 : ℕ) : ℝ) : ℂ) := by
  unfold gammaCross
  apply Finset.sum_congr rfl
  intro n hn
  rw [coupledDivisor_primePhase y (Finset.mem_Icc.mp hn).1,
    coupledDivisor_primePhase y (by omega : 0 < n+1), map_mul, Complex.conj_ofReal]
  ring

/-- Exact phase in physical integer coordinates, before estimating. -/
theorem successorPhase_eq (n : ℕ) (y : ℝ) :
    primePhase y n*conj (primePhase y (n+1)) =
      Complex.exp (I*(y*(Real.log ((n+1 : ℕ) : ℝ)-Real.log n) : ℝ)) := by
  unfold primePhase
  rw [← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem log_successor_gap {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log ((n+1 : ℕ) : ℝ)-Real.log n ∧
      Real.log ((n+1 : ℕ) : ℝ)-Real.log n ≤ (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · apply sub_nonneg.mpr
    exact Real.log_le_log hnR (by norm_cast; omega)
  · have hh := Real.log_le_sub_one_of_pos (x := ((n+1 : ℕ) : ℝ)/(n : ℝ))
      (div_pos (by positivity) hnR)
    rw [Real.log_div (by positivity) hnR.ne'] at hh
    have he : ((n+1 : ℕ) : ℝ)/(n : ℝ)-1 = (n : ℝ)⁻¹ := by
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    exact hh.trans_eq he

private theorem norm_successorPhase_sub_one {n : ℕ} (hn : 0 < n) (y : ℝ) :
    ‖primePhase y n*conj (primePhase y (n+1))-1‖ ≤ |y| *(n : ℝ)⁻¹ := by
  rw [successorPhase_eq]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := y*(Real.log ((n+1 : ℕ) : ℝ)-Real.log n))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (log_successor_gap hn).1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (log_successor_gap hn).2 (abs_nonneg y))

/-- Complete correlated Gamma/reference cancellation has only a
polylogarithmic cost. This is an actual integer-prime identity followed
by an estimate of its Gamma-compatible term, not of `primeCross`. -/
theorem norm_gammaCross_sub_reference_le {X : ℕ} (hX : 0 < X) (y : ℝ) :
    ‖gammaCross X y-(integerReference X : ℂ)‖ ≤
      |y| *(Real.log ((X+1 : ℕ) : ℝ))^2*(1+Real.log X) := by
  classical
  rw [gammaCross_eq, integerReference, Complex.ofReal_sum]
  simp only [Complex.ofReal_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
      ‖(primePhase y n*conj (primePhase y (n+1)))*
        (Real.log n : ℂ)*(Real.log ((n+1 : ℕ) : ℝ) : ℂ)-
          (Real.log n : ℂ)*(Real.log ((n+1 : ℕ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (|y| *(Real.log ((X+1 : ℕ) : ℝ))^2)*(n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnX⟩ := Finset.mem_Icc.mp hn
      have ha : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn0)
      have hb : 0 ≤ Real.log ((n+1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
      have hc : 0 ≤ Real.log ((X+1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
      have hna : Real.log (n : ℝ) ≤ Real.log ((X+1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hn0) (by norm_cast; omega)
      have hnb : Real.log ((n+1 : ℕ) : ℝ) ≤ Real.log ((X+1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by norm_cast; omega)
      rw [show (primePhase y n*conj (primePhase y (n+1)))*
          (Real.log n : ℂ)*(Real.log ((n+1 : ℕ) : ℝ) : ℂ)-
          (Real.log n : ℂ)*(Real.log ((n+1 : ℕ) : ℝ) : ℂ) =
        (primePhase y n*conj (primePhase y (n+1))-1)*
          (Real.log n : ℂ)*(Real.log ((n+1 : ℕ) : ℝ) : ℂ) by ring,
        norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      calc
        _ ≤ (|y| *(n : ℝ)⁻¹)*Real.log n*Real.log ((n+1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (norm_successorPhase_sub_one hn0 y) ha) hb
        _ ≤ (|y| *(n : ℝ)⁻¹)*Real.log ((X+1 : ℕ) : ℝ)*Real.log ((X+1 : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hna (by positivity)) hnb hb (by positivity)
        _ = _ := by ring
    _ = |y| *(Real.log ((X+1 : ℕ) : ℝ))^2*(harmonic X : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by positivity)

/-- Explicit dyadic polynomial bound, independent of any zero hypothesis. -/
theorem norm_dyadic_gammaCross_sub_reference_le (J : ℕ) (y : ℝ) :
    ‖gammaCross (2^J) y-(integerReference (2^J) : ℂ)‖ ≤
      |y| *(1+Real.log 2)^3*((J+1 : ℕ) : ℝ)^3 := by
  have hx : 0 < 2^J := by positivity
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ha : Real.log ((2^J+1 : ℕ) : ℝ) ≤ ((J+1 : ℕ) : ℝ)*Real.log 2 := by
    calc
      _ ≤ Real.log ((2^(J+1) : ℕ) : ℝ) := Real.log_le_log (by positivity) (by
        norm_cast
        rw [pow_succ]
        have : 1 ≤ 2^J := Nat.one_le_pow J 2 (by norm_num)
        omega)
      _ = _ := by rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hb : Real.log ((2^J : ℕ) : ℝ) = (J : ℝ)*Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hc : 0 ≤ Real.log ((2^J+1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have he : 0 ≤ ((J+1 : ℕ) : ℝ) := by positivity
  have hf : 0 ≤ 1+Real.log ((2^J : ℕ) : ℝ) := by rw [hb]; positivity
  calc
    _ ≤ |y| *(Real.log ((2^J+1 : ℕ) : ℝ))^2*(1+Real.log ((2^J : ℕ) : ℝ)) :=
      norm_gammaCross_sub_reference_le hx y
    _ ≤ |y| *(((J+1 : ℕ) : ℝ)*Real.log 2)^2*
        (((J+1 : ℕ) : ℝ)*(1+Real.log 2)) := by
      apply mul_le_mul
      · gcongr
      · rw [hb]
        push_cast
        nlinarith
      · exact hf
      · positivity
    _ ≤ _ := by
      have hd : (Real.log (2 : ℝ))^2 ≤ (1+Real.log 2)^2 := by nlinarith
      calc
        _ = |y| *((J+1 : ℕ) : ℝ)^3*(1+Real.log 2)*(Real.log 2)^2 := by ring
        _ ≤ |y| *((J+1 : ℕ) : ℝ)^3*(1+Real.log 2)*(1+Real.log 2)^2 :=
          mul_le_mul_of_nonneg_left hd (by positivity)
        _ = _ := by ring

/-- This centered nonlinear Gamma-compatible successor response loses
EVERY positive-power source. The prime-only discrepancy remains unpaid. -/
theorem tendsto_scaled_gammaCross_sub_reference {beta : ℝ} (hb : 0 < beta) (y : ℝ) :
    Tendsto (fun J : ℕ => ((Real.exp (-beta*Real.log 2))^J : ℂ)*
      (gammaCross (2^J) y-(integerReference (2^J) : ℂ))) atTop (𝓝 0) := by
  have hr : Real.exp (-beta*Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by
    have hh : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith)
  have ht := (tendsto_shifted_polynomial_geometric 3 (Real.exp_pos _) hr).const_mul
    (|y| *(1+Real.log 2)^3)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-beta*Real.log 2))^J*
      (|y| *(1+Real.log 2)^3*((J+1 : ℕ) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left (norm_dyadic_gammaCross_sub_reference_le J y) (by positivity)
    _ = _ := by ring

end
end RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit
