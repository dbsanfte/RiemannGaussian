/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovGaussianResonance
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

/-!
# Explicit bounds for every translated Gaussian tail

The complete periodized kernel is bounded by two nearest-side Gaussian
terms and an explicit geometric denominator. The bound holds uniformly
at every real phase, including phases which vary with the original zeta
parameters. Its product bound retains the joint attainable difference
support. Estimating that arithmetic resonance support remains separate.
-/

namespace RiemannGaussian.VinogradovGaussianBounds
noncomputable section
open VinogradovGaussianKernel VinogradovGaussianResonance VinogradovShiftedMoment
open scoped BigOperators

/-- The full kernel is the existing periodic Hurwitz Gaussian kernel at
the reciprocal scale. This is an exact identity, before any tail bound. -/
theorem kernel_eq_F_int (a x : ℝ) :
    kernel a x = (1 / a ^ (1 / 2 : ℝ)) *
      HurwitzKernelBounds.F_int 0 ((-x : ℝ) : UnitAddCircle) (1 / a) := by
  unfold kernel HurwitzKernelBounds.F_int
  rw [Function.Periodic.lift_coe]
  congr 1
  apply tsum_congr
  intro n
  simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
  congr 1
  ring

/-- An explicit bound retaining the Gaussian on each side of the
fractional phase. The denominator pays every further integer translate. -/
def tailEnvelope (a x : ℝ) : ℝ :=
  (1 / a ^ (1 / 2 : ℝ)) *
    ((Real.exp (-Real.pi * (Int.fract (-x)) ^ 2 / a) +
      Real.exp (-Real.pi * (1 - Int.fract (-x)) ^ 2 / a)) /
      (1 - Real.exp (-Real.pi / a)))

/-- Every positive Gaussian scale has a strictly positive geometric
tail denominator. -/
theorem tail_denominator_pos {a : ℝ} (ha : 0 < a) :
    0 < 1 - Real.exp (-Real.pi / a) := by
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha

/-- The explicit envelope is positive even at exact integer resonance. -/
theorem tailEnvelope_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < tailEnvelope a x := by
  unfold tailEnvelope
  exact mul_pos (by positivity)
    (div_pos (add_pos (Real.exp_pos _) (Real.exp_pos _)) (tail_denominator_pos ha))

/-- All integer translates are bounded uniformly by a closed expression
in the fractional phase. No fixed-phase asymptotic or omitted tail is used. -/
theorem kernel_le_tailEnvelope {a : ℝ} (ha : 0 < a) (x : ℝ) :
    kernel a x ≤ tailEnvelope a x := by
  have ht : 0 < 1 / a := one_div_pos.mpr ha
  have hr : Int.fract (-x) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [kernel_eq_F_int, ← AddCircle.coe_fract (-x),
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 hr ht]
  unfold tailEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h₀ := HurwitzKernelBounds.F_nat_zero_le hr.1 ht
  have h₁ := HurwitzKernelBounds.F_nat_zero_le (sub_nonneg.mpr hr.2) ht
  have h := add_le_add ((le_abs_self _).trans h₀) ((le_abs_self _).trans h₁)
  simpa only [Real.norm_eq_abs, mul_one_div, ← add_div] using h

/-- The distance of the fractional phase to the nearer integer endpoint. -/
def integerDistance (x : ℝ) : ℝ :=
  min (Int.fract (-x)) (1 - Int.fract (-x))

/-- The nearest-integer phase distance is nonnegative at every real phase. -/
theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := by
  exact le_min (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)

/-- Nearest-integer distance never exceeds half the period. -/
theorem integerDistance_le_half (x : ℝ) : integerDistance x ≤ 1 / 2 := by
  have h₀ := min_le_left (Int.fract (-x)) (1 - Int.fract (-x))
  have h₁ := min_le_right (Int.fract (-x)) (1 - Int.fract (-x))
  unfold integerDistance
  linarith

/-- The two-tail envelope has an explicit Gaussian decay factor in the
distance to integer resonance, uniformly in both the phase and the scale. -/
theorem tailEnvelope_le_distance {a : ℝ} (ha : 0 < a) (x : ℝ) :
    tailEnvelope a x ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        Real.exp (-Real.pi * (integerDistance x) ^ 2 / a) := by
  have hG {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
      Real.exp (-Real.pi * v ^ 2 / a) ≤ Real.exp (-Real.pi * u ^ 2 / a) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ ha.le
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv 2) Real.pi_pos.le
    nlinarith
  have h₀ := hG (integerDistance_nonneg x)
    (min_le_left (Int.fract (-x)) (1 - Int.fract (-x)))
  have h₁ := hG (integerDistance_nonneg x)
    (min_le_right (Int.fract (-x)) (1 - Int.fract (-x)))
  unfold tailEnvelope
  calc
    _ ≤ (1 / a ^ (1 / 2 : ℝ)) *
        ((Real.exp (-Real.pi * (integerDistance x) ^ 2 / a) +
          Real.exp (-Real.pi * (integerDistance x) ^ 2 / a)) /
          (1 - Real.exp (-Real.pi / a))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (add_le_add h₀ h₁) (tail_denominator_pos ha).le)
        (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Quantitative Gaussian suppression away from integer resonance, with
every translated tail included in the explicit prefactor. -/
theorem kernel_le_distance {a : ℝ} (ha : 0 < a) (x : ℝ) :
    kernel a x ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        Real.exp (-Real.pi * (integerDistance x) ^ 2 / a) :=
  (kernel_le_tailEnvelope ha x).trans (tailEnvelope_le_distance ha x)

/-- The finite product of explicit one-coordinate envelopes. Its phase
arguments remain coupled through the original difference vector. -/
def latticeEnvelope {k : ℕ} (a x : Fin k → ℝ) : ℝ :=
  ∏ j, tailEnvelope (a j) (x j)

/-- The full lattice Gaussian is bounded without dropping any translate
or projecting any coordinate of the phase. -/
theorem latticeKernel_le_envelope {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ j, 0 < a j) (x : Fin k → ℝ) :
    latticeKernel a x ≤ latticeEnvelope a x := by
  exact Finset.prod_le_prod (fun j _ => kernel_nonneg (ha j) (x j))
    (fun j _ => kernel_le_tailEnvelope (ha j) (x j))

/-- A finite explicit exponential envelope on the complete attainable
power-sum difference support, with no rectangular enlargement. -/
def resonanceEnvelope {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (a γ : Fin k → ℝ) (v : ι → Fin k → ℤ) : ℝ :=
  ∑ h ∈ differenceSupport (tupleFrequency s v), latticeEnvelope a (linearSample γ h)

/-- The complete finite resonance envelope is nonnegative at positive
scales, so it can transport explicit support-cost improvements. -/
theorem resonanceEnvelope_nonneg {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (γ : Fin k → ℝ) (v : ι → Fin k → ℤ) :
    0 ≤ resonanceEnvelope s a γ v := by
  exact Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg
    (fun j _ => (tailEnvelope_pos (ha j) _).le))

/-- Every translated tail in the joint resonance sum is paid by a finite
explicit expression. Quantitative arithmetic spacing is still needed. -/
theorem resonanceSum_le_envelope {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (γ : Fin k → ℝ) (v : ι → Fin k → ℤ) :
    resonanceSum s a γ v ≤ resonanceEnvelope s a γ v := by
  exact Finset.sum_le_sum (fun h _ => latticeKernel_le_envelope ha (linearSample γ h))

end
end RiemannGaussian.VinogradovGaussianBounds
