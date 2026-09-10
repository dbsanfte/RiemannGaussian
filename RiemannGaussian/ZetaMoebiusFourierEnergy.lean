/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFourierBoundary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual continuous energy behind the finite Fourier estimate

The sample differences are integrals of the full complex lowering
operator. Its two terms remain coupled inside the square. The first
sample vanishes at positive moment order, and the last cyclic jump is
retained explicitly. No decay of the resulting arithmetic budget is assumed.
-/

open Complex Filter MeasureTheory Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- At positive moment order the factorial kernel vanishes at one. -/
theorem zetaPrimeFilterKernel_one_succ (p : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    zetaPrimeFilterKernel p (N + 1) s 1 = 0 := by
  simp [zetaPrimeFilterKernel, zetaFactorialPolynomial, Polynomial.sum]

private theorem continuousOn_lowering (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ ↦
      (zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ))
      (Set.Icc a b) := by
  have hc (n : ℕ) : ContinuousOn (zetaPrimeFilterKernel p n s) (Set.Icc a b) :=
    fun x hx ↦ (contDiffAt_zetaPrimeFilterKernel p n s (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  exact ((hc N).sub (continuousOn_const.mul (hc (N + 1)))).div
    Complex.continuous_ofReal.continuousOn
      (fun x hx ↦ Complex.ofReal_ne_zero.mpr (ha.trans_le hx.1).ne')

/-- Every positive finite interval gives an exact signed difference,
with the damping and phase rotation still coupled inside the integral. -/
theorem zetaPrimeFilterKernel_sub_eq_integral_lowering (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    zetaPrimeFilterKernel p (N + 1) s b - zetaPrimeFilterKernel p (N + 1) s a =
      ∫ x in a..b,
        (zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ) := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_zetaPrimeFilterKernel p N s (ha.trans_le hx.1)
  · exact (continuousOn_lowering p N s ha).intervalIntegrable_of_Icc hab

private theorem norm_unit_integral_sq_le {g : ℝ → ℂ} {a : ℝ}
    (hg : ContinuousOn g (Set.Icc a (a + 1))) :
    ‖∫ x in a..a + 1, g x‖ ^ 2 ≤ ∫ x in a..a + 1, ‖g x‖ ^ 2 := by
  let m : ℝ := ∫ x in a..a + 1, ‖g x‖
  have hab : a ≤ a + 1 := by linarith
  have hi := hg.norm.intervalIntegrable_of_Icc (μ := volume) hab
  have hi2 := (hg.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  change IntervalIntegrable (fun x ↦ ‖g x‖ ^ 2) volume a (a + 1) at hi2
  have hv := intervalIntegral.integral_nonneg_of_forall (μ := volume) (a := a) (b := a + 1) hab
    (fun x ↦ sq_nonneg (‖g x‖ - m))
  have he (x : ℝ) : (‖g x‖ - m) ^ 2 = ‖g x‖ ^ 2 - 2 * m * ‖g x‖ + m ^ 2 := by ring
  simp_rw [he] at hv
  rw [intervalIntegral.integral_add (hi2.sub (hi.const_mul (2 * m)))
      (intervalIntegrable_const (c := m ^ 2)),
    intervalIntegral.integral_sub hi2 (hi.const_mul (2 * m)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hv
  simp only [add_sub_cancel_left, smul_eq_mul, one_mul] at hv
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) hab
  have hm : 0 ≤ m := intervalIntegral.integral_nonneg_of_forall hab (fun x ↦ norm_nonneg (g x))
  have hs : ‖∫ x in a..a + 1, g x‖ ^ 2 ≤ m ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  dsimp only [m] at hv hm hs ⊢
  nlinarith

/-- One adjacent kernel difference is controlled by its actual lowering
energy. The norm is taken only after the complex subtraction. -/
theorem norm_zetaPrimeFilterKernel_sub_sq_le_lowering_integral (p : Polynomial ℂ)
    (N : ℕ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    ‖zetaPrimeFilterKernel p (N + 1) s (a + 1) - zetaPrimeFilterKernel p (N + 1) s a‖ ^ 2 ≤
      ∫ x in a..a + 1,
        ‖(zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ)‖ ^ 2 := by
  rw [zetaPrimeFilterKernel_sub_eq_integral_lowering p N s ha (by linarith)]
  exact norm_unit_integral_sq_le (continuousOn_lowering p N s ha)

/-- A positive natural sample agrees with the original complex kernel
through the last index of the embedding. -/
theorem zetaMoebiusKernelSamples_nat (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {n : ℕ} (hn : 0 < n) (hN : n < 2 ^ (32 * N) + 1) :
    zetaMoebiusKernelSamples p N y n = zetaPrimeFilterKernel p N (3 / 2 + I * y) n := by
  simp [zetaMoebiusKernelSamples, ZMod.val_natCast_of_lt hN, hn.ne']

private theorem continuousOn_lowering_pred (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    (hN : 1 ≤ N) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ ↦
      (zetaPrimeFilterKernel p (N - 1) s x - s * zetaPrimeFilterKernel p N s x) / (x : ℂ))
      (Set.Icc a b) := by
  simpa only [Nat.sub_add_cancel hN] using continuousOn_lowering p (N - 1) s (b := b) ha

/-- The entire cyclic sample energy is a sum of signed lowering
integrals and the exact last endpoint jump. The first endpoint vanishes
because the moment order is positive. -/
theorem sum_cyclicDifference_zetaMoebiusKernelSamples_sq (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    (∑ j, ‖cyclicDifference (zetaMoebiusKernelSamples p N y) j‖ ^ 2) =
      (∑ n ∈ Finset.Ico 1 (2 ^ (32 * N) : ℕ),
        ‖∫ x in (n : ℝ)..(n : ℝ) + 1,
          (zetaPrimeFilterKernel p (N - 1) (3 / 2 + I * y) x -
            (3 / 2 + I * y) * zetaPrimeFilterKernel p N (3 / 2 + I * y) x) /
              (x : ℂ)‖ ^ 2) +
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ^ 2 := by
  let M : ℕ := 2 ^ (32 * N)
  let f := zetaMoebiusKernelSamples p N y
  have hM : 0 < M := by dsimp [M]; positivity
  have hz : f 0 = 0 := by simp [f, zetaMoebiusKernelSamples]
  have hK : zetaPrimeFilterKernel p N (3 / 2 + I * y) 1 = 0 := by
    simpa only [Nat.sub_add_cancel hN] using zetaPrimeFilterKernel_one_succ p (N - 1) (3 / 2 + I * y)
  have h1 : f 1 = 0 := by
    have h := zetaMoebiusKernelSamples_nat p N y (n := 1) (by omega) (by change 1 < M + 1; omega)
    simpa only [Nat.cast_one, hK] using h
  have hm : f M = zetaPrimeFilterKernel p N (3 / 2 + I * y) M :=
    zetaMoebiusKernelSamples_nat p N y hM (by change M < M + 1; omega)
  change (∑ j, ‖cyclicDifference f j‖ ^ 2) = _
  rw [sum_cyclicDifference_sq_eq_boundary, Finset.sum_range_eq_add_Ico _ hM]
  simp only [Nat.cast_zero, zero_add, Nat.cast_one, hz, h1, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_sub, norm_neg]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hn0 : 0 < n := by omega
    dsimp only [f]
    rw [zetaMoebiusKernelSamples_nat p N y (by omega : 0 < n + 1)
        (by change n + 1 < M + 1; omega),
      zetaMoebiusKernelSamples_nat p N y hn0 (by change n < M + 1; omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    have he := zetaPrimeFilterKernel_sub_eq_integral_lowering p (N - 1) (3 / 2 + I * y)
      (by exact_mod_cast hn0 : (0 : ℝ) < n) (by linarith : (n : ℝ) ≤ n + 1)
    rw [Nat.sub_add_cancel hN] at he
    rw [he]
  · exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hm

/-- The physical difference energy has a continuous upper bound with
the signed complex lowering operator still inside its square. All endpoint
costs and integrability conditions are explicit. -/
theorem sum_cyclicDifference_zetaMoebiusKernelSamples_sq_le (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    (∑ j, ‖cyclicDifference (zetaMoebiusKernelSamples p N y) j‖ ^ 2) ≤
      (∫ x in (1 : ℝ)..((2 ^ (32 * N) : ℕ) : ℝ),
        ‖(zetaPrimeFilterKernel p (N - 1) (3 / 2 + I * y) x -
          (3 / 2 + I * y) * zetaPrimeFilterKernel p N (3 / 2 + I * y) x) /
            (x : ℂ)‖ ^ 2) +
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ^ 2 := by
  rw [sum_cyclicDifference_zetaMoebiusKernelSamples_sq p N y hN]
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ n ∈ Finset.Ico 1 (2 ^ (32 * N) : ℕ), ∫ x in (n : ℝ)..(n : ℝ) + 1,
        ‖(zetaPrimeFilterKernel p (N - 1) (3 / 2 + I * y) x -
          (3 / 2 + I * y) * zetaPrimeFilterKernel p N (3 / 2 + I * y) x) /
            (x : ℂ)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        have hn' := (Finset.mem_Ico.mp hn).1
        exact_mod_cast (show 0 < n by omega)
      exact norm_unit_integral_sq_le (continuousOn_lowering_pred p N _ hN hn0)
    _ = _ := by
      let g : ℝ → ℝ := fun x ↦
        ‖(zetaPrimeFilterKernel p (N - 1) (3 / 2 + I * y) x -
          (3 / 2 + I * y) * zetaPrimeFilterKernel p N (3 / 2 + I * y) x) / (x : ℂ)‖ ^ 2
      have he := intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun n : ℕ ↦ (n : ℝ)) (m := 1) (n := 2 ^ (32 * N)) (f := g) (μ := volume)
        (by
          have hp : 0 < (2 : ℕ) ^ (32 * N) := by positivity
          omega) (fun n hn ↦ by
          have hn0 : (0 : ℝ) < n := by
            have hn' := hn.1
            exact_mod_cast (show 0 < n by omega)
          exact ((continuousOn_lowering_pred p N (3 / 2 + I * y) hN hn0).norm.pow 2).intervalIntegrable_of_Icc
            (by push_cast; linarith))
      simpa only [Nat.cast_add, Nat.cast_one] using he

/-- The remaining continuous energy retains the damping, phase rotation,
and adjacent factorial moments within the same complex square. -/
def zetaMoebiusFourierInteriorEnergy (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..((2 ^ (32 * N) : ℕ) : ℝ),
    ‖(zetaPrimeFilterKernel p (N - 1) (3 / 2 + I * y) x -
      (3 / 2 + I * y) * zetaPrimeFilterKernel p N (3 / 2 + I * y) x) / (x : ℂ)‖ ^ 2

/-- The actual nonresonant interaction is bounded by the interior
lowering energy plus a geometrically decaying boundary allowance. The
arithmetic energy, symbol-gap cost, and remaining resonant part are explicit. -/
theorem norm_zetaMoebiusBand_sub_resonant_sq_le_interior (p : Polynomial ℂ)
    (D N : ℕ) (y : ℝ) (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    ‖zetaMoebiusBandFilter p D N y -
      zetaMoebiusBandFourierPart p D N y (zetaMoebiusResonantModes N δ)‖ ^ 2 ≤
      δ⁻¹ ^ 2 * ((∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) *
        zetaMoebiusFourierInteriorEnergy p N y +
          ((1 / 2 : ℝ) ^ N * zetaMoebiusFourierBoundaryConstant p) ^ 2) := by
  have h := norm_zetaMoebiusBand_sub_resonant_sq_le p D N 1 y hδ
  simp only [pow_one, Function.iterate_one] at h
  apply h.trans
  have hd := sum_cyclicDifference_zetaMoebiusKernelSamples_sq_le p N y hN
  calc
    _ ≤ δ⁻¹ ^ 2 * (∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) *
        (zetaMoebiusFourierInteriorEnergy p N y +
          ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hd
        (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))
    _ = δ⁻¹ ^ 2 *
        ((∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) *
          zetaMoebiusFourierInteriorEnergy p N y +
          (∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) *
            ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (zetaMoebiusFourierBoundary_energy_le p D N y)) (sq_nonneg _)

end
end RiemannGaussian
