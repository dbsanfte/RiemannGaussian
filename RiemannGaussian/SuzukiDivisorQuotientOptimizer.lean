/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiDivisorDualOptimality
import RiemannGaussian.EtaMoebiusFinitePrefix
import Mathlib.Data.Nat.Sqrt

/-!
# Exact Suzuki weights on complete quotient cells

Finite Möbius inversion gives explicit weights attaining every divisor
constraint. For the Suzuki target these weights are affine in `log m`,
after multiplication by `sqrt m`, on each cell of constant `N / m`.
The coefficients are exact finite Möbius sums, not numerical choices.

This removes approximation loss from the coefficient search. It does not
provide an independent lower bound on the resulting logarithmic sum.
-/

namespace RiemannGaussian

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

/-- The finite inverse over multiples, retaining its complete quotient cutoff. -/
def suzukiDivisorMobiusInverse (N : ℕ) (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (N / m), (μ k : ℝ) * f (m * k)

private theorem kernel_eq_multiples (w : ℕ → ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    suzukiDivisorDualKernel w N d = ∑ k ∈ Finset.Icc 1 (N / d), w (d * k) := by
  classical
  rw [suzukiDivisorDualKernel, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k _ ↦ d * k) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkN⟩, dvd_mul_right d k⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · intro m hm
    obtain ⟨hmI, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmI
    refine ⟨m / d, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hmN⟩, ?_⟩
    · exact (Nat.le_div_iff_mul_le hd).mpr (by
        simpa using Nat.le_of_dvd (by omega : 0 < m) hdm)
    · exact Nat.mul_div_cancel' hdm
  · intro k _
    rfl

private theorem sum_moebius_divisors_real (n : ℕ) :
    (∑ k ∈ n.divisors, (μ k : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

/-- The explicit finite inverse attains every target value exactly. -/
theorem suzukiDivisorDualKernel_mobiusInverse (N : ℕ) (f : ℕ → ℝ)
    {d : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    suzukiDivisorDualKernel (suzukiDivisorMobiusInverse N f) N d = f d := by
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hdN := (Finset.mem_Icc.mp hd).2
  have hQ : 1 ≤ N / d := (Nat.le_div_iff_mul_le hd1).mpr (by simpa using hdN)
  rw [kernel_eq_multiples _ _ hd1]
  simp only [suzukiDivisorMobiusInverse, ← Nat.div_div_eq_div_mul, mul_assoc]
  have hregroup :
      (∑ n ∈ Finset.Icc 1 (N / d), ∑ p ∈ n.divisorsAntidiagonal,
        (μ p.2 : ℝ) * f (d * (p.1 * p.2))) =
      ∑ k ∈ Finset.Icc 1 (N / d), ∑ j ∈ Finset.Icc 1 ((N / d) / k),
        (μ j : ℝ) * f (d * (k * j)) := by
    exact_mod_cast sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix (N / d)
      (fun k j ↦ (((μ j : ℝ) * f (d * (k * j))) : ℂ))
  rw [← hregroup]
  have hpoint (n : ℕ) :
      (∑ p ∈ n.divisorsAntidiagonal, (μ p.2 : ℝ) * f (d * (p.1 * p.2))) =
        (if n = 1 then 1 else 0) * f (d * n) := by
    calc
      _ = (∑ p ∈ n.divisorsAntidiagonal, (μ p.2 : ℝ)) * f (d * n) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
      _ = _ := by
        rw [Nat.sum_divisorsAntidiagonal' (fun _ k ↦ (μ k : ℝ)),
          sum_moebius_divisors_real]
  simp_rw [hpoint]
  simp [Finset.sum_ite_eq', Finset.mem_Icc, hQ]

/-- The exact slope coefficient on the cell of quotient `q`. -/
def suzukiQuotientSlope (q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 q, (μ k : ℝ) / Real.sqrt k

/-- The exact intercept coefficient on the cell of quotient `q`. -/
def suzukiQuotientIntercept (q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 q, (μ k : ℝ) * Real.log k / Real.sqrt k

/-- A mathematically defined Suzuki weight, affine in logarithmic position
on each complete quotient cell. Neither coefficient depends on `r`. -/
def suzukiQuotientWeight (N : ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  (suzukiQuotientSlope (N / m) * (Real.log m - r) +
    suzukiQuotientIntercept (N / m)) / Real.sqrt m

/-- The two quotient coefficients are exactly the finite Möbius inverse
of the Suzuki kernel, with no tail or rounding term discarded. -/
theorem suzukiQuotientWeight_eq_mobiusInverse (N : ℕ) (r : ℝ) {m : ℕ} (hm : 0 < m) :
    suzukiQuotientWeight N r m =
      suzukiDivisorMobiusInverse N (fun d ↦ (Real.log d - r) / Real.sqrt d) m := by
  unfold suzukiQuotientWeight suzukiQuotientSlope suzukiQuotientIntercept
    suzukiDivisorMobiusInverse
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 := (Finset.mem_Icc.mp hk).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  dsimp only
  rw [Nat.cast_mul, Real.log_mul hmR.ne' hkR.ne', Real.sqrt_mul hmR.le]
  ring

/-- The explicit quotient family has zero slack at every positive integer,
and hence also under the prime-power-only certificate test. -/
theorem suzukiDivisorDualKernel_quotientWeight (N : ℕ) (r : ℝ)
    {d : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    suzukiDivisorDualKernel (suzukiQuotientWeight N r) N d =
      (Real.log d - r) / Real.sqrt d := by
  have he : suzukiDivisorDualKernel (suzukiQuotientWeight N r) N d =
      suzukiDivisorDualKernel
        (suzukiDivisorMobiusInverse N (fun d ↦ (Real.log d - r) / Real.sqrt d)) N d := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [suzukiQuotientWeight_eq_mobiusInverse N r (Finset.mem_Icc.mp hm).1]
  rw [he]
  exact suzukiDivisorDualKernel_mobiusInverse N _ hd

/-- The logarithmic sum of these exact quotient weights attains the
unrestricted optimum for every endpoint and every center. -/
theorem suzukiQuotientWeight_log_sum (N : ℕ) (r : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, suzukiQuotientWeight N r m * Real.log m) =
      suzukiLegendreLinearForm N r := by
  have h := suzukiLegendreLinearForm_sub_dual_eq (suzukiQuotientWeight N r) N r
  have hz : (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d *
      ((Real.log d - r) / Real.sqrt d -
        suzukiDivisorDualKernel (suzukiQuotientWeight N r) N d)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [suzukiDivisorDualKernel_quotientWeight N r hd, sub_self, mul_zero]
  exact (sub_eq_zero.mp (h.trans hz)).symm

/-- Evaluation at the mass center gives the literal nonlinear potential.
This is an exact certificate formula, not a uniform arithmetic floor. -/
theorem suzukiMassLegendrePotential_eq_quotient_certificate (count : ℕ) :
    suzukiMassLegendrePotential count =
      suzukiArchimedeanIntercept + 4 * Real.exp (suzukiLegendreMassCenter count / 2) +
        suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count +
        (∑ m ∈ Finset.Icc 1 (count + 2),
          suzukiQuotientWeight (count + 2) (suzukiLegendreMassCenter count) m * Real.log m) := by
  rw [suzukiQuotientWeight_log_sum, ← suzukiLegendreTrial_massCenter]
  rfl

/-- Within a complete quotient cell, the weighted slope between any two
positions is exactly the same finite Möbius coefficient. -/
theorem suzukiQuotientWeight_same_cell (N : ℕ) (r : ℝ) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hcell : N / m = N / n) :
    Real.sqrt m * suzukiQuotientWeight N r m -
      Real.sqrt n * suzukiQuotientWeight N r n =
        suzukiQuotientSlope (N / m) * (Real.log m - Real.log n) := by
  have hm0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne'
  have hn0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  unfold suzukiQuotientWeight
  rw [← hcell]
  field_simp
  ring

/-- Adjacent quotient coefficients have one coupled Möbius increment.
The intercept jump is fixed by the slope jump, so separate approximation
of the two coefficients discards this exact cancellation. -/
theorem suzukiQuotientCoefficient_step (q : ℕ) (u r : ℝ) :
    (suzukiQuotientSlope (q + 1) * (u - r) + suzukiQuotientIntercept (q + 1)) -
      (suzukiQuotientSlope q * (u - r) + suzukiQuotientIntercept q) =
        (μ (q + 1) : ℝ) / Real.sqrt (q + 1) * (u + Real.log (q + 1) - r) := by
  unfold suzukiQuotientSlope suzukiQuotientIntercept
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

/-- At a real quotient boundary, the jump of the scaled weight is exactly
proportional to the displacement of the center from `log X`. In particular
the endpoint-centered formulas join continuously across the boundary. -/
theorem suzukiQuotientCoefficient_boundary (q : ℕ) {X : ℝ} (hX : 0 < X) (r : ℝ) :
    (suzukiQuotientSlope (q + 1) * (Real.log (X / (q + 1)) - r) +
        suzukiQuotientIntercept (q + 1)) -
      (suzukiQuotientSlope q * (Real.log (X / (q + 1)) - r) +
        suzukiQuotientIntercept q) =
      (μ (q + 1) : ℝ) / Real.sqrt (q + 1) * (Real.log X - r) := by
  rw [suzukiQuotientCoefficient_step,
    Real.log_div hX.ne' (show (q : ℝ) + 1 ≠ 0 by positivity)]
  ring

/-- Complete quotient cells require at most twice the integer square root
of the endpoint. Their number is not a fixed truncation parameter. -/
theorem suzukiQuotientCell_card_le (N : ℕ) :
    ((Finset.Icc 1 N).image (fun m ↦ N / m)).card ≤ 2 * Nat.sqrt N := by
  classical
  have hsub : (Finset.Icc 1 N).image (fun m ↦ N / m) ⊆
      Finset.Icc 1 (Nat.sqrt N) ∪
        (Finset.Icc 1 (Nat.sqrt N)).image (fun m ↦ N / m) := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    by_cases hsmall : m ≤ Nat.sqrt N
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hsmall⟩, rfl⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_Icc.mpr
      constructor
      · exact (Nat.le_div_iff_mul_le hm1).mpr (by simpa using hmN)
      · have hprod := Nat.div_mul_le_self N m
        have hroot := Nat.lt_succ_sqrt N
        by_contra hbig
        have hmroot : Nat.sqrt N + 1 ≤ m := by omega
        have hqroot : Nat.sqrt N + 1 ≤ N / m := by omega
        have hmul := Nat.mul_le_mul hqroot hmroot
        nlinarith
  calc
    _ ≤ (Finset.Icc 1 (Nat.sqrt N) ∪
        (Finset.Icc 1 (Nat.sqrt N)).image (fun m ↦ N / m)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (Nat.sqrt N)).card +
        ((Finset.Icc 1 (Nat.sqrt N)).image (fun m ↦ N / m)).card := Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (Nat.sqrt N)).card + (Finset.Icc 1 (Nat.sqrt N)).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by simp; omega

end
end RiemannGaussian
