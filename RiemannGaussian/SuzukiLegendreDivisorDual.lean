/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiSignedLegendreRemainder

/-!
# Divisor minorants for the exact Suzuki Legendre potential

The divisor identity for von Mangoldt transports pointwise kernel minorants
to lower bounds for the joint mass--moment form. The nonlinear potential is
the minimum of the exponential trial form, not its maximum. A lower bound
therefore uses the exact mass center, or pays the full convexity cost of a
different center. No arithmetic floor is assumed or proved here.
-/

namespace RiemannGaussian

noncomputable section
open Filter
open scoped BigOperators Topology

/-- Sum of the weight over the positive multiples of `d` up to `N`.
The divisibility formulation also fixes the harmless value at `d = 0`. -/
def suzukiDivisorDualKernel (w : ℕ → ℝ) (N d : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, if d ∣ m then w m else 0

/-- Exact finite divisor duality, with every signed weight retained. -/
theorem sum_weight_mul_log_eq_vonMangoldt_divisorDual (w : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, w m * Real.log m =
      ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * suzukiDivisorDualKernel w N d := by
  classical
  have hd (m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
      (∑ d ∈ Finset.Icc 1 N, if d ∣ m then ArithmeticFunction.vonMangoldt d else 0) =
        Real.log m := by
    rw [← Finset.sum_filter]
    have he : (Finset.Icc 1 N).filter (fun d ↦ d ∣ m) = m.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hdm⟩
        exact ⟨hdm, by have := (Finset.mem_Icc.mp hm).1; omega⟩
      · rintro ⟨hdm, hm0⟩
        exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hdm, hm0⟩),
          (Nat.le_of_dvd (by omega) hdm).trans (Finset.mem_Icc.mp hm).2⟩, hdm⟩
    rw [he, ArithmeticFunction.vonMangoldt_sum]
  unfold suzukiDivisorDualKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← hd m hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> ring

/-- The linear form keeps mass and logarithmic moment at the same endpoint. -/
def suzukiLegendreLinearForm (N : ℕ) (r : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt d * (Real.log d - r) / Real.sqrt d

/-- Exact certificate slack: only von Mangoldt-weighted kernel gaps are lost. -/
theorem suzukiLegendreLinearForm_sub_dual_eq (w : ℕ → ℝ) (N : ℕ) (r : ℝ) :
    suzukiLegendreLinearForm N r - (∑ m ∈ Finset.Icc 1 N, w m * Real.log m) =
      ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d *
        ((Real.log d - r) / Real.sqrt d - suzukiDivisorDualKernel w N d) := by
  rw [sum_weight_mul_log_eq_vonMangoldt_divisorDual]
  unfold suzukiLegendreLinearForm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Pointwise kernel minorants give a lower bound without a zero hypothesis. -/
theorem suzukiLegendreLinearForm_ge_dual (w : ℕ → ℝ) (N : ℕ) (r : ℝ)
    (hminor : ∀ d ∈ Finset.Icc 1 N,
      suzukiDivisorDualKernel w N d ≤ (Real.log d - r) / Real.sqrt d) :
    (∑ m ∈ Finset.Icc 1 N, w m * Real.log m) ≤ suzukiLegendreLinearForm N r := by
  apply sub_nonneg.mp
  rw [suzukiLegendreLinearForm_sub_dual_eq]
  exact Finset.sum_nonneg (fun d hd ↦
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr (hminor d hd)))

/-- The exact arithmetic minimizer, expressed through the same corrected mass. -/
def suzukiLegendreMassCenter (count : ℕ) : ℝ :=
  2 * Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2)

/-- The exponential trial form before minimizing its center. -/
def suzukiLegendreTrial (count : ℕ) (r : ℝ) : ℝ :=
  suzukiArchimedeanIntercept + 4 * Real.exp (r / 2) +
    suzukiArchimedeanSlopeConstant * r + suzukiLegendreLinearForm (count + 2) r

private theorem linear_eq (count : ℕ) (r : ℝ) :
    suzukiLegendreLinearForm (count + 2) r =
      screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1) -
        r * suzukiOldPrimeMass count := by
  unfold suzukiOldPrimeMass
  rw [screwPrefixMoment_suzukiPrime_eq_suzukiChebyshevLogMomentSum,
    screwPrefixMass_suzukiPrimeWeight_eq_suzukiChebyshevMassSum]
  simp only [Nat.add_assoc, suzukiChebyshevLogMomentKernel_nat_eq,
    suzukiChebyshevMassKernel_nat_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold suzukiLegendreLinearForm
  rw [← Finset.sum_Ioc_add_eq_sum_Icc (by omega : 1 ≤ count + 2)]
  simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_mul, zero_div, add_zero]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Evaluation at the actual mass center is exactly the nonlinear potential. -/
theorem suzukiLegendreTrial_massCenter (count : ℕ) :
    suzukiLegendreTrial count (suzukiLegendreMassCenter count) =
      suzukiMassLegendrePotential count := by
  have hm := suzukiFirstTailCorrectedMass_pos count
  change 0 < suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant at hm
  unfold suzukiLegendreTrial
  rw [linear_eq]
  unfold suzukiLegendreMassCenter suzukiMassLegendrePotential
  rw [show 2 * Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2) / 2 =
    Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2) by ring,
    Real.exp_log (by positivity)]
  ring

/-- The full cost of moving away from the exact mass center, with its sign kept. -/
theorem suzukiLegendreTrial_sub_potential_eq (count : ℕ) (r : ℝ) :
    suzukiLegendreTrial count r - suzukiMassLegendrePotential count =
      2 * (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) *
        (Real.exp ((r - suzukiLegendreMassCenter count) / 2) - 1 -
          (r - suzukiLegendreMassCenter count) / 2) := by
  let m := suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant
  have hm : 0 < m := suzukiFirstTailCorrectedMass_pos count
  have he : Real.exp ((r - suzukiLegendreMassCenter count) / 2) =
      Real.exp (r / 2) / (m / 2) := by
    unfold suzukiLegendreMassCenter
    rw [show (r - 2 * Real.log (m / 2)) / 2 = r / 2 - Real.log (m / 2) by ring,
      Real.exp_sub, Real.exp_log (by positivity)]
  unfold suzukiLegendreTrial
  rw [linear_eq, he]
  unfold suzukiMassLegendrePotential suzukiLegendreMassCenter
  change _ = 2 * m * (Real.exp (r / 2) / (m / 2) - 1 - (r - 2 * Real.log (m / 2)) / 2)
  field_simp
  dsimp [m]
  ring

/-- Every trial gives an upper bound for the minimum. In particular the
opposite inequality cannot be used to certify a floor at an arbitrary center. -/
theorem suzukiMassLegendrePotential_le_trial (count : ℕ) (r : ℝ) :
    suzukiMassLegendrePotential count ≤ suzukiLegendreTrial count r := by
  apply sub_nonneg.mp
  rw [suzukiLegendreTrial_sub_potential_eq]
  apply mul_nonneg (le_of_lt (mul_pos (by norm_num) (suzukiFirstTailCorrectedMass_pos count)))
  linarith [Real.add_one_le_exp ((r - suzukiLegendreMassCenter count) / 2)]

/-- A divisor minorant at the exact minimizing center certifies a lower
bound on the original nonlinear potential, with no loss from minimization. -/
theorem suzukiMassLegendrePotential_ge_of_divisorDual (count : ℕ) (w : ℕ → ℝ)
    (hminor : ∀ d ∈ Finset.Icc 1 (count + 2),
      suzukiDivisorDualKernel w (count + 2) d ≤
        (Real.log d - suzukiLegendreMassCenter count) / Real.sqrt d) :
    suzukiArchimedeanIntercept + 4 * Real.exp (suzukiLegendreMassCenter count / 2) +
      suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count +
      (∑ m ∈ Finset.Icc 1 (count + 2), w m * Real.log m) ≤
        suzukiMassLegendrePotential count := by
  rw [← suzukiLegendreTrial_massCenter]
  exact add_le_add le_rfl (suzukiLegendreLinearForm_ge_dual w _ _ hminor)

/-- A minorant at another center remains usable if its entire exponential
convexity cost is subtracted. The cost is exact, rather than a quadratic surrogate. -/
theorem suzukiMassLegendrePotential_ge_of_divisorDual_with_cost
    (count : ℕ) (r : ℝ) (w : ℕ → ℝ)
    (hminor : ∀ d ∈ Finset.Icc 1 (count + 2),
      suzukiDivisorDualKernel w (count + 2) d ≤ (Real.log d - r) / Real.sqrt d) :
    suzukiArchimedeanIntercept + 4 * Real.exp (r / 2) +
      suzukiArchimedeanSlopeConstant * r +
      (∑ m ∈ Finset.Icc 1 (count + 2), w m * Real.log m) -
      2 * (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) *
        (Real.exp ((r - suzukiLegendreMassCenter count) / 2) - 1 -
          (r - suzukiLegendreMassCenter count) / 2) ≤
        suzukiMassLegendrePotential count := by
  have hd := suzukiLegendreLinearForm_ge_dual w _ _ hminor
  have he := suzukiLegendreTrial_sub_potential_eq count r
  unfold suzukiLegendreTrial at he
  linarith

/-- A finite eventual floor for the exact potential suffices for the existing
RH criterion. Its comparison error and any finite initial prefix are absorbed
into the constant; the independent arithmetic floor remains a hypothesis. -/
theorem riemannHypothesis_of_suzukiMassLegendrePotential_eventually_bounded_below
    (B : ℝ) (hfloor : ∀ᶠ count : ℕ in atTop, -B ≤ suzukiMassLegendrePotential count) :
    RiemannHypothesis := by
  obtain ⟨start, hstart⟩ := eventually_atTop.mp hfloor
  let E := ∑ j ∈ Finset.range start, |suzukiFirstTailCanonicalGap j|
  let D := suzukiMassLegendrePotential 0 - suzukiFirstTailCanonicalGap 0
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  apply riemannHypothesis_of_suzukiCanonicalGap_bounded_below
    (C := |B| + |D| + E) (by positivity)
  intro count
  by_cases hc : start ≤ count
  · have he : suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count ≤ D :=
      antitone_suzukiMassLegendrePotential_sub_gap (Nat.zero_le count)
    linarith [hstart count hc, le_abs_self B, le_abs_self D]
  · have he : |suzukiFirstTailCanonicalGap count| ≤ E :=
      Finset.single_le_sum (f := fun j ↦ |suzukiFirstTailCanonicalGap j|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr (lt_of_not_ge hc))
    linarith [neg_abs_le (suzukiFirstTailCanonicalGap count), abs_nonneg B, abs_nonneg D]

/-- An eventual family of feasible divisor certificates with a common finite
floor would prove RH. Both feasibility and the floor are open obligations;
the center is fixed by the actual finite corrected mass. -/
theorem riemannHypothesis_of_suzukiDivisorDual_eventual_floor
    (B : ℝ) (w : ℕ → ℕ → ℝ)
    (hminor : ∀ᶠ count : ℕ in atTop, ∀ d ∈ Finset.Icc 1 (count + 2),
      suzukiDivisorDualKernel (w count) (count + 2) d ≤
        (Real.log d - suzukiLegendreMassCenter count) / Real.sqrt d)
    (hfloor : ∀ᶠ count : ℕ in atTop,
      -B ≤ suzukiArchimedeanIntercept + 4 * Real.exp (suzukiLegendreMassCenter count / 2) +
        suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count +
        (∑ m ∈ Finset.Icc 1 (count + 2), w count m * Real.log m)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiMassLegendrePotential_eventually_bounded_below B
  filter_upwards [hminor, hfloor] with count hm hf
  exact hf.trans (suzukiMassLegendrePotential_ge_of_divisorDual count (w count) hm)

end
end RiemannGaussian
