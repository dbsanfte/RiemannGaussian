/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLegendreDivisorDual

/-!
# Analytic tests for all finite divisor weights

The finite multiples transform is surjective, so unrestricted feasible
weights attain the original linear arithmetic value exactly. Every
optimizer is characterized by equality on prime powers. This identifies
the optimum, but does not bound it uniformly in the endpoint.

A nonnegative comparison mass matching a class's divisor observations
gives a simultaneous upper bound on every feasible certificate in that
class. The comparison mass need not be the actual von Mangoldt function.
-/

namespace RiemannGaussian

noncomputable section
open scoped BigOperators

/-- Every finite target kernel is attained by real weights. The proof uses
finite descending elimination, with no arithmetic cancellation hypothesis. -/
theorem exists_suzukiDivisorDualKernel_eq (N : ℕ) (f : ℕ → ℝ) :
    ∃ w : ℕ → ℝ, ∀ d ∈ Finset.Icc 1 N, suzukiDivisorDualKernel w N d = f d := by
  classical
  induction N generalizing f with
  | zero => exact ⟨fun _ ↦ 0, by simp⟩
  | succ N ih =>
    obtain ⟨w, hw⟩ := ih (fun d ↦ f d - if d ∣ N + 1 then f (N + 1) else 0)
    let v : ℕ → ℝ := fun m ↦ if m = N + 1 then f (N + 1) else w m
    refine ⟨v, ?_⟩
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdN := (Finset.mem_Icc.mp hd).2
    unfold suzukiDivisorDualKernel
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hold : (∑ m ∈ Finset.Icc 1 N, if d ∣ m then v m else 0) =
        suzukiDivisorDualKernel w N d := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmN := (Finset.mem_Icc.mp hm).2
      simp [v, show m ≠ N + 1 by omega]
    rw [hold]
    by_cases he : d = N + 1
    · subst d
      have hz : suzukiDivisorDualKernel w N (N + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hm1 := (Finset.mem_Icc.mp hm).1
        have hmN := (Finset.mem_Icc.mp hm).2
        have hnot : ¬N + 1 ∣ m := by
          intro hdiv
          have := Nat.le_of_dvd (by omega : 0 < m) hdiv
          omega
        simp [hnot]
      simp [hz, v]
    · rw [hw d (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)]
      simp [v]

/-- All feasible optimizers are exactly those with zero kernel slack on
every prime power. Slack at other integers carries no von Mangoldt cost. -/
theorem suzukiLegendreLinearForm_eq_dual_iff (w : ℕ → ℝ) (N : ℕ) (r : ℝ)
    (hminor : ∀ d ∈ Finset.Icc 1 N,
      suzukiDivisorDualKernel w N d ≤ (Real.log d - r) / Real.sqrt d) :
    (∑ m ∈ Finset.Icc 1 N, w m * Real.log m) = suzukiLegendreLinearForm N r ↔
      ∀ d ∈ Finset.Icc 1 N, IsPrimePow d →
        suzukiDivisorDualKernel w N d = (Real.log d - r) / Real.sqrt d := by
  have hn (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      0 ≤ ArithmeticFunction.vonMangoldt d *
        ((Real.log d - r) / Real.sqrt d - suzukiDivisorDualKernel w N d) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr (hminor d hd))
  constructor
  · intro he d hd hp
    have hz : (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d *
        ((Real.log d - r) / Real.sqrt d - suzukiDivisorDualKernel w N d)) = 0 := by
      rw [← suzukiLegendreLinearForm_sub_dual_eq, he, sub_self]
    have hd0 := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz d hd
    have hp0 := ne_of_gt (ArithmeticFunction.vonMangoldt_pos_iff.mpr hp)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hd0).resolve_left hp0)).symm
  · intro he
    have hz : (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d *
        ((Real.log d - r) / Real.sqrt d - suzukiDivisorDualKernel w N d)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hp : IsPrimePow d
      · rw [he d hd hp, sub_self, mul_zero]
      · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, zero_mul]
    rw [← suzukiLegendreLinearForm_sub_dual_eq] at hz
    exact (sub_eq_zero.mp hz).symm

/-- Kernel constraints are needed only on prime powers. Removing every
other constraint preserves the lower bound because its arithmetic mass is zero. -/
theorem suzukiLegendreLinearForm_ge_dual_on_primePowers (w : ℕ → ℝ) (N : ℕ) (r : ℝ)
    (hminor : ∀ d ∈ Finset.Icc 1 N, IsPrimePow d →
      suzukiDivisorDualKernel w N d ≤ (Real.log d - r) / Real.sqrt d) :
    (∑ m ∈ Finset.Icc 1 N, w m * Real.log m) ≤ suzukiLegendreLinearForm N r := by
  apply sub_nonneg.mp
  rw [suzukiLegendreLinearForm_sub_dual_eq]
  apply Finset.sum_nonneg
  intro d hd
  by_cases hp : IsPrimePow d
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr (hminor d hd hp))
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, zero_mul]

/-- The actual Suzuki potential inherits the support-exact certificate:
no minorant constraints at non-prime-power integers are required. -/
theorem suzukiMassLegendrePotential_ge_of_primePower_divisorDual
    (count : ℕ) (w : ℕ → ℝ)
    (hminor : ∀ d ∈ Finset.Icc 1 (count + 2), IsPrimePow d →
      suzukiDivisorDualKernel w (count + 2) d ≤
        (Real.log d - suzukiLegendreMassCenter count) / Real.sqrt d) :
    suzukiArchimedeanIntercept + 4 * Real.exp (suzukiLegendreMassCenter count / 2) +
      suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count +
      (∑ m ∈ Finset.Icc 1 (count + 2), w m * Real.log m) ≤
        suzukiMassLegendrePotential count := by
  rw [← suzukiLegendreTrial_massCenter]
  exact add_le_add le_rfl (suzukiLegendreLinearForm_ge_dual_on_primePowers w _ _ hminor)

/-- The unrestricted finite certificate optimum is attained and is exactly
the original linear form. This is an identity, not an independent floor. -/
theorem suzukiLegendreLinearForm_isGreatest_dual (N : ℕ) (r : ℝ) :
    IsGreatest {v : ℝ | ∃ w : ℕ → ℝ,
      (∀ d ∈ Finset.Icc 1 N,
        suzukiDivisorDualKernel w N d ≤ (Real.log d - r) / Real.sqrt d) ∧
      v = ∑ m ∈ Finset.Icc 1 N, w m * Real.log m} (suzukiLegendreLinearForm N r) := by
  obtain ⟨w, hw⟩ := exists_suzukiDivisorDualKernel_eq N
    (fun d ↦ (Real.log d - r) / Real.sqrt d)
  have hm : ∀ d ∈ Finset.Icc 1 N,
      suzukiDivisorDualKernel w N d ≤ (Real.log d - r) / Real.sqrt d :=
    fun d hd ↦ (hw d hd).le
  constructor
  · refine ⟨w, hm, ?_⟩
    exact ((suzukiLegendreLinearForm_eq_dual_iff w N r hm).mpr (fun d hd _ ↦ hw d hd)).symm
  · rintro v ⟨vweight, hv, rfl⟩
    exact suzukiLegendreLinearForm_ge_dual vweight N r hv

/-- Maximizing over every admissible finite weight recovers the exact
Suzuki potential. The all-endpoint lower bound for this maximum remains open. -/
theorem suzukiMassLegendrePotential_isGreatest_dual (count : ℕ) :
    IsGreatest {v : ℝ | ∃ w : ℕ → ℝ,
      (∀ d ∈ Finset.Icc 1 (count + 2),
        suzukiDivisorDualKernel w (count + 2) d ≤
          (Real.log d - suzukiLegendreMassCenter count) / Real.sqrt d) ∧
      v = suzukiArchimedeanIntercept + 4 * Real.exp (suzukiLegendreMassCenter count / 2) +
        suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count +
        (∑ m ∈ Finset.Icc 1 (count + 2), w m * Real.log m)}
      (suzukiMassLegendrePotential count) := by
  have h := suzukiLegendreLinearForm_isGreatest_dual (count + 2) (suzukiLegendreMassCenter count)
  constructor
  · obtain ⟨w, hm, he⟩ := h.1
    refine ⟨w, hm, ?_⟩
    rw [← suzukiLegendreTrial_massCenter]
    exact congrArg (fun x ↦ suzukiArchimedeanIntercept +
      4 * Real.exp (suzukiLegendreMassCenter count / 2) +
      suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count + x) he
  · rintro v ⟨w, hm, rfl⟩
    exact suzukiMassLegendrePotential_ge_of_divisorDual count w hm

/-- Any nonnegative comparison mass which reproduces a class's logarithmic
observations gives an upper ceiling for every feasible weight in that class.
The comparison need not be the actual von Mangoldt mass. -/
theorem suzukiDivisorDual_class_upper_bound (W : Set (ℕ → ℝ)) (N : ℕ)
    (f ν : ℕ → ℝ) (hν : ∀ d ∈ Finset.Icc 1 N, 0 ≤ ν d)
    (hmatch : ∀ w ∈ W, (∑ m ∈ Finset.Icc 1 N, w m * Real.log m) =
      ∑ d ∈ Finset.Icc 1 N, ν d * suzukiDivisorDualKernel w N d) :
    ∀ w ∈ W, (∀ d ∈ Finset.Icc 1 N, suzukiDivisorDualKernel w N d ≤ f d) →
      (∑ m ∈ Finset.Icc 1 N, w m * Real.log m) ≤
        ∑ d ∈ Finset.Icc 1 N, ν d * f d := by
  intro w hw hm
  rw [hmatch w hw]
  exact Finset.sum_le_sum (fun d hd ↦ mul_le_mul_of_nonneg_left (hm d hd) (hν d hd))

private theorem kernel_linear {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (φ : ι → ℕ → ℝ) (N d : ℕ) :
    suzukiDivisorDualKernel (fun m ↦ ∑ j, a j * φ j m) N d =
      ∑ j, a j * suzukiDivisorDualKernel (φ j) N d := by
  unfold suzukiDivisorDualKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : d ∣ m <;> simp [hm]

/-- Matching only the finitely many basis observations bounds every real
coefficient choice in their span. This tests an entire weight class at once,
including negative coefficients, without optimizing candidates individually. -/
theorem suzukiDivisorDual_span_upper_bound {ι : Type*} [Fintype ι]
    (φ : ι → ℕ → ℝ) (N : ℕ) (f ν : ℕ → ℝ)
    (hν : ∀ d ∈ Finset.Icc 1 N, 0 ≤ ν d)
    (hmatch : ∀ j, (∑ m ∈ Finset.Icc 1 N, φ j m * Real.log m) =
      ∑ d ∈ Finset.Icc 1 N, ν d * suzukiDivisorDualKernel (φ j) N d) :
    ∀ a : ι → ℝ,
      (∀ d ∈ Finset.Icc 1 N,
        suzukiDivisorDualKernel (fun m ↦ ∑ j, a j * φ j m) N d ≤ f d) →
      (∑ m ∈ Finset.Icc 1 N, (∑ j, a j * φ j m) * Real.log m) ≤
        ∑ d ∈ Finset.Icc 1 N, ν d * f d := by
  intro a hm
  have he : (∑ m ∈ Finset.Icc 1 N, (∑ j, a j * φ j m) * Real.log m) =
      ∑ d ∈ Finset.Icc 1 N,
        ν d * suzukiDivisorDualKernel (fun m ↦ ∑ j, a j * φ j m) N d := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hmatch, Finset.mul_sum, kernel_linear, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_le_sum (fun d hd ↦ mul_le_mul_of_nonneg_left (hm d hd) (hν d hd))

end
end RiemannGaussian
