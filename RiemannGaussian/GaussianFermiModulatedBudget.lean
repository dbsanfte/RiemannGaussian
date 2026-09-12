/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FermiCosineModulation
import RiemannGaussian.GaussianFermiMarginBudget

/-!
# The actual zero and prime budget for positive cosine modulation

Three coupled evaluations implement the nonnegative modulated window.
The original convergent prime series is recombined before its sign is
used. The full selected-zero budget keeps the same outside allowance:
the three positive weights sum to one. Every frequency and both shifts
must remain in the known half-height band. No new zero-free constant or
bound on the separate factorial-moment prime source is asserted here.
-/

namespace RiemannGaussian.GaussianFermiModulatedBudget
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open FermiCosineModulation GaussianFermiPrimeFormula GaussianFermiSpectralWeight
open GaussianFermiCosineAverage
open GaussianFermiZeroTail GaussianFermiPoleFormula GaussianFermiMovingAllowance

/-- The three coupled frequencies of one positive cosine modulation. -/
def average (δ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t / 2 + f (t + δ) / 4 + f (t - δ) / 4

/-- Finite zero and phase sums retain every term under modulation. -/
theorem average_sum {ι : Type*} (J : Finset ι) (δ : ℝ) (f : ι → ℝ → ℝ) (t : ℝ) :
    average δ (fun v ↦ ∑ j ∈ J, f j v) t = ∑ j ∈ J, average δ (f j) t := by
  simp only [average, Finset.sum_add_distrib, Finset.sum_div]

/-- The three cosine evaluations are one nonnegative time multiplier
times the original signed cosine phase. -/
theorem average_cos (δ t x : ℝ) :
    average δ (fun v ↦ Real.cos (v * x)) t = factor δ x * Real.cos (t * x) := by
  simp only [average, add_mul, sub_mul, Real.cos_add, Real.cos_sub, factor]
  ring

/-- The exact three-frequency prime identity includes genuine convergence
and every original von Mangoldt prime-power coefficient. -/
theorem hasSum_prime_modulated {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (δ t : ℝ) :
    HasSum (fun n : ℕ ↦ factor δ (Real.log n) * primeSummand a B t n)
      (average δ (primeSum a B) t) := by
  have h := (((summable_primeSummand ha hB t).hasSum.div_const 2).add
    ((summable_primeSummand ha hB (t + δ)).hasSum.div_const 4)).add
      ((summable_primeSummand ha hB (t - δ)).hasSum.div_const 4)
  apply h.congr_fun
  intro n
  have he := average_cos δ t (Real.log n)
  unfold average at he
  unfold primeSummand
  linear_combination
    -(ArithmeticFunction.vonMangoldt n / Real.sqrt n * signal a B (Real.log n)) * he

/-- All finite phase families retain their original cosine kernel inside
the literal, fully convergent modulated prime sum. -/
theorem hasSum_prime_phase {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (δ t : ℝ) :
    HasSum (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      signal a B (Real.log n) * factor δ (Real.log n) *
        (∑ j ∈ J, w j * Real.cos (ω j * (t * Real.log n))))
      (∑ j ∈ J, w j * average δ (primeSum a B) (ω j * t)) := by
  have h := hasSum_sum (s := J) fun j _ ↦ (hasSum_prime_modulated ha hB δ (ω j * t)).mul_left (w j)
  apply h.congr_fun
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold primeSummand
  rw [mul_assoc (ω j) t (Real.log n)]
  ring

/-- A nonnegative original cosine test still controls the entire actual
prime series after modulation, for every shift and Gaussian width. -/
theorem prime_phase_nonneg {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x)) (δ t : ℝ) :
    0 ≤ ∑ j ∈ J, w j * average δ (primeSum a B) (ω j * t) := by
  rw [← (hasSum_prime_phase J w ω ha hB δ t).tsum_eq]
  apply tsum_nonneg
  intro n
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (signal_pos a B _).le)
    (factor_bounds δ _).1) (hphase _)

/-- The complete actual selected-zero budget retains the signed
modulated prime term. Its outside cost is unchanged because the three
positive frequency weights have total mass one. -/
theorem selected_zero_phase_budget_with_prime {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    {m H b c δ t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ht : ∀ j ∈ J, 2 * (|ω j * t| + |δ|) ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ j ∈ J, w j * average δ (fun v ↦ ∑ ρ ∈ S, contribution (b + c) (1 - m) v ρ) (ω j * t)) +
      (∑ j ∈ J, w j * average δ (primeSum (1 - 2 * m) (b + c)) (ω j * t)) ≤
      (∑ j ∈ J, w j * average δ (fun v ↦ polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
        digammaAverage (1 - 2 * m) b c v) (ω j * t)) +
      (∑ j ∈ J, w j) * allowance (b + c) H := by
  have hσ : 1 / 2 ≤ 1 - m := by linarith
  have heq : 2 * (1 - m) - 1 = 1 - 2 * m := by ring
  have hpoint (v : ℝ) (hv : 2 * |v| ≤ H) :
      (∑ ρ ∈ S, contribution (b + c) (1 - m) v ρ) + primeSum (1 - 2 * m) (b + c) v ≤
        (polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
          digammaAverage (1 - 2 * m) b c v) + allowance (b + c) H := by
    have h := GaussianFermiMarginBudget.selected_zero_sum_le_full_add_allowance
      (add_pos hb hc) hv hH hm hmu hscale hzeros S hS
    rw [zero_side_eq_poles_digamma_sub_prime hb hc hσ, heq] at h
    linarith
  have hj (j : ι) (hmem : j ∈ J) :
      average δ (fun v ↦ ∑ ρ ∈ S, contribution (b + c) (1 - m) v ρ) (ω j * t) +
        average δ (primeSum (1 - 2 * m) (b + c)) (ω j * t) ≤
        average δ (fun v ↦ polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
          digammaAverage (1 - 2 * m) b c v) (ω j * t) + allowance (b + c) H := by
    have h0 := hpoint (ω j * t) (by linarith [ht j hmem, abs_nonneg δ])
    have hp := hpoint (ω j * t + δ) (by
      linarith [ht j hmem, abs_add_le (ω j * t) δ])
    have hn := hpoint (ω j * t - δ) (by
      linarith [ht j hmem, abs_sub (ω j * t) δ])
    unfold average
    linarith
  have h := Finset.sum_le_sum fun j hj' ↦ mul_le_mul_of_nonneg_left (hj j hj') (hw j hj')
  simpa only [mul_add, Finset.sum_add_distrib, Finset.sum_mul] using h

/-- Recombining the original prime phases gives the modulated
selected-zero inequality without any new arithmetic sign hypothesis. -/
theorem selected_zero_phase_budget {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {m H b c δ t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ht : ∀ j ∈ J, 2 * (|ω j * t| + |δ|) ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ j ∈ J, w j * average δ (fun v ↦ ∑ ρ ∈ S, contribution (b + c) (1 - m) v ρ) (ω j * t)) ≤
      (∑ j ∈ J, w j * average δ (fun v ↦ polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
        digammaAverage (1 - 2 * m) b c v) (ω j * t)) +
      (∑ j ∈ J, w j) * allowance (b + c) H := by
  have h := selected_zero_phase_budget_with_prime J w ω hw hH hb hc hm hmu hscale hzeros ht S hS
  have hp := prime_phase_nonneg J w ω (by linarith : 0 ≤ 1 - 2 * m)
    (add_pos hb hc) hphase δ t
  linarith

end
end RiemannGaussian.GaussianFermiModulatedBudget
