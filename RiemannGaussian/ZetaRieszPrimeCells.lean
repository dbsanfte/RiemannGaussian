/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszArithmeticCycles
import RiemannGaussian.ZetaSquarefreeEulerLogDecay
import RiemannGaussian.ZetaRieszWholeWindow
import RiemannGaussian.ZetaRieszPrimeEndpoint

/-!
# Exact affine profiles inside divisor cells

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszPrimeCells
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy

/-- The actual active divisors at a real prime-logarithm target. -/
def activeDivisors (L : ℝ) (n : ℕ) (x : ℝ) : Finset ℕ :=
  n.divisors.filter (fun d => Real.log d < L - x)

/-- The complete signed Mobius slope of the target profile on its cell. -/
def cellSlope (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ activeDivisors L n x, ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- Clipping vanishes exactly on the literal active-divisor complement. -/
theorem riesz_eq_active (L : ℝ) (n : ℕ) (x : ℝ) :
    VaughanLogAverage.riesz (L - x) n =
      ∑ d ∈ activeDivisors L n x,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (L - x - Real.log d) := by
  unfold VaughanLogAverage.riesz activeDivisors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : Real.log d < L - x
  · rw [if_pos h, max_eq_right (by linarith : 0 ≤ L - x - Real.log d)]
  · rw [if_neg h, max_eq_left (by linarith : L - x - Real.log d ≤ 0), mul_zero]

/-- On one divisor cell the exact profile is affine, with its signed
slope retained instead of charged to a Lipschitz error. -/
theorem targetProfile_eq_affine (L : ℝ) (n : ℕ) (x y : ℝ)
    (hcell : activeDivisors L n y = activeDivisors L n x) :
    targetProfile L n y = targetProfile L n x + (y - x) * cellSlope L n x := by
  unfold targetProfile cellSlope
  rw [riesz_eq_active L n y, riesz_eq_active L n x, hcell]
  have ht (d : ℕ) : ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (L - y - Real.log d) =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (L - x - Real.log d) -
        (y - x) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Each actual inserted prime in the same cell has the exact signed
linear profile, with no arithmetic approximation. -/
theorem prime_profile_eq_affine (L x : ℝ) {q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hcell : activeDivisors L n (Real.log q) = activeDivisors L n x) :
    VaughanLogAverage.riesz L (q * n) =
      targetProfile L n x + (Real.log q - x) * cellSlope L n x := by
  rw [riesz_prime_eq_target L hq hqn]
  exact targetProfile_eq_affine L n x (Real.log q) hcell

/-- The entire full-filter prime packet becomes two coupled complex
prime moments. All signed coefficients and previously chosen weights stay
inside those moments; the identity does not take their separate norms. -/
theorem prime_packet_eq_two_moments (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n)
    (hcell : ∀ q ∈ Q, activeDivisors L n (Real.log q) = activeDivisors L n x) :
    (∑ q ∈ Q, eta q * bandWeight L P N t (q * n)) =
      (targetProfile L n x : ℂ) * (∑ q ∈ Q, eta q * bandAmplitude L P N t (q * n)) +
      (cellSlope L n x : ℂ) *
        (∑ q ∈ Q, ((Real.log q - x : ℝ) : ℂ) * eta q * bandAmplitude L P N t (q * n)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [bandWeight_eq_amplitude_mul_riesz,
    prime_profile_eq_affine L x (hQ q hq).1 (hQ q hq).2 (hcell q hq)]
  push_cast
  ring

end
end RiemannGaussian.ZetaRieszPrimeCells
