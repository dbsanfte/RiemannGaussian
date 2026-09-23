/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordGlobalStep

/-!
# Repeated original Ford iteration from the diagonal moment

Every coefficient and defect is specified by the original finite
recurrence. Iteration begins with the proved k-th diagonal moment and
covers every positive integer endpoint. No source moment bound is assumed.
The short-prime supply and the scalar restrictions on the chosen depth and
rank schedules remain explicit; the published optimized schedule and its
subsequent numerical estimates are not claimed here.
-/

namespace RiemannGaussian.VinogradovFordMomentSequence
noncomputable section
open VinogradovMeanValue VinogradovFordScales VinogradovFordSchedule
open VinogradovFordGlobalStep

/-- The actual moment order after j steps, with j=0 the diagonal moment. -/
def order (k j : ℕ) : ℕ := (j + 1) * k

/-- The original defect recurrence for specified rank and depth schedules. -/
def defect (k : ℕ) (r depth : ℕ → ℕ) : ℕ → ℝ
  | 0 => (k : ℝ) * ((k : ℝ) - 1) / 2
  | j + 1 => nextDefect k (r j) (defect k r depth j)
      (schedule k (r j) (depth j) (defect k r depth j) 0)

/-- The published coefficient recurrence, retaining the exact maximum
between the large-endpoint and small-endpoint costs. -/
def coefficient (k : ℕ) (r depth : ℕ → ℕ) (omega : ℝ) : ℕ → ℝ
  | 0 => k.factorial
  | j + 1 => coefficient k r depth omega j *
      stepCoefficient k (order k j) omega (defect k r depth j) (defect k r depth (j + 1))

/-- Only explicit scalar restrictions on the rank and depth schedules.
There is no moment estimate or prime-supply assumption in admissibility. -/
def Admissible (k : ℕ) (r depth : ℕ → ℕ) (J : ℕ) : Prop :=
  ∀ j < J, 1 ≤ r j ∧ r j ≤ k ∧ 10 * (depth j + 1) ≤ 9 * r j ∧
    (depth j : ℝ) * ((depth j : ℝ) - 1) ≤ depthReserve k (r j) (defect k r depth j) ∧
      1 / ((k : ℝ) + 1) ≤ stationaryScale k (r j) (defect k r depth j)

/-- Every prefix inherits all scalar restrictions of the full schedule. -/
theorem Admissible.prefix {k J I : ℕ} {r depth : ℕ → ℕ}
    (h : Admissible k r depth J) (hIJ : I ≤ J) : Admissible k r depth I := by
  intro j hj
  exact h j (by omega)

/-- The moment order increases by the original fixed degree at each step. -/
theorem order_succ (k j : ℕ) : order k (j + 1) = order k j + k := by
  unfold order
  ring

/-- The full finite schedule stays in the initial defect range without
requiring that invariant as an extra hypothesis. -/
theorem defect_le_initial {k J : ℕ} {r depth : ℕ → ℕ} (hk : 0 < k)
    (h : Admissible k r depth J) :
    defect k r depth J ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction J with
  | zero => exact le_rfl
  | succ J ih =>
    have hprevious := ih (h.prefix (by omega))
    obtain ⟨hr1, _hr, _hlimit, hdepth, hroot⟩ := h J (by omega)
    exact (nextDefect_le hk (by omega) hprevious hdepth hroot).trans hprevious

/-- Every literal coefficient is positive, including before any supply
or schedule hypotheses are used. -/
theorem coefficient_pos {k : ℕ} (hk : 0 < k) (r depth : ℕ → ℕ)
    {omega : ℝ} (homega : 0 < omega) (J : ℕ) :
    0 < coefficient k r depth omega J := by
  induction J with
  | zero =>
    change (0 : ℝ) < k.factorial
    exact_mod_cast Nat.factorial_pos k
  | succ J ih => exact mul_pos ih (stepCoefficient_pos hk homega)

/-- The initial exponent is exactly the exponent of the proved diagonal
moment, so the repeated iteration has no unproved starting estimate. -/
theorem initial_exponent (k : ℕ) (r depth : ℕ → ℕ) :
    sourceExponent k (order k 0) (defect k r depth 0) = k := by
  simp only [sourceExponent, order, zero_add, one_mul, defect]
  ring

/-- The published finite coefficient and defect recurrences bound the
actual moments at all positive endpoints, starting from the diagonal
count. The exact short-prime input and scalar schedule restrictions are
the only unproved inputs beyond the numerical parameter range. -/
theorem iterated_moment_bound {k J : ℕ} (r depth : ℕ → ℕ) {omega : ℝ}
    (hk : 26 ≤ k) (horder : J + 1 ≤ k ^ 2)
    (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hsupply : ShortPrimeSupply k omega) (hadmissible : Admissible k r depth J) :
    ∀ P : ℕ, 1 ≤ P → meanValue (order k J) k P ≤
      coefficient k r depth omega J *
        (P : ℝ) ^ sourceExponent k (order k J) (defect k r depth J) := by
  induction J with
  | zero =>
    intro P _hP
    rw [initial_exponent, Real.rpow_natCast]
    have hh := VinogradovPowerSumRigidity.meanValue_le (r := k) (k := k) (N := P) le_rfl
    simpa only [order, coefficient, zero_add, one_mul, mul_one, mul_comm] using hh
  | succ J ih =>
    have hprefix := hadmissible.prefix (show J ≤ J + 1 by omega)
    have hsource := ih (by omega) hprefix
    obtain ⟨hr1, hr, hlimit, hdepth, hroot⟩ := hadmissible J (by omega)
    have hs : k ≤ order k J := by
      dsimp only [order]
      exact Nat.le_mul_of_pos_left _ (by omega)
    have hsMax : order k J ≤ k ^ 3 := by
      have hh := Nat.mul_le_mul_right k (show J + 1 ≤ k ^ 2 by omega)
      simpa only [order, pow_succ] using hh
    have hh := all_endpoint_bound k (r J) (depth J) (order k J) hk hs hsMax
      hr1 hr hlimit (coefficient_pos (by omega) r depth homega J) homega homegaHalf
      (defect_le_initial (by omega) hprefix) hdepth hroot hsupply hsource
    simpa only [order_succ, coefficient, defect] using hh

end
end RiemannGaussian.VinogradovFordMomentSequence
