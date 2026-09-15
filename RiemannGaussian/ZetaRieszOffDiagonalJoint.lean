/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrefixDiagonal

/-!
# The whole carrier after paying its diagonal

An exact integer partition removes the independently bounded diagonal
from the completed prime prefix. The remaining whole signed carrier
retains its full negative multiplicity source on the existing annular
interval. The independent floor for that carrier remains open.
-/

namespace RiemannGaussian.ZetaRieszOffDiagonalJoint
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCrossCompletion ZetaRieszAnnulusCompletion ZetaRieszAnnulusJoint
open ZetaRieszPrefixDiagonal

/-- The actual finite physical prefix with precisely its selected
prime-square diagonal removed; every other integer incidence remains. -/
def offDiagonalPrefix (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) \
      A.image (fun p => p ^ 2),
    prefixCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The literal physical prefix splits exactly into its off-diagonal
part and the independently bounded, uniquely counted prime-square part. -/
theorem prefix_sum_eq_offDiagonal_add_diagonal (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    (∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
      prefixCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      offDiagonalPrefix A P u y N + diagonalResponse A P u y N := by
  have hsub := diagonalLabels_subset_range A u N (fun p hp => (hA p hp).2)
  have he := Finset.sum_inter_add_sum_sdiff
    (Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2))
    (A.image (fun p => p ^ 2))
    (fun n => prefixCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
  rw [Finset.inter_eq_right.mpr hsub, sum_prefix_diagonal_eq_response A P u y N hA] at he
  exact he.symm.trans (add_comm _ _)

/-- The whole completed carrier after paying its genuine diagonal
correction. The completed head and distinct-prime prefix remain coupled
to the all-subcutoff contribution. -/
def offDiagonalJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  subcutoffResponse P u y N +
    ZetaPrimeCofactorCompletion.completedCofactorHead (intermediatePrimes u N) P N
      (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N) -
    offDiagonalPrefix (intermediatePrimes u N) P u y N

/-- Removing the actual diagonal adds exactly its signed response to
the completed carrier; no multiplicity or prefix term is lost. -/
theorem offDiagonalJoint_eq_joint_add_diagonal (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    offDiagonalJoint P u y N = jointResponse P u y N +
      diagonalResponse (intermediatePrimes u N) P u y N := by
  have hA : ∀ p ∈ intermediatePrimes u N, p.Prime ∧
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := fun p hp =>
    ⟨((mem_intermediatePrimes u N p).mp hp).1,
    ((mem_intermediatePrimes u N p).mp hp).2.2⟩
  unfold offDiagonalJoint jointResponse completedCross
  rw [prefix_sum_eq_offDiagonal_add_diagonal _ P u y N hA]
  ring

/-- The exact diagonal deletion has independent vanishing source error
for every 0<u<1. This does not extend the annular-completion interval. -/
theorem tendsto_offDiagonal_sub_joint (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (offDiagonalJoint P u y N - jointResponse P u y N)) atTop (𝓝 0) := by
  have hA : ∀ N p, p ∈ intermediatePrimes u N → p.Prime ∧
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := fun N p hp =>
    ⟨((mem_intermediatePrimes u N p).mp hp).1,
    ((mem_intermediatePrimes u N p).mp hp).2.2⟩
  have h := tendsto_diagonalResponse (intermediatePrimes u) P y hu hu1 hA
  apply h.congr'
  filter_upwards [] with N
  rw [offDiagonalJoint_eq_joint_add_diagonal, add_sub_cancel_left]

/-- The whole response retains its full negative multiplicity source
after the independently bounded diagonal is deleted. The remaining signed
floor is for the complete head, off-diagonal prefix and subcutoff class. -/
theorem tendsto_offDiagonalJoint_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      offDiagonalJoint 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have h := (tendsto_offDiagonal_sub_joint 1 rho.1.im hu hu1).add
    (tendsto_jointResponse_exposed rho hrho hexposed huh)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end

end RiemannGaussian.ZetaRieszOffDiagonalJoint
