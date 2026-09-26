/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastOrderOverflow

/-!
# Cancelling the one-cofactor head across the two factorial boundaries

The original rectangle is zero when its auxiliary least slot is either
empty or the entire cofactor. Its signed derivative therefore kills a
constant cofactor response exactly, including an arbitrary complex phase.
The literal two-prime allocation has the same exact cancellation.

This justifies a numerical control variate for the joined boundary sum.
It does not estimate the surviving counts three through fifty-five.
-/

namespace RiemannGaussian.ZetaRieszJoinedHeadCancellation
noncomputable section
open MeasureTheory
open scoped BigOperators
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszLeastVariation
open ZetaRieszJointOwnerTransfer ZetaRieszLeastOrderOverflow

/-- A sole cofactor cannot simultaneously satisfy the owner and least
order cuts. This is exact, rather than a concentration error. -/
theorem rectangle_full_slot (N : ℕ) (x : ℝ) : rectangleMass N x 1 = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hi : (∑ h ∈ rectangleOrders N j, mass (N+1-j) h 1) = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    have hc := (Finset.mem_filter.mp hh).2
    have he : N+1-j-h ≠ 0 := by omega
    simp [mass,zero_pow he]
  rw [hi,mul_zero]

theorem rectangle_contDiff (N : ℕ) (x : ℝ) :
    ContDiff ℝ 1 (fun z : ℝ => rectangleMass N x z) := by
  unfold rectangleMass mass
  fun_prop

/-- Both endpoints, including the empty slot, are accounted for before
integrating the signed boundary weight. -/
theorem integral_rectangle_deriv (N : ℕ) (hN : 101 ≤ N) (x : ℝ) :
    (∫ z : ℝ in (0 : ℝ)..1, deriv (fun t => rectangleMass N x t) z) = 0 := by
  have hc := rectangle_contDiff N x
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun _ _ => (hc.differentiable (by norm_num)).differentiableAt)
    (hc.continuous_deriv_one.intervalIntegrable 0 1),
    rectangle_full_slot, rectangle_zero_slot N hN, sub_self]

/-- A cutoff-independent head cancels with its full complex phase.
No separate absolute allowance is assigned to either boundary. -/
theorem constant_head_integral (N : ℕ) (hN : 101 ≤ N) (x : ℝ) (c : ℂ) :
    (∫ z : ℝ in (0 : ℝ)..1,
      c*((deriv (fun t => rectangleMass N x t) z : ℝ) : ℂ)) = 0 := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_rectangle_deriv N hN, Complex.ofReal_zero, mul_zero]

/-- Exact vanishing of the literal marked allocation on two-prime
labels. Its full multinomial total order is retained. -/
theorem markedWeight_two_primes {n p : ℕ} (hn : 1 < n)
    (hp : p ∈ n.primeFactors) (hc : n.primeFactors.card = 2) (N : ℕ) :
    markedWeight N n p = 0 := by
  by_cases hpr : p = n.minFac
  · subst p
    exact ZetaRieszLeastBoundary.markedWeight_least_eq_zero N n
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn.ne').mem_primeFactors (Nat.minFac_dvd n) (by omega)
  have hsub : ({p,n.minFac} : Finset ℕ) ⊆ n.primeFactors := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (Finset.mem_singleton.mp hq) ▸ hr
  have hpair : n.primeFactors = {p,n.minFac} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hc,hpr])).symm
  have he : markedAllocations N n p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨ha,hrect⟩ := Finset.mem_filter.mp hd
    have hsum := (Finset.mem_piAntidiag.mp ha).1
    rw [hpair,Finset.sum_pair hpr] at hsum
    have h := (Finset.mem_filter.mp hrect).2
    omega
  simp [markedWeight,he]

/-- The two actual boundary weights are identical on this head.
This equality does not alter the retained count mask. -/
theorem lower_eq_overflow_two_primes {n p : ℕ} (hsf : Squarefree n)
    (hn : 1 < n) (hp : p ∈ n.primeFactors) (hc : n.primeFactors.card = 2) (N : ℕ) :
    lowerWeight N n p = overflowWeight N n p := by
  rw [lowerWeight_ledger hsf hn hp N,markedWeight_two_primes hn hp hc,zero_add]

/-- Extending the joined boundary target by any literal two-prime
support adds exactly zero. The actual carrier coefficient, phase and
arbitrary additional label selection are retained in this statement. -/
theorem two_prime_extension_eq_zero (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 1 < n ∧ n.primeFactors.card = 2)
    (u y : ℝ) (N : ℕ) :
    (∑ n ∈ S,
      (((∑ p ∈ n.primeFactors, lowerWeight N n p) -
        ∑ p ∈ n.primeFactors, overflowWeight N n p : ℝ) : ℂ) *
        carrierAtom u y N n) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hb := hS n hn
  have he := Finset.sum_congr rfl (fun p hp =>
    lower_eq_overflow_two_primes hb.1 hb.2.1 hp hb.2.2 N)
  rw [he, sub_self, Complex.ofReal_zero, zero_mul]

end
end RiemannGaussian.ZetaRieszJoinedHeadCancellation
