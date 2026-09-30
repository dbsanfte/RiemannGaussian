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

/-- A label with at most one distinct prime has no marked rectangle mass.
The marked incidence, when present, is necessarily its least prime. -/
theorem markedWeight_count_le_one {n p : ℕ} (hp : p ∈ n.primeFactors)
    (hc : n.primeFactors.card ≤ 1) (N : ℕ) : markedWeight N n p = 0 := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hp
  have hn1 : n ≠ 1 := by intro h; simp [h] at hp
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn0
  have he : p=n.minFac := Finset.card_le_one.mp hc p hp n.minFac hr
  rw [he]
  exact ZetaRieszLeastBoundary.markedWeight_least_eq_zero N n

/-- Every low-count marked incidence vanishes, with no squarefreeness or
phase premise. Empty prime-factor sets have no marked incidence. -/
theorem markedWeight_count_le_two {n p : ℕ} (hp : p ∈ n.primeFactors)
    (hc : n.primeFactors.card ≤ 2) (N : ℕ) : markedWeight N n p = 0 := by
  by_cases h : n.primeFactors.card ≤ 1
  · exact markedWeight_count_le_one hp h N
  · have hn0 : n ≠ 0 := by intro h; simp [h] at hp
    have hn1 : n ≠ 1 := by intro h; simp [h] at hp
    exact markedWeight_two_primes (by omega) hp (by omega) N

/-- Inserting an ordinary-prime cofactor produces only a two-prime label
(one prime if the two are equal), so its joined marked correction is zero. -/
theorem markedWeight_prime_cofactor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (N : ℕ) : markedWeight N (p*q) p = 0 := by
  have hpf : (p*q).primeFactors = {p,q} := by
    rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors,hq.primeFactors]
    simp
  apply markedWeight_count_le_two (by simp [hpf]) _ N
  rw [hpf]
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- The complete ordinary-prime head correction vanishes even with
arbitrary additional masks, factorial factors and complex cofactor phases. -/
theorem ordinary_prime_correction_eq_zero {p : ℕ} (hp : p.Prime)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (N : ℕ) (F : ℕ → ℂ) :
    (∑ q ∈ Q, (markedWeight N (p*q) p : ℂ)*F q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  rw [markedWeight_prime_cofactor hp (hQ q hq),Complex.ofReal_zero,zero_mul]

/-- A finite cofactor completion may add its unit and prime head for free
only while retaining the literal joined marked weight. All other omitted
cofactors remain outside this identity. -/
theorem cofactor_head_completion {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) (N : ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ S, (markedWeight N (p*n) p : ℂ)*F n) =
      ∑ n ∈ S.filter (fun n => n ≠ 1 ∧ ¬n.Prime),
        (markedWeight N (p*n) p : ℂ)*F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have h : n=1 ∨ n.Prime := by
    simp only [Finset.mem_filter] at hnot
    tauto
  rcases h with rfl | h
  · have hz : markedWeight N (p*1) p=0 := by
      simp only [mul_one]
      exact markedWeight_count_le_one (by simp [hp.primeFactors])
        (by simp [hp.primeFactors]) N
    rw [hz,Complex.ofReal_zero,zero_mul]
  · rw [markedWeight_prime_cofactor hp h,Complex.ofReal_zero,zero_mul]

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
