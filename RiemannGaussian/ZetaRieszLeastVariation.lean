/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastBoundary

/-!
# Literal least-prime variation, before estimating the signed sum

The finite rectangle is evaluated at an auxiliary cutoff and telescoped
before taking any norm. The unit endpoint is exactly zero at large order.
The coincident-mark correction has an independent exponential bound.
All original label masks, counts, Riesz signs and phases stay in the same
finite sum. The remaining signed variation is not asserted to be small.
-/

namespace RiemannGaussian.ZetaRieszLeastVariation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszJointBoundary
open ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint ZetaRieszAnnulusJoint
open ZetaRieszParityPacket ZetaRieszWideOwnerAudit ZetaRieszJointOwnerTransfer

/-- The original rectangle with an auxiliary least-prime log slot.
This does not replace a prime by its continuous density. -/
def virtualWeight (N n p r : ℕ) : ℝ :=
  rectangleMass N (1-Real.log p/Real.log n)
    ((Real.log r/Real.log n)/(1-Real.log p/Real.log n))

/-- The zero-log slot cannot meet the original positive least-order cut. -/
theorem rectangle_zero_slot (N : ℕ) (hN : 101 ≤ N) (x : ℝ) :
    rectangleMass N x 0 = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hi : (∑ h ∈ rectangleOrders N j, mass (N+1-j) h 0) = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    have hhlo := (Finset.mem_filter.mp hh).2.2.2.2.1
    have hh0 : h ≠ 0 := by omega
    simp [mass, zero_pow hh0]
  rw [hi, mul_zero]

theorem virtualWeight_one (N n p : ℕ) (hN : 101 ≤ N) :
    virtualWeight N n p 1 = 0 := by
  simp only [virtualWeight, Nat.cast_one, Real.log_one, zero_div]
  exact rectangle_zero_slot N hN _

/-- The two distinct marked coordinates recover the literal full
multinomial allocation, including all low orders on the other primes. -/
theorem virtualWeight_eq_marked {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (hpr : p ≠ n.minFac) (N : ℕ) :
    virtualWeight N n p n.minFac = markedWeight N n p := by
  let x : ℕ → ℝ := fun q => Real.log q/Real.log n
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hxr : 0 < x n.minFac := div_pos
    (Real.log_pos (by exact_mod_cast (Nat.minFac_prime hn1.ne').one_lt)) hlog
  have hx (q : ℕ) (_hq : q ∈ n.primeFactors) : 0 ≤ x q :=
    div_nonneg (Real.log_natCast_nonneg _) hlog.le
  have hs : (∑ q ∈ n.primeFactors, x q) = 1 := shares_sum hn hn1
  have her := Finset.sum_erase_add n.primeFactors x hp
  rw [hs] at her
  have hl := Finset.single_le_sum (s := n.primeFactors.erase p) (f := x)
    (fun q hq => hx q (Finset.mem_of_mem_erase hq))
    (Finset.mem_erase.mpr ⟨hpr.symm,hr⟩)
  have hxp : x p ≠ 1 := by linarith
  exact rectangleMass_eq_allocations n.primeFactors hp hr hpr.symm x hs hxp N

/-- Telescoping uses the original rectangle at consecutive literal log
cutoffs; it is a signed difference, not a total-variation allowance. -/
def variationWeight (N n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n.minFac-1), ∑ p ∈ n.primeFactors,
    (virtualWeight N n p (k+2)-virtualWeight N n p (k+1))

/-- The auxiliary slot can coincide with the marked prime. That term is
subtracted explicitly rather than counted as a second carrier incidence. -/
def coincidentWeight (N n : ℕ) : ℝ := virtualWeight N n n.minFac n.minFac

theorem variationWeight_eq (N n : ℕ) (hmin : 1 ≤ n.minFac) :
    variationWeight N n = ∑ p ∈ n.primeFactors,
      (virtualWeight N n p n.minFac-virtualWeight N n p 1) := by
  rw [variationWeight, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have h := Finset.sum_range_sub (fun k => virtualWeight N n p (k+1)) (n.minFac-1)
  simpa only [Nat.sub_add_cancel hmin, Nat.zero_add, Nat.add_assoc] using h

/-- The exact literal allocation ledger; no count class or phase has
been separated into an absolute allowance. -/
theorem allocation_variation_ledger {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (N : ℕ) (hN : 101 ≤ N) :
    (∑ p ∈ n.primeFactors, markedWeight N n p) =
      variationWeight N n-coincidentWeight N n := by
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  rw [variationWeight_eq N n (Nat.minFac_prime hn1.ne').pos]
  simp only [virtualWeight_one N n _ hN, sub_zero]
  rw [← Finset.sum_erase_add _ _ hr, ← Finset.sum_erase_add _ _ hr,
    ZetaRieszLeastBoundary.markedWeight_least_eq_zero, add_zero, coincidentWeight,
    add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro p hp
  exact (virtualWeight_eq_marked hn hn1 (Finset.mem_of_mem_erase hp)
    (Finset.mem_erase.mp hp).1 N).symm

/-- A duplicate small slot is still governed by the large-order
coordinate's original factorial tail. -/
theorem duplicate_rectangle_bound (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1/2) :
    0 ≤ rectangleMass N (1-x) (x/(1-x)) ∧
      rectangleMass N (1-x) (x/(1-x)) ≤ 2*Real.exp (-(N : ℝ)/1600) := by
  let S : Finset (Fin 3) := Finset.univ
  let a : Fin 3 → ℝ := ![x,x,1-2*x]
  have ha (i : Fin 3) (_hi : i ∈ S) : 0 ≤ a i := by
    fin_cases i <;> simp [a] <;> linarith
  have hs : (∑ i ∈ S, a i) = 1 := by simp [S,a,Fin.sum_univ_succ]; ring
  have he := rectangleMass_eq_allocations S (p := 0) (r := 1)
    (by simp [S]) (by simp [S]) (by decide) a hs (by simp [a]; linarith) N
  simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  rw [he]
  have hw := allocationWeight_nonneg S a ha
  refine ⟨Finset.sum_nonneg (fun d _ => hw d), ?_⟩
  have ht := coordinate_upper_tail S a ha hs (p := 0) (by simp [S])
    (a := 21/40) (b := 21/20) (q := 11/10) (c := 1/1600) (D := 1)
    (by norm_num) (by norm_num) (by simp [a]; linarith) exterior_tilt_rates.1 N
  have hsub : ((Finset.piAntidiag S (N+1)).filter
      (fun d => d 1 ∈ rectangleOrders N (d 0))) ⊆
      (Finset.piAntidiag S (N+1)).filter (fun d => (21/40 : ℝ)*N-1 < d 0) := by
    intro d hd
    obtain ⟨hd, hr⟩ := Finset.mem_filter.mp hd
    have hj := (Finset.mem_filter.mp hr).2.2.1
    have hjR : (21 : ℝ)*N ≤ 40*d 0 := by exact_mod_cast hj
    exact Finset.mem_filter.mpr ⟨hd, by linarith⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
  apply ht.trans
  rw [one_mul, Real.exp_log (by norm_num : (0 : ℝ) < 11/10),
    show -(1/1600 : ℝ)*N = -(N : ℝ)/1600 by ring]
  nlinarith [Real.exp_pos (-(N : ℝ)/1600)]

/-- Exactly the currently unbounded count selection, with its old masks. -/
def lowSupport (u : ℝ) (N K : ℕ) : Finset ℕ :=
  ((ZetaRieszLeastBoundary.fullBand u N K).filter ZetaRieszLeastBoundary.interior).filter
    (fun n => n.primeFactors.card < 56)

/-- The original signed coefficient and full product phase. -/
def carrierAtom (u y : ℝ) (N n : ℕ) : ℂ :=
  SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- All surviving count classes and marked incidences remain coupled in
the same signed variation. No prime sum is completed. -/
def variationPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ lowSupport u N K, (variationWeight N n : ℂ)*carrierAtom u y N n

/-- The explicitly subtracted coincident-mark term. -/
def coincidentPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ lowSupport u N K, (coincidentWeight N n : ℂ)*carrierAtom u y N n

/-- Exact arithmetic ledger, retaining the original finite support. -/
theorem jointLow_variation_ledger (u y : ℝ) (N K : ℕ) (hN : 101 ≤ N) :
    ZetaRieszLeastBoundary.jointLowCountPacket u y N K =
      variationPacket u y N K-coincidentPacket u y N K := by
  rw [ZetaRieszLeastBoundary.jointLowCountPacket, variationPacket, coincidentPacket,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
  rw [allocation_variation_ledger hb.1 hb.2.1 N hN, Complex.ofReal_sub, sub_mul]
  rfl

theorem coincidentWeight_bound {u : ℝ} {N K n : ℕ} (hn : n ∈ lowSupport u N K) :
    0 ≤ coincidentWeight N n ∧
      coincidentWeight N n ≤ 2*Real.exp (-(N : ℝ)/1600) := by
  have hi := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hx : 0 ≤ Real.log n.minFac/Real.log n :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  exact duplicate_rectangle_bound N hx (by have h := hi.2.2; linarith)

/-- The correction has a genuine source-scale arithmetic saving,
uniformly in height, radius and the retained prime-count cutoff. -/
theorem coincidentPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*coincidentPacket u y N K‖ ≤
      (2*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ lowSupport u N K) :
      ‖(u : ℂ)^(N+1)*((coincidentWeight N n : ℂ)*carrierAtom u y N n)‖ ≤
        (2*radiusCeiling)*exteriorRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hw := coincidentWeight_bound hn
    have hc := SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/1600) = Real.exp (-(1/1600 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.1, carrierAtom, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((2*Real.exp (-(N : ℝ)/1600))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        all_goals first
          | exact zetaMoebiusLogMajorant_nonneg n
          | exact hw.2
          | exact mul_nonneg hw.1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          | (unfold radiusCeiling; positivity)
      _ = _ := by rw [he, exteriorRate, mul_pow, mul_pow, pow_succ]; ring
  rw [coincidentPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ lowSupport u N K, (2*radiusCeiling)*exteriorRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg exteriorRate_bounds.1 _))

/-- The difference, not the unestimated joint variation, has a proved
geometric bound. In particular this theorem assumes no cancellation. -/
theorem jointLow_sub_variation_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) (hN : 101 ≤ N) :
    ‖(u : ℂ)^(N+1)*(ZetaRieszLeastBoundary.jointLowCountPacket u y N K-
      variationPacket u y N K)‖ ≤
      (2*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [jointLow_variation_ledger u y N K hN,
    show variationPacket u y N K-coincidentPacket u y N K-variationPacket u y N K =
      -coincidentPacket u y N K by ring, mul_neg, norm_neg]
  exact coincidentPacket_bound hu hU y N K

end
end RiemannGaussian.ZetaRieszLeastVariation
