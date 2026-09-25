/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastVariation

/-!
# Paying the upper least-order boundary jointly with prime count

On labels with at least fourteen prime factors, the joint large/least
factorial tilt pays the entire overflow above the original least-order
ceiling. The lower cutoff, every phase and all literal arithmetic masks
remain. This is an independent bound for that boundary contribution;
the remaining joint signed low-count sum is still open.
-/

namespace RiemannGaussian.ZetaRieszLeastOrderOverflow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszJointBoundary
open ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint ZetaRieszAnnulusJoint
open ZetaRieszParityPacket ZetaRieszWideOwnerAudit ZetaRieszJointOwnerTransfer
open ZetaRieszLeastVariation

/-- The literal two distinct slots, retaining the lower least-order cut. -/
def lowerAllocations (N n p : ℕ) : Finset (ℕ → ℕ) :=
  if p = n.minFac then ∅ else
    (Finset.piAntidiag n.primeFactors (N+1)).filter (fun d =>
      21*N ≤ 40*d p ∧ 40*d p ≤ 23*N ∧ N ≤ 100*(d n.minFac+1))

/-- Only the upper least-order condition is removed. -/
def overflowAllocations (N n p : ℕ) : Finset (ℕ → ℕ) :=
  (lowerAllocations N n p).filter (fun d => 4*N < 100*(d n.minFac+1))

/-- Nonnegative literal factorial mass of the upper-cutoff overflow. -/
def overflowWeight (N n p : ℕ) : ℝ :=
  ∑ d ∈ overflowAllocations N n p,
    allocationWeight n.primeFactors (fun q => Real.log q/Real.log n) d

/-- The broadened lower-cutoff mass; all other orders are retained. -/
def lowerWeight (N n p : ℕ) : ℝ :=
  ∑ d ∈ lowerAllocations N n p,
    allocationWeight n.primeFactors (fun q => Real.log q/Real.log n) d

theorem overflow_subset (N n p : ℕ) :
    overflowAllocations N n p ⊆ Finset.piAntidiag n.primeFactors (N+1) := by
  intro d hd
  have h := (Finset.mem_filter.mp hd).1
  simp only [lowerAllocations] at h
  split_ifs at h with hp
  · simp at h
  · exact (Finset.mem_filter.mp h).1

theorem overflow_orders {N n p : ℕ} {d : ℕ → ℕ} (hd : d ∈ overflowAllocations N n p) :
    21*N ≤ 40*d p ∧ 4*N < 100*(d n.minFac+1) := by
  obtain ⟨hl,hh⟩ := Finset.mem_filter.mp hd
  refine ⟨?_,hh⟩
  simp only [lowerAllocations] at hl
  split_ifs at hl with hp
  · simp at hl
  · exact (Finset.mem_filter.mp hl).2.1

theorem overflowWeight_least_zero (N n : ℕ) : overflowWeight N n n.minFac = 0 := by
  simp [overflowWeight, overflowAllocations, lowerAllocations]

theorem overflowWeight_nonneg (N n p : ℕ) : 0 ≤ overflowWeight N n p :=
  Finset.sum_nonneg (fun d _ => allocationWeight_nonneg _ _
    (fun _ _ => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)) d)

/-- Exact rational powers certify the source-beating joint tilt. -/
theorem upper_tilt_rate :
    (19/40 : ℝ)*Real.log (126/125)-(1/25)*Real.log (138/125) ≤ -(1/6000) := by
  have hp : (126/125 : ℝ)^95/(138/125)^8 ≤ 1-(1/30 : ℝ) := by norm_num
  have he : (126/125 : ℝ)^95/(138/125)^8 ≤ Real.exp (-(1/30 : ℝ)) :=
    hp.trans (by linarith [Real.add_one_le_exp (-(1/30 : ℝ))])
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (126/125)^95/(138/125)^8) he
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_exp] at hl
  norm_num at hl
  linarith

theorem fourteen_share {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (hc : 14 ≤ n.primeFactors.card) :
    Real.log p/Real.log n+13*(Real.log n.minFac/Real.log n) ≤ 1 := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hs : (∑ _q ∈ n.primeFactors.erase p, Real.log n.minFac) ≤
      ∑ q ∈ n.primeFactors.erase p, Real.log q := by
    apply Finset.sum_le_sum
    intro q hq
    have hqq := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
    exact Real.log_le_log (by exact_mod_cast (Nat.minFac_prime hn1.ne').pos)
      (by exact_mod_cast (Nat.minFac_le_of_dvd hqq.two_le
        (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))))
  have he := Finset.sum_erase_add n.primeFactors (fun q : ℕ => Real.log q) hp
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at he
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hp,
    Nat.cast_sub (by omega : 1 ≤ n.primeFactors.card), Nat.cast_one] at hs
  have hcR : (14 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hm := Real.log_natCast_nonneg n.minFac
  have h : Real.log p+13*Real.log n.minFac ≤ Real.log n := by nlinarith
  calc
    _ = (Real.log p+13*Real.log n.minFac)/Real.log n := by ring
    _ ≤ 1 := (div_le_one hl).mpr h

theorem overflowWeight_bound {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (hc : 14 ≤ n.primeFactors.card) (N : ℕ) :
    overflowWeight N n p ≤ 2*Real.exp (-(N : ℝ)/6000) := by
  by_cases hpr : p = n.minFac
  · subst p
    rw [overflowWeight_least_zero]
    positivity
  let S := n.primeFactors
  let x : ℕ → ℝ := fun q => Real.log q/Real.log n
  let v : ℕ → ℝ := fun q => if q = p then 126/125 else if q = n.minFac then 138/125 else 1
  let y : ℕ → ℝ := fun q => v q*x q
  have hpS : p ∈ S := hp
  have hr : n.minFac ∈ S :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hx (q : ℕ) : 0 ≤ x q := div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hv (q : ℕ) : 0 < v q := by dsimp [v]; split_ifs <;> norm_num
  have hy (q : ℕ) : 0 ≤ y q := mul_nonneg (hv q).le (hx q)
  have hsum : ∑ q ∈ S, x q = 1 := shares_sum hn hn1
  have hbase : ∑ q ∈ S, y q ≤ 126/125 := by
    have hi (q : ℕ) : y q = x q+
        (if q = p then (1/125)*x q else 0)+
        (if q = n.minFac then (13/125)*x q else 0) := by
      dsimp [y,v]
      split_ifs with hq hq'
      · exact False.elim (hpr (hq.symm.trans hq'))
      all_goals ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum]
    simp only [Finset.sum_ite_eq', if_pos hpS, if_pos hr]
    have hh := fourteen_share hn hn1 hp hc
    change x p+13*x n.minFac ≤ 1 at hh
    linarith
  have hm (d : ℕ → ℕ) : allocationWeight S y d =
      ((126/125 : ℝ)^(d p)*(138/125 : ℝ)^(d n.minFac))*allocationWeight S x d := by
    have hpv : ∏ q ∈ S, v q^(d q) = (126/125 : ℝ)^(d p)*(138/125 : ℝ)^(d n.minFac) := by
      have hi (q : ℕ) : v q^(d q) =
          (if q = p then (126/125 : ℝ)^(d q) else 1)*
          (if q = n.minFac then (138/125 : ℝ)^(d q) else 1) := by
        dsimp [v]
        split_ifs with hq hq'
        · exact False.elim (hpr (hq.symm.trans hq'))
        all_goals simp
      simp_rw [hi]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite_eq', if_pos hpS, if_pos hr]
    simp only [allocationWeight, y, mul_pow, Finset.prod_mul_distrib]
    rw [hpv]
    ring
  let B := Real.exp (-((21/40 : ℝ)*N*Real.log (126/125)+
    ((N : ℝ)/25-1)*Real.log (138/125)))
  have ht (d : ℕ → ℕ) (hd : d ∈ overflowAllocations N n p) :
      allocationWeight S x d ≤ B*allocationWeight S y d := by
    have hh := overflow_orders hd
    have hj : (21 : ℝ)*N ≤ 40*d p := by exact_mod_cast hh.1
    have hk : (4 : ℝ)*N < 100*((d n.minFac : ℝ)+1) := by exact_mod_cast hh.2
    have hlq : 0 ≤ Real.log (126/125 : ℝ) := Real.log_nonneg (by norm_num)
    have hlr : 0 ≤ Real.log (138/125 : ℝ) := Real.log_nonneg (by norm_num)
    have htilt : 1 ≤ B*((126/125 : ℝ)^(d p)*(138/125 : ℝ)^(d n.minFac)) := by
      rw [show (126/125 : ℝ)^(d p) = Real.exp ((d p : ℝ)*Real.log (126/125)) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)],
        show (138/125 : ℝ)^(d n.minFac) = Real.exp ((d n.minFac : ℝ)*Real.log (138/125)) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
      dsimp [B]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith [mul_nonneg hlq (show 0 ≤ (d p : ℝ)-(21/40)*N by linarith),
        mul_nonneg hlr (show 0 ≤ (d n.minFac : ℝ)-((N : ℝ)/25-1) by linarith)]
    rw [hm, ← mul_assoc]
    exact le_mul_of_one_le_left (allocationWeight_nonneg S x (fun q _ => hx q) d) htilt
  calc
    _ ≤ ∑ d ∈ overflowAllocations N n p, B*allocationWeight S y d := Finset.sum_le_sum ht
    _ ≤ ∑ d ∈ Finset.piAntidiag S (N+1), B*allocationWeight S y d :=
      Finset.sum_le_sum_of_subset_of_nonneg (overflow_subset N n p)
        (fun d _ _ => mul_nonneg (Real.exp_pos _).le
          (allocationWeight_nonneg S y (fun q _ => hy q) d))
    _ = B*(∑ q ∈ S, y q)^(N+1) := by
      rw [← Finset.mul_sum]
      congr 1
      exact (Finset.sum_pow_eq_sum_piAntidiag S y (N+1)).symm
    _ ≤ B*(126/125 : ℝ)^(N+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun q _ => hy q)) hbase _) (Real.exp_pos _).le
    _ = (126/125 : ℝ)*(138/125)*Real.exp
        (((19/40)*Real.log (126/125)-(1/25)*Real.log (138/125))*N) := by
      dsimp [B]
      rw [show (126/125 : ℝ)^(N+1) = Real.exp (((N+1 : ℕ) : ℝ)*Real.log (126/125)) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)], ← Real.exp_add]
      conv_rhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 126/125),
        ← Real.exp_log (by norm_num : (0 : ℝ) < 138/125)]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      simp only [Real.log_exp]
      ring
    _ ≤ _ := by
      have he := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right upper_tilt_rate (Nat.cast_nonneg (α := ℝ) N))
      rw [show -(1/6000 : ℝ)*N = -(N : ℝ)/6000 by ring] at he
      exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le)

/-- Restoring the upper cut recovers exactly the original allocation,
including its owner-order condition. -/
theorem lower_upper_filter_eq {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (N : ℕ) :
    (lowerAllocations N n p).filter (fun d => 100*(d n.minFac+1) ≤ 4*N) =
      markedAllocations N n p := by
  ext d
  by_cases hpr : p = n.minFac
  · subst p
    have he : lowerAllocations N n n.minFac = ∅ := by simp [lowerAllocations]
    simp only [he, Finset.filter_empty, Finset.notMem_empty, false_iff]
    intro hd
    have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).2).2
    omega
  · simp only [lowerAllocations, if_neg hpr, Finset.mem_filter, markedAllocations]
    constructor
    · rintro ⟨⟨hd,hlo,hhi,hmin⟩,hmax⟩
      refine ⟨hd, Finset.mem_filter.mpr ⟨?_, rectangle_mem_owner hlo hhi hmax,
        hlo,hhi,hmin,hmax⟩⟩
      have hr : n.minFac ∈ n.primeFactors :=
        (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
      have hsub : ({p,n.minFac} : Finset ℕ) ⊆ n.primeFactors := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hp
        · rcases Finset.mem_singleton.mp hq with rfl
          exact hr
      have hpair := Finset.sum_le_sum_of_subset (f := d) hsub
      rw [Finset.sum_pair hpr, (Finset.mem_piAntidiag.mp hd).1] at hpair
      exact Finset.mem_range.mpr (by omega)
    · rintro ⟨hd,hh⟩
      have h := (Finset.mem_filter.mp hh).2
      exact ⟨⟨hd,h.2.1,h.2.2.1,h.2.2.2.1⟩,h.2.2.2.2⟩

/-- Removing the upper cut adds precisely the proved overflow mass. -/
theorem lowerWeight_ledger {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (N : ℕ) :
    lowerWeight N n p = markedWeight N n p+overflowWeight N n p := by
  rw [lowerWeight, markedWeight, overflowWeight, overflowAllocations,
    ← lower_upper_filter_eq hn hn1 hp N]
  symm
  simpa only [not_le] using Finset.sum_filter_add_sum_filter_not (lowerAllocations N n p)
    (fun d => 100*(d n.minFac+1) ≤ 4*N)
    (allocationWeight n.primeFactors (fun q => Real.log q/Real.log n))

/-- The original cutoff is kept on counts 3..13. On counts 14..55 only
the upper least-order cutoff is removed, with a separately bounded error. -/
def relaxedPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ lowSupport u N K,
    ((∑ p ∈ n.primeFactors,
      if 14 ≤ n.primeFactors.card then lowerWeight N n p else markedWeight N n p : ℝ) : ℂ)*
      carrierAtom u y N n

/-- The exact finite overflow, with all its arithmetic signs and phases. -/
def overflowPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (lowSupport u N K).filter (fun n => 14 ≤ n.primeFactors.card),
    ((∑ p ∈ n.primeFactors, overflowWeight N n p : ℝ) : ℂ)*carrierAtom u y N n

theorem relaxedPacket_ledger (u y : ℝ) (N K : ℕ) :
    relaxedPacket u y N K =
      ZetaRieszLeastBoundary.jointLowCountPacket u y N K+overflowPacket u y N K := by
  have hov : overflowPacket u y N K = ∑ n ∈ lowSupport u N K,
      if 14 ≤ n.primeFactors.card then
        ((∑ p ∈ n.primeFactors, overflowWeight N n p : ℝ) : ℂ)*carrierAtom u y N n else 0 := by
    exact Finset.sum_filter _ _
  change relaxedPacket u y N K =
    (∑ n ∈ lowSupport u N K,
      ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*carrierAtom u y N n)+_
  rw [relaxedPacket, hov, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
  by_cases hc : 14 ≤ n.primeFactors.card
  · simp only [if_pos hc]
    have hw := Finset.sum_congr rfl (fun p hp => lowerWeight_ledger hb.1 hb.2.1 hp N)
    rw [hw, Finset.sum_add_distrib, Complex.ofReal_add, add_mul]
  · simp only [if_neg hc, add_zero]

/-- The lower least-order threshold, with counts 3..55 still summed
together. It has not been given a positive allowance. -/
def lowerThresholdPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ lowSupport u N K,
    ((∑ p ∈ n.primeFactors, lowerWeight N n p : ℝ) : ℂ)*carrierAtom u y N n

/-- Only counts 3..13 retain an unpaid upper-order correction. Its
sign must remain coupled to the full lower-threshold packet. -/
def shortOverflowPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (lowSupport u N K).filter (fun n => n.primeFactors.card < 14),
    ((∑ p ∈ n.primeFactors, overflowWeight N n p : ℝ) : ℂ)*carrierAtom u y N n

/-- The joint signed target is a difference, not two independent norm
allowances. Counts 14..55 remain present in its first term. -/
theorem relaxedPacket_eq_joint_boundary (u y : ℝ) (N K : ℕ) :
    relaxedPacket u y N K = lowerThresholdPacket u y N K-shortOverflowPacket u y N K := by
  have hs : shortOverflowPacket u y N K = ∑ n ∈ lowSupport u N K,
      if n.primeFactors.card < 14 then
        ((∑ p ∈ n.primeFactors, overflowWeight N n p : ℝ) : ℂ)*carrierAtom u y N n else 0 := by
    exact Finset.sum_filter _ _
  rw [relaxedPacket, lowerThresholdPacket, hs, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
  by_cases hc : 14 ≤ n.primeFactors.card
  · simp only [if_pos hc, if_neg (not_lt.mpr hc), sub_zero]
  · have hl : n.primeFactors.card < 14 := Nat.lt_of_not_ge hc
    simp only [if_neg hc, if_pos hl]
    have hw := Finset.sum_congr rfl (fun p hp => lowerWeight_ledger hb.1 hb.2.1 hp N)
    rw [hw, Finset.sum_add_distrib, Complex.ofReal_add, add_mul, add_sub_cancel_right]

/-- Exact original-target ledger after summing the prime incidences
and all retained counts. The final term has an independent geometric bound. -/
theorem jointLow_boundary_ledger (u y : ℝ) (N K : ℕ) :
    ZetaRieszLeastBoundary.jointLowCountPacket u y N K =
      lowerThresholdPacket u y N K-shortOverflowPacket u y N K-overflowPacket u y N K := by
  have h := relaxedPacket_ledger u y N K
  rw [relaxedPacket_eq_joint_boundary] at h
  linear_combination -h

/-- This rate is strictly below one after the arithmetic majorant. -/
def overflowRate : ℝ := radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/6000))

theorem overflowRate_bounds : 0 ≤ overflowRate ∧ overflowRate < 1 := by
  constructor
  · unfold overflowRate radiusCeiling; positivity
  · have h : radiusCeiling*(131071/262144 : ℝ)⁻¹ < Real.exp (1/6000) :=
      lt_of_lt_of_le (by norm_num [radiusCeiling]) (Real.add_one_le_exp (1/6000))
    simpa only [overflowRate, Real.exp_neg, ← div_eq_mul_inv] using
      (div_lt_one (Real.exp_pos (1/6000))).mpr h

/-- Independent arithmetic bound on the entire upper overflow for
counts 14..55, uniform in the full phase height and every retained mask. -/
theorem overflowPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*overflowPacket u y N K‖ ≤
      (110*radiusCeiling)*overflowRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ (lowSupport u N K).filter (fun n => 14 ≤ n.primeFactors.card)) :
      ‖(u : ℂ)^(N+1)*(((∑ p ∈ n.primeFactors, overflowWeight N n p : ℝ) : ℂ)*
        carrierAtom u y N n)‖ ≤
        (110*radiusCeiling)*overflowRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hlo := (Finset.mem_filter.mp hn).1
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hlo).1).1).2
    have hcount : n.primeFactors.card < 56 := (Finset.mem_filter.mp hlo).2
    have hcR : (n.primeFactors.card : ℝ) ≤ 55 := by exact_mod_cast (by omega : n.primeFactors.card ≤ 55)
    have hw0 : 0 ≤ ∑ p ∈ n.primeFactors, overflowWeight N n p :=
      Finset.sum_nonneg (fun p _ => overflowWeight_nonneg N n p)
    have hw : (∑ p ∈ n.primeFactors, overflowWeight N n p) ≤
        110*Real.exp (-(N : ℝ)/6000) := by
      have hh := Finset.sum_le_sum (fun p (hp : p ∈ n.primeFactors) =>
        overflowWeight_bound hb.1 hb.2.1 hp (Finset.mem_filter.mp hn).2 N)
      simp only [Finset.sum_const, nsmul_eq_mul] at hh
      nlinarith [Real.exp_pos (-(N : ℝ)/6000)]
    have hc := SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/6000) = Real.exp (-(1/6000 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, carrierAtom, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((110*Real.exp (-(N : ℝ)/6000))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        all_goals first | exact zetaMoebiusLogMajorant_nonneg n | (unfold radiusCeiling; positivity)
      _ = _ := by rw [he, overflowRate, mul_pow, mul_pow, pow_succ]; ring
  rw [overflowPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (lowSupport u N K).filter (fun n => 14 ≤ n.primeFactors.card),
        (110*radiusCeiling)*overflowRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg overflowRate_bounds.1 _))

theorem tendsto_relaxed_sub_jointLow {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(relaxedPacket u (heights t) (orders t) (counts t)-
      ZetaRieszLeastBoundary.jointLowCountPacket u (heights t) (orders t) (counts t)))
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one overflowRate_bounds.1
    overflowRate_bounds.2).const_mul (110*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  apply squeeze_zero_norm _ ht
  intro t
  rw [relaxedPacket_ledger, add_sub_cancel_left]
  exact overflowPacket_bound hu hU _ _ _

/-- The original joined packet differs from the joint signed boundary
expression by four independently paid arithmetic errors. No estimate for
either of the two retained signed terms is assumed or concluded. -/
theorem fullPacket_sub_joint_boundary_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*(ZetaRieszLeastBoundary.fullPacket u y N K-
      (lowerThresholdPacket u y N K-shortOverflowPacket u y N K))‖ ≤
      (400*radiusCeiling)*ZetaRieszLeastBoundary.jointCountTailRate^N*
        zetaMoebiusLogMajorantMass (1+1/1048576)+
      (600*radiusCeiling)*rectangleAllocationRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144)+
      (3*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144)+
      (110*radiusCeiling)*overflowRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have he : ZetaRieszLeastBoundary.fullPacket u y N K-
      (lowerThresholdPacket u y N K-shortOverflowPacket u y N K) =
      (ZetaRieszLeastBoundary.fullPacket u y N K-
        ZetaRieszLeastBoundary.jointLowCountPacket u y N K)-overflowPacket u y N K := by
    rw [jointLow_boundary_ledger]
    ring
  rw [he, mul_sub]
  exact (norm_sub_le _ _).trans (add_le_add
    (ZetaRieszLeastBoundary.fullPacket_sub_jointLow_bound hu hU y N K hN)
    (overflowPacket_bound hu hU y N K))

/-- The full joined carrier and the joint boundary expression have the
same source asymptotics, even with moving heights and count cutoffs. -/
theorem tendsto_full_sub_joint_boundary {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(ZetaRieszLeastBoundary.fullPacket u
      (heights t) (orders t) (counts t)-
      (lowerThresholdPacket u (heights t) (orders t) (counts t)-
        shortOverflowPacket u (heights t) (orders t) (counts t)))) atTop (𝓝 0) := by
  have h := (ZetaRieszLeastBoundary.tendsto_full_sub_jointLow hu hU heights orders counts ho).sub
    (tendsto_relaxed_sub_jointLow hu hU heights orders counts ho)
  simp only [sub_zero] at h
  convert h using 1
  ext t
  rw [relaxedPacket_eq_joint_boundary]
  ring


end
end RiemannGaussian.ZetaRieszLeastOrderOverflow
