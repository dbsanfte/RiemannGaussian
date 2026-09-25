/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointOwnerTransfer

/-!
# Removing the old allocation on the joined literal carrier

The old allocated fraction and the retained factorial rectangle must be
estimated jointly. Their overlap has a geometric bound even after the
largest-share cut and the owner restriction have been removed. The Riesz
hinge, least-prime, physical and total-order masks remain unchanged.
-/

namespace RiemannGaussian.ZetaRieszJointAllocationError
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszJointBoundary
open ZetaRieszJointOwnerTransfer ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint ZetaRieszParityPacket ZetaRieszWideOwnerAudit
open ZetaRieszBalancedCompanion

theorem weight_le_marginal {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : largestPrime n ∈ n.primeFactors) (N : ℕ) :
    weight N n ≤ rectangleMarginal N (1-Real.log (largestPrime n)/Real.log n) := by
  let x : ℕ → ℝ := fun p => Real.log p/Real.log n
  have hx (p : ℕ) (_hp : p ∈ n.primeFactors) : 0 ≤ x p :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hw := allocationWeight_nonneg n.primeFactors x hx
  have hsub : rectangleAllocations N n ⊆
      (Finset.piAntidiag n.primeFactors (N+1)).filter (fun d => 40*d (largestPrime n) ≤ 23*N) := by
    intro d hd
    obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨ha, (Finset.mem_filter.mp hr).2.2.2.1⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans_eq
  rw [Finset.sum_filter,
    marked_allocation_range n.primeFactors hp x (N+1) (fun k => 40*k ≤ 23*N)]
  have he : (∑ p ∈ n.primeFactors.erase (largestPrime n), x p) = 1-x (largestPrime n) := by
    have h := Finset.sum_erase_add n.primeFactors x hp
    rw [show (∑ p ∈ n.primeFactors, x p) = 1 from shares_sum hn hn1] at h
    linarith
  rw [he, rectangleMarginal, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [mass, sub_sub_cancel, x]
    ring
  · rfl

/-- The joint overlap estimate before inserting a support-specific count ceiling. -/
theorem old_allocation_weight_card (A : Finset ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime)
    (hp : largestPrime n ∈ n.primeFactors) (N : ℕ) :
    boundedShare A N n*weight N n ≤
      (n.primeFactors.card : ℝ)*Real.exp (-(N : ℝ)/3200) := by
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have howner : Real.log (n/largestPrime n : ℕ) = Real.log n-Real.log (largestPrime n) := by
    rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp)
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero), Real.log_div
      (by exact_mod_cast hn.ne_zero)
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  have hx : 0 ≤ Real.log (n/largestPrime n : ℕ)/Real.log n :=
    div_nonneg (Real.log_natCast_nonneg _) hln.le
  have hm : weight N n ≤ rectangleMarginal N (Real.log (n/largestPrime n : ℕ)/Real.log n) := by
    have h := weight_le_marginal hn hn1 hp N
    convert h using 2
    rw [howner]
    field_simp
  apply (mul_le_mul_of_nonneg_left hm (boundedShare_bounds A N n).1).trans
  rw [boundedShare, if_pos ⟨hn, hn1, hnp⟩,
    share_eq_binomial_sum A N hn hn1, Finset.sum_mul]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, Real.exp (-(N : ℝ)/3200) := by
      apply Finset.sum_le_sum
      intro p hp'
      split_ifs
      · have hpp := Nat.prime_of_mem_primeFactors hp'
        have hlogs : Real.log (n/p : ℕ) = Real.log n-Real.log p := by
          rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp') (by exact_mod_cast hpp.ne_zero),
            Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
        have hmax : p ≤ largestPrime n := by
          rw [largestPrime, dif_pos (show n.primeFactors.Nonempty from ⟨p,hp'⟩)]
          exact Finset.le_max' _ _ hp'
        have hl : Real.log p ≤ Real.log (largestPrime n) :=
          Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hmax)
        apply unpaid_mul_rectangleMarginal N hx
        · apply div_le_div_of_nonneg_right _ hln.le
          rw [hlogs,howner]
          linarith
        · apply (div_le_one hln).mpr
          rw [hlogs]
          linarith [Real.log_natCast_nonneg p]
      · simpa only [zero_mul] using (Real.exp_pos (-(N : ℝ)/3200)).le
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The joint estimate applies to every prime incidence, rather than
assuming all primes remain below the old 9/16 share cut. -/
theorem old_allocation_weight (A : Finset ℕ) {n : ℕ} (hn : JointBox n) (N : ℕ) :
    boundedShare A N n*weight N n ≤ 83*Real.exp (-(N : ℝ)/3200) := by
  have hnp : ¬n.Prime := by
    intro h
    have hc := hn.count_lower
    rw [h.primeFactors, Finset.card_singleton] at hc
    omega
  exact (old_allocation_weight_card A hn.squarefree hn.nontrivial hnp hn.largest_mem N).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast jointBox_count_le hn) (Real.exp_pos _).le)

theorem marked_old_allocation (A : Finset ℕ) {n : ℕ} (hn : JointBox n) (N : ℕ) :
    boundedShare A N n*(∑ p ∈ n.primeFactors, markedWeight N n p) ≤
      249*Real.exp (-(N : ℝ)/3200) := by
  rw [incidence_weight_ledger hn.largest_mem, mul_add]
  have h := old_allocation_weight A hn N
  have hw := wrongWeight_bound hn N
  have he : Real.exp (-(N : ℝ)/1600) ≤ Real.exp (-(N : ℝ)/3200) :=
    Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hb := mul_le_of_le_one_left hw.1 (boundedShare_bounds A N n).2
  nlinarith

/-- The literal old-allocation error in the unrestricted marked-prime sum. -/
def allocationError (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ band u N K,
    ((boundedShare (intermediatePrimes u N) N n*
      (∑ p ∈ n.primeFactors, markedWeight N n p) : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The same finite marked packet with its original Riesz coefficient,
before multiplying by the old unassigned fraction. -/
def rawMarkedPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ band u N K, ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem allocation_ledger (u y : ℝ) (N K : ℕ) :
    rawMarkedPacket u y N K = markedPacket u y N K+allocationError u y N K := by
  rw [rawMarkedPacket, markedPacket, allocationError, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [residualCoefficient]
  push_cast
  ring

/-- Independent geometric removal of this mask on the enlarged packet. -/
theorem allocationError_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*allocationError u y N K‖ ≤
      (249*radiusCeiling)*rectangleAllocationRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ band u N K) :
      ‖(u : ℂ)^(N+1)*(((boundedShare (intermediatePrimes u N) N n*
        (∑ p ∈ n.primeFactors, markedWeight N n p) : ℝ) : ℂ)*
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
        (249*radiusCeiling)*rectangleAllocationRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hb := marked_old_allocation (intermediatePrimes u N) (Finset.mem_filter.mp hn).2.1 N
    have hpos : 0 ≤ boundedShare (intermediatePrimes u N) N n*
        (∑ p ∈ n.primeFactors, markedWeight N n p) :=
      mul_nonneg (boundedShare_bounds _ _ _).1
        (Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p))
    have hc := SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/3200) = Real.exp (-(1/3200 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((249*Real.exp (-(N : ℝ)/3200))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        · unfold radiusCeiling; positivity
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = _ := by rw [he, rectangleAllocationRate, mul_pow, mul_pow, pow_succ]; ring
  rw [allocationError, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ band u N K, (249*radiusCeiling)*rectangleAllocationRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg rectangleAllocationRate_bounds.1 _))

theorem tendsto_rawMarked_sub_marked {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(rawMarkedPacket u (heights t) (orders t) (counts t)-
      markedPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  simp_rw [allocation_ledger, add_sub_cancel_left]
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one rectangleAllocationRate_bounds.1
    rectangleAllocationRate_bounds.2).const_mul (249*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  exact squeeze_zero_norm (fun t => allocationError_bound hu hU _ _ _) ht

/-- Both arithmetic mask removals, with the original packet and its exact
neighbor contribution on the other side of the comparison. -/
theorem rawMarked_joint_transfer_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*(rawMarkedPacket u y N K-
      (fullParityPacket u y N K+neighbors u y N K))‖ ≤
      ((249*radiusCeiling)*rectangleAllocationRate^N+
        (166*radiusCeiling)*exteriorRate^N)*
          zetaMoebiusLogMajorantMass (1+1/262144) := by
  have he : rawMarkedPacket u y N K-(fullParityPacket u y N K+neighbors u y N K) =
      allocationError u y N K+
        (markedPacket u y N K-(fullParityPacket u y N K+neighbors u y N K)) := by
    rw [allocation_ledger]; ring
  rw [he, mul_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (allocationError_bound hu hU y N K)
    (marked_joint_transfer_bound hu hU y N K))

theorem tendsto_rawMarked_sub_joint {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(rawMarkedPacket u (heights t) (orders t) (counts t)-
      (fullParityPacket u (heights t) (orders t) (counts t)+
        neighbors u (heights t) (orders t) (counts t)))) atTop (𝓝 0) := by
  have h := (tendsto_rawMarked_sub_marked hu hU heights orders counts ho).add
    (tendsto_marked_sub_joint hu hU heights orders counts ho)
  simp only [zero_add] at h
  convert h using 1
  ext t
  ring

/-- The allocation factor is now paid. All least-prime, Riesz, physical,
count, total-log and factorial-order correlations remain in this finite sum. -/
theorem rawMarkedPacket_riesz_expansion (u y : ℝ) (N K : ℕ) :
    rawMarkedPacket u y N K = ∑ n ∈ band u N K,
      (-((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        (VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n : ℂ)*
      ∑ p ∈ n.primeFactors, ∑ d ∈ markedAllocations N n p,
        ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) (3/2+Complex.I*y) q := by
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp hn).2.1
  have hnp : ¬n.Prime := by
    intro hp
    have hc := hb.count_lower
    rw [hp.primeFactors, Finset.card_singleton] at hc
    omega
  have hlog : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hb.nontrivial)).ne'
  have hL : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  rw [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show (markedWeight N n p : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        ((markedWeight N n p : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n) by ring,
    marked_kernel hb.squarefree hb.nontrivial,
    SquarefreeVaughanLogSource.coefficient, if_pos ⟨hb.squarefree, hnp⟩]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  field_simp [hlog, hL]

end
end RiemannGaussian.ZetaRieszJointAllocationError
