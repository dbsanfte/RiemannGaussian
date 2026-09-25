/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeTransfer

/-!
# Removing the largest-prime ordering after joining literal shares

Every incorrectly marked prime has share at most one half. Its exact
rectangle allocation has an exponential upper tail. Thus summing every
marked-prime incidence changes the joint arithmetic packet by o(1) at
source scale, without completing a prime, deleting low orders, or using
a zero hypothesis. The least-prime and all other masks are retained.
-/

namespace RiemannGaussian.ZetaRieszJointOwnerTransfer
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszJointBoundary
open ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint ZetaRieszAnnulusJoint
open ZetaRieszParityPacket ZetaRieszWideOwnerAudit

/-- The original rectangle with a specified prime in its large-order slot. -/
def markedAllocations (N n p : ℕ) : Finset (ℕ → ℕ) :=
  (Finset.piAntidiag n.primeFactors (N+1)).filter
    (fun d => d n.minFac ∈ rectangleOrders N (d p))

/-- The exact multinomial mass of one marked-prime incidence. -/
def markedWeight (N n p : ℕ) : ℝ :=
  ∑ d ∈ markedAllocations N n p,
    allocationWeight n.primeFactors (fun q => Real.log q/Real.log n) d

theorem markedWeight_nonneg (N n p : ℕ) : 0 ≤ markedWeight N n p :=
  Finset.sum_nonneg (fun d _ => allocationWeight_nonneg _ _
    (fun _q _ => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)) d)

theorem markedWeight_largest (N n : ℕ) : markedWeight N n (largestPrime n) = weight N n := rfl

/-- The original squarefree product forces a wrong owner below one half. -/
theorem wrong_owner_share {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hl : largestPrime n ∈ n.primeFactors) (hp : p ∈ n.primeFactors)
    (hne : p ≠ largestPrime n) : Real.log p/Real.log n ≤ 1/2 := by
  have hmax : p ≤ largestPrime n := by
    rw [largestPrime, dif_pos (show n.primeFactors.Nonempty from ⟨p,hp⟩)]
    exact Finset.le_max' _ _ hp
  have hlog : Real.log p ≤ Real.log (largestPrime n) := Real.log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) (by exact_mod_cast hmax)
  have hsub : ({p, largestPrime n} : Finset ℕ) ⊆ n.primeFactors := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · rw [Finset.mem_singleton] at hq
      exact hq ▸ hl
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => Real.log q)
    hsub (fun q _ _ => Real.log_natCast_nonneg q)
  rw [Finset.sum_pair hne, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at hs
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast hn1))).mpr
  linarith

theorem markedWeight_small_share {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (N : ℕ)
    (hshare : Real.log p/Real.log n ≤ 1/2) :
    markedWeight N n p ≤ 2*Real.exp (-(N : ℝ)/1600) := by
  let x : ℕ → ℝ := fun q => Real.log q/Real.log n
  have hx (q : ℕ) (_hq : q ∈ n.primeFactors) : 0 ≤ x q :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hw := allocationWeight_nonneg n.primeFactors x hx
  have ht := coordinate_upper_tail n.primeFactors x hx (shares_sum hn hn1) hp
    (a := 21/40) (b := 21/20) (q := 11/10) (c := 1/1600) (D := 1)
    (by norm_num) (by norm_num) (by dsimp [x]; linarith) exterior_tilt_rates.1 N
  have hsub : markedAllocations N n p ⊆
      (Finset.piAntidiag n.primeFactors (N+1)).filter
        (fun d => (21/40 : ℝ)*N-1 < d p) := by
    intro d hd
    obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
    have hj := (Finset.mem_filter.mp hr).2.2.1
    have hjR : (21 : ℝ)*N ≤ 40*d p := by exact_mod_cast hj
    exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
  apply ht.trans
  rw [one_mul, Real.exp_log (by norm_num : (0 : ℝ) < 11/10),
    show -(1/1600 : ℝ)*N = -(N : ℝ)/1600 by ring]
  nlinarith [Real.exp_pos (-(N : ℝ)/1600)]

/-- The count ceiling changes when the old largest-share interval is
removed. No use is made of the old, now inapplicable ceiling 39. -/
theorem jointBox_count_le {n : ℕ} (hn : JointBox n) : n.primeFactors.card ≤ 83 := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn.nontrivial)
  have hs : (∑ _p ∈ n.primeFactors, (3/250 : ℝ)*Real.log n) ≤
      ∑ p ∈ n.primeFactors, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact hn.least_lower.trans (Real.log_le_log
      (by exact_mod_cast (Nat.minFac_prime hn.nontrivial.ne').pos)
      (by exact_mod_cast Nat.minFac_le_of_dvd hpp.two_le (Nat.dvd_of_mem_primeFactors hp)))
  rw [Finset.sum_const, nsmul_eq_mul, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn.squarefree] at hs
  by_contra hc
  have hcR : (84 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast (by omega : 84 ≤ n.primeFactors.card)
  nlinarith

/-- All incidences not owned by the canonical largest prime. -/
def wrongWeight (N n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors.erase (largestPrime n), markedWeight N n p

theorem incidence_weight_ledger {n : ℕ} (hp : largestPrime n ∈ n.primeFactors) (N : ℕ) :
    (∑ p ∈ n.primeFactors, markedWeight N n p) = weight N n+wrongWeight N n := by
  simpa only [markedWeight_largest, add_comm, wrongWeight] using
    (Finset.sum_erase_add _ (markedWeight N n) hp).symm

theorem wrongWeight_bound {n : ℕ} (hn : JointBox n) (N : ℕ) :
    0 ≤ wrongWeight N n ∧ wrongWeight N n ≤ 166*Real.exp (-(N : ℝ)/1600) := by
  refine ⟨Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p), ?_⟩
  calc
    _ ≤ ∑ _p ∈ n.primeFactors.erase (largestPrime n), 2*Real.exp (-(N : ℝ)/1600) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hne,hp⟩ := Finset.mem_erase.mp hp
      exact markedWeight_small_share hn.squarefree hn.nontrivial hp N
        (wrong_owner_share hn.squarefree hn.nontrivial hn.largest_mem hp hne)
    _ ≤ 166*Real.exp (-(N : ℝ)/1600) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : (n.primeFactors.erase (largestPrime n)).card ≤ 83 :=
        (Finset.card_erase_le).trans (jointBox_count_le hn)
      have hcR : ((n.primeFactors.erase (largestPrime n)).card : ℝ) ≤ 83 := by exact_mod_cast hc
      nlinarith [Real.exp_pos (-(N : ℝ)/1600)]

/-- The original signed arithmetic sum of the wrong-incidence weights. -/
def wrongPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ band u N K, (wrongWeight N n : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Every actual prime incidence and its original correlated allocation.
This is still finite; the Riesz, least-prime and physical masks remain. -/
def markedPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ band u N K, ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem markedPacket_ledger (u y : ℝ) (N K : ℕ) :
    markedPacket u y N K = packet u y N K+wrongPacket u y N K := by
  rw [markedPacket, packet, wrongPacket, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [incidence_weight_ledger (Finset.mem_filter.mp hn).2.1.largest_mem]
  simp only [atom, Complex.ofReal_add, add_mul]

/-- The canonical-owner removal has an independent geometric error.
This is uniform in y, and uses no completed prime phases. -/
theorem wrongPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*wrongPacket u y N K‖ ≤
      (166*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ band u N K) :
      ‖(u : ℂ)^(N+1)*((wrongWeight N n : ℂ)*
        (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
        (166*radiusCeiling)*exteriorRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hb := wrongWeight_bound (Finset.mem_filter.mp hn).2.1 N
    have hc := norm_residualCoefficient_le (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) N n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/1600) = Real.exp (-(1/1600 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.1, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((166*Real.exp (-(N : ℝ)/1600))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        · exact mul_nonneg hb.1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · unfold radiusCeiling; positivity
        · exact hb.2
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = _ := by rw [he, exteriorRate, mul_pow, mul_pow, pow_succ]; ring
  rw [wrongPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ band u N K, (166*radiusCeiling)*exteriorRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg exteriorRate_bounds.1 _))

/-- Full literal signed joint transfer with the owner restriction paid. -/
theorem marked_joint_transfer_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*(markedPacket u y N K-
      (fullParityPacket u y N K+neighbors u y N K))‖ ≤
      (166*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [← joint_ledger, markedPacket_ledger, add_sub_cancel_left]
  exact wrongPacket_bound hu hU y N K

/-- The incidence sum still uses at most one allocation: the marked
order is a strict majority. We have not duplicated the carrier. -/
theorem marked_mass_le_one {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (N : ℕ) (hN : 21 ≤ N) : (∑ p ∈ n.primeFactors, markedWeight N n p) ≤ 1 := by
  let U := (Finset.range (N+2)).filter (fun k => 21*N ≤ 40*(N+1-k))
  have hU : ∀ k ∈ U, 2*k < N+1 := by
    intro k hk
    have h := Finset.mem_filter.mp hk
    have := Finset.mem_range.mp h.1
    omega
  have hx (p : ℕ) (_hp : p ∈ n.primeFactors) : 0 ≤ Real.log p/Real.log n :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hw := allocationWeight_nonneg n.primeFactors _ hx
  calc
    _ ≤ ∑ p ∈ n.primeFactors, ∑ d ∈
        (Finset.piAntidiag n.primeFactors (N+1)).filter (fun d => N+1-d p ∈ U),
          allocationWeight n.primeFactors (fun q => Real.log q/Real.log n) d := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hw d)
      intro d hd
      obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
      have hs := (Finset.mem_piAntidiag.mp ha).1
      have hdp : d p ≤ N+1 := by
        rw [← hs]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
      have hj := (Finset.mem_filter.mp hr).2.2.1
      apply Finset.mem_filter.mpr ⟨ha, ?_⟩
      simp only [U, Finset.mem_filter, Finset.mem_range]
      omega
    _ ≤ (∑ p ∈ n.primeFactors, Real.log p/Real.log n)^(N+1) :=
      selected_allocation_le _ _ hx U (N+1) hU
    _ = 1 := by rw [shares_sum hn hn1, one_pow]

theorem marked_kernel {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (N : ℕ) (s : ℂ) :
    (markedWeight N n p : ℂ)*zetaPrimeLogKernel N s n =
      ((N+1 : ℕ) : ℂ)/(Real.log n : ℂ)*
        ∑ d ∈ markedAllocations N n p,
          ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) s q := by
  rw [markedWeight, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have h := ZetaRieszJointPrimeTransfer.allocation_kernel hn hn1 (Finset.mem_filter.mp hd).1 s
  have hk := ZetaRieszHeadOrders.log_mul_kernel N n s
  have hlog : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn1)).ne'
  rw [← h]
  field_simp
  linear_combination (allocationWeight n.primeFactors (fun q => Real.log q/Real.log n) d : ℂ)*hk

/-- Exact sum over actual prime incidences, with all other correlations
still inside the same finite summand. No complete prime moment is used. -/
theorem markedPacket_prime_expansion (u y : ℝ) (N K : ℕ) :
    markedPacket u y N K = ∑ n ∈ band u N K,
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        (((N+1 : ℕ) : ℂ)/(Real.log n : ℂ)))*
      ∑ p ∈ n.primeFactors, ∑ d ∈ markedAllocations N n p,
        ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) (3/2+Complex.I*y) q := by
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp hn).2.1
  rw [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show (markedWeight N n p : ℂ)*
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        ((markedWeight N n p : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n) by ring,
    marked_kernel hb.squarefree hb.nontrivial]
  ring

theorem tendsto_marked_sub_joint {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(markedPacket u (heights t) (orders t) (counts t)-
      (fullParityPacket u (heights t) (orders t) (counts t)+
        neighbors u (heights t) (orders t) (counts t)))) atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one exteriorRate_bounds.1
    exteriorRate_bounds.2).const_mul (166*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  exact squeeze_zero_norm (fun t => marked_joint_transfer_bound hu hU _ _ _) ht

/-- The product-log factor cancels exactly against the factorial transfer.
The surviving signed hinge, allocation and coupled order sum are explicit. -/
theorem markedPacket_riesz_expansion (u y : ℝ) (N K : ℕ) :
    markedPacket u y N K = ∑ n ∈ band u N K,
      (-((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        ((1-boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ)*
        (VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n : ℂ)*
      ∑ p ∈ n.primeFactors, ∑ d ∈ markedAllocations N n p,
        ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) (3/2+Complex.I*y) q := by
  rw [markedPacket_prime_expansion]
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
  rw [residualCoefficient, SquarefreeVaughanLogSource.coefficient, if_pos ⟨hb.squarefree, hnp⟩]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  field_simp [hlog, hL]

end
end RiemannGaussian.ZetaRieszJointOwnerTransfer
