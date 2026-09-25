/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointShift
import RiemannGaussian.ZetaRieszParityShareError

/-!
# Paying the literal shifted correction on the existing fixed share box

All factorial orders and the original rectangle remain. The fixed lower
prime share supplies an exponential arithmetic gain, independently of
prime-mode completion. This does not extend to a shrinking share cutoff,
and does not prove decay of the filtered packet itself.
-/

namespace RiemannGaussian.ZetaRieszJointShiftError
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszShiftedCenter ZetaRieszParityPacket ZetaRieszParityOrderTail
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszWideOwnerAudit
open ZetaRieszAnnulusJoint ZetaRieszPrimeEndpoint

theorem rectangle_order_le {N n : ℕ} {d : ℕ → ℕ}
    (hd : d ∈ rectangleAllocations N n) {p : ℕ} (hp : p ∈ n.primeFactors) :
    legOrder n d p ≤ N+2 := by
  have hs := (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hd).1).1
  have hle := Finset.single_le_sum (s := n.primeFactors) (f := d)
    (fun _ _ => Nat.zero_le _) hp
  rw [hs] at hle
  dsimp [legOrder]
  split_ifs <;> omega

/-- Each literal prime is exponentially large in N on this FIXED box. -/
theorem prime_log_lower {u : ℝ} {N K n p : ℕ} (hn : n ∈ fullParityBand u N K)
    (hp : p ∈ n.primeFactors) : (117/5000 : ℝ)*N ≤ Real.log p := by
  have hb := (Finset.mem_filter.mp hn).2.1
  have hcore := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hb.nontrivial)
  have hs := (fullParityBox_shares hb).1 p hp
  have hx := (le_div_iff₀ ht).mp hs
  change (39/20 : ℝ)*N < Real.log n at hcore
  linarith

theorem leg_correction_bound {u y : ℝ} (hy : 54 < |y|) {N K n p k : ℕ}
    (hN : 1 ≤ N) (hn : n ∈ fullParityBand u N K) (hp : p ∈ n.primeFactors)
    (hk : k ≤ N+2) : ‖ratio y^k/(p : ℂ)‖ ≤ Real.exp (-(N : ℝ)/50) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hC : ‖ratio y‖ ≤ Real.exp (1/1000 : ℝ) :=
    (norm_ratio_lt hy).le.trans (by linarith [Real.add_one_le_exp (1/1000 : ℝ)])
  have hkR : (k : ℝ) ≤ N+2 := by exact_mod_cast hk
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [norm_div, norm_pow, Complex.norm_natCast, ← Real.exp_log hpR]
  calc
    _ ≤ (Real.exp (1/1000 : ℝ))^k/Real.exp (Real.log p) := by gcongr
    _ = Real.exp ((k : ℝ)/1000-Real.log p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [prime_log_lower hn hp])

theorem rectangle_multiplier_bound {u y : ℝ} (hy : 54 < |y|) {N K n : ℕ}
    (hN : 1 ≤ N) (hn : n ∈ fullParityBand u N K) {d : ℕ → ℕ}
    (hd : d ∈ rectangleAllocations N n) :
    ‖(∏ p ∈ n.primeFactors, (1-ratio y^(legOrder n d p)/(p : ℂ)))-1‖ ≤
      (2 : ℝ)^39*Real.exp (-(N : ℝ)/50) := by
  have hε : Real.exp (-(N : ℝ)/50) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have h := product_phase_error n.primeFactors
    (fun p => -(1-ratio y^(legOrder n d p)/(p : ℂ))) hε (fun p hp => by
      simpa only [neg_sub, sub_add_cancel] using
        leg_correction_bound hy hN hn hp (rectangle_order_le hd hp))
  have he : (∏ p ∈ n.primeFactors, -(1-ratio y^(legOrder n d p)/(p : ℂ)))-
      (-1 : ℂ)^n.primeFactors.card = (-1 : ℂ)^n.primeFactors.card*
        ((∏ p ∈ n.primeFactors, (1-ratio y^(legOrder n d p)/(p : ℂ)))-1) := by
    rw [Finset.prod_neg]; ring
  rw [he, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h
  apply h.trans
  have hc := fullParityBox_count_le (Finset.mem_filter.mp hn).2.1
  have hp : (2 : ℝ)^n.primeFactors.card ≤ 2^39 := pow_le_pow_right₀ (by norm_num) hc
  nlinarith [Real.exp_pos (-(N : ℝ)/50)]

/-- The exact signed correction, averaged over the ORIGINAL factorial
rectangle. No orders, masks, phases or prime classes have been removed. -/
def correctionWeight (y : ℝ) (N n : ℕ) : ℂ :=
  ∑ d ∈ rectangleAllocations N n,
    (allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d : ℂ)*
      ((∏ p ∈ n.primeFactors, (1-ratio y^(legOrder n d p)/(p : ℂ)))-1)

theorem correctionWeight_bound {u y : ℝ} (hy : 54 < |y|) {N K n : ℕ}
    (hN : 1 ≤ N) (hn : n ∈ fullParityBand u N K) :
    ‖correctionWeight y N n‖ ≤ (2 : ℝ)^39*Real.exp (-(N : ℝ)/50) := by
  have hb := (Finset.mem_filter.mp hn).2.1
  have hx (p : ℕ) (hp : p ∈ n.primeFactors) : 0 ≤ Real.log p/Real.log n :=
    (by norm_num : (0 : ℝ) ≤ 3/250).trans ((fullParityBox_shares hb).1 p hp)
  have hw := allocationWeight_nonneg n.primeFactors _ hx
  have hmass : (∑ d ∈ rectangleAllocations N n,
      allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d) ≤ 1 := by
    calc
      _ ≤ ∑ d ∈ Finset.piAntidiag n.primeFactors (N+1),
          allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d _ _ => hw d)
      _ = 1 := by
        simp only [allocationWeight]
        rw [← Finset.sum_pow_eq_sum_piAntidiag, (fullParityBox_shares hb).2, one_pow]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ rectangleAllocations N n,
        allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d*
          ((2 : ℝ)^39*Real.exp (-(N : ℝ)/50)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw d)]
      exact mul_le_mul_of_nonneg_left (rectangle_multiplier_bound hy hN hn hd) (hw d)
    _ ≤ _ := by rw [← Finset.sum_mul]; nlinarith [Real.exp_pos (-(N : ℝ)/50)]

/-- A literal finite signed arithmetic correction on the existing packet. -/
def correctionPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullParityBand u N K, correctionWeight y N n*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The original rectangle with the exact product of per-kernel shifts. -/
def shiftedWeight (y : ℝ) (N n : ℕ) : ℂ :=
  ∑ d ∈ rectangleAllocations N n,
    (allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d : ℂ)*
      ∏ p ∈ n.primeFactors, (1-ratio y^(legOrder n d p)/(p : ℂ))

theorem shiftedWeight_ledger {n : ℕ} (hn : FullParityBox n) (N : ℕ) (y : ℝ) :
    shiftedWeight y N n =
      (rectangleMass N (1-Real.log (largestPrime n)/Real.log n)
        (Real.log n.minFac/(Real.log n-Real.log (largestPrime n))) : ℂ)+correctionWeight y N n := by
  have hm := rectangleMass_eq_good_add_bad hn N
  rw [goodRectangleMass, badRectangleMass, Finset.sum_filter_add_sum_filter_not] at hm
  rw [hm, shiftedWeight, correctionWeight, Complex.ofReal_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The finite rectangle packet with its kernel multipliers included
before summing factorial allocations; no mode interpretation is assumed. -/
def shiftedPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullParityBand u N K, shiftedWeight y N n*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Exact source ledger: the only difference is the explicitly paid
finite correction. All literal support and allocation masks remain. -/
theorem shiftedPacket_ledger (u y : ℝ) (N K : ℕ) :
    shiftedPacket u y N K = fullParityPacket u y N K+correctionPacket u y N K := by
  have he : fullParityPacket u y N K = ∑ n ∈ fullParityBand u N K,
      (fullParitySelection u N K n : ℂ)*
        (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n _ hn
    change n ∉ fullParityBand u N K at hn
    rw [fullParitySelection, if_neg hn, Complex.ofReal_zero, zero_mul]
  rw [he, shiftedPacket, correctionPacket, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [shiftedWeight_ledger (Finset.mem_filter.mp hn).2.1,
    fullParitySelection, if_pos hn]
  ring

/-- The strict geometric rate after paying the arithmetic majorant. -/
def correctionRate : ℝ := radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/50 : ℝ))

theorem correctionRate_bounds : 0 ≤ correctionRate ∧ correctionRate < 1 := by
  constructor
  · unfold correctionRate radiusCeiling; positivity
  · rw [correctionRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/50 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

theorem correctionPacket_bound {u y : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hy : 54 < |y|) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*correctionPacket u y N K‖ ≤
      (2^39*radiusCeiling)*correctionRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ fullParityBand u N K) :
      ‖(u : ℂ)^(N+1)*(correctionWeight y N n*
        (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
        (2^39*radiusCeiling)*correctionRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hb := correctionWeight_bound hy hN hn
    have hc := norm_residualCoefficient_le (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) N n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/50) = Real.exp (-(1/50 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*(((2 : ℝ)^39*Real.exp (-(N : ℝ)/50))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        · unfold radiusCeiling; positivity
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = _ := by rw [he, correctionRate, mul_pow, mul_pow, pow_succ]; ring
  rw [correctionPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ fullParityBand u N K, (2^39*radiusCeiling)*correctionRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum (fun n hn => ha n hn)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg correctionRate_bounds.1 _))

theorem tendsto_correctionPacket {u y : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hy : 54 < |y|) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*correctionPacket u y (orders t) (counts t))
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one correctionRate_bounds.1
    correctionRate_bounds.2).const_mul (2^39*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [ho.eventually (eventually_ge_atTop 1)] with t ht
  exact correctionPacket_bound hu hU hy _ _ ht

theorem tendsto_shiftedPacket_sub_original {u y : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hy : 54 < |y|) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (shiftedPacket u y (orders t) (counts t)-fullParityPacket u y (orders t) (counts t)))
      atTop (𝓝 0) := by
  simpa only [shiftedPacket_ledger, add_sub_cancel_left] using
    tendsto_correctionPacket hu hU hy orders counts ho

end
end RiemannGaussian.ZetaRieszJointShiftError
