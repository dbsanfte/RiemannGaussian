/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityWindow

/-!
# Independent allocation saving for the literal five-prime packet

Every prime in the smaller packet has logarithmic share at most 113/200.
Consequently the original allocated part is exponentially small. The
finite packet and all its masks remain unchanged; no prime is completed.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open scoped BigOperators Classical
open Filter Topology ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszBalancedCompanion ZetaRieszAnnulusJoint ZetaRieszSkewAllocation

theorem packet_allocation_log_rate :
    Real.log (4913/5000 : ℝ)+(13/32 : ℝ)*Real.log (25/24 : ℝ) ≤ -(1/2200 : ℝ) := by
  have h₁ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4913/5000)
  have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 25/24)
  linarith

/-- A concrete tail estimate at the actual upper prime-share endpoint. -/
theorem unpaid_mass_packet_le (N : ℕ) {x : ℝ} (hx : (87/200 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(N : ℝ)/2200) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (25/24 : ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0 : ℝ) ≤ 24/25)
    (Real.exp_pos ((13/32 : ℝ)*N*Real.log (25/24 : ℝ))).le ?_
  · have hb : ((24/25 : ℝ)*x+(1-x))^(N+1) ≤ (4913/5000 : ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp ((13/32 : ℝ)*N*Real.log (25/24 : ℝ)) * (4913/5000 : ℝ)^(N+1) =
        (4913/5000 : ℝ)*Real.exp ((N : ℝ)*
          (Real.log (4913/5000 : ℝ)+(13/32 : ℝ)*Real.log (25/24 : ℝ))) := by
      rw [pow_succ]
      have hp : (4913/5000 : ℝ)^N = Real.exp ((N : ℝ)*Real.log (4913/5000 : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<4913/5000)]
      rw [hp]
      rw [show (N : ℝ)*(Real.log (4913/5000 : ℝ)+(13/32 : ℝ)*Real.log (25/24 : ℝ)) =
        (13/32 : ℝ)*N*Real.log (25/24 : ℝ)+(N : ℝ)*Real.log (4913/5000 : ℝ) by ring,
        Real.exp_add]
      ring
    have hrate : Real.exp ((N : ℝ)*
        (Real.log (4913/5000 : ℝ)+(13/32 : ℝ)*Real.log (25/24 : ℝ))) ≤
        Real.exp (-(N : ℝ)/2200) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left packet_allocation_log_rate (Nat.cast_nonneg (α:=ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos ((13/32 : ℝ)*N*Real.log (25/24 : ℝ))).le
    rw [he] at hprod
    nlinarith [Real.exp_pos (-(N : ℝ)/2200)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k : ℝ) ≤ (13/32 : ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32 : ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (24/25 : ℝ) = Real.exp (-Real.log (25/24 : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ)<25/24)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- Ordering and the literal smaller box bound every prime factor, not
just the distinguished largest one. -/
theorem quintuple_prime_share {u : ℝ} {N K n z : ℕ}
    (hn : n ∈ quintupleBand u N K) (hz : z ∈ n.primeFactors) :
    200*Real.log z ≤ 113*Real.log n := by
  obtain ⟨_, _, p, a, b, c, r, hg, hb, _⟩ := Finset.mem_filter.mp hn
  have hzp := Nat.prime_of_mem_primeFactors hz
  have hzd := Nat.dvd_of_mem_primeFactors hz
  rw [hg.factorization] at hzd
  have hle : z ≤ p := by
    rcases hzp.dvd_mul.mp hzd with h | h
    · exact ((Nat.prime_dvd_prime_iff_eq hzp hg.hp).mp h).le
    rcases hzp.dvd_mul.mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hzp hg.ha).mp h
      have := hg.hpa
      omega
    rcases hzp.dvd_mul.mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hzp hg.hb).mp h
      have := hg.hpa; have := hg.hab
      omega
    rcases hzp.dvd_mul.mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hzp hg.hc).mp h
      have := hg.hpa; have := hg.hab; have := hg.hbc
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hzp hg.hr).mp h
      have := hg.hpa; have := hg.hab; have := hg.hbc; have := hg.hcr
      omega
  have hl : Real.log (z : ℝ) ≤ Real.log p :=
    Real.log_le_log (by exact_mod_cast hzp.pos) (by exact_mod_cast hle)
  linarith [hb.2.1]

/-- The original allocation, with its original prime selection, pays at
most five exponentially small tails on the actual quintuple packet. -/
theorem quintuple_boundedShare_le {u : ℝ} {N K n : ℕ}
    (hn : n ∈ quintupleBand u N K) :
    boundedShare (intermediatePrimes u N) N n ≤ 5*Real.exp (-(N : ℝ)/2200) := by
  obtain ⟨_, hcard, p, a, b, c, r, hg, _⟩ := Finset.mem_filter.mp hn
  by_cases hn1 : 1 < n
  · have hnp : ¬ n.Prime := by
      intro hp
      rw [hp.primeFactors, Finset.card_singleton] at hcard
      omega
    rw [boundedShare, if_pos ⟨hg.squarefree, hn1, hnp⟩,
      share_eq_binomial_sum _ N hg.squarefree hn1]
    calc
      _ ≤ ∑ _z ∈ n.primeFactors, Real.exp (-(N : ℝ)/2200) := by
        apply Finset.sum_le_sum
        intro z hz
        split_ifs
        · have hzp := Nat.prime_of_mem_primeFactors hz
          have hzd := Nat.dvd_of_mem_primeFactors hz
          have hlog : Real.log (n/z : ℕ) = Real.log n-Real.log z := by
            rw [Nat.cast_div hzd (by exact_mod_cast hzp.ne_zero), Real.log_div
              (by exact_mod_cast hg.squarefree.ne_zero) (by exact_mod_cast hzp.ne_zero)]
          have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
          apply unpaid_mass_packet_le
          · apply (le_div_iff₀ hln).mpr
            rw [hlog]
            linarith [quintuple_prime_share hn hz]
          · apply (div_le_one hln).mpr
            rw [hlog]
            linarith [Real.log_natCast_nonneg z]
        · exact (Real.exp_pos _).le
      _ = _ := by simp [hcard]
  · simp only [boundedShare, hn1, and_false, false_and, ↓reduceIte]
    positivity

/-- No support is changed: this is just the original allocated part
restricted to the literal five-prime packet. -/
def quintupleAllocation (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ quintupleBand u N K,
    assignedCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The explicit geometric rate after source normalization and factorial tilt. -/
def quintupleAllocationRate : ℝ :=
  ZetaRieszWideOwnerAudit.radiusCeiling / rectangleTilt * Real.exp (-(1/2200 : ℝ))

theorem quintupleAllocationRate_bounds :
    0 ≤ quintupleAllocationRate ∧ quintupleAllocationRate < 1 := by
  constructor
  · unfold quintupleAllocationRate ZetaRieszWideOwnerAudit.radiusCeiling rectangleTilt
    positivity
  · rw [quintupleAllocationRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/2200 : ℝ)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling, rectangleTilt] at h ⊢
    linarith

/-- A height-uniform, source-normalized geometric bound for the actual
old allocation lost from the five-prime packet. -/
theorem quintuple_allocation_bound (N K : ℕ) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*quintupleAllocation u y N K‖ ≤
      5*ZetaRieszWideOwnerAudit.radiusCeiling*quintupleAllocationRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ quintupleBand u N K) :
      ‖assignedCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (5*Real.exp (-(N : ℝ)/2200)*rectangleTilt⁻¹^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        rectangleTilt⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num [rectangleTilt] : 0 < rectangleTilt) using 1
      norm_num [rectangleTilt]
    rw [assignedCoefficient, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (boundedShare_bounds _ N n).1]
    have hb := mul_le_mul (quintuple_boundedShare_le hn)
      (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)
      (norm_nonneg _) (by positivity : 0 ≤ 5*Real.exp (-(N : ℝ)/2200))
    exact (mul_le_mul hb hk (norm_nonneg _) (mul_nonneg (by positivity)
      (zetaMoebiusLogMajorant_nonneg n))).trans_eq (by ring)
  have hs : ‖quintupleAllocation u y N K‖ ≤
      (5*Real.exp (-(N : ℝ)/2200)*rectangleTilt⁻¹^N)*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum ha).trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by unfold rectangleTilt; positivity)
    exact Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
      (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ ≤ u^(N+1)*((5*Real.exp (-(N : ℝ)/2200)*rectangleTilt⁻¹^N)*
        zetaMoebiusLogMajorantMass (1+1/262144)) :=
      mul_le_mul_of_nonneg_left hs (pow_nonneg hu _)
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*
        ((5*Real.exp (-(N : ℝ)/2200)*rectangleTilt⁻¹^N)*
          zetaMoebiusLogMajorantMass (1+1/262144)) := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huU _)
      apply mul_nonneg _ (zetaMoebiusLogMajorantMass_nonneg _)
      unfold rectangleTilt
      positivity
    _ = _ := by
      have he : Real.exp (-(N : ℝ)/2200) = Real.exp (-(1/2200 : ℝ))^N := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [quintupleAllocationRate, div_eq_mul_inv, mul_pow, pow_succ]
      ring

/-- The allocation error is paid independently of prime counts, zeros,
and phase, even when the phase height changes with the order. -/
theorem tendsto_quintuple_allocation (K : ℕ → ℕ) (y : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*quintupleAllocation u (y N) N (K N)) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one quintupleAllocationRate_bounds.1
    quintupleAllocationRate_bounds.2).const_mul (5*ZetaRieszWideOwnerAudit.radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [mul_zero, zero_mul] at ht
  exact squeeze_zero_norm (fun N => quintuple_allocation_bound N (K N) (y N) hu huU) ht

end
end RiemannGaussian.ZetaRieszParityPacket
