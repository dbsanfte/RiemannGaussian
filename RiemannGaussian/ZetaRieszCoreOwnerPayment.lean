/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointDominantFloor
import RiemannGaussian.ZetaRieszJoinedPhysical
import RiemannGaussian.ZetaRieszRejoinedPopulationFloor

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# A larger source-paid owner sector of the literal core

The exact binomial allocation pays every core label with an eligible prime
carrying at least 751/1250 of its logarithm. All counts, periods, phases
and literal masks remain. The whole floor is not asserted: the signed
complement is retained, with a geometric error rather than a relative debit.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCoreOwnerPayment
open ZetaRieszJointAllocation ZetaRieszParityPacket ZetaRieszAnnulusJoint
open ZetaRieszWideOwnerAudit ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint

/-- The enlarged owner threshold, below the previously paid 601/1000. -/
def ownerThreshold : ℝ := 751/1250

/-- A tighter summable reference: its error pays the newly added sector. -/
def referenceExponent : ℝ := 1+1/1048576

/-- Certified upper-tail log rate for the exact 103/100 tilt. -/
theorem upper_tilt_log :
    log (126497/125000 : ℝ)-(13/32 : ℝ)*log (103/100 : ℝ) ≤ -(1033/10000000) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 3/203)
    (by norm_num : (3/203 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : log (126497/125000 : ℝ) ≤ 119049/10000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 119049/10000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- Both literal missing-order tails decay uniformly on the wider
cofactor interval [7/25,499/1250]; no factorial order is discarded. -/
theorem missing_mass_bound {N : ℕ} (hN : 320 ≤ N) {x : ℝ}
    (hx : (7/25 : ℝ) ≤ x) (hx1 : x ≤ (499/1250 : ℝ)) :
    1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x ≤
      (9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N) := by
  have hx0 : 0 ≤ x := by linarith
  have hxone : x ≤ 1 := by linarith
  have ht : 0 ≤ log (103/100 : ℝ) := log_nonneg (by norm_num)
  have hl : 0 ≤ log (5/4 : ℝ) := log_nonneg (by norm_num)
  have hm := missed_mass_bound N hN hx0 hxone
    (exp_pos (-(13/32 : ℝ)*N*log (103/100 : ℝ))).le
    (exp_pos (((N : ℝ)/5+1)*log (5/4 : ℝ))).le
    (by norm_num : (0 : ℝ) ≤ 103/100) (by norm_num : (0 : ℝ) ≤ 4/5) (by
      intro k hk hcut
      have hc : (13/32 : ℝ)*N ≤ k := by
        have hh : 13*(N : ℝ) < 32*k := by exact_mod_cast (by omega : 13*N < 32*k)
        linarith
      rw [← exp_log (by norm_num : (0 : ℝ) < 103/100),← exp_nat_mul,← exp_add]
      apply one_le_exp_iff.mpr
      simp only [log_exp]
      nlinarith [mul_le_mul_of_nonneg_right hc ht]) (by
      intro k hk hcut
      have hkN : k ≤ N+1 := by have := Finset.mem_range.mp hk; omega
      have hc : (k : ℝ) ≤ (N : ℝ)/5+1 := by
        have hh : 5*(k : ℝ) ≤ N+5 := by exact_mod_cast (by omega : 5*k ≤ N+5)
        linarith
      rw [show (4/5 : ℝ)=exp (-log (5/4 : ℝ)) by
        rw [exp_neg,exp_log (by norm_num : (0 : ℝ) < 5/4)]; norm_num,
        ← exp_nat_mul,← exp_add]
      apply one_le_exp_iff.mpr
      nlinarith [mul_le_mul_of_nonneg_right hc hl])
  have hhi : (103/100 : ℝ)*x+(1-x) ≤ 126497/125000 := by linarith
  have hlo : (4/5 : ℝ)*x+(1-x) ≤ 118/125 := by linarith
  have hb := hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hhi (N+1)) (exp_pos _).le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlo (N+1)) (exp_pos _).le))
  have hlow : log (118/125 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ) ≤ -(1033/10000000) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 118/125)
    linarith [log_tilt_bounds.2]
  have hehi : exp (-(13/32 : ℝ)*N*log (103/100 : ℝ))*(126497/125000 : ℝ)^(N+1) =
      (126497/125000 : ℝ)*exp ((N : ℝ)*(log (126497/125000 : ℝ)-(13/32 : ℝ)*log (103/100 : ℝ))) := by
    rw [pow_succ,show (126497/125000 : ℝ)^N=exp ((N : ℝ)*log (126497/125000 : ℝ)) by
      rw [exp_nat_mul,exp_log (by norm_num)],
      show (N : ℝ)*(log (126497/125000 : ℝ)-(13/32 : ℝ)*log (103/100 : ℝ))=
        -(13/32 : ℝ)*N*log (103/100 : ℝ)+(N : ℝ)*log (126497/125000 : ℝ) by ring,exp_add]
    ring
  have helo : exp (((N : ℝ)/5+1)*log (5/4 : ℝ))*(118/125 : ℝ)^(N+1) =
      ((5/4 : ℝ)*(118/125))*exp ((N : ℝ)*(log (118/125 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))) := by
    rw [pow_succ,show (118/125 : ℝ)^N=exp ((N : ℝ)*log (118/125 : ℝ)) by
      rw [exp_nat_mul,exp_log (by norm_num)],
      show ((N : ℝ)/5+1)*log (5/4 : ℝ)=(N : ℝ)/5*log (5/4 : ℝ)+log (5/4 : ℝ) by ring,
      exp_add,exp_log (by norm_num)]
    rw [show (N : ℝ)*(log (118/125 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))=
      (N : ℝ)/5*log (5/4 : ℝ)+(N : ℝ)*log (118/125 : ℝ) by ring,exp_add]
    ring
  rw [hehi,helo] at hb
  have hu := exp_le_exp.mpr (mul_le_mul_of_nonneg_left upper_tilt_log (Nat.cast_nonneg (α := ℝ) N))
  have hd := exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg (α := ℝ) N))
  rw [show (N : ℝ)*(-(1033/10000000 : ℝ))=-(1033/10000000 : ℝ)*N by ring] at hu hd
  nlinarith [exp_pos (-(1033/10000000 : ℝ)*N)]

/-- The enlarged binomial saving beats the actual source growth, not
just an unnormalized probability or a polynomial envelope. -/
theorem source_rate_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    u^(N+1)*(9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N)*
      (1048576/524287 : ℝ)^N ≤ (9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/1000000) := by
  have hb : radiusCeiling*(1048576/524287 : ℝ) ≤ exp (1/9800 : ℝ) := by
    have h := add_one_le_exp (1/9800 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num [radiusCeiling]) hb N
  rw [← exp_nat_mul] at hp
  have hh := mul_le_mul_of_nonneg_right hp
    (exp_pos (-(1033/10000000 : ℝ)*N)).le
  rw [← exp_add] at hh
  have he : exp ((N : ℝ)*(1/9800)+(-(1033/10000000 : ℝ)*N)) ≤ exp (-(N : ℝ)/1000000) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ ≤ radiusCeiling^(N+1)*(9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N)*
        (1048576/524287 : ℝ)^N := by gcongr
    _ = (9/4 : ℝ)*radiusCeiling*((radiusCeiling*(1048576/524287 : ℝ))^N*
        exp (-(1033/10000000 : ℝ)*N)) := by rw [mul_pow,pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hh.trans he) (by norm_num [radiusCeiling])

/-- The eligible incidence is enough to bound the entire original
residual; other allocations stay in it and need no second error credit. -/
theorem residual_coefficient_bound (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    {N n p : ℕ} (hN : 320 ≤ N) (hn : Squarefree n) (hn1 : 1 < n)
    (hnp : ¬n.Prime) (hp : p ∈ n.primeFactors) (hpA : p ∈ A)
    (he : eligibleCofactor p (n/p))
    (hx : (7/25 : ℝ) ≤ log (n/p : ℕ)/log n)
    (hx1 : log (n/p : ℕ)/log n ≤ (499/1250 : ℝ)) :
    ‖residualCoefficient A L N n‖ ≤
      (9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N)*zetaMoebiusLogMajorant n := by
  have hs := single_prime_mass_le_share A N hn hn1 hp hpA he
  have hm := missing_mass_bound hN hx hx1
  have hb := boundedShare_bounds A N n
  have hsmall : 1-boundedShare A N n ≤ (9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N) := by
    rw [boundedShare,if_pos ⟨hn,hn1,hnp⟩]
    linarith
  rw [residualCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith only [hb.2])]
  exact mul_le_mul hsmall (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
    (norm_nonneg _) (by positivity)

/-- One literal atom is paid at the source scale, uniformly in height
and in every retained physical/count/allocation mask. -/
theorem normalized_atom_bound (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    {N n p : ℕ} (hN : 320 ≤ N) (hn : Squarefree n) (hn1 : 1 < n)
    (hnp : ¬n.Prime) (hp : p ∈ n.primeFactors) (hpA : p ∈ A)
    (he : eligibleCofactor p (n/p))
    (hx : (7/25 : ℝ) ≤ log (n/p : ℕ)/log n)
    (hx1 : log (n/p : ℕ)/log n ≤ (499/1250 : ℝ))
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
      ((9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/1000000))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by
  have hc := residual_coefficient_bound A hL hN hn hn1 hnp hp hpA he hx hx1
  have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (1048576/524287 : ℝ)^N*zetaPrimeExpWeight referenceExponent n := by
    convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
      (by norm_num : (0 : ℝ) < 524287/1048576) using 1
    norm_num [referenceExponent]
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  calc
    _ = (u^(N+1)*‖residualCoefficient A L N n‖)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by ring
    _ ≤ u^(N+1)*((9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N)*zetaMoebiusLogMajorant n)*
        ((1048576/524287 : ℝ)^N*zetaPrimeExpWeight referenceExponent n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc (pow_nonneg hu _)) hk (norm_nonneg _)
        (mul_nonneg (pow_nonneg hu _) (mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)))
    _ = (u^(N+1)*(9/4 : ℝ)*exp (-(1033/10000000 : ℝ)*N)*(1048576/524287 : ℝ)^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (source_rate_bound hu hU N)
      (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)

/-- Finite error allowance with an absolute geometric rate. It is not
a relative price times a growing positive radial supply. -/
def allowance (N : ℕ) : ℝ :=
  ((9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/1000000))*zetaMoebiusLogMajorantMass referenceExponent

/-- All selected counts and periods are summed together. Arbitrary
bounded correlated weights may select the still-unpaid population. -/
theorem selected_sum_bound (A D : Finset ℕ) (w : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    {N : ℕ} (hN : 320 ≤ N)
    (hw : ∀ n ∈ D, ‖w n‖ ≤ 1)
    (hD : ∀ n ∈ D, Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
      ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
        (7/25 : ℝ) ≤ log (n/p : ℕ)/log n ∧ log (n/p : ℕ)/log n ≤ (499/1250 : ℝ))
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D, w n*residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ allowance N := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, ((9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/1000000))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hs,hn1,hnp,p,hp,hpA,he,hx,hx1⟩ := hD n hn
      have hb := normalized_atom_bound A hL hN hs hn1 hnp hp hpA he hx hx1 hu hU y
      have heq : (u : ℂ)^(N+1)*(w n*residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
          w n*((u : ℂ)^(N+1)*(residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n)) := by ring
      rw [heq,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw n hn)).trans hb
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum D (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num [referenceExponent])))
        (by norm_num [radiusCeiling]; positivity)

/-- The full absolute error tends to zero; its finite arithmetic
constant has not been evaluated at any experimental order. -/
theorem tendsto_allowance : Tendsto allowance atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => ((9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/1000000))*
    zetaMoebiusLogMajorantMass referenceExponent) atTop (𝓝 0)
  have he : Tendsto (fun N : ℕ => exp (-(N : ℝ)/1000000)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (exp_pos (-(1/1000000 : ℝ))).le (exp_lt_one_iff.mpr (by norm_num))
    convert h using 1
    ext N
    rw [← exp_nat_mul]
    congr 1
    ring
  have h := (he.const_mul ((9/4 : ℝ)*radiusCeiling)).mul_const
    (zetaMoebiusLogMajorantMass referenceExponent)
  simpa only [mul_zero,zero_mul] using h

/-- Literal support discharges the lower cofactor share. In particular,
small-cofactor tails cannot be hidden in the new global payment. -/
theorem core_cofactor_share_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K n p : ℕ} (hN : 2 ≤ N) (hn : n ∈ coreBand u N K)
    (hs : Squarefree n) (hp : p ∈ n.primeFactors)
    (hshare : ownerThreshold*log n ≤ log p) :
    (7/25 : ℝ) ≤ log (n/p : ℕ)/log n ∧
      log (n/p : ℕ)/log n ≤ (499/1250 : ℝ) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := hpp.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hpd)
  have hln : 0 < log n := log_pos (by exact_mod_cast hn1)
  have hlog : log (n/p : ℕ)=log n-log p := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),log_div
      (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  have hcen : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N := by
    simp only [coreBand,ZetaRieszTypeII.narrowBand,LogarithmicDeviation.deviationBand,
      ZetaRieszDominantAllocation.nondominantBand,ZetaRieszMaskSupport.retainedBand,
      ZetaRieszCompanionMask.originalMask,ZetaRieszHarmonicWindow.fewBand,
      Finset.mem_filter,Finset.mem_sdiff] at hn
    tauto
  have hphys := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hcen).1).1).2 p hp
  have hpl : log p ≤ SquarefreeVaughanLogSource.length u N := by
    have h := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
      (show (p : ℝ) ≤ ((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) by
        exact_mod_cast hphys.le)
    simpa only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using h
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : log 2 ≤ (7/10 : ℝ) := by linarith [log_two_lt_d9]
  have hL : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg (α := ℝ) N)]
  have hlo : (39/20 : ℝ)*N < log n := (Finset.mem_filter.mp hn).2.1
  rw [hlog]
  constructor
  · apply (le_div_iff₀ hln).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · apply (div_le_iff₀ hln).mpr
    dsimp [ownerThreshold] at hshare
    linarith

/-- Every high-share core prime is actually eligible on the original
cofinal schedule. This is proved from the original count/physical masks. -/
theorem core_prime_eligible (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n p : ℕ}
    (hn : n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hs : Squarefree n) (hp : p ∈ n.primeFactors)
    (hshare : ownerThreshold*log n ≤ log p) :
    p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧ eligibleCofactor p (n/p) := by
  let N := dyadicMomentOrder j
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have he := ZetaRieszDominantAllocation.eligible_of_three_prime_factors hs hc hp
  have hcen : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N ∧
      n.primeFactors.card < dyadicPrimeCount j := by
    simp only [coreBand,ZetaRieszTypeII.narrowBand,LogarithmicDeviation.deviationBand,
      ZetaRieszDominantAllocation.nondominantBand,ZetaRieszMaskSupport.retainedBand,
      ZetaRieszCompanionMask.originalMask,ZetaRieszHarmonicWindow.fewBand,
      Finset.mem_filter,Finset.mem_sdiff] at hn
    exact ⟨by tauto,by tauto⟩
  have hphys := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hcen.1).1).1).2 p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hN : 0 < (N : ℝ) := by
    dsimp [N,dyadicMomentOrder,dyadicPrimeCount]
    positivity
  have hpN : N^2 < p := by
    by_contra hh
    have hpN' : p ≤ N^2 := le_of_not_gt hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hs hpd hcen.2 (by
      intro q hq
      have hqp : q=p := by simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    change log p ≤ (N : ℝ)/4 at hsmall
    have hlo : (39/20 : ℝ)*N < log n := (Finset.mem_filter.mp hn).2.1
    dsimp [ownerThreshold] at hshare
    nlinarith
  exact ⟨(mem_intermediatePrimes u N p).mpr ⟨hpp,hpN,hphys⟩,he⟩

/-- The new paid sector is an intersection with the SAME literal core. -/
def largeOwnerSector (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => ownerThreshold*log n ≤ log (largestPrime n))

/-- The new global arithmetic payment applies to every label of that
sector, including all counts and phases and zero nonsquarefree rows. -/
theorem core_atom_bound (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) {n : ℕ}
    (hn : n ∈ largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j)) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*
      (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)‖ ≤
      ((9/4 : ℝ)*radiusCeiling*exp (-(dyadicMomentOrder j : ℝ)/1000000))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by
  have hzero : 0 ≤ ((9/4 : ℝ)*radiusCeiling*exp (-(dyadicMomentOrder j : ℝ)/1000000))*
      (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) :=
    mul_nonneg (by norm_num [radiusCeiling]; positivity)
      (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  by_cases hs : Squarefree n
  · obtain ⟨hn,hshare⟩ := Finset.mem_filter.mp hn
    have hc := ZetaRieszJointPrimeEnergy.core_count hn
    have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hn1 : 1 < n := hpp.one_lt.trans_le
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hp))
    have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
    have hN : 320 ≤ dyadicMomentOrder j := by
      unfold dyadicMomentOrder
      nlinarith [four_le_dyadicPrimeCount j]
    have hd := core_prime_eligible j hj u hn hs hp hshare
    have hx := core_cofactor_share_bounds hu (by omega : 2 ≤ dyadicMomentOrder j) hn hs hp hshare
    exact normalized_atom_bound _ (SquarefreeVaughanLogSource.length_pos u _) hN hs hn1 hnp
      hp hd.1 hd.2 hx.1 hx.2 (by linarith) hU y
  · simpa [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs] using hzero

/-- Actual source-normalized cost of the WHOLE selected sector. Bounded
correlated masks can select any part of the current unpaid population. -/
theorem core_subset_sum_bound (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) (D : Finset ℕ) (w : ℕ → ℂ)
    (hD : D ⊆ largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hw : ∀ n ∈ D, ‖w n‖ ≤ 1) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ D,
      w n*residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤ allowance (dyadicMomentOrder j) := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, ((9/4 : ℝ)*radiusCeiling*exp (-(dyadicMomentOrder j : ℝ)/1000000))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := core_atom_bound j hj hu hU y (hD hn)
      have heq : (u : ℂ)^(dyadicMomentOrder j+1)*(w n*
          residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)=
          w n*((u : ℂ)^(dyadicMomentOrder j+1)*
            (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
              (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
                zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)) := by ring
      rw [heq,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw n hn)).trans hb
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum D (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num [referenceExponent])))
        (by norm_num [radiusCeiling]; positivity)

/-- Exact cropping of the entire current core, with an absolute
source-scale payment. No paid funding/head labels are credited twice. -/
theorem core_sub_cropped_bound (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*
      (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
        ∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
          largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j),
            residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
              (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
                zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)‖ ≤ allowance (dyadicMomentOrder j) := by
  have hb := core_subset_sum_bound j hj hu hU y
    (largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j)) (fun _ => 1)
    (fun _ h => h) (by intro n _; norm_num)
  simp only [one_mul] at hb
  have he := Finset.sum_sdiff (f := fun n =>
    residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)
    (show largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j) ⊆
      coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) from Finset.filter_subset _ _)
  have heq : coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      (∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
        largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j),
          residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n) =
      ∑ n ∈ largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j),
        residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n := by
    unfold coreResponse
    linear_combination -he
  rw [heq]
  exact hb

/-- The new crop is source-o(1), uniformly for arbitrary moving heights.
It does not assert smallness of the complementary signed sum. -/
theorem tendsto_core_sub_cropped {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℕ → ℝ) :
    Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      (coreResponse u (y j) (dyadicMomentOrder j) (dyadicPrimeCount j)-
        ∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
          largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j),
            residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
              (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
                zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*(y j)) n)) atTop (𝓝 0) := by
  have ht := tendsto_allowance.comp tendsto_dyadicMomentOrder
  apply squeeze_zero_norm' (a := fun j => allowance (dyadicMomentOrder j)) ?_ ht
  filter_upwards [eventually_ge_atTop (32 : ℕ)] with j hj
  exact core_sub_cropped_bound j hj hu hU (y j)

/-- Every prime logarithm in the still-retained complement is strictly
below the new threshold. This is a literal support fact for all counts. -/
theorem remaining_prime_share_lt {u : ℝ} {N K n p : ℕ}
    (hn : n ∈ coreBand u N K\largeOwnerSector u N K) (hp : p ∈ n.primeFactors) :
    log p < ownerThreshold*log n := by
  obtain ⟨hn,hnnot⟩ := Finset.mem_sdiff.mp hn
  have hlo : log (largestPrime n) < ownerThreshold*log n := by
    by_contra hh
    exact hnnot (Finset.mem_filter.mpr ⟨hn,le_of_not_gt hh⟩)
  have hpf : n.primeFactors.Nonempty := ⟨p,hp⟩
  have hmax : p ≤ largestPrime n := by
    rw [largestPrime,dif_pos hpf]
    exact Finset.le_max' _ _ hp
  exact (log_le_log (show (0 : ℝ) < p by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    (show (p : ℝ) ≤ largestPrime n by exact_mod_cast hmax)).trans_lt hlo

/-- The paid crop is connected directly to the existing endgame carrier.
The retained signed sum is still unevaluated; no numerical floor follows
without an independent lower bound for it. -/
theorem eventually_joined_cropped_bounds {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℕ → ℝ) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let q := (u : ℂ)^(N+1)*∑ n ∈ coreBand u N K\largeOwnerSector u N K,
          residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*(y j)) n
        let P := (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u (y j) N K
        q.re-err j ≤ P.re ∧ P.re ≤ q.re+err j := by
  let q := fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
    ∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
      largeOwnerSector u (dyadicMomentOrder j) (dyadicPrimeCount j),
        residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*(y j)) n
  let P := fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
    ZetaRieszGammaJoint.joinedPhysical u (y j) (dyadicMomentOrder j) (dyadicPrimeCount j)
  have he := ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u) hU y
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder
  have ht := (tendsto_core_sub_cropped hu hU y).sub he
  simp only [sub_zero] at ht
  have hT : Tendsto (fun j => P j-q j) atTop (𝓝 0) :=
    ht.congr' (Eventually.of_forall fun _ => by dsimp [P,q]; ring)
  refine ⟨fun j => ‖P j-q j‖,fun _ => norm_nonneg _,?_,Eventually.of_forall fun j => ?_⟩
  · simpa only [norm_zero] using hT.norm
  · change (q j).re-‖P j-q j‖ ≤ (P j).re ∧ (P j).re ≤ (q j).re+‖P j-q j‖
    have h := Complex.abs_re_le_norm (P j-q j)
    rw [Complex.sub_re,abs_le] at h
    constructor <;> linarith

/-- The same absolute payment applies inside the CURRENT signed
unpaid set. All of its arithmetic/correlated selections are retained. -/
theorem source_scaled_subset_crop_floor (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) (H : Finset ℕ) :
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let f := fun n => residualCoefficient (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    u^(N+1)*(∑ n ∈ H\largeOwnerSector u N K,f n).re-allowance N ≤
      u^(N+1)*(∑ n ∈ H,f n).re := by
  dsimp only
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let D := largeOwnerSector u N K
  let f := fun n => residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb := core_subset_sum_bound j hj hu hU y (H ∩ D) (fun _ => 1)
    (fun n hn => (Finset.mem_inter.mp hn).2) (by intro n _; norm_num)
  simp only [one_mul] at hb
  have he := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := H) (s₂ := D))
  have hset : H\(H ∩ D)=H\D := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hset] at he
  have heq : (∑ n ∈ H,f n)-(∑ n ∈ H\D,f n)=∑ n ∈ H ∩ D,f n := by
    linear_combination -he
  change ‖(u : ℂ)^(N+1)*∑ n ∈ H ∩ D,f n‖ ≤ allowance N at hb
  rw [← heq] at hb
  have hr := (Complex.abs_re_le_norm ((u : ℂ)^(N+1)*
    ((∑ n ∈ H,f n)-(∑ n ∈ H\D,f n)))).trans hb
  rw [mul_sub,Complex.sub_re] at hr
  have hreal (z : ℂ) : ((u : ℂ)^(N+1)*z).re=u^(N+1)*z.re := by
    have hpow : (u : ℂ)^(N+1)=((u^(N+1) : ℝ) : ℂ) := by norm_cast
    rw [hpow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hreal,hreal] at hr
  have hlo := (abs_le.mp hr).1
  change u^(N+1)*(∑ n ∈ H\D,f n).re-allowance N ≤ u^(N+1)*(∑ n ∈ H,f n).re
  linarith

open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSevenCountTail ZetaRieszDenseCountCoverFloor ZetaRieszFewBinCoverFloor
open ZetaRieszRejoinedPopulationFloor
open ZetaRieszJoinedPopulationFloor
open ZetaRieszLowCountRefund (tailCost)

/-- The new payment is spent on the actual unresolved signed population
in the latest ledger. Funding, both growing payments and every debit stay
unchanged. Only one absolutely vanishing error is added. -/
theorem eventually_rejoined_floor_without_large_owners {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let A := intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N K
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N 0
        let Ys := radialSupply N h w
        let D := S.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
        let Ds := dense56Band u N K
        let Bs := bin56Band u N K
        let Paid := (D ∪ Ds) ∪ Bs
        let H := S\(Paid ∪ wholeTail S N 0)
        let E := H\largeOwnerSector u N K
        0 < (∑ n ∈ Ys,f n).re ∧
          u^(N+1)*((∑ n ∈ E,f n).re+max (∑ n ∈ Paid,f n).re 0+
            max (∑ n ∈ Ts,f n).re 0-
            (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ := eventually_joined_floor_rejoined_populations hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨e,he0,he,hfloor⟩ := hbase ε hε
  have ha0 N : 0 ≤ allowance N := by
    unfold allowance
    exact mul_nonneg (by norm_num [radiusCeiling]; positivity)
      (zetaMoebiusLogMajorantMass_nonneg referenceExponent)
  refine ⟨fun j => e j+allowance (dyadicMomentOrder j),fun j => add_nonneg (he0 j) (ha0 _),?_,?_⟩
  · have ht := he.add (tendsto_allowance.comp tendsto_dyadicMomentOrder)
    simpa only [add_zero,Function.comp_def] using ht
  · filter_upwards [hfloor,eventually_ge_atTop (32 : ℕ)] with j hj hj32
    obtain ⟨w,hw,hpos,hbound⟩ := hj
    refine ⟨w,hw,hpos,?_⟩
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N K
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let Ts := radialTail S N 0
    let Ys := radialSupply N h w
    let D := S.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
    let Paid := (D ∪ dense56Band u N K) ∪ bin56Band u N K
    let H := S\(Paid ∪ wholeTail S N 0)
    have hcrop := source_scaled_subset_crop_floor j hj32 hu.le hU y H
    change u^(N+1)*(∑ n ∈ H\largeOwnerSector u N K,f n).re-allowance N ≤
      u^(N+1)*(∑ n ∈ H,f n).re at hcrop
    change u^(N+1)*((∑ n ∈ H,f n).re+max (∑ n ∈ Paid,f n).re 0+
      max (∑ n ∈ Ts,f n).re 0-(tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-e j ≤
        ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re at hbound
    change u^(N+1)*((∑ n ∈ H\largeOwnerSector u N K,f n).re+max (∑ n ∈ Paid,f n).re 0+
      max (∑ n ∈ Ts,f n).re 0-(tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-
        (e j+allowance N) ≤ ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re
    nlinarith only [hcrop,hbound]

/-- The new remaining population has every old count/bin restriction
AND the stronger owner/share restriction. No unmatched layer is omitted. -/
theorem remaining_rejoined_geometry {u : ℝ} {N K n : ℕ} (A : Finset ℕ) (L y : ℝ)
    (hn : n ∈ (coreBand u N K\
      ((((coreBand u N K).filter (fun n : ℕ =>
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
        bin56Band u N K) ∪ wholeTail (coreBand u N K) N 0))\largeOwnerSector u N K)
    (hne : residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n ≠ 0) :
    Squarefree n ∧ 56 ≤ n.primeFactors.card ∧
      (n.primeFactors.card : ℝ) < 5*log ((N : ℝ)+1)+2 ∧
      ⌊log ((N : ℝ)+1)/16⌋₊ <
        (ZetaRieszFewBinCoverFloor.cofactorBins N (n/largestPrime n)).card ∧
      ∀ p ∈ n.primeFactors, log p < ownerThreshold*log n := by
  obtain ⟨hnH,hnnot⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hs,h56,hupper,hbins⟩ := remaining_effective_geometry A L y hnH hne
  refine ⟨hs,h56,hupper,hbins,?_⟩
  intro p hp
  exact remaining_prime_share_lt (Finset.mem_sdiff.mpr
    ⟨(Finset.mem_sdiff.mp hnH).1,hnnot⟩) hp

end RiemannGaussian.ZetaRieszCoreOwnerPayment
