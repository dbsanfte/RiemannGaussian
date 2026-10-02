/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoreOwnerPayment

/-!
# A source-scale payment closer to the allocation transition

The concrete owner cut is lowered from 751/1250 to 60069/100000.
The missing factorial mass is bounded before all original labels are
summed, and its exponent exceeds the source growth after a summable
reference exponent is inserted. The payment is uniform over counts,
occupied bins, periods and bounded correlated masks. No signed complement
is estimated or completed, and the numerical whole-floor remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSharpOwnerPayment
open ZetaRieszJointAllocation ZetaRieszParityPacket ZetaRieszAnnulusJoint
open ZetaRieszWideOwnerAudit ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint

/-- A fixed concrete cut; every original allocation and mask is unchanged. -/
def ownerThreshold : ℝ := 60069/100000

private def referenceExponent : ℝ := 1+1/134217728

/-- Rational Taylor enclosures certify the upper tail, independently of
the exploratory logarithm evaluation. -/
theorem upper_tilt_log :
    log (10119793/10000000 : ℝ)-(13/32 : ℝ)*log (103/100 : ℝ) ≤
      -(10013/100000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 3/203)
    (by norm_num : (3/203 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : log (10119793/10000000 : ℝ) ≤ 119081162/10000000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 119081162/10000000000) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- Both literal missing-order tails are retained on the larger share
interval. This is a bound for the exact finite factorial allocation. -/
theorem missing_mass_bound {N : ℕ} (hN : 320 ≤ N) {x : ℝ}
    (hx : (7/25 : ℝ) ≤ x) (hx1 : x ≤ (39931/100000 : ℝ)) :
    1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x ≤
      (9/4 : ℝ)*exp (-(10013/100000000 : ℝ)*N) := by
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
  have hhi : (103/100 : ℝ)*x+(1-x) ≤ 10119793/10000000 := by linarith
  have hlo : (4/5 : ℝ)*x+(1-x) ≤ 118/125 := by linarith
  have hb := hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hhi (N+1)) (exp_pos _).le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlo (N+1)) (exp_pos _).le))
  have hlow : log (118/125 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ) ≤
      -(10013/100000000 : ℝ) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 118/125)
    linarith [log_tilt_bounds.2]
  have hehi : exp (-(13/32 : ℝ)*N*log (103/100 : ℝ))*(10119793/10000000 : ℝ)^(N+1) =
      (10119793/10000000 : ℝ)*exp ((N : ℝ)*
        (log (10119793/10000000 : ℝ)-(13/32 : ℝ)*log (103/100 : ℝ))) := by
    rw [pow_succ,show (10119793/10000000 : ℝ)^N=
      exp ((N : ℝ)*log (10119793/10000000 : ℝ)) by
        rw [exp_nat_mul,exp_log (by norm_num)],
      show (N : ℝ)*(log (10119793/10000000 : ℝ)-(13/32 : ℝ)*log (103/100 : ℝ))=
        -(13/32 : ℝ)*N*log (103/100 : ℝ)+
          (N : ℝ)*log (10119793/10000000 : ℝ) by ring,exp_add]
    ring
  have helo : exp (((N : ℝ)/5+1)*log (5/4 : ℝ))*(118/125 : ℝ)^(N+1) =
      ((5/4 : ℝ)*(118/125))*exp ((N : ℝ)*
        (log (118/125 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))) := by
    rw [pow_succ,show (118/125 : ℝ)^N=exp ((N : ℝ)*log (118/125 : ℝ)) by
      rw [exp_nat_mul,exp_log (by norm_num)],
      show ((N : ℝ)/5+1)*log (5/4 : ℝ)=
        (N : ℝ)/5*log (5/4 : ℝ)+log (5/4 : ℝ) by ring,
      exp_add,exp_log (by norm_num)]
    rw [show (N : ℝ)*(log (118/125 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))=
      (N : ℝ)/5*log (5/4 : ℝ)+(N : ℝ)*log (118/125 : ℝ) by ring,exp_add]
    ring
  rw [hehi,helo] at hb
  have hu := exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left upper_tilt_log (Nat.cast_nonneg (α := ℝ) N))
  have hd := exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg (α := ℝ) N))
  rw [show (N : ℝ)*(-(10013/100000000 : ℝ))=
    -(10013/100000000 : ℝ)*N by ring] at hu hd
  nlinarith [exp_pos (-(10013/100000000 : ℝ)*N)]

private theorem source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    u^(N+1)*(9/4 : ℝ)*exp (-(10013/100000000 : ℝ)*N)*
      (134217728/67108863 : ℝ)^N ≤
        (9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/10000000) := by
  have hb : radiusCeiling*(134217728/67108863 : ℝ) ≤ exp (100015/1000000000 : ℝ) := by
    have h := add_one_le_exp (100015/1000000000 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num [radiusCeiling]) hb N
  rw [← exp_nat_mul] at hp
  have hh := mul_le_mul_of_nonneg_right hp
    (exp_pos (-(10013/100000000 : ℝ)*N)).le
  rw [← exp_add] at hh
  have he : exp ((N : ℝ)*(100015/1000000000)+(-(10013/100000000 : ℝ)*N)) ≤
      exp (-(N : ℝ)/10000000) := exp_le_exp.mpr (by
    nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ ≤ radiusCeiling^(N+1)*(9/4 : ℝ)*exp (-(10013/100000000 : ℝ)*N)*
        (134217728/67108863 : ℝ)^N := by gcongr
    _ = (9/4 : ℝ)*radiusCeiling*((radiusCeiling*(134217728/67108863 : ℝ))^N*
        exp (-(10013/100000000 : ℝ)*N)) := by rw [mul_pow,pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hh.trans he) (by norm_num [radiusCeiling])

/-- An absolute source-scale error, with no radial funding multiplier. -/
def allowance (N : ℕ) : ℝ :=
  ((9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/10000000))*
    zetaMoebiusLogMajorantMass referenceExponent

theorem allowance_nonneg (N : ℕ) : 0 ≤ allowance N :=
  mul_nonneg (by norm_num [radiusCeiling]; positivity)
    (zetaMoebiusLogMajorantMass_nonneg _)

theorem tendsto_allowance : Tendsto allowance atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => ((9/4 : ℝ)*radiusCeiling*exp (-(N : ℝ)/10000000))*
    zetaMoebiusLogMajorantMass referenceExponent) atTop (𝓝 0)
  have he : Tendsto (fun N : ℕ => exp (-(N : ℝ)/10000000)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (exp_pos (-(1/10000000 : ℝ))).le (exp_lt_one_iff.mpr (by norm_num))
    convert h using 1
    ext N
    rw [← exp_nat_mul]
    congr 1
    ring
  simpa only [mul_zero,zero_mul] using
    (he.const_mul ((9/4 : ℝ)*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass referenceExponent)

/-- The paid population is selected inside the existing literal core. -/
def sector (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => ownerThreshold*log n ≤ log (largestPrime n))

private theorem core_data (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    {n : ℕ} (hn : n ∈ sector u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hs : Squarefree n) :
    let N := dyadicMomentOrder j
    let p := largestPrime n;
    1 < n ∧ ¬n.Prime ∧ p ∈ n.primeFactors ∧
      p ∈ intermediatePrimes u N ∧ eligibleCofactor p (n/p) ∧
      (7/25 : ℝ) ≤ log (n/p : ℕ)/log n ∧
      log (n/p : ℕ)/log n ≤ (39931/100000 : ℝ) := by
  obtain ⟨hn,hshare⟩ := Finset.mem_filter.mp hn
  let N := dyadicMomentOrder j
  let p := largestPrime n
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp : p ∈ n.primeFactors :=
    ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := hpp.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hpd)
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
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
  have hN : 0 < (N : ℝ) := by dsimp [N,dyadicMomentOrder,dyadicPrimeCount]; positivity
  have hlo : (39/20 : ℝ)*N < log n := (Finset.mem_filter.mp hn).2.1
  have hpN : N^2 < p := by
    by_contra hh
    have hpN' : p ≤ N^2 := le_of_not_gt hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hs hpd hcen.2 (by
      intro q hq
      have hqp : q=p := by simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    change log p ≤ (N : ℝ)/4 at hsmall
    dsimp [ownerThreshold] at hshare
    nlinarith
  have hpl : log p ≤ SquarefreeVaughanLogSource.length u N := by
    have h := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
      (show (p : ℝ) ≤ ((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) by
        exact_mod_cast hphys.le)
    simpa only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using h
  have hN2 : 2 ≤ N := by dsimp [N,dyadicMomentOrder]; nlinarith [four_le_dyadicPrimeCount j]
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN2
  have hL : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right
      (show log 2 ≤ (7/10 : ℝ) by linarith [log_two_lt_d9])
      (Nat.cast_nonneg (α := ℝ) N)]
  have hln : 0 < log n := log_pos (by exact_mod_cast hn1)
  have hlog : log (n/p : ℕ)=log n-log p := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),log_div
      (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  refine ⟨hn1,hnp,hp,(mem_intermediatePrimes u N p).mpr ⟨hpp,hpN,hphys⟩,he,?_,?_⟩
  · rw [hlog]
    apply (le_div_iff₀ hln).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · rw [hlog]
    apply (div_le_iff₀ hln).mpr
    dsimp [ownerThreshold] at hshare
    linarith

private theorem core_atom_bound (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) {n : ℕ}
    (hn : n ∈ sector u (dyadicMomentOrder j) (dyadicPrimeCount j)) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*
      (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)‖ ≤
      ((9/4 : ℝ)*radiusCeiling*exp (-(dyadicMomentOrder j : ℝ)/10000000))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by
  have hzero : 0 ≤ ((9/4 : ℝ)*radiusCeiling*exp (-(dyadicMomentOrder j : ℝ)/10000000))*
      (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) :=
    mul_nonneg (by norm_num [radiusCeiling]; positivity)
      (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  by_cases hs : Squarefree n
  · let N := dyadicMomentOrder j
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    have hu0 : 0 ≤ u := by linarith
    obtain ⟨hn1,hnp,hp,hpA,he,hx,hx1⟩ := core_data j hj hu hn hs
    have hN : 320 ≤ N := by dsimp [N,dyadicMomentOrder]; nlinarith [four_le_dyadicPrimeCount j]
    have hb := boundedShare_bounds A N n
    have hmass := single_prime_mass_le_share A N hs hn1 hp hpA he
    have hm := missing_mass_bound hN hx hx1
    have hsmall : 1-boundedShare A N n ≤ (9/4 : ℝ)*exp (-(10013/100000000 : ℝ)*N) := by
      rw [boundedShare,if_pos ⟨hs,hn1,hnp⟩]
      linarith
    have hc : ‖residualCoefficient A L N n‖ ≤
        (9/4 : ℝ)*exp (-(10013/100000000 : ℝ)*N)*zetaMoebiusLogMajorant n := by
      rw [residualCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by linarith only [hb.2])]
      exact mul_le_mul hsmall
        (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)
        (norm_nonneg _) (by positivity)
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (134217728/67108863 : ℝ)^N*zetaPrimeExpWeight referenceExponent n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 67108863/134217728) using 1
      norm_num [referenceExponent]
    change ‖(u : ℂ)^(N+1)*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤ _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
    have ht := mul_le_mul (mul_le_mul_of_nonneg_left hc (pow_nonneg hu0 (N+1))) hk
      (norm_nonneg _) (mul_nonneg (pow_nonneg hu0 (N+1)) ((norm_nonneg _).trans hc))
    have hw0 : 0 ≤ zetaMoebiusLogMajorant n * zetaPrimeExpWeight referenceExponent n :=
      mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le
    have hr := mul_le_mul_of_nonneg_right (source_rate hu0 hU N) hw0
    nlinarith only [ht,hr]
  · simpa [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs] using hzero

/-- All original counts, bins and periods are joined with their literal
correlated mask. The whole new sector has an absolute geometric cost. -/
theorem core_subset_source_bound (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) (D : Finset ℕ) (w : ℕ → ℂ)
    (hD : D ⊆ sector u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hw : ∀ n ∈ D, ‖w n‖ ≤ 1) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ D,
      w n*residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
      allowance (dyadicMomentOrder j) := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, ((9/4 : ℝ)*radiusCeiling*exp (-(dyadicMomentOrder j : ℝ)/10000000))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := core_atom_bound j hj hu hU y (hD hn)
      rw [show (u : ℂ)^(dyadicMomentOrder j+1)*(w n*
        residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)=
        w n*((u : ℂ)^(dyadicMomentOrder j+1)*
          (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)) by ring,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw n hn)).trans hb
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum D (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num [referenceExponent])))
        (by norm_num [radiusCeiling]; positivity)

/-- The old source-paid owner sector is contained in the new one.
Its original stronger rate and every previous theorem remain available. -/
theorem old_sector_subset (u : ℝ) (N K : ℕ) :
    ZetaRieszCoreOwnerPayment.largeOwnerSector u N K ⊆ sector u N K := by
  intro n hn
  obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn,?_⟩
  have h := mul_le_mul_of_nonneg_right
    (show ownerThreshold ≤ ZetaRieszCoreOwnerPayment.ownerThreshold by
      norm_num [ownerThreshold,ZetaRieszCoreOwnerPayment.ownerThreshold])
    (log_natCast_nonneg n)
  exact h.trans hs

/-- The new payment is valid on the literal unpaid set itself. All
its correlated masks remain, and only an absolutely vanishing cost is added. -/
theorem subset_crop_floor (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) (H : Finset ℕ) :
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let f := fun n => residualCoefficient (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    u^(N+1)*(∑ n ∈ H\sector u N K,f n).re-allowance N ≤
      u^(N+1)*(∑ n ∈ H,f n).re := by
  dsimp only
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let D := sector u N K
  let f := fun n => residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb := core_subset_source_bound j hj hu hU y (H ∩ D) (fun _ => 1)
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
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor
open ZetaRieszLowCountRefund (tailCost)

/-- The strengthened payment is spent on the whole retained-floor ledger.
The old credit, funding witness and every debit stay unchanged. The new
unpaid population has a smaller owner-share cap and one new o(1) error.
This is not yet the final numerical -79/1000 floor. -/
theorem eventually_rejoined_floor {u y : ℝ} (hu : 1/2 < u)
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
        let Paid := (D ∪ dense56Band u N K) ∪ bin56Band u N K
        let H := S\(Paid ∪ wholeTail S N 0)
        let E := H\sector u N K
        0 < (∑ n ∈ Ys,f n).re ∧
          u^(N+1)*((∑ n ∈ E,f n).re+max (∑ n ∈ Paid,f n).re 0+
            max (∑ n ∈ Ts,f n).re 0-
            (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    ZetaRieszCoreOwnerPayment.eventually_rejoined_floor_without_large_owners hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨e,he0,he,hfloor⟩ := hbase ε hε
  refine ⟨fun j => e j+allowance (dyadicMomentOrder j),
    fun j => add_nonneg (he0 j) (allowance_nonneg _),?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using
      he.add (tendsto_allowance.comp tendsto_dyadicMomentOrder)
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
    let Old := ZetaRieszCoreOwnerPayment.largeOwnerSector u N K
    have hset : (H\Old)\sector u N K=H\sector u N K := by
      ext n
      have hsubset := old_sector_subset u N K
      simp only [Finset.mem_sdiff]
      constructor
      · tauto
      · intro hn
        exact ⟨⟨hn.1,fun ho => hn.2 (hsubset ho)⟩,hn.2⟩
    have hcrop := subset_crop_floor j hj32 hu.le hU y (H\Old)
    change u^(N+1)*(∑ n ∈ (H\Old)\sector u N K,f n).re-allowance N ≤
      u^(N+1)*(∑ n ∈ H\Old,f n).re at hcrop
    rw [hset] at hcrop
    change u^(N+1)*((∑ n ∈ H\Old,f n).re+max (∑ n ∈ Paid,f n).re 0+
      max (∑ n ∈ Ts,f n).re 0-(tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-e j ≤
        ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re at hbound
    change u^(N+1)*((∑ n ∈ H\sector u N K,f n).re+max (∑ n ∈ Paid,f n).re 0+
      max (∑ n ∈ Ts,f n).re 0-(tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-
        (e j+allowance N) ≤ ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re
    nlinarith only [hcrop,hbound]

/-- Every prime of every remaining original core label is below the
new smaller logarithmic share, without count or bin restrictions. -/
theorem remaining_prime_share_lt {u : ℝ} {N K n p : ℕ}
    (hn : n ∈ coreBand u N K\sector u N K) (hp : p ∈ n.primeFactors) :
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

end RiemannGaussian.ZetaRieszSharpOwnerPayment
