/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszInnerHingeTransport
import RiemannGaussian.ZetaRieszOwnerMaximal
import RiemannGaussian.ZetaRieszSharpOwnerPayment
import RiemannGaussian.ZetaRieszRejoinedPhaseFloor

/-!
# A one-sided owner-allocation saving before parity-pair pricing

On the retained cofactor shares, the actual owner weight is increasing up
to an exponentially small LOWER cumulative tail. Its change is favorable
when the first original signed atom is negative. Pairing before pricing
therefore needs no absolute allocation-difference allowance. All funding
and phase differences stay in the unallocated pair, and matching coverage
is not assumed. The lower-tail cost is paid globally at source scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszOwnerPairFloor
open ZetaRieszJointAllocation ZetaRieszOwnerMaximal ZetaRieszBalancedCompanion
open ZetaRieszPrimeEndpoint ZetaRieszWideOwnerAudit

/-- The exact low endpoint of the original interval has exponential
mass on EVERY share above3/8; no order, count or low atom is discarded. -/
theorem lower_tail_exp (N : ℕ) {x : ℝ} (hx : (3/8 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    lowerMass (N+1) (N/5+1) x ≤ 2*exp (-(N : ℝ)/25) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hS : Finset.range (N/5+2) ⊆ Finset.range (N+2) :=
    Finset.range_mono (by omega)
  have hb := selected_tilt_bound (N+1) (Finset.range (N/5+2)) hS hx0 hx1
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (exp_pos (((N : ℝ)/5+1)*log 2)).le (by
      intro k hk
      have hc : (k : ℝ) ≤ (N : ℝ)/5+1 := by
        have hn : 5*k ≤ N+5 := by
          have := Finset.mem_range.mp hk
          omega
        have hr : 5*(k : ℝ) ≤ N+5 := by exact_mod_cast hn
        linarith
      rw [show (1/2 : ℝ)=exp (-log 2) by
        rw [exp_neg,exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num,
        ← exp_nat_mul,← exp_add]
      apply one_le_exp_iff.mpr
      nlinarith [mul_le_mul_of_nonneg_right hc ht])
  have hp : ((1/2 : ℝ)*x+(1-x))^(N+1) ≤ (13/16 : ℝ)^(N+1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hr : log (13/16 : ℝ)+(1/5 : ℝ)*log 2 ≤ -(1/25) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13/16)
    have h2 : log 2 ≤ (7/10 : ℝ) := by linarith [log_two_lt_d9]
    linarith
  have he : exp (((N : ℝ)/5+1)*log 2)*(13/16 : ℝ)^(N+1) =
      (13/8 : ℝ)*exp ((N : ℝ)*(log (13/16)+(1/5)*log 2)) := by
    rw [pow_succ,
      show (13/16 : ℝ)^N=exp ((N : ℝ)*log (13/16)) by
        rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ) < 13/16)],
      show ((N : ℝ)/5+1)*log 2=log 2+(N : ℝ)/5*log 2 by ring,
      exp_add,exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [show (N : ℝ)*(log (13/16)+(1/5)*log 2)=
      (N : ℝ)/5*log 2+(N : ℝ)*log (13/16) by ring,exp_add]
    ring
  have hrate : exp ((N : ℝ)*(log (13/16)+(1/5)*log 2)) ≤
      exp (-(N : ℝ)/25) := exp_le_exp.mpr (by
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) N)])
  change lowerMass (N+1) (N/5+1) x ≤ _ at hb
  have hh := hb.trans (mul_le_mul_of_nonneg_left hp (exp_pos _).le)
  rw [he] at hh
  nlinarith [exp_pos (-(N : ℝ)/25)]

/-- The literal owner weight increases with share except for one
globally payable tail. No absolute variation is charged. -/
theorem ownerWeight_almost_monotone {N : ℕ} (hN : 32 ≤ N) {x x' : ℝ}
    (hx : (3/8 : ℝ) ≤ x) (hxx : x ≤ x') (hx1 : x' ≤ 1) :
    ownerWeight N x ≤ ownerWeight N x'+2*exp (-(N : ℝ)/25) := by
  have hx0 : 0 ≤ x := by linarith
  have hx'0 : 0 ≤ x' := by linarith
  have hxone : x ≤ 1 := hxx.trans hx1
  have hh := lowerMass_antitone (N+1) (13*N/32) ⟨hx0,hxone⟩ ⟨hx'0,hx1⟩ hxx
  have hl := (lowerMass_bounds (N+1) (N/5+1) hx'0 hx1).1
  have he := lower_tail_exp N hx hxone
  rw [ownerWeight,ownerWeight,ownerMass_eq_difference hN,ownerMass_eq_difference hN]
  linarith

/-- Price a favorable fractional-weight change AFTER joining the signed
pair. The second amplitude includes its original funding and phase. -/
theorem fractional_pair_floor {a a' e : ℝ} (ha' : 0 ≤ a') (ha'1 : a' ≤ 1)
    (he : 0 ≤ e) (haa : a ≤ a'+e) (F G : ℂ) (hF : F.re ≤ 0) :
    -‖F+G‖-e*‖F‖ ≤ ((a : ℂ)*F+(a' : ℂ)*G).re := by
  have hf : -‖F‖ ≤ F.re := by
    have h := Complex.abs_re_le_norm F
    exact (abs_le.mp h).1
  have hfg : -‖F+G‖ ≤ (F+G).re := (abs_le.mp (Complex.abs_re_le_norm (F+G))).1
  have hvar := mul_le_mul_of_nonpos_right (show a-a' ≤ e by linarith) hF
  have hel := mul_le_mul_of_nonneg_left hf he
  have hpair := mul_le_mul_of_nonneg_left hfg ha'
  have hcap := mul_le_mul_of_nonneg_right ha'1 (norm_nonneg (F+G))
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.add_re] at *
  nlinarith

/-- On a negative ORIGINAL atom, the entire owner-weight mismatch is
replaced by an exponential tail. The unallocated pair stays joined. -/
theorem owner_pair_floor {N : ℕ} (hN : 32 ≤ N) {x x' : ℝ}
    (hx : (3/8 : ℝ) ≤ x) (hxx : x ≤ x') (hx1 : x' ≤ 1)
    (F G : ℂ) (hF : F.re ≤ 0) :
    -‖F+G‖-(2*exp (-(N : ℝ)/25))*‖F‖ ≤
      ((ownerWeight N x : ℂ)*F+(ownerWeight N x' : ℂ)*G).re :=
  fractional_pair_floor
    (ownerWeight_bounds N (by linarith : 0 ≤ x') hx1).1
    (ownerWeight_bounds N (by linarith : 0 ≤ x') hx1).2
    (by positivity) (ownerWeight_almost_monotone hN hx hxx hx1) F G hF

/-- Two genuine original owner fibres inherit the one-sided saving with
their own exact allocation. No native membership or partner exists by fiat. -/
theorem literal_owner_pair_floor (A A' : Finset ℕ) {N : ℕ} (hN : 32 ≤ N)
    (L y v v' : ℝ) {p p' a a' : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime)
    (hmax : ∀ q ∈ a.primeFactors, q < p) (hpA : p ∈ A)
    (ha' : Squarefree a') (hc' : 2 ≤ a'.primeFactors.card) (hp' : p'.Prime)
    (hmax' : ∀ q ∈ a'.primeFactors, q < p') (hpA' : p' ∈ A')
    (hx : (3/8 : ℝ) ≤ log a/log (p*a : ℕ))
    (hxx : log a/log (p*a : ℕ) ≤ log a'/log (p'*a' : ℕ))
    (hx1 : log a'/log (p'*a' : ℕ) ≤ 1)
    (hF : ((v : ℂ)*SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ≤ 0) :
    -‖(v : ℂ)*SquarefreeVaughanLogSource.coefficient L (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)+
      (v' : ℂ)*SquarefreeVaughanLogSource.coefficient L (p'*a')*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*a')‖-
      (2*exp (-(N : ℝ)/25))*‖(v : ℂ)*SquarefreeVaughanLogSource.coefficient L (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)‖ ≤
      ((v : ℂ)*residualCoefficient (A ∩ {largestPrime (p*a)}) L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)+
        (v' : ℂ)*residualCoefficient (A' ∩ {largestPrime (p'*a')}) L N (p'*a')*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*a')).re := by
  have h := owner_pair_floor hN hx hxx hx1
    ((v : ℂ)*SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a))
    ((v' : ℂ)*SquarefreeVaughanLogSource.coefficient L (p'*a')*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*a')) hF
  rw [ownerWeight_eq_fibre A N ha hc hp hmax hpA,
    ownerWeight_eq_fibre A' N ha' hc' hp' hmax' hpA'] at h
  convert h using 1
  simp only [residualCoefficient]
  push_cast
  ring_nf

/-- The paid lower-tail rate beats source growth uniformly at the full
requested radius. This is an ABSOLUTE saving, not a relative supply debit. -/
theorem lower_tail_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (N : ℕ) :
    u^(N+1)*(2*exp (-(N : ℝ)/25))*(131071/262144 : ℝ)⁻¹^N ≤
      2*radiusCeiling*exp (-(N : ℝ)/50) := by
  have hb : radiusCeiling*(131071/262144 : ℝ)⁻¹ ≤ exp (1/1000 : ℝ) := by
    have h := add_one_le_exp (1/1000 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num [radiusCeiling] :
    (0 : ℝ) ≤ radiusCeiling*(131071/262144 : ℝ)⁻¹) hb N
  rw [← exp_nat_mul] at hp
  have hh := mul_le_mul_of_nonneg_right hp (exp_pos (-(N : ℝ)/25)).le
  rw [← exp_add] at hh
  have he : exp ((N : ℝ)*(1/1000)+(-(N : ℝ)/25)) ≤ exp (-(N : ℝ)/50) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ ≤ radiusCeiling^(N+1)*(2*exp (-(N : ℝ)/25))*(131071/262144 : ℝ)⁻¹^N := by
      gcongr
    _ = 2*radiusCeiling*((radiusCeiling*(131071/262144 : ℝ)⁻¹)^N*exp (-(N : ℝ)/25)) := by
      rw [mul_pow,pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hh.trans he) (by norm_num [radiusCeiling])

/-- ONE global bound for all original matched-tail prices, at every
count and radial period. Arbitrary signed funding weights are kept. -/
theorem total_lower_tail_price (D : Finset ℕ) (w : ℕ → ℂ) {B L u : ℝ}
    (hB : 0 ≤ B) (hw : ∀ n ∈ D, ‖w n‖ ≤ B) (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) (y : ℝ) :
    u^(N+1)*(2*exp (-(N : ℝ)/25))*
      (∑ n ∈ D, ‖w n*SquarefreeVaughanLogSource.coefficient L n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (2*radiusCeiling*B*exp (-(N : ℝ)/50))*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have hs : (∑ n ∈ D, ‖w n*SquarefreeVaughanLogSource.coefficient L n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      B*(131071/262144 : ℝ)⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
    calc
      _ ≤ ∑ n ∈ D, B*(131071/262144 : ℝ)⁻¹^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
            (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
          convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
            (by norm_num : (0 : ℝ) < 131071/262144) using 1
          norm_num
        rw [norm_mul,norm_mul]
        have hh := mul_le_mul (hw n hn) (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
          (norm_nonneg _) hB
        have hprod := mul_le_mul hh hk (norm_nonneg _) (mul_nonneg hB (zetaMoebiusLogMajorant_nonneg n))
        exact hprod.trans_eq (by ring)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (Summable.sum_le_tsum D (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
            (exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
          (mul_nonneg hB (by positivity))
  calc
    _ ≤ u^(N+1)*(2*exp (-(N : ℝ)/25))*
        (B*(131071/262144 : ℝ)⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (u^(N+1)*(2*exp (-(N : ℝ)/25))*(131071/262144 : ℝ)⁻¹^N)*
        (B*zetaMoebiusLogMajorantMass (1+1/262144)) := by ring
    _ ≤ _ := by
      have hmass : 0 ≤ zetaMoebiusLogMajorantMass (1+1/262144) :=
        tsum_nonneg (fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
      have h := mul_le_mul_of_nonneg_right (lower_tail_source_rate hu hU N) (mul_nonneg hB hmass)
      exact h.trans_eq (by ring)

/-- The numerical lower-tail price is source-o(1) even after any fixed
polynomial funding envelope. This does not bound the remaining pair gaps. -/
theorem tendsto_polynomial_lower_tail_price (C : ℝ) (d : ℕ) :
    Tendsto (fun N : ℕ => C*((N : ℝ)+1)^d*exp (-(N : ℝ)/50)) atTop (𝓝 0) := by
  have hr : 0 < exp (-(1/50 : ℝ)) := exp_pos _
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric d hr
    (exp_lt_one_iff.mpr (by norm_num : -(1/50 : ℝ) < 0))
  have hh := ht.const_mul C
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    rw [← exp_nat_mul]
    have he : exp ((N : ℝ)*(-(1/50 : ℝ)))=exp (-(N : ℝ)/50) := by congr 1; ring
    rw [he]
    ring)

/-- Literal owner shrinkage and insertion increase the cofactor share.
The total integer logarithm and its full phase have not been frozen. -/
theorem insertion_cofactor_share_le {p p' r a : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hr : 0 < r) (ha : 0 < a) (hpp : p' ≤ p) :
    log a/log (p*a : ℕ) ≤ log (r*a : ℕ)/log (p'*(r*a) : ℕ) := by
  have hPa : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne')]
  have hRa : log (r*a : ℕ)=log r+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hr.ne') (by exact_mod_cast ha.ne')]
  have hPr : log (p'*(r*a) : ℕ)=log p'+log r+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp'.ne_zero)
      (by exact_mod_cast (mul_pos hr ha).ne'),hRa]
    ring
  have hP : 0 < log p := log_pos (by exact_mod_cast hp.one_lt)
  have hP' : 0 < log p' := log_pos (by exact_mod_cast hp'.one_lt)
  have hpp' := log_le_log (show (0 : ℝ) < p' by exact_mod_cast hp'.pos)
    (show (p' : ℝ) ≤ p by exact_mod_cast hpp)
  have hA : 0 ≤ log a := log_natCast_nonneg a
  have hR : 0 ≤ log r := log_natCast_nonneg r
  rw [hPa,hRa,hPr]
  apply (div_le_div_iff₀ (by linarith : 0 < log p+log a)
    (by linarith : 0 < log p'+log r+log a)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hpp' hA,mul_nonneg hP.le hR]

/-- A genuinely small inserted prime preserves EVERY actual occupied
cofactor bin. Small primes are not forbidden by the whole core mask. -/
theorem small_insertion_bins_eq (N : ℕ) {r a : ℕ} (hr : r.Prime)
    (ha : a ≠ 0) (hsmall : log r ≤ ZetaRieszFewBinCoverFloor.binHead N) :
    ZetaRieszFewBinCoverFloor.cofactorBins N (r*a) =
      ZetaRieszFewBinCoverFloor.cofactorBins N a := by
  rw [ZetaRieszFewBinCoverFloor.cofactorBins,ZetaRieszFewBinCoverFloor.cofactorBins,
    Nat.primeFactors_mul hr.ne_zero ha,hr.primeFactors,Finset.filter_union,Finset.image_union]
  have hf : ({r} : Finset ℕ).filter (fun p : ℕ => ZetaRieszFewBinCoverFloor.binHead N<log p)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    have hpr : p=r := Finset.mem_singleton.mp hp
    subst p
    exact not_lt.mpr hsmall
  rw [hf,Finset.image_empty,Finset.empty_union]

/-- An occupied actual cofactor bin makes the canonical owner eligible
for the ORIGINAL allocation. No all-leg roughness hypothesis is needed. -/
theorem manybin_owner_eligible {u : ℝ} {N n : ℕ} (hN : 0 < N)
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N)
    (hc : 2 ≤ n.primeFactors.card)
    (hB : (ZetaRieszFewBinCoverFloor.cofactorBins N (n/largestPrime n)).Nonempty) :
    largestPrime n ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two hc
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hn0 := (Nat.mem_primeFactors.mp hp).2.2
  obtain ⟨i,hi⟩ := hB
  obtain ⟨r,hr,_⟩ := Finset.mem_image.mp hi
  obtain ⟨hr,hhead⟩ := Finset.mem_filter.mp hr
  have hrP := Nat.prime_of_mem_primeFactors hr
  have hrn : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hrP,(Nat.dvd_of_mem_primeFactors hr).trans
      (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)),hn0⟩
  have hmax : r ≤ largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨r,hrn⟩)]
    exact Finset.le_max' _ _ hrn
  have hlog := log_le_log (show (0 : ℝ) < r by exact_mod_cast hrP.pos)
    (show (r : ℝ) ≤ largestPrime n by exact_mod_cast hmax)
  have hhead' := le_max_right (5000 : ℝ) (32*log ((N : ℝ)+1))
  change 32*log ((N : ℝ)+1) ≤ ZetaRieszFewBinCoverFloor.binHead N at hhead'
  have hlogN : log (N : ℝ) ≤ log ((N : ℝ)+1) :=
    log_le_log (by exact_mod_cast hN) (by linarith)
  have hlow : N^2 < largestPrime n := by
    by_contra h
    have hpn : largestPrime n ≤ N^2 := Nat.le_of_not_gt h
    have hle := log_le_log (show (0 : ℝ) < largestPrime n by exact_mod_cast hpP.pos)
      (show (largestPrime n : ℝ) ≤ (N^2 : ℕ) by exact_mod_cast hpn)
    rw [Nat.cast_pow,log_pow] at hle
    norm_num only [Nat.cast_ofNat] at hle
    linarith [log_natCast_nonneg N]
  have hphys := (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1).2
  exact (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N _).mpr
    ⟨hpP,hlow,hphys _ hp⟩

/-- Every retained core owner has ample margin for the lower-tail
saving. This uses the CURRENT paid owner crop, not a new share assumption. -/
theorem remaining_owner_share_gt {u : ℝ} {N K n : ℕ}
    (hn : n ∈ ZetaRieszParityPacket.coreBand u N K\
      ZetaRieszSharpOwnerPayment.sector u N K) (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) :
    (3/8 : ℝ) < log (n/largestPrime n : ℕ)/log n := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := hpP.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hd)
  have hln : 0 < log n := log_pos (by exact_mod_cast hn1)
  have hshare := ZetaRieszSharpOwnerPayment.remaining_prime_share_lt hn hp
  have hlog : log (n/largestPrime n : ℕ)=log n-log (largestPrime n) := by
    rw [Nat.cast_div hd (by exact_mod_cast hpP.ne_zero),log_div
      (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpP.ne_zero)]
  rw [hlog]
  apply (lt_div_iff₀ hln).mpr
  dsimp [ZetaRieszSharpOwnerPayment.ownerThreshold] at hshare
  nlinarith

/-- Join every admissible original pair before pricing, retaining every
unmatched signed term. The allocation error is ONE global lower-tail price. -/
theorem matching_owner_floor (S : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : ZetaRieszPairMatching.separatedPairs E) (hS : E ⊆ S ×ˢ S)
    {N : ℕ} (hN : 32 ≤ N) (x : ℕ → ℝ) (F : ℕ → ℂ)
    (hx : ∀ e ∈ E, (3/8 : ℝ) ≤ x e.1 ∧ x e.1 ≤ x e.2 ∧ x e.2 ≤ 1)
    (hF : ∀ e ∈ E, (F e.1).re ≤ 0) :
    -(∑ e ∈ E, ‖F e.1+F e.2‖)-
      (2*exp (-(N : ℝ)/25))*(∑ n ∈ ZetaRieszPairMatching.matchedVertices E, ‖F n‖)+
      (∑ n ∈ S\ZetaRieszPairMatching.matchedVertices E,
        (ownerWeight N (x n) : ℂ)*F n).re ≤
      (∑ n ∈ S, (ownerWeight N (x n) : ℂ)*F n).re := by
  have hb := ZetaRieszInnerHingeTransport.matching_floor_with_signed_rest S E hE hS
    (fun n => (ownerWeight N (x n) : ℂ)*F n)
    (fun e => ‖F e.1+F e.2‖+(2*exp (-(N : ℝ)/25))*‖F e.1‖) (by
      intro e he
      have hh := hx e he
      have ht := owner_pair_floor hN hh.1 hh.2.1 hh.2.2 (F e.1) (F e.2) (hF e he)
      linarith)
  have he : (∑ e ∈ E, ‖F e.1‖) ≤
      ∑ n ∈ ZetaRieszPairMatching.matchedVertices E, ‖F n‖ := by
    rw [ZetaRieszPairMatching.sum_matchedVertices E hE]
    apply Finset.sum_le_sum
    intro e _
    linarith [norm_nonneg (F e.2)]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hb
  have ht := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*exp (-(N : ℝ)/25))
  linarith

/-- The global matching inequality for the actual literal owner residual,
all counts joined. Native coverage and the unallocated pair costs remain
explicit. Arbitrary signed funding is inside w, never set to one. -/
theorem matching_literal_owner_floor (A S : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : ZetaRieszPairMatching.separatedPairs E) (hS : E ⊆ S ×ˢ S)
    {N : ℕ} (hN : 32 ≤ N) {L u B : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hB : 0 ≤ B)
    (y : ℝ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ ZetaRieszPairMatching.matchedVertices E, ‖w n‖ ≤ B)
    (hdata : ∀ n ∈ ZetaRieszPairMatching.matchedVertices E,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hx : ∀ e ∈ E,
      (3/8 : ℝ) ≤ log (e.1/largestPrime e.1 : ℕ)/log e.1 ∧
      log (e.1/largestPrime e.1 : ℕ)/log e.1 ≤ log (e.2/largestPrime e.2 : ℕ)/log e.2 ∧
      log (e.2/largestPrime e.2 : ℕ)/log e.2 ≤ 1)
    (hF : ∀ e ∈ E, (w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
      zetaPrimeLogKernel N (3/2+Complex.I*y) e.1).re ≤ 0) :
    -u^(N+1)*(∑ e ∈ E, ‖w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
        zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
      w e.2*SquarefreeVaughanLogSource.coefficient L e.2*
        zetaPrimeLogKernel N (3/2+Complex.I*y) e.2‖)-
      (2*radiusCeiling*B*exp (-(N : ℝ)/50))*zetaMoebiusLogMajorantMass (1+1/262144)+
      u^(N+1)*(∑ n ∈ S\ZetaRieszPairMatching.matchedVertices E,
        w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
      u^(N+1)*(∑ n ∈ S, w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  let F := fun n => w n*SquarefreeVaughanLogSource.coefficient L n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let O := fun n => w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let D := ZetaRieszPairMatching.matchedVertices E
  have he (n : ℕ) (hn : n ∈ D) :
      O n=(ownerWeight N (log (n/largestPrime n : ℕ)/log n) : ℂ)*F n := by
    obtain ⟨hs,hc,hA⟩ := hdata n hn
    have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
    have hw' := ZetaRieszOwnerVariation.single_prime_share A N hs hc hp hA
    have hweight : ownerWeight N (log (n/largestPrime n : ℕ)/log n) =
        1-boundedShare (A ∩ {largestPrime n}) N n := by
      rw [hw']
      rfl
    rw [hweight]
    dsimp [O,F,residualCoefficient]
    push_cast
    ring
  have hpair : ∀ e ∈ E,
      -(‖F e.1+F e.2‖+(2*exp (-(N : ℝ)/25))*‖F e.1‖) ≤ (O e.1+O e.2).re := by
    intro e ht
    have hv1 : e.1 ∈ D := Finset.mem_biUnion.mpr ⟨e,ht,by simp [ZetaRieszPairMatching.pairVertices]⟩
    have hv2 : e.2 ∈ D := Finset.mem_biUnion.mpr ⟨e,ht,by simp [ZetaRieszPairMatching.pairVertices]⟩
    rw [he e.1 hv1,he e.2 hv2]
    have hh := hx e ht
    have hb := owner_pair_floor hN hh.1 hh.2.1 hh.2.2 (F e.1) (F e.2) (hF e ht)
    linarith
  have hb := ZetaRieszInnerHingeTransport.matching_floor_with_signed_rest S E hE hS O
    (fun e => ‖F e.1+F e.2‖+(2*exp (-(N : ℝ)/25))*‖F e.1‖) hpair
  have hd : (∑ e ∈ E, ‖F e.1‖) ≤ ∑ n ∈ D, ‖F n‖ := by
    dsimp [D]
    rw [ZetaRieszPairMatching.sum_matchedVertices E hE]
    apply Finset.sum_le_sum
    intro e _
    linarith [norm_nonneg (F e.2)]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hu (N+1))
  have hp := total_lower_tail_price D w hB hw hL hu hU N y
  change u^(N+1)*(2*exp (-(N : ℝ)/25))*(∑ n ∈ D, ‖F n‖) ≤ _ at hp
  have ht := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ u^(N+1)*(2*exp (-(N : ℝ)/25)) by positivity)
  change -u^(N+1)*(∑ e ∈ E, ‖F e.1+F e.2‖)-
    (2*radiusCeiling*B*exp (-(N : ℝ)/50))*zetaMoebiusLogMajorantMass (1+1/262144)+
      u^(N+1)*(∑ n ∈ S\D, O n).re ≤ u^(N+1)*(∑ n ∈ S, O n).re
  nlinarith

/-- The ORIGINAL joined funding coefficients have a uniform envelope;
overlap keeps both credit and debit. No sign is replaced inside a pair. -/
theorem rejoined_weights_abs_le (H P T Y : Finset ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (debit : ℝ) (n : ℕ) :
    |ZetaRieszRejoinedPhaseFloor.rejoinedWeights H P T Y a b debit n| ≤ 3+|debit| := by
  have hd := abs_le.mp (le_rfl : |debit| ≤ |debit|)
  unfold ZetaRieszRejoinedPhaseFloor.rejoinedWeights
  split_ifs <;> simp only [mul_one,mul_zero,add_zero,zero_add,sub_zero] <;>
    apply abs_le.mpr <;> constructor <;> linarith

/-- With the SAME fixed epsilon and native relative debit, every original
funding multiplier is eventually bounded by ONE constant4+|epsilon|. -/
theorem eventually_rejoined_weights_bound (c κ ε : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (H P T Y : Finset ℕ) (a b : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → ∀ n : ℕ,
      ‖(ZetaRieszRejoinedPhaseFloor.rejoinedWeights H P T Y a b
        (ZetaRieszLowCountRefund.tailCost c N+ε+
          ZetaRieszRejoinedPopulationFloor.growingDebit κ N) n : ℝ)‖ ≤ 4+|ε| := by
  have ht := (ZetaRieszRejoinedPopulationFloor.tendsto_total_relative_debit c κ).norm
  simp only [norm_zero,Real.norm_eq_abs] at ht
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |ZetaRieszLowCountRefund.tailCost c N+
        ZetaRieszRejoinedPopulationFloor.growingDebit κ N| < 1 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with N hN
  intro H P T Y a b ha ha1 hb hb1 n
  have hw := rejoined_weights_abs_le H P T Y ha ha1 hb hb1
    (ZetaRieszLowCountRefund.tailCost c N+ε+
      ZetaRieszRejoinedPopulationFloor.growingDebit κ N) n
  have hd : |ZetaRieszLowCountRefund.tailCost c N+ε+
      ZetaRieszRejoinedPopulationFloor.growingDebit κ N| ≤
      |ZetaRieszLowCountRefund.tailCost c N+
        ZetaRieszRejoinedPopulationFloor.growingDebit κ N|+|ε| := by
    calc
      _ = |(ZetaRieszLowCountRefund.tailCost c N+
          ZetaRieszRejoinedPopulationFloor.growingDebit κ N)+ε| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  rw [Real.norm_eq_abs]
  linarith

/-- ONE global absolute lower-tail payment for the actual funded ledger,
all original counts/periods and overlaps together. The geometric cost is
independent of any matching capacity or assumed prime cancellation. -/
theorem eventually_funded_lower_tail_price {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ radiusCeiling) (c κ ε : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (H P T Y D : Finset ℕ) (a b L y : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 < L →
      u^(N+1)*(2*exp (-(N : ℝ)/25))*
        (∑ n ∈ D, ‖((ZetaRieszRejoinedPhaseFloor.rejoinedWeights H P T Y a b
          (ZetaRieszLowCountRefund.tailCost c N+ε+
            ZetaRieszRejoinedPopulationFloor.growingDebit κ N) n : ℝ) : ℂ)*
          SquarefreeVaughanLogSource.coefficient L n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
        (2*radiusCeiling*(4+|ε|)*exp (-(N : ℝ)/50))*
          zetaMoebiusLogMajorantMass (1+1/262144) := by
  filter_upwards [eventually_rejoined_weights_bound c κ ε] with N hN
  intro H P T Y D a b L y ha ha1 hb hb1 hL
  apply total_lower_tail_price D _ (by positivity : 0 ≤ (4 : ℝ)+|ε|) ?_ hL hu hU N y
  intro n _
  simpa only [Complex.norm_real] using hN H P T Y a b ha ha1 hb hb1 n

/-- The actual global funded lower-tail price tends to zero with all
moving masks/heights retained. This does not pay the joined pair gaps. -/
theorem tendsto_funded_lower_tail_price {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ radiusCeiling) (c κ ε : ℝ)
    (H P T Y D : ℕ → Finset ℕ) (a b L y : ℕ → ℝ)
    (ha : ∀ N, 0 ≤ a N) (ha1 : ∀ N, a N ≤ 1)
    (hb : ∀ N, 0 ≤ b N) (hb1 : ∀ N, b N ≤ 1) (hL : ∀ N, 0 < L N) :
    Tendsto (fun N : ℕ => u^(N+1)*(2*exp (-(N : ℝ)/25))*
      (∑ n ∈ D N, ‖((ZetaRieszRejoinedPhaseFloor.rejoinedWeights
        (H N) (P N) (T N) (Y N) (a N) (b N)
        (ZetaRieszLowCountRefund.tailCost c N+ε+
          ZetaRieszRejoinedPopulationFloor.growingDebit κ N) n : ℝ) : ℂ)*
        SquarefreeVaughanLogSource.coefficient (L N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*(y N)) n‖)) atTop (𝓝 0) := by
  have hsmall := tendsto_polynomial_lower_tail_price
    (2*radiusCeiling*(4+|ε|)*zetaMoebiusLogMajorantMass (1+1/262144)) 0
  simp only [pow_zero,mul_one] at hsmall
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hsmall
  filter_upwards [eventually_funded_lower_tail_price hu hU c κ ε] with N hN
  have ht := hN (H N) (P N) (T N) (Y N) (D N) (a N) (b N) (L N) (y N)
    (ha N) (ha1 N) (hb N) (hb1 N) (hL N)
  exact ht.trans_eq (by ring)

/-- Reuse the single existing nonowner payment with a bounded ORIGINAL
funding coefficient. It is not a new credit or a per-pair charge. -/
theorem weighted_nonowner_error (A D : Finset ℕ) (w : ℕ → ℂ) {B L u : ℝ}
    (hB : 0 < B) (hw : ∀ n ∈ D, ‖w n‖ ≤ B) (hL : 0 < L)
    (N : ℕ) (hD : D ⊆ ZetaRieszJointAllocation.literalWindow N)
    (y : ℝ) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D, w n*
      (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      B*((4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) := by
  have huU : u ≤ exp (-(11/16 : ℝ)) :=
    hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le
  have hb := ZetaRieszNonownerAllocation.residual_sub_owner_bound (fun _ => A) D
    (fun n => w n/(B : ℂ)) hL N hD (by
      intro n hn
      rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hB.le]
      exact (div_le_one hB).mpr (hw n hn)) y hu huU
  have he : (u : ℂ)^(N+1)*∑ n ∈ D, w n*
      (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      (B : ℂ)*((u : ℂ)^(N+1)*∑ n ∈ D, (w n/(B : ℂ))*
        (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    field_simp [Complex.ofReal_ne_zero.mpr hB.ne']
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hB.le]
  exact mul_le_mul_of_nonneg_left hb hB.le

/-- A source-normalized lower inequality for the WHOLE ORIGINAL signed
sum. Matching costs contain only the joined unallocated pair; original
unmatched atoms stay signed. Allocation errors are geometric and paid once.
No partner coverage or numerical bound on the joined pair gaps is assumed. -/
theorem matching_original_floor (A S : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : ZetaRieszPairMatching.separatedPairs E) (hS : E ⊆ S ×ˢ S)
    {N : ℕ} (hN : 32 ≤ N) {L u B : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hB : 0 < B)
    (y : ℝ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ ZetaRieszPairMatching.matchedVertices E, ‖w n‖ ≤ B)
    (hD : ZetaRieszPairMatching.matchedVertices E ⊆ ZetaRieszJointAllocation.literalWindow N)
    (hdata : ∀ n ∈ ZetaRieszPairMatching.matchedVertices E,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hx : ∀ e ∈ E,
      (3/8 : ℝ) ≤ log (e.1/largestPrime e.1 : ℕ)/log e.1 ∧
      log (e.1/largestPrime e.1 : ℕ)/log e.1 ≤ log (e.2/largestPrime e.2 : ℕ)/log e.2 ∧
      log (e.2/largestPrime e.2 : ℕ)/log e.2 ≤ 1)
    (hF : ∀ e ∈ E, (w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
      zetaPrimeLogKernel N (3/2+Complex.I*y) e.1).re ≤ 0) :
    -u^(N+1)*(∑ e ∈ E, ‖w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
        zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
      w e.2*SquarefreeVaughanLogSource.coefficient L e.2*
        zetaPrimeLogKernel N (3/2+Complex.I*y) e.2‖)-
      (2*radiusCeiling*B*exp (-(N : ℝ)/50))*zetaMoebiusLogMajorantMass (1+1/262144)-
      B*((4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))))+
      u^(N+1)*(∑ n ∈ S\ZetaRieszPairMatching.matchedVertices E,
        w n*residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
      u^(N+1)*(∑ n ∈ S, w n*residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  let D := ZetaRieszPairMatching.matchedVertices E
  let F := fun n => w n*residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let O := fun n => w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hDS : D ⊆ S := ZetaRieszPairMatching.matchedVertices_subset hS
  have hES : E ⊆ D ×ˢ D := by
    intro e he
    exact Finset.mem_product.mpr
      ⟨Finset.mem_biUnion.mpr ⟨e,he,by simp [ZetaRieszPairMatching.pairVertices]⟩,
        Finset.mem_biUnion.mpr ⟨e,he,by simp [ZetaRieszPairMatching.pairVertices]⟩⟩
  have hm := matching_literal_owner_floor A D E hE hES hN hL hu hU hB.le y w hw hdata hx hF
  dsimp [D] at hm
  simp only [Finset.sdiff_self,Finset.sum_empty,Complex.zero_re,mul_zero,add_zero] at hm
  have he := weighted_nonowner_error A D w hB hw hL N hD y hu hU
  have heq : (u : ℂ)^(N+1)*∑ n ∈ D, w n*
      (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      (u : ℂ)^(N+1)*((∑ n ∈ D,F n)-(∑ n ∈ D,O n)) := by
    simp only [F,O,mul_sub,sub_mul,Finset.sum_sub_distrib]
  rw [heq] at he
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.sub_re] at hr
  have hsum := Finset.sum_sdiff (f := F) hDS
  have hrsum := congrArg Complex.re hsum
  rw [Complex.add_re] at hrsum
  have hscaled := congrArg (fun z : ℝ => u^(N+1)*z) hrsum
  rw [mul_add] at hscaled
  rw [mul_sub] at hr
  change _ + u^(N+1)*(∑ n ∈ S\D,F n).re ≤ u^(N+1)*(∑ n ∈ S,F n).re
  change _ ≤ u^(N+1)*(∑ n ∈ D,O n).re at hm
  linarith

end RiemannGaussian.ZetaRieszOwnerPairFloor
