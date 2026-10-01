/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDenseSmallTopFloor
import RiemannGaussian.ZetaRieszRoughFivePeriodFloor
import RiemannGaussian.ZetaRieszRoughFiveJoinedFloor
import RiemannGaussian.ZetaRieszLogCountBudget

set_option autoImplicit false

/-!
# Signed count tilt inside the actually unpaid count band

The very small-top population is already in the old logarithmic tail.
This module instead keeps a lower count cutoff in the literal signed
owner-prime periods. The tilt applies after period cancellation. It
requires no occupied-bin, parity, spread or opposite-rank matching premise.
The original allocation and both Riesz hinges remain present.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszUnpaidCountTiltFloor
open ZetaRieszDenseSmallTopFloor ZetaRieszParityLayerCost
open ZetaRieszBroadOwnerPeriodFloor ZetaRieszSmallCofactorCancellation
open ZetaRieszSmallOwnerBoundary ZetaRieszSignedPeriodFloor
open ZetaRieszFixedCountPeriod ZetaRieszPrimeEndpoint ZetaRieszAllowancePrimeBoxes
open ZetaRieszStaggeredFloor ZetaRieszLogShellPeriodFloor
open ZetaRieszRoughFivePeriodFloor
open ZetaRieszRadialCompensation ZetaRieszSmallPrimeCompensation
open ZetaRieszFourPrimeHead ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead
open ZetaRieszBandCompensation ZetaRieszMultiPeriodSix

set_option maxHeartbeats 800000

/-- A convenient rational certificate for the count marker, not a
numerically assumed exponent. -/
theorem log_count_marker_lower : (9/10 : ℝ) ≤ log (5/2 : ℝ) := by
  rw [log_div (by norm_num : (5 : ℝ)≠0) (by norm_num : (2 : ℝ)≠0)]
  linarith [log_five_gt_d9,log_two_lt_d9]

/-- Keep the hard lower count BEFORE summing the factorial population
price. This is the cost of an already cancelled signed period, not an
absolute majorant for the source carrier. -/
theorem count_price_log_tail_le (I : Finset ℕ) {M x : ℝ}
    (hM : 0 ≤ M) (_hx : 1 ≤ x) (hI : ∀ k∈I,5*log x ≤ (k : ℝ)) :
    (∑ k∈I,(2*M)^k/(k.factorial : ℝ)) ≤
      exp (5*M-5*log x*log (5/2 : ℝ)) := by
  have hl : 0 ≤ log (5/2 : ℝ) := by linarith only [log_count_marker_lower]
  have hpoint k (hk : k∈I) :
      exp (5*log x*log (5/2 : ℝ))*((2*M)^k/(k.factorial : ℝ)) ≤
        (5*M)^k/(k.factorial : ℝ) := by
    have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hI k hk) hl)
    rw [← log_pow,exp_log (by positivity : (0 : ℝ)<(5/2 : ℝ)^k)] at he
    have hh := mul_le_mul_of_nonneg_right he
      (by positivity : 0 ≤ (2*M)^k/(k.factorial : ℝ))
    calc
      _ ≤ (5/2 : ℝ)^k*((2*M)^k/(k.factorial : ℝ)) := hh
      _ = _ := by rw [← mul_div_assoc,← mul_pow,show (5/2 : ℝ)*(2*M)=5*M by ring]
  have he := NormedSpace.expSeries_div_hasSum_exp (5*M)
  have hs := he.summable.sum_le_tsum I (fun k _ => by positivity)
  rw [he.tsum_eq,← Real.exp_eq_exp_ℝ] at hs
  have hh := (Finset.sum_le_sum hpoint).trans hs
  rw [← Finset.mul_sum] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (exp_pos (-5*log x*log (5/2 : ℝ))).le
  rw [← mul_assoc,show exp (-5*log x*log (5/2 : ℝ))*exp (5*log x*log (5/2 : ℝ))=1 by
    rw [← exp_add,show -5*log x*log (5/2 : ℝ)+5*log x*log (5/2 : ℝ)=0 by ring,exp_zero],one_mul] at hh'
  exact hh'.trans_eq (by
    rw [← exp_add]
    congr 1
    ring)

/-- The finite actual prime mass has leading coefficient ONE in log x.
Together with the exact count tilt this costs at most sqrt x. -/
theorem count_price_sqrt_le (I : Finset ℕ) {M C x : ℝ}
    (hM : 0 ≤ M) (hx : 1 ≤ x) (hm : M ≤ C+log x)
    (hI : ∀ k∈I,5*log x ≤ (k : ℝ)) :
    (∑ k∈I,(2*M)^k/(k.factorial : ℝ)) ≤ exp (5*C+log x/2) := by
  have hl := log_nonneg hx
  have hp := mul_le_mul_of_nonneg_left log_count_marker_lower
    (show 0 ≤ 5*log x by positivity)
  exact (count_price_log_tail_le I hM hx hI).trans
    (exp_le_exp.mpr (by nlinarith only [hm,hp]))

/-- The old already-paid count tail lies below 16 log(N+1). -/
theorem paid_count_threshold_le {N : ℕ} (hN : 7 ≤ N) :
    (ZetaRieszLogCountBudget.countThreshold N : ℝ) ≤ 16*log ((N : ℝ)+1) := by
  have hx : (8 : ℝ) ≤ (N : ℝ)+1 := by exact_mod_cast (show 8 ≤ N+1 by omega)
  have hl2 : (2/3 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hlx := log_le_log (by norm_num : (0 : ℝ)<8) hx
  rw [show (8 : ℝ)=(2 : ℝ)^3 by norm_num,log_pow] at hlx
  have hl : (2 : ℝ) ≤ log ((N : ℝ)+1) := by norm_num at hlx; linarith only [hlx,hl2]
  have hk : 1 ≤ Nat.clog 2 (N+1) := Nat.clog_pos (by decide) (by omega)
  have hp : (2 : ℝ)^(Nat.clog 2 (N+1)-1)<(N : ℝ)+1 := by
    exact_mod_cast Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<N+1 by omega)
  have hh := log_lt_log (by positivity : (0 : ℝ)<(2 : ℝ)^(Nat.clog 2 (N+1)-1)) hp
  rw [log_pow,Nat.cast_sub hk,Nat.cast_one] at hh
  have hkR : (1 : ℝ) ≤ (Nat.clog 2 (N+1) : ℝ) := by exact_mod_cast hk
  have hkn : (0 : ℝ) ≤ (Nat.clog 2 (N+1) : ℝ)-1 := by linarith only [hkR]
  have hlow := mul_le_mul_of_nonneg_left hl2 hkn
  simp only [ZetaRieszLogCountBudget.countThreshold,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hh,hlow,hl]

/-- The former small-top examples are not new unpaid floor coverage:
their original labels belong to the tail already spent in the ledger. -/
theorem small_top_mem_paid_tail (S : Finset ℕ) {N R n a : ℕ}
    (hN : 7 ≤ N) (hnS : n∈S) (hn : Squarefree n) (ha : Squarefree a)
    (had : a∣n) {v J : ℝ} (hJ : 0<J)
    (hlog : ∀ p∈a.primeFactors,log p ≤ 4*J)
    (hcore : v/4 ≤ log a) (hscale : 512*J*log ((N : ℝ)+1) ≤ v) :
    n∈ZetaRieszSevenCountTail.wholeTail S N R := by
  have hc := small_top_count_lower ha hJ hlog hcore hscale
  have hsub := Finset.card_le_card (Nat.primeFactors_mono had hn.ne_zero)
  have hcR : (a.primeFactors.card : ℝ) ≤ (n.primeFactors.card : ℝ) := by exact_mod_cast hsub
  have hl : 0 ≤ log ((N : ℝ)+1) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hpay : (ZetaRieszLogCountBudget.countThreshold N : ℝ) ≤ (n.primeFactors.card : ℝ) := by
    linarith only [paid_count_threshold_le hN,hc,hcR,hl]
  apply Finset.mem_filter.mpr
  exact ⟨hnS,hn,Or.inl (by exact_mod_cast hpay)⟩

/-- The high-count tail is one of the ORIGINAL spent classes. -/
theorem whole_tail_subset_spent (S : Finset ℕ) (N Q P V R : ℕ)
    (η h L : ℝ) (w : ℕ→ℝ) :
    ZetaRieszSevenCountTail.wholeTail S N R ⊆ spent S N Q P V R η h L w := by
  intro n hn
  simp only [spent,Finset.mem_union]
  tauto

/-- Every squarefree label actually remaining in the floor has count
strictly below the OLD paid logarithmic threshold. -/
theorem unpaid_count_lt (S : Finset ℕ) (N Q P V R : ℕ) (η h L : ℝ)
    (w : ℕ→ℝ) {n : ℕ} (hn : n∈S\spent S N Q P V R η h L w)
    (hs : Squarefree n) : n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N := by
  by_contra hc
  have ht : n∈ZetaRieszSevenCountTail.wholeTail S N R :=
    Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1,hs,Or.inl (by omega)⟩
  exact (Finset.mem_sdiff.mp hn).2 (whole_tail_subset_spent S N Q P V R η h L w ht)

/-- All counts from eight up to the old tail threshold miss EVERY old
head, supply and tail charge, independently of prime roughness. Thus a
new complete owner fibre in this band has no previously-spent holes. -/
theorem middle_count_not_spent (S : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0<h) (hhu : h≤1/20)
    (w : ℕ→ℝ) (hw : ∀ M∈radialIndices N,0≤w M ∧ w M≤1/2)
    (hc : 8≤n.primeFactors.card)
    (hct : n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N) :
    n∉spent S N Q P V R η h L w := by
  have hX : n∉radialTriples S N η := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hZ : n∉(radialIndices N).biUnion
      (fun M => smallTriples (S\radialTriples S N η) M Q) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hH : n∉(radialIndices N).biUnion (fun M => smallFours S M Q) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hY : n∉radialSupply N h w := by
    intro hn
    have hm := radialSupply_count hN hh hhu w hw hn
    omega
  have hF : n∉(radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hG : n∉radialHeads S N P V L := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.2.2
    rcases hm with ⟨h6,_⟩ | ⟨h5,_⟩ <;> omega
  have htail : ¬ ZetaRieszSevenPrimeHead.tailCondition N R n := by
    intro hm
    rcases hm with hm | ⟨hm,_⟩ <;> omega
  have hT : n∉ZetaRieszSevenCountTail.radialTail S N R := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact htail (Finset.mem_filter.mp hn).2.2.2.2
  have hC : n∉ZetaRieszSevenCountTail.wholeTail S N R := by
    intro hn
    exact htail (Finset.mem_filter.mp hn).2.2
  simp only [spent,Finset.mem_union]
  tauto

/-- The new dense band lies in the ORIGINAL unpaid ledger whenever its
labels lie in the original core. There is no new carrier or credit. -/
theorem middle_population_subset_unpaid (S D : Finset ℕ) {N Q P V R : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0<h) (hhu : h≤1/20)
    (w : ℕ→ℝ) (hw : ∀ M∈radialIndices N,0≤w M ∧ w M≤1/2)
    (hDS : D⊆S) (hD : ∀ n∈D,8≤n.primeFactors.card ∧
      n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N) :
    D⊆S\spent S N Q P V R η h L w := by
  intro n hn
  exact Finset.mem_sdiff.mpr ⟨hDS hn,
    middle_count_not_spent S hN η hh hhu w hw (hD n hn).1 (hD n hn).2⟩

/-- A genuinely unpaid label cannot have all its prime logs too small:
its old count ceiling supplies the owner scale needed for the new tilt. -/
theorem unpaid_owner_scale (S : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 7≤N) (η h L : ℝ) (w : ℕ→ℝ)
    (hn : n∈S\spent S N Q P V R η h L w) (hs : Squarefree n)
    {v H : ℝ} (hH : 0≤H) (hcore : v/2≤log n)
    (hlog : ∀ p∈n.primeFactors,log p≤4*H) :
    v≤128*H*log ((N : ℝ)+1) := by
  have hc := unpaid_count_lt S N Q P V R η h L w hn hs
  have hcR : (n.primeFactors.card : ℝ) ≤
      (ZetaRieszLogCountBudget.countThreshold N : ℝ) := by exact_mod_cast hc.le
  have hcnt := hcR.trans (paid_count_threshold_le hN)
  have hsum := Finset.sum_le_sum hlog
  rw [Finset.sum_const,nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hsum
  have hh := mul_le_mul_of_nonneg_right hcnt (show 0≤4*H by positivity)
  nlinarith only [hcore,hsum,hh]

/-- The literal signed main for every selected count above 5 log x.
The actual owner allocation, phase and both hinge crossings remain. -/
theorem retained_count_lower_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (Q : Finset ℕ) {v y L H M x : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p∈Q,log p≤4*H)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hx : 1≤x) (hcount : ∀ k∈I,5*log x≤(k : ℝ))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(481*exp (5*M-5*log x*log (5/2 : ℝ))/H)*(amplitude N v/v)≤
      ∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
  have hH0 : 0<H := by linarith only [hH]
  have hv : 0<v := by linarith [hNv,Nat.cast_nonneg (α := ℝ) N]
  have hf : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv.le) hv.le
  have hrow k (hk : k∈I) :
      -(481*(2*M)^k/(H*(k.factorial : ℝ)))*(amplitude N v/v)≤
        ∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
          signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
    have hm := interval_cofactor_mass_le (S k) Q k hQmass (hS k hk)
    have hh := Finset.sum_le_sum (fun a ha => by
      have hs := hS k hk a ha
      have ha1 : a≠1 := by
        intro ha1
        simp [ha1] at hs
        have := hI k hk
        omega
      have hmin := (Nat.minFac_prime ha1).mem_primeFactors (Nat.minFac_dvd a) hs.1.ne_zero
      exact retained_owner_row_floor (hI k hk) he A hH hNv hy hL hs.1 hs.2.1
        (hQlog _ (hs.2.2 hmin)) (hP k hk a ha) (howner k hk a ha) (hA k hk a ha) hpeak hsign)
    rw [← Finset.mul_sum] at hh
    have hc := neg_le_neg (mul_le_mul_of_nonneg_left hm
      (by positivity : 0≤(amplitude N v/v)*(481*(2 : ℝ)^k/H)))
    have hid : -((amplitude N v/v)*(481*(2 : ℝ)^k/H)*(M^k/(k.factorial : ℝ)))=
        -(481*(2*M)^k/(H*(k.factorial : ℝ)))*(amplitude N v/v) := by
      simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hid] at hc
    exact hc.trans (by simpa only [neg_mul,mul_assoc] using hh)
  have ht := count_price_log_tail_le I hM hx hcount
  have hc : (481/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤
      481*exp (5*M-5*log x*log (5/2 : ℝ))/H := by
    exact (mul_le_mul_of_nonneg_left ht (show 0≤481/H by positivity)).trans_eq (by ring)
  have hh := Finset.sum_le_sum hrow
  simp only [neg_mul] at hh
  rw [Finset.sum_neg_distrib,← Finset.sum_mul] at hh
  have heq : (∑ k∈I,481*(2*M)^k/(H*(k.factorial : ℝ)))=
      (481/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at hh
  simpa only [neg_mul] using (neg_le_neg (mul_le_mul_of_nonneg_right hc hf)).trans
    (by simpa only [neg_mul] using hh)

/-- Every ACTUAL clipped ownership boundary keeps the same hard count
cutoff. The two missed sign selections will spend this boundary once. -/
theorem clipped_count_lower_norm_bound (A D Q : Finset ℕ)
    (y : ℝ) (N : ℕ) {v L H M x : ℝ} (hH : 10000≤H) (hv : 0<v)
    (hNv : (N : ℝ)+1≤v) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p∈Q,log p≤4*H) (hx : 1≤x)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      5*log x+2≤(n.primeFactors.card : ℝ) ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆Q) :
    (∑ n∈D,‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
        (1536*exp (5*M-5*log x*log (5/2 : ℝ))/H)*(amplitude N v/v) := by
  let I := D.image (fun n => n.primeFactors.card-2)
  let S := fun k => D.filter (fun n => n.primeFactors.card-2=k)
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hH0 : 0<H := by linarith only [hH]
  have hf : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv.le) hv.le
  have hI k (hk : k∈I) : 0<k := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have := (hD n hn).2.1
    omega
  have hcount k (hk : k∈I) : 5*log x≤(k : ℝ) := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have hd := hD n hn
    have he : (n.primeFactors.card : ℝ)=(n.primeFactors.card-2 : ℕ)+2 := by
      exact_mod_cast (show n.primeFactors.card=n.primeFactors.card-2+2 by omega)
    linarith only [hd.2.2.1,he]
  have hrow k (hk : k∈I) :
      (∑ n∈S k,f n)≤((1536*(2*M)^k/(k.factorial : ℝ))/H)*(amplitude N v/v) := by
    apply broad_clipped_count_norm_bound (hI k hk) A (S k) Q y hH hv hNv hL hM hQmass hQlog
    intro n hn
    obtain ⟨hn,hcnt⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2.2⟩
  have heq : (∑ k∈I,∑ n∈S k,f n)=∑ n∈D,f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have ht := count_price_log_tail_le I hM hx hcount
  have hcost : (1536/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤
      1536*exp (5*M-5*log x*log (5/2 : ℝ))/H := by
    exact (mul_le_mul_of_nonneg_left ht (show 0≤1536/H by positivity)).trans_eq (by ring)
  have hh := Finset.sum_le_sum hrow
  rw [heq,← Finset.sum_mul] at hh
  have heq' : (∑ k∈I,(1536*(2*M)^k/(k.factorial : ℝ))/H)=
      (1536/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq'] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcost hf)

/-- Join all selected count ranks and BOTH actual missed sign selections.
The boundary is paid once, while the signed prime main is never normed. -/
theorem count_lower_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (D Pplus Pminus Q : Finset ℕ) {v y L H M x : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 10000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p∈Q,log p≤4*H)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hx : 1≤x) (hcount : ∀ k∈I,5*log x≤(k : ℝ))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      5*log x+2≤(n.primeFactors.card : ℝ) ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆Q)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(2017*exp (5*M-5*log x*log (5/2 : ℝ))/H)*(amplitude N v/v)≤
      (∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\Pplus,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Pminus,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  have hv : 0<v := by linarith [hNv,Nat.cast_nonneg (α := ℝ) N]
  have hmain := retained_count_lower_floor I N e A S Q hI he
    (by linarith only [hH]) hNv hy hL hM hQmass hQlog hS hx hcount hP howner hA hpeak hsign
  have hn := clipped_count_lower_norm_bound ∅ D Q y N hH hv
    (by linarith only [hNv]) hL hM hQmass hQlog hx hD
  have ha := (Finset.sum_le_sum (fun n (_hn : n∈D) =>
    allocation_family_atom_norm_le (fun n => A∩{largestPrime n}) L y N n)).trans hn
  have hh := add_le_add hmain ((neg_le_neg ha).trans
    (missed_parts_floor (fun n => A∩{largestPrime n}) D Pplus Pminus L y N))
  convert! hh using 1 <;> ring

/-- The old unpaid upper count forces H of order at least N/log N.
Together with the new hard lower count, the joined cost is vanishing
in ACTUAL amplitude/v supply units. -/
theorem lower_count_rate_bound {M C x v H : ℝ} (hx : 1≤x) (hH : 0<H)
    (hM : M≤C+log x) (hxv : x≤v) (hscale : v≤128*H*log x) :
    2017*exp (5*M-5*log x*log (5/2 : ℝ))/H≤
      258176*exp (5*C)*log x*exp (-log x/2) := by
  have hx0 : 0<x := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) hx
  have hl := log_nonneg hx
  have hp := mul_le_mul_of_nonneg_left log_count_marker_lower
    (show 0≤5*log x by positivity)
  have he := exp_le_exp.mpr (show 5*M-5*log x*log (5/2 : ℝ)≤5*C+log x/2 by
    nlinarith only [hM,hp])
  have hi : (1 : ℝ)/H≤128*log x/x := (div_le_div_iff₀ hH hx0).mpr
    (by nlinarith only [hxv,hscale])
  have hh := mul_le_mul_of_nonneg_left hi
    (show 0≤2017*exp (5*C+log x/2) by positivity)
  calc
    _ ≤ 2017*exp (5*C+log x/2)/H := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by norm_num)) hH.le
    _ ≤ 2017*exp (5*C+log x/2)*(128*log x/x) := by simpa only [div_eq_mul_inv,one_mul] using hh
    _ = _ := by
      rw [show exp (5*C+log x/2)=exp (5*C)*exp (log x/2) by rw [exp_add]]
      have heq : exp (log x/2)/x=exp (-log x/2) := by
        conv_lhs => rw [← exp_log hx0]
        rw [log_exp,← exp_sub]
        congr 1
        ring
      calc
        _ = 258176*exp (5*C)*log x*(exp (log x/2)/x) := by ring
        _ = _ := by rw [heq]

/-- The actual finite prime universe, the original signed main and
the actual owner clips all have this single lower-count period floor.
Neither prime-log bins nor parity-layer matching restrict the label set. -/
theorem lower_count_period_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (D Pplus Pminus Q : Finset ℕ) {v y L H : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 10000≤H) (hHx : H≤4*((N : ℝ)+1))
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hQ : ∀ p∈Q,p.Prime ∧ log p≤4*H)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hcount : ∀ k∈I,5*log ((N : ℝ)+1)≤(k : ℝ))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ) ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆Q)
    (hscale : v≤128*H*log ((N : ℝ)+1))
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
        exp (-log ((N : ℝ)+1)/2))*(amplitude N v/v)≤
      (∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\Pplus,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Pminus,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  let C := smallPrimeHeadMass+log 16+1/5000
  let M := C+log ((N : ℝ)+1)
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M := whole_mass_log_bound Q hx
    (by linarith only [hH]) hHx hQ
  have hM : 0≤M := (Finset.sum_nonneg (fun _ _ => by positivity)).trans hmass
  have hh := count_lower_with_boundary_floor I N e A S D Pplus Pminus Q hI he hH
    hNv hy hL hM hmass (fun p hp => (hQ p hp).2) hS hx hcount hP howner hA hD hpeak hsign
  have hp := lower_count_rate_bound hx (by linarith only [hH])
    (show M≤C+log ((N : ℝ)+1) from le_rfl) (by linarith only [hNv]) hscale
  have hv : 0<v := by linarith [hNv,Nat.cast_nonneg (α := ℝ) N]
  have hc := mul_le_mul_of_nonneg_right hp
    (show 0≤amplitude N v/v by positivity [amplitude_nonneg N hv.le])
  simpa only [neg_mul,C] using (neg_le_neg hc).trans (by simpa only [neg_mul] using hh)

/-- One relative price for ALL radial periods and owner scales of the
new dense-count band. This is not an absolute source-envelope price. -/
def unpaidCountSupplyPrice (N : ℕ) : ℝ :=
  258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
    exp (-log ((N : ℝ)+1)/2)*(1+log (4*((N : ℝ)+1))/log 2)

/-- The whole selected owner/radial cost is bounded at once, without
enumerating individual count geometries or spending separate reserves. -/
theorem global_lower_count_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v : ℕ→ℝ) {H : ℝ} (hH : 1≤H)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i) :
    (∑ i∈V,∑ _j∈O i,
      (258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
        exp (-log ((N : ℝ)+1)/2))*(amplitude N (v i)/v i))≤
      unpaidCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hrow i (hi : i∈V) :
      (∑ _j∈O i,
        (258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
          exp (-log ((N : ℝ)+1)/2))*(amplitude N (v i)/v i))≤
        unpaidCountSupplyPrice N*(amplitude N (v i)/v i) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hc := dyadic_owner_card_le (O i) hH
      (by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N] : 1≤v i) (hO i hi)
    have hl := div_le_div_of_nonneg_right (log_le_log hv (hvG i hi))
      (log_pos (by norm_num : (1 : ℝ)<2)).le
    have hcg : ((O i).card : ℝ)≤1+log (4*((N : ℝ)+1))/log 2 := by linarith only [hc,hl]
    have hh := mul_le_mul_of_nonneg_right hcg
      (show 0≤(258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
        exp (-log ((N : ℝ)+1)/2))*(amplitude N (v i)/v i) by
          positivity [log_nonneg (show 1≤(N : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) N]),
            amplitude_nonneg N hv.le])
    simpa only [Finset.sum_const,nsmul_eq_mul,unpaidCountSupplyPrice,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh := Finset.sum_le_sum hrow
  simpa only [Finset.mul_sum] using hh

/-- The full new count-band cost tends to zero. Its conservative proven
rate is O(log(N)^2 / sqrt(N)); the fixed arithmetic head is unevaluated. -/
theorem tendsto_unpaidCountSupplyPrice : Tendsto unpaidCountSupplyPrice atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := tendsto_log_atTop.comp hn
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/2) (by norm_num)).comp hl
  have h₂ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/2) (by norm_num)).comp hl
  simp only [Function.comp_def,rpow_one] at h₁
  simp only [Function.comp_def] at h₂
  have ht := ((h₁.const_mul (1+log 4/log 2)).add
    (h₂.const_mul (log 2)⁻¹)).const_mul (258176*exp (5*(smallPrimeHeadMass+log 16+1/5000)))
  convert ht using 1
  · funext N
    unfold unpaidCountSupplyPrice
    rw [log_mul (by norm_num : (4 : ℝ)≠0) (by positivity : (N : ℝ)+1≠0),rpow_two]
    simp only [div_eq_mul_inv]
    ring
  · ring

/-- The global SIGNED inequality, joining every selected radial period,
dyadic owner scale and count rank with both missed ownership selections.
It covers every share spread and either parity; no matching assumption
or positive absolute main allowance enters. All literal fibre premises
stay explicit. -/
theorem global_lower_count_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v e : ℕ→ℝ) (I : ℕ→ℕ→Finset ℕ)
    (S : ℕ→ℕ→ℕ→Finset ℕ) (D Pplus Pminus Q : ℕ→ℕ→Finset ℕ) (A : Finset ℕ)
    {H y L : ℝ} (hH : 10000≤H) (hy : 54≤y)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (he : ∀ i∈V,|e i|=1) (hL : ∀ i∈V,v i/2≤L)
    (hscale : ∀ i∈V,∀ j∈O i,v i≤128*(H*(2 : ℝ)^j)*log ((N : ℝ)+1))
    (hQ : ∀ i∈V,∀ j∈O i,∀ p∈Q i j,p.Prime ∧ log p≤4*(H*(2 : ℝ)^j))
    (hI : ∀ i∈V,∀ j∈O i,∀ k∈I i j,2≤k)
    (hcount : ∀ i∈V,∀ j∈O i,∀ k∈I i j,5*log ((N : ℝ)+1)≤(k : ℝ))
    (hS : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q i j)
    (hP : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ n∈D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ) ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆Q i j)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -unpaidCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
         (∑ n∈D i j\Pplus i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
         (∑ n∈D i j\Pminus i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) :
      -(258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
          exp (-log ((N : ℝ)+1)/2))*(amplitude N (v i)/v i)≤
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
         (∑ n∈D i j\Pplus i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
         (∑ n∈D i j\Pminus i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hHj : 10000≤H*(2 : ℝ)^j := by
      have hp := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hH,hp]
    exact lower_count_period_floor (I i j) N (e i) A (S i j) (D i j) (Pplus i j) (Pminus i j) (Q i j)
      (hI i hi j hj) (he i hi) hHj ((hO i hi j hj).trans (hvG i hi))
      (hNv i hi) hy (hL i hi) (hQ i hi j hj) (hS i hi j hj) (hcount i hi j hj)
      (hP i hi j hj) (howner i hi j hj) (hA i hi j hj) (hD i hi j hj)
      (hscale i hi j hj) (hpeak i hi) (hsign i hi)
  have ht := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  simp only [neg_mul,Finset.sum_neg_distrib] at ht
  have hc := global_lower_count_cost_le V O N v (by linarith only [hH]) hNv hvG hO
  simpa only [neg_mul] using (neg_le_neg hc).trans ht

/-- ANY fixed fresh fraction of the same positive radial reserve pays
the entire new global count-band price eventually. This compares true
supply units and does not assert source-scale decay of those units. -/
theorem eventually_unpaid_count_price_paid {κ : ℝ} (hκ : 0<κ) :
    ∀ᶠ N : ℕ in atTop,unpaidCountSupplyPrice N≤κ :=
  (tendsto_order.1 tendsto_unpaidCountSupplyPrice).2 κ hκ |>.mono (fun _ h => h.le)

/-- The price is paid by the SAME literal four-prime supply selection
as the published whole floor, consuming at most half its retained
1/128 fraction. No second phase-window witness or anonymous fresh
reserve is introduced. The source-scale growth of the positive units
is immaterial to this relative signed payment. -/
theorem eventually_count_cost_paid_by_same_supply {c y : ℝ}
    (hc : 0<c) (hy : 54≤y) :
    ∀ᶠ N : ℕ in atTop,∀ (h v : ℝ) (w : ℕ→ℝ) (f : ℕ→ℂ)
      (H : Finset ℕ) (I J : ℕ→Finset ℕ),
      h≤1/20 →
      (∀ M∈radialIndices N,0≤w M ∧ w M≤1/2) →
      (∀ M∈radialIndices N,
        c*(M : ℝ)*exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
          (∑ n∈supply M h (w M),f n).re) →
      H⊆radialIndices N →
      (∀ M∈H,∀ i∈I M,2*(M : ℝ)≤center v y i ∧ center v y i<2*M+2) →
      (∀ M∈H,∀ i∈J M,2*(M : ℝ)≤center (v+Real.pi/y) y i ∧
        center (v+Real.pi/y) y i<2*M+2) →
      unpaidCountSupplyPrice N*
        ((∑ i∈H.biUnion I,exp (-center v y i/2)*(center v y i)^N/N.factorial)+
         (∑ i∈H.biUnion J,exp (-center (v+Real.pi/y) y i/2)*
           (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (1/256 : ℝ)*(∑ n∈radialSupply N h w,f n).re := by
  let κ := c/(512*((⌊2*y⌋₊ : ℝ)+1)*exp 2)
  have hκ : 0<κ := by dsimp [κ]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_unpaid_count_price_paid (show 0<κ/2 by positivity)]
    with N hN hprice h v w f H I J hhu hw hscale hH hI hJ
  have hp := ZetaRieszRoughFiveJoinedFloor.period_grids_cost_paid hN hc hy hhu
    (show κ=c/(512*((⌊2*y⌋₊ : ℝ)+1)*exp 2) from rfl)
    w f H I J hw hscale hH hI hJ
  have hi : 0≤∑ i∈H.biUnion I,exp (-center v y i/2)*(center v y i)^N/N.factorial := by
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨M,hM,hi⟩ := Finset.mem_biUnion.mp hi
    have hv : 0≤center v y i := (show 0≤2*(M : ℝ) by positivity).trans (hI M hM i hi).1
    positivity
  have hj : 0≤∑ i∈H.biUnion J,exp (-center (v+Real.pi/y) y i/2)*
      (center (v+Real.pi/y) y i)^N/N.factorial := by
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨M,hM,hi⟩ := Finset.mem_biUnion.mp hi
    have hv : 0≤center (v+Real.pi/y) y i :=
      (show 0≤2*(M : ℝ) by positivity).trans (hJ M hM i hi).1
    positivity
  have hh := mul_le_mul_of_nonneg_right hprice (add_nonneg hi hj)
  have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ)≤1/2)
  nlinarith only [hh,hp']

/-- Complete owner fibres preserve squarefreeness and count literally,
without the old fixed-count cofactor-share cap. -/
theorem owner_fibre_count {a p : ℕ} (ha : Squarefree a) {v y : ℝ}
    (ho : ∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hp : p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)) :
    Squarefree (a*p) ∧ (a*p).primeFactors.card=a.primeFactors.card+1 := by
  have hpp := (logPrimes_bounds hp).1
  have hnot : p∉a.primeFactors := by
    intro hpa
    exact (not_lt_of_ge (ho p hpa)) (logPrimes_bounds hp).2.1
  have hnd : ¬p∣a := fun hd => hnot (hpp.mem_primeFactors hd ha.ne_zero)
  have hs : Squarefree (p*a) := Nat.squarefree_mul_iff.mpr
    ⟨hpp.coprime_iff_not_dvd.mpr hnd,hpp.squarefree,ha⟩
  have hc : (p*a).primeFactors.card=a.primeFactors.card+1 := by
    rw [Nat.primeFactors_mul hpp.ne_zero ha.ne_zero,hpp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem hnot]
  simpa only [Nat.mul_comm a p] using And.intro hs hc

/-- No label in these literal growing-count owner fibres was previously
spent. Only containment in the original core remains a support premise. -/
theorem literal_owner_population_subset_unpaid (S M : Finset ℕ)
    {N Q P V R : ℕ} (hN : 1000≤N) (η : ℝ) {h L v y : ℝ}
    (hh : 0<h) (hhu : h≤1/20) (w : ℕ→ℝ)
    (hw : ∀ i∈radialIndices N,0≤w i ∧ w i≤1/2)
    (hM : ∀ a∈M,Squarefree a ∧ 7≤a.primeFactors.card ∧
      a.primeFactors.card+1<ZetaRieszLogCountBudget.countThreshold N)
    (ho : ∀ a∈M,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hcore : M.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)).image (fun p => a*p))⊆S) :
    M.biUnion (fun a => (logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)).image (fun p => a*p))⊆
      S\spent S N Q P V R η h L w := by
  apply middle_population_subset_unpaid S _ hN η hh hhu w hw hcore
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hd := owner_fibre_count (hM a ha).1 (ho a ha) hp
  rw [hd.2]
  have hc := (hM a ha).2.1
  exact ⟨by omega,(hM a ha).2.2⟩

/-- Reindex the proved signed count inequality onto LITERAL integer
labels. Counts and marked incidences cannot multiply a label. This
bound has the same hard cutoff and full allocation as the finite row
estimate; no new representation or completed cofactor is introduced. -/
theorem retained_literal_count_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (Q : Finset ℕ) {v y L H M x : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p∈Q,log p≤4*H)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hx : 1≤x) (hcount : ∀ k∈I,5*log x≤(k : ℝ))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(481*exp (5*M-5*log x*log (5/2 : ℝ))/H)*(amplitude N v/v)≤
      ∑ n∈(I.biUnion S).biUnion (fun a =>
        (logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)).image (fun p => a*p)),
          signedPart e (A∩{largestPrime n}) L y N n := by
  have hdata a (ha : a∈I.biUnion S) : Squarefree a ∧
      (∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a) := by
    obtain ⟨k,hk,ha⟩ := Finset.mem_biUnion.mp ha
    exact ⟨(hS k hk a ha).1,howner k hk a ha⟩
  have hd : (I : Set ℕ).Pairwise (fun k k' => Disjoint (S k) (S k')) := by
    intro k hk k' hk' hne
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    exact hne ((hS k hk a ha).2.1.symm.trans (hS k' hk' a ha').2.1)
  have heq := congrArg Complex.re (ZetaRieszCoupledWindow.sum_owned_products
    (I.biUnion S) (fun a => logPrimes (v-Real.pi/y-log a) (2*Real.pi/y))
    (fun n => (signedPart e (A∩{largestPrime n}) L y N n : ℂ))
    (fun a ha => (hdata a ha).1.ne_zero) (by
      intro a ha p hp
      have hpp := (logPrimes_bounds hp).1
      refine ⟨hpp,?_⟩
      intro q hq hqa
      have hqm := hq.mem_primeFactors hqa (hdata a ha).1.ne_zero
      have hl := ((hdata a ha).2 q hqm).trans_lt (logPrimes_bounds hp).2.1
      exact_mod_cast (log_lt_log_iff (by exact_mod_cast hq.pos) (by exact_mod_cast hpp.pos)).mp hl))
  simp only [Complex.re_sum,Complex.ofReal_re] at heq
  rw [Finset.sum_biUnion hd] at heq
  have ht := retained_count_lower_floor I N e A S Q hI he hH hNv hy hL hM hQmass hQlog
    hS hx hcount hP howner hA hpeak hsign
  rw [heq]
  simpa only [Nat.mul_comm] using ht

end RiemannGaussian.ZetaRieszUnpaidCountTiltFloor
