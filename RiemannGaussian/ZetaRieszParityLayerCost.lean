/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCrossCountTransport
import RiemannGaussian.ZetaRieszSmallOwnerBoundary

/-!
# Price the complete signed periods with their logarithmic count constraint

Opposite-count transport can leave reinforcing parity layers. Their cost
must be aggregated over the actual cofactor population, rather than over
all possible counts without the original total-log constraint. A tilted
factorial count sum retains that constraint through the signed prime period
and the literal ownership boundary. All prices below use `amplitude/v`,
the actual positive radial-supply unit. No whole-core cover is asserted.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszParityLayerCost
open ZetaRieszBroadOwnerPeriodFloor ZetaRieszSmallCofactorCancellation
open ZetaRieszSmallOwnerBoundary ZetaRieszClippedOwnerPeriodFloor
open ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszPrimeEndpoint ZetaRieszAllowancePrimeBoxes
open ZetaRieszOwnerCurvatureFloor ZetaRieszJointOwnerFibreFloor
open ZetaRieszStaggeredFloor
open ZetaRieszTinyOwnerPeriodFloor ZetaRieszLogShellPeriodFloor
open ZetaRieszSymmetricPeriodPayment

set_option maxHeartbeats 800000

private theorem count_tilt {v H : ℝ} (hH : 0<H) {k : ℕ}
    (hc : v≤4*H*((k : ℝ)+3)) : exp (v/(8*H))≤8*(2 : ℝ)^k := by
  have hlog : (1/2 : ℝ)≤log 2 := by linarith [log_two_gt_d9]
  have harg : v/(8*H)≤((k : ℝ)+3)*log 2 := by
    have hh : v/(8*H)≤((k : ℝ)+3)/2 :=
      (div_le_iff₀ (show 0<8*H by positivity)).mpr (by nlinarith only [hc])
    have ht := mul_le_mul_of_nonneg_left hlog
      (by positivity : 0≤(k : ℝ)+3)
    nlinarith only [hh,ht]
  have hh := exp_le_exp.mpr harg
  rw [show ((k : ℝ)+3)*log 2=log ((2 : ℝ)^(k+3)) by
    rw [log_pow,Nat.cast_add,Nat.cast_ofNat]] at hh
  rw [exp_log (by positivity),pow_add] at hh
  norm_num at hh ⊢
  simpa only [mul_comm] using hh

/-- ALL selected count ranks retain the actual logarithmic support. The
tilt applies after signed prime-period cancellation, never to the raw
source envelope. No fixed count ceiling enters. -/
theorem sum_count_price_tilted_le (I : Finset ℕ) {M v H : ℝ}
    (hM : 0≤M) (hH : 0<H) (hcount : ∀ k∈I,v≤4*H*((k : ℝ)+3)) :
    (∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤8*exp (4*M-v/(8*H)) := by
  have hpoint k (hk : k∈I) :
      exp (v/(8*H))*((2*M)^k/(k.factorial : ℝ))≤
        8*((4*M)^k/(k.factorial : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right (count_tilt hH (hcount k hk))
      (by positivity : 0≤(2*M)^k/(k.factorial : ℝ))
    calc
      _ ≤ 8*(2 : ℝ)^k*((2*M)^k/(k.factorial : ℝ)) := hh
      _ = _ := by
        rw [mul_assoc,← mul_div_assoc,← mul_pow,show (2 : ℝ)*(2*M)=4*M by ring]
  have hh := (Finset.sum_le_sum hpoint).trans
    (by simpa only [← Finset.mul_sum,mul_div_assoc,show (2 : ℝ)*(2*M)=4*M by ring] using
      sum_count_price_le I (show 0≤2*M by positivity) (show (0 : ℝ)≤8 by norm_num))
  rw [← Finset.mul_sum] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (exp_pos (-v/(8*H))).le
  rw [← mul_assoc,show exp (-v/(8*H))*exp (v/(8*H))=1 by
    rw [← exp_add,show -v/(8*H)+v/(8*H)=0 by ring,exp_zero],one_mul] at hh'
  exact hh'.trans_eq (by
    rw [show 4*M-v/(8*H)=4*M+(-v/(8*H)) by ring,exp_add]
    ring)

/-- The count tilt removes the apparent inverse-owner-scale singularity
uniformly in that scale. The extra `1/v` is in the CORRECT supply units. -/
theorem tilted_owner_price_le {v H : ℝ} (hv : 0<v) (hH : 0<H) :
    exp (-v/(8*H))/H≤8/v := by
  have hx := mul_exp_neg_le_exp_neg_one (v/(8*H))
  have h1 : exp (-1 : ℝ)≤1 := exp_le_one_iff.mpr (by norm_num)
  have hh : v/(8*H)*exp (-v/(8*H))≤1 := by simpa only [neg_div] using hx.trans h1
  apply (le_div_iff₀ hv).mpr
  have hh' := (mul_le_mul_of_nonneg_right hh (show 0≤8 by norm_num))
  convert hh' using 1 <;> field_simp

/-- The cofactor log scale may be MUCH smaller than the owner scale.
Keep the count tilt at the former scale, and the period estimate at the
latter. This covers growing clustered counts rather than only fixed
owner-relative geometries. -/
theorem tilted_separated_owner_price_le {v H J : ℝ} (hv : 0<v)
    (hJ : 0<J) (hJH : J≤H) : exp (-v/(32*J))/H≤32/v := by
  have hh := tilted_owner_price_le (show 0<v/4 by positivity) hJ
  have heq : -(v/4)/(8*J)=-v/(32*J) := by ring
  rw [heq] at hh
  have hm := div_le_div_of_nonneg_left (exp_pos (-v/(32*J))).le hJ hJH
  exact hm.trans (hh.trans_eq (by ring))

/-- A literal squarefree cofactor whose primes have log at most `4H`
has total log at most `4H` times its count. -/
theorem cofactor_log_le_count {a : ℕ} (hs : Squarefree a) {H : ℝ}
    (hlog : ∀ p∈a.primeFactors,log p≤4*H) :
    log a≤4*H*(a.primeFactors.card : ℝ) := by
  rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hs, mul_comm,
    ← nsmul_eq_mul,← Finset.sum_const]
  exact Finset.sum_le_sum hlog

private theorem response_count_bound (k : ℕ) : responseConstant k≤6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ)≤(2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    exact_mod_cast hh.trans (Nat.pow_le_pow_right (by norm_num : 1≤(2 : ℕ)) (by omega : k-2≤k))
  have h0 := hp 0
  have h1 := hp 1
  unfold responseConstant
  nlinarith only [h0,h1,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := k)]

/-- The same quantitative row estimate with the LITERAL unique-owner
allocation retained. Every count is allowed; no lower cofactor-prime
cutoff, factorial deletion or allocation approximation enters. -/
theorem retained_owner_row_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    (A : Finset ℕ) {v y L H : ℝ} (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : v/2 ≤ L) {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hmin : log a.minFac ≤ 4*H)
    (hP : H ≤ v-Real.pi/y-log a)
    (howner : ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hA : ∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
  have hH0 : 0 < H := by linarith
  have hπ0 : 0 ≤ Real.pi/y := by positivity
  have hv100 : 100 ≤ v := by linarith [log_natCast_nonneg a]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hP0 : 0 < v-Real.pi/y-log a := hH0.trans_le hP
  let B := responseConstant k*log a.minFac
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  have hB : 0 ≤ B := by dsimp [B]; positivity [responseConstant_pos k,log_natCast_nonneg a.minFac]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hV0 : 0 < v-Real.pi/y := by linarith [log_natCast_nonneg a]
  have hCb : 0 ≤ jointPeriodCost N v y (log a) := by
    unfold jointPeriodCost
    positivity
  have hBbound : B ≤ responseConstant k*(4*H) :=
    mul_le_mul_of_nonneg_left hmin (responseConstant_pos k).le
  have hEbound : E ≤ (2 : ℝ)^k/64 := by
    have hh := mul_le_mul_of_nonneg_left (quarter_period_width_le hy)
      (by positivity : (0 : ℝ) ≤ 2^k)
    exact (show E=(2 : ℝ)^k*(Real.pi/(4*y)) by dsimp [E]; ring) ▸
      hh.trans_eq (by ring)
  have hinner : B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a) ≤
      (20*responseConstant k+(2 : ℝ)^k/64)/H := by
    have hbc := mul_le_mul hBbound (jointPeriodCost_shell_le hy hNv hH0 hP)
      hCb (by positivity [responseConstant_pos k])
    have hec := (div_le_div_of_nonneg_left hE hH0 hP).trans
      (div_le_div_of_nonneg_right hEbound hH0.le)
    have heq : (responseConstant k*(4*H))*(5/H^2)+((2 : ℝ)^k/64)/H =
        (20*responseConstant k+(2 : ℝ)^k/64)/H := by
      field_simp
      ring
    exact (add_le_add hbc hec).trans_eq heq
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity [amplitude_nonneg N hv0.le] :
        0 ≤ 2*amplitude N v) (by positivity : 0 < v/2) hL)
      (inv_nonneg.mpr ha0.le)
    convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have htotal := mul_le_mul hpre hinner (by positivity :
      0 ≤ B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a))
      (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have hcoeff : 4*(20*responseConstant k+(2 : ℝ)^k/64) ≤ 481*(2 : ℝ)^k := by
    nlinarith only [response_count_bound k,(show 0 ≤ (2 : ℝ)^k by positivity)]
  have hcost := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hcoeff hH0.le)
    (mul_nonneg hbase (inv_nonneg.mpr ha0.le))
  have hfloor := ZetaRieszTinyOwnerPeriodFloor.owner_fibre_floor hk he A hv100 hNv hy hL0 ha hc howner
    (by linarith : 5000 ≤ v-Real.pi/y-log a) hA hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤ _ at hfloor
  have hpaid : (2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤
      (amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ := by
    exact htotal.trans (by convert hcost using 1 <;> ring)
  rw [neg_mul] at hfloor
  simpa only [neg_mul] using (neg_le_neg hpaid).trans hfloor

/-- The complete original cofactor periods, INCLUDING reinforcing
unmatched parity layers, have one constrained count price. Their phase,
two hinges and factorial/radial weight have already been joined. -/
theorem constrained_all_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (Q : Finset ℕ) {v y L H J M : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p∈Q,log p≤4*H)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hJ : 0<J) (hJH : J≤H) (hcount : ∀ k∈I,v/4≤4*J*((k : ℝ)+3))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(123136*exp (4*M)/v)*(amplitude N v/v)≤
      ∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
  have hH0 : 0<H := by linarith
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hf : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv.le) hv.le
  have hrow k (hk : k∈I) :
      -(481*(2*M)^k/(H*(k.factorial : ℝ)))*(amplitude N v/v)≤
        ∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
          signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
    have hm := interval_cofactor_mass_le (S k) Q k hQmass (hS k hk)
    have hh := Finset.sum_le_sum (fun a ha => by
      have hs := hS k hk a ha
      have ha1 : a≠1 := by intro ha1; simp [ha1] at hs; have := hI k hk; omega
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
  have ht := sum_count_price_tilted_le I hM hJ hcount
  have ho := tilted_separated_owner_price_le hv hJ hJH
  have hc : (481/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤123136*exp (4*M)/v := by
    have hh := mul_le_mul_of_nonneg_left ht (show 0≤481/H by positivity)
    have hh' := mul_le_mul_of_nonneg_left ho (show 0≤3848*exp (4*M) by positivity)
    rw [show 4*M-(v/4)/(8*J)=4*M+(-v/(32*J)) by ring,exp_add] at hh
    exact hh.trans (by convert hh' using 1 <;> first | rfl | (field_simp; ring))
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

/-- The count constraint at a literal clipped boundary follows from its
ACTUAL near-tied prime and total log. It is not an extra sieve hypothesis. -/
theorem clipped_count_constraint {n : ℕ} (hs : Squarefree n)
    (hc : 3≤n.primeFactors.card) {v H : ℝ} (hH : 1≤H)
    (hT : v-1/16<log n)
    (hclip : ∃ q∈(n/largestPrime n).primeFactors,
      H≤log q ∧ log (largestPrime n)-log q≤1/8)
    (hlog : ∀ q∈(n/largestPrime n).primeFactors,log q≤4*H) :
    v≤4*H*((n.primeFactors.card-2 : ℕ)+3 : ℝ) := by
  have hd := canonical_owner_data hs hc
  obtain ⟨q,hq,_,hpq⟩ := hclip
  have hp : log (largestPrime n)≤4*H+1/8 := by linarith [hlog q hq]
  have ha := cofactor_log_le_count hd.2.2.1 hlog
  have hln : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hd.2.1]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast hd.2.2.1.ne_zero)]
  have hcard : (n/largestPrime n).primeFactors.card=(n.primeFactors.card-2)+1 := by
    have := hd.2.2.2.1
    omega
  rw [hcard,Nat.cast_add,Nat.cast_one] at ha
  change v≤4*H*((n.primeFactors.card-2 : ℕ)+3) at ⊢
  nlinarith only [ha,hp,hln,hT,hH]

/-- ALL original ownership clips keep the logarithmic count tilt. The
original allocation, full phase, total-log mask and every count are kept. -/
theorem constrained_clipped_all_counts_norm_bound (A D Q : Finset ℕ)
    (y : ℝ) (N : ℕ) {v L H J M : ℝ} (hH : 10000≤H) (hv : 0<v)
    (hNv : (N : ℝ)+1≤v) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hJ : 1≤J) (hJH : J≤H) (hQlog : ∀ p∈Q,log p≤4*J)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆Q) :
    (∑ n∈D,‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
        (98304*exp (4*M)/v)*(amplitude N v/v) := by
  let I := D.image (fun n => n.primeFactors.card-2)
  let S := fun k => D.filter (fun n => n.primeFactors.card-2=k)
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hH0 : 0<H := by linarith
  have hJ0 : 0<J := by linarith
  have hf : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv.le) hv.le
  have hI k (hk : k∈I) : 0<k := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have := (hD n hn).2.1
    omega
  have hcount k (hk : k∈I) : v≤4*J*((k : ℝ)+3) := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have hd := hD n hn
    exact clipped_count_constraint hd.1 hd.2.1 hJ hd.2.2.1.1
      (by obtain ⟨q,hq,hqH,hp⟩ := hd.2.2.2.1; exact ⟨q,hq,hJH.trans hqH,hp⟩)
      (fun p hp => hQlog p (hd.2.2.2.2 hp))
  have hrow k (hk : k∈I) :
      (∑ n∈S k,f n)≤((1536*(2*M)^k/(k.factorial : ℝ))/H)*(amplitude N v/v) := by
    apply broad_clipped_count_norm_bound (hI k hk) A (S k) Q y hH hv hNv hL hM hQmass
      (fun p hp => (hQlog p hp).trans (by linarith))
    intro n hn
    obtain ⟨hn,hcnt⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2⟩
  have heq : (∑ k∈I,∑ n∈S k,f n)=∑ n∈D,f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have ht := sum_count_price_tilted_le I hM hJ0 hcount
  have ho : exp (-v/(8*J))/H≤8/v :=
    (div_le_div_of_nonneg_left (exp_pos (-v/(8*J))).le hJ0 hJH).trans
      (tilted_owner_price_le hv hJ0)
  have hcost : (1536/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤98304*exp (4*M)/v := by
    have hh := mul_le_mul_of_nonneg_left ht (show 0≤1536/H by positivity)
    have hh' := mul_le_mul_of_nonneg_left ho (show 0≤12288*exp (4*M) by positivity)
    rw [show 4*M-v/(8*J)=4*M+(-v/(8*J)) by ring,exp_add] at hh
    exact hh.trans (by convert hh' using 1 <;> first | rfl | (field_simp; ring))
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

/-- Any literal allocation family, in particular the exact changing
canonical owner, remains below the same unallocated BOUNDARY atom.
No allocation is removed from the signed prime-period main. -/
theorem allocation_family_atom_norm_le (A : ℕ→Finset ℕ) (L y : ℝ) (N n : ℕ) :
    ‖ZetaRieszJointAllocation.residualCoefficient (A n) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
    ‖ZetaRieszJointAllocation.residualCoefficient ∅ L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
  have hz : ZetaRieszJointAllocation.boundedShare ∅ N n=0 := by
    unfold ZetaRieszJointAllocation.boundedShare
    split_ifs <;> simp [ZetaRieszJointAllocation.allocationShare,ZetaRieszJointAllocation.assignedAmplitude]
  rw [ZetaRieszJointAllocation.residualCoefficient,ZetaRieszJointAllocation.residualCoefficient,
    hz,sub_zero,Complex.ofReal_one,one_mul,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (ZetaRieszJointAllocation.boundedShare_bounds (A n) N n).2)]
  rw [norm_mul]
  have hh := mul_le_of_le_one_left (norm_nonneg (SquarefreeVaughanLogSource.coefficient L n))
    (show 1-ZetaRieszJointAllocation.boundedShare (A n) N n≤1 by
      linarith [(ZetaRieszJointAllocation.boundedShare_bounds (A n) N n).1])
  exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)

private theorem missed_family_parts_floor (A : ℕ→Finset ℕ) (D P Q : Finset ℕ)
    (L y : ℝ) (N : ℕ) :
    -(∑ n∈D,‖ZetaRieszJointAllocation.residualCoefficient (A n) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
      (∑ n∈D\P,signedPart 1 (A n) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A n) L y N n) := by
  have h₁ := Finset.sum_le_sum_of_subset_of_nonneg
    (show D\P⊆D from Finset.sdiff_subset) (fun n _ _ => abs_nonneg (signedPart 1 (A n) L y N n))
  have h₂ := Finset.sum_le_sum_of_subset_of_nonneg
    (show D\Q⊆D from Finset.sdiff_subset) (fun n _ _ => abs_nonneg (signedPart (-1) (A n) L y N n))
  have hab := Finset.sum_le_sum (fun n (_hn : n∈D) =>
    (ZetaRieszOwnerTieFloor.signedParts_abs_eq (A n) L y N n).le.trans (Complex.abs_re_le_norm _))
  rw [Finset.sum_add_distrib] at hab
  have hlow₁ := Finset.sum_le_sum (fun n (_hn : n∈D\P) => neg_abs_le (signedPart 1 (A n) L y N n))
  have hlow₂ := Finset.sum_le_sum (fun n (_hn : n∈D\Q) => neg_abs_le (signedPart (-1) (A n) L y N n))
  simp only [Finset.sum_neg_distrib] at hlow₁ hlow₂
  linarith only [h₁,h₂,hab,hlow₁,hlow₂]

/-- One complete signed count/parity price WITH the actual ownership
boundary. Both missed sign selections spend ONE original boundary atom. -/
theorem constrained_period_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (D P Q U : Finset ℕ) {v y L H J M : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 10000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hUmass : (∑ p∈U,(p : ℝ)⁻¹)≤M)
    (hJ : 1≤J) (hJH : J≤H) (hUlog : ∀ p∈U,log p≤4*J)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆U)
    (hcount : ∀ k∈I,v/4≤4*J*((k : ℝ)+3))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(221440*exp (4*M)/v)*(amplitude N v/v)≤
      (∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\P,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmain := constrained_all_counts_floor I N e A S U hI he (by linarith) hNv hy hL
    hM hUmass (fun p hp => (hUlog p hp).trans (by linarith)) hS
    (by linarith) hJH hcount hP howner hA hpeak hsign
  have hn := constrained_clipped_all_counts_norm_bound ∅ D U y N hH hv
    (by linarith) hL hM hUmass hJ hJH hUlog hD
  have ha := (Finset.sum_le_sum (fun n (_hn : n∈D) =>
    allocation_family_atom_norm_le (fun n => A∩{largestPrime n}) L y N n)).trans hn
  have hh := add_le_add hmain ((neg_le_neg ha).trans
    (missed_family_parts_floor (fun n => A∩{largestPrime n}) D P Q L y N))
  convert! hh using 1 <;> ring

/-- Fixed arithmetic-head and macroscopic-log-shell constant. The head
is finite, positive and unevaluated; no effective starting order is claimed. -/
def gappedHeadCost : ℝ := smallPrimeHeadCost^2*(8 : ℝ)^4*exp 1

theorem gappedHeadCost_pos : 0<gappedHeadCost := by
  unfold gappedHeadCost
  positivity [smallPrimeHeadCost_pos]

/-- Every small prime remains available. The restriction concerns only
INTERMEDIATE log scales: the other primes lie in one macroscopic shell,
which may move and shrink relative to the owner scale as counts grow. -/
theorem gapped_count_exponential_le (Q : Finset ℕ) {B J W : ℝ}
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J)
    (hQ : ∀ p∈Q,p.Prime ∧ log p≤4*J ∧ (log p≤B ∨ J/W≤log p)) :
    exp (4*(∑ p∈Q,(p : ℝ)⁻¹))≤gappedHeadCost*B^4*W^4 := by
  let A := Q.filter (fun p : ℕ => log p≤B)
  let E := Q\A
  have hB0 : 0<B := by linarith
  have hW0 : 0<W := by linarith
  have hJ0 : 0<J := by linarith
  have hmass := whole_count_exponential_le A hB (by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact ⟨(hQ p hh.1).1,hh.2.trans (by linarith)⟩)
  have hhead : exp (4*(∑ p∈A,(p : ℝ)⁻¹)) ≤ smallPrimeHeadCost^2*B^4 := by
    have hh := pow_le_pow_left₀ (exp_pos _).le hmass 2
    rw [← exp_nat_mul] at hh
    convert hh using 1 <;> first | rfl | ring
  have hsub : E⊆(Finset.Ioc ⌊exp (J/(2*W))⌋₊ ⌊exp (4*J)⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpQ,hpA⟩ := Finset.mem_sdiff.mp hp
    have hh := hQ p hpQ
    have hpl : J/W≤log p := hh.2.2.resolve_left
      (fun h => hpA (Finset.mem_filter.mpr ⟨hpQ,h⟩))
    have hlo : J/(2*W)<log p :=
      (div_lt_div_of_pos_left hJ0 hW0 (by linarith : W<2*W)).trans_le hpl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hh.1⟩
    · apply (Nat.floor_lt (by positivity : 0≤exp (J/(2*W)))).mpr
      rw [← exp_log (by exact_mod_cast hh.1.pos : (0 : ℝ)<p)]
      exact exp_lt_exp.mpr hlo
    · apply Nat.le_floor
      simpa only [exp_log (by exact_mod_cast hh.1.pos : (0 : ℝ)<p)] using
        exp_le_exp.mpr hh.2.1
  have htail := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by intro p _ _; positivity)).trans
      (prime_interval_mass_le
        ((le_div_iff₀ (show 0<2*W by positivity)).mpr (by nlinarith only [hJ]) : 5000≤J/(2*W))
        ((div_le_iff₀ (show 0<2*W by positivity)).mpr (by nlinarith [hW,hJ0]) : J/(2*W)≤4*J))
  have heq : 4*J/(J/(2*W))=8*W := by field_simp; ring
  rw [heq,show 1/(J/(2*W))=2*W/J by field_simp] at htail
  have hbound : 4*(∑ p∈E,(p : ℝ)⁻¹)≤4*log (8*W)+1 := by
    have hh : 8*W/J≤1 := (div_le_one hJ0).mpr (by linarith)
    calc
      _ ≤ 4*(log (8*W)+2*W/J) := mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 4*log (8*W)+8*W/J := by ring
      _ ≤ _ := by linarith only [hh]
  have hexp : exp (4*(∑ p∈E,(p : ℝ)⁻¹))≤(8*W)^4*exp 1 := by
    have hh := exp_le_exp.mpr hbound
    rw [exp_add,show 4*log (8*W)=log ((8*W)^4) by rw [log_pow]; norm_num,
      exp_log (by positivity)] at hh
    exact hh
  have hsplit : (∑ p∈Q,(p : ℝ)⁻¹)=
      (∑ p∈A,(p : ℝ)⁻¹)+(∑ p∈E,(p : ℝ)⁻¹) := by
    rw [← Finset.sum_inter_add_sum_sdiff Q A (fun p => (p : ℝ)⁻¹),
      Finset.inter_eq_right.mpr (show A⊆Q from Finset.filter_subset _ _)]
  rw [hsplit,mul_add,exp_add]
  have hh := mul_le_mul hhead hexp (exp_pos _).le (by positivity [smallPrimeHeadCost_pos])
  exact hh.trans_eq (by unfold gappedHeadCost; ring)

/-- The constrained population cost over all counts and literal owner
clips is now `poly(B)/v` in the ACTUAL supply units. Reinforcing parity
layers need not have any local matching for this estimate to apply. -/
theorem gapped_period_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (D P Q U : Finset ℕ) {v y L H J B W : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 10000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J) (hJH : J≤H)
    (hU : ∀ p∈U,p.Prime ∧ log p≤4*J ∧ (log p≤B ∨ J/W≤log p))
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆U)
    (hcount : ∀ k∈I,v/4≤4*J*((k : ℝ)+3))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(221440*gappedHeadCost*B^4*W^4/v)*(amplitude N v/v)≤
      (∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\P,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hh := constrained_period_with_boundary_floor I N e A S D P Q U hI he hH hNv hy hL
    (Finset.sum_nonneg (fun p _ => by positivity)) (le_refl _)
    (by linarith) hJH (fun p hp => (hU p hp).2.1) hS hcount hP howner hA hD hpeak hsign
  have hc := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (gapped_count_exponential_le U hB hW hJ hU) (show (0 : ℝ)≤221440 by norm_num)) hv.le)
    (div_nonneg (amplitude_nonneg N hv.le) hv.le)
  simpa only [neg_mul,mul_assoc] using (neg_le_neg hc).trans (by simpa only [neg_mul] using hh)

/-- A whole eligible cofactor population supplies the count constraint
automatically. This is purely its literal log geometry, not a signed
arithmetic estimate: retain at least a quarter of the total log in it. -/
theorem count_constraint_of_cofactor_population (I : Finset ℕ) (S : ℕ→Finset ℕ)
    {v J : ℝ} (hJ : 0≤J) (hne : ∀ k∈I,(S k).Nonempty)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧
      v/4≤log a ∧ ∀ p∈a.primeFactors,log p≤4*J) :
    ∀ k∈I,v/4≤4*J*((k : ℝ)+3) := by
  intro k hk
  obtain ⟨a,ha⟩ := hne k hk
  have hs := hS k hk a ha
  have hh := cofactor_log_le_count hs.1 hs.2.2.2
  rw [hs.2.1] at hh
  nlinarith only [hs.2.2.1,hh,hJ]

/-- The literal retained central window and already-retained owner cap
leave MORE than a quarter of the total radial log in the cofactor. This
discharges the geometric input of the count tilt without a new bound
on primes or on the signed carrier. -/
theorem literal_core_cofactor_quarter {N n : ℕ} (hN : 1≤N)
    (hs : Squarefree n) (hc : 3≤n.primeFactors.card) {v : ℝ}
    (hlo : (197/100 : ℝ)*N<log n)
    (hp : log (largestPrime n)≤(243/200 : ℝ)*N) (hv : v≤log n+1/16) :
    v/4<log (n/largestPrime n : ℕ) := by
  have hd := canonical_owner_data hs hc
  have hl : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hd.2.1]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast hd.2.2.1.ne_zero)]
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  linarith only [hl,hlo,hp,hv,hn]

/-- One signed bound over EVERY selected count, dyadic owner scale and
radial period in the structured population. It includes unmatched parity
layers and the original ownership clips without any fixed count cutoff. -/
theorem gapped_radial_supply_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (I : ℕ→ℕ→Finset ℕ) (N : ℕ) (A : Finset ℕ) (e v : ℕ→ℝ)
    (S : ℕ→ℕ→ℕ→Finset ℕ) (D P Q U : ℕ→ℕ→Finset ℕ) (J : ℕ→ℕ→ℝ)
    {y L H B G W : ℝ} (hH : 10000≤H) (hB : 5000≤B) (hW : 1≤W) (hy : 54≤y)
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (hI : ∀ i∈V,∀ j∈O i,∀ k∈I i j,2≤k)
    (he : ∀ i∈V,|e i|=1) (hNv : ∀ i∈V,(N : ℝ)+2≤v i)
    (hvG : ∀ i∈V,v i≤G) (hL : ∀ i∈V,v i/2≤L)
    (hJ : ∀ i∈V,∀ j∈O i,10000*W≤J i j ∧ J i j≤H*(2 : ℝ)^j)
    (hU : ∀ i∈V,∀ j∈O i,∀ p∈U i j,
      p.Prime ∧ log p≤4*J i j ∧ (log p≤B ∨ J i j/W≤log p))
    (hS : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆U i j)
    (hcount : ∀ i∈V,∀ j∈O i,∀ k∈I i j,v i/4≤4*J i j*((k : ℝ)+3))
    (hP : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ n∈D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U i j)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -(221440*gappedHeadCost*B^4*W^4*(1+log G/log 2)/((N : ℝ)+1))*
        (∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
          (∑ n∈D i j\P i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
          (∑ n∈D i j\Q i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hn : 0<(N : ℝ)+1 := by positivity
  have hC : 0≤221440*gappedHeadCost*B^4*W^4 := by positivity [gappedHeadCost_pos]
  have hrow i (hi : i∈V) :
      -(221440*gappedHeadCost*B^4*W^4*(1+log G/log 2)/((N : ℝ)+1))*
        (amplitude N (v i)/v i)≤
      ∑ j∈O i,
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
          (∑ n∈D i j\P i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
          (∑ n∈D i j\Q i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hf : 0≤amplitude N (v i)/v i := div_nonneg (amplitude_nonneg N hv.le) hv.le
    have hcard := dyadic_owner_card_le (O i) (by linarith : 1≤H)
      (by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N] : 1≤v i) (hO i hi)
    have hlog := div_le_div_of_nonneg_right (log_le_log hv (hvG i hi))
      (log_pos (by norm_num : (1 : ℝ)<2)).le
    have hcg : ((O i).card : ℝ)≤1+log G/log 2 := by linarith only [hcard,hlog]
    have hG : 0≤1+log G/log 2 := (Nat.cast_nonneg (α := ℝ) (O i).card).trans hcg
    have hp : 221440*gappedHeadCost*B^4*W^4/v i≤221440*gappedHeadCost*B^4*W^4/((N : ℝ)+1) :=
      div_le_div_of_nonneg_left hC hn (by linarith [hNv i hi])
    have hc := mul_le_mul hcg hp (div_nonneg hC hv.le) hG
    have hc' := mul_le_mul_of_nonneg_right hc hf
    have hh := Finset.sum_le_sum (s := O i) (fun j (hj : j∈O i) =>
      gapped_period_with_boundary_floor (I i j) N (e i) A (S i j) (D i j) (P i j) (Q i j) (U i j)
        (hI i hi j hj) (he i hi)
        (hH.trans (by
          have hh := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
          nlinarith only [hh,hH] : H≤H*(2 : ℝ)^j))
        (hNv i hi) hy (hL i hi) hB hW (hJ i hi j hj).1 (hJ i hi j hj).2
        (hU i hi j hj) (hS i hi j hj) (hcount i hi j hj)
        (hP i hi j hj) (howner i hi j hj) (hA i hi j hj) (hD i hi j hj) (hpeak i hi) (hsign i hi))
    rw [Finset.sum_const,nsmul_eq_mul] at hh
    calc
      _ = -((1+log G/log 2)*(221440*gappedHeadCost*B^4*W^4/((N : ℝ)+1))*
          (amplitude N (v i)/v i)) := by ring
      _ ≤ -(((O i).card : ℝ)*(221440*gappedHeadCost*B^4*W^4/v i)*(amplitude N (v i)/v i)) :=
        neg_le_neg hc'
      _ = ((O i).card : ℝ)*(-(221440*gappedHeadCost*B^4*W^4/v i)*(amplitude N (v i)/v i)) := by ring
      _ ≤ _ := hh
  have hh := Finset.sum_le_sum hrow
  simpa only [← Finset.mul_sum] using hh

/-- This price is in `amplitude/v` units, unlike the withdrawn earlier
`log²(N)/N` amplitude-only price. The shell scale is independent of the
owner scale and may vary across every radial/count population. -/
def gappedSupplyPrice (N : ℕ) : ℝ :=
  221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
    (1+log (4*((N : ℝ)+1))/log 2)/((N : ℝ)+1)

theorem tendsto_gappedSupplyPrice : Tendsto gappedSupplyPrice atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₈ : Tendsto (fun N : ℕ => (log ((N : ℝ)+1))^8/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 8 one_ne_zero).comp hn
  have h₉ : Tendsto (fun N : ℕ => (log ((N : ℝ)+1))^9/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 9 one_ne_zero).comp hn
  have ht := ((h₈.const_mul (1+log 4/log 2)).add
    (h₉.const_mul (log 2)⁻¹)).const_mul (221440*gappedHeadCost*(32 : ℝ)^8)
  convert ht using 1
  · funext N
    unfold gappedSupplyPrice
    rw [log_mul (by norm_num : (4 : ℝ)≠0) (by positivity : (N : ℝ)+1≠0)]
    simp only [div_eq_mul_inv,mul_pow]
    ring
  · ring

/-- This structured all-count/global-period cost fits ANY fixed positive
supply fraction eventually. It does not assert the original unmatched
population satisfies the displayed log-spectrum gap. -/
theorem eventually_gappedSupplyPrice_lt {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,gappedSupplyPrice N<ε :=
  tendsto_gappedSupplyPrice.eventually (gt_mem_nhds hε)

/-- The exact price can be spent against a disjoint positive reserve in
the SAME radial units. An absolute source envelope is neither assumed
nor used. The reserve's compatibility with prior credits is still required
by any application to the full floor ledger. -/
theorem cost_paid_by_radial_reserve (N : ℕ) (V : Finset ℕ) (v : ℕ→ℝ)
    {κ ε T : ℝ} (hε : 0≤ε)
    (hv : ∀ i∈V,0<v i) (hprice : gappedSupplyPrice N≤ε*κ)
    (hreserve : κ*(∑ i∈V,amplitude N (v i)/v i)≤T) :
    gappedSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤ε*T := by
  have hs : 0≤∑ i∈V,amplitude N (v i)/v i :=
    Finset.sum_nonneg (fun i hi => div_nonneg (amplitude_nonneg N (hv i hi).le) (hv i hi).le)
  have hh := mul_le_mul_of_nonneg_right hprice hs
  have ht := mul_le_mul_of_nonneg_left hreserve hε
  exact hh.trans (by simpa only [mul_assoc] using ht)

/-- Enlarging the small-prime head to a square-root log scale does NOT
pay a mesoscopic gap with this positive price. Even before owner/radial
multiplicity it grows at least linearly in the correct supply units. -/
theorem large_head_price_lower (N : ℕ) {B W v : ℝ} (hv : 0<v)
    (hvN : v≤4*((N : ℝ)+1)) (hW : 1≤W) (hB : (N : ℝ)+1≤B^2) :
    55360*gappedHeadCost*((N : ℝ)+1)≤221440*gappedHeadCost*B^4*W^4/v := by
  have hn : 0<(N : ℝ)+1 := by positivity
  have hb : ((N : ℝ)+1)^2≤B^4 := by
    have hh := pow_le_pow_left₀ hn.le hB 2
    simpa only [← pow_mul] using hh
  have hw : (1 : ℝ)≤W^4 := one_le_pow₀ hW
  have hbw : ((N : ℝ)+1)^2≤B^4*W^4 :=
    hb.trans (le_mul_of_one_le_right (by positivity) hw)
  have hg := gappedHeadCost_pos
  apply (le_div_iff₀ hv).mpr
  have hh := mul_le_mul_of_nonneg_left hvN
    (by positivity : 0≤55360*gappedHeadCost*((N : ℝ)+1))
  have ht := mul_le_mul_of_nonneg_left hbw (show 0≤221440*gappedHeadCost by positivity)
  exact hh.trans (by convert ht using 1 <;> first | rfl | ring)

end RiemannGaussian.ZetaRieszParityLayerCost
