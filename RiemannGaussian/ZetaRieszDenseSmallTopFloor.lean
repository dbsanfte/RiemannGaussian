/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDenseShellCost

/-!
# Signed periods for dense cofactors with a small largest log

Retain the original count tilt instead of replacing it by the uniform
inverse-owner price. When every cofactor prime has small log compared
with the total log, the retained window forces large counts and their
tilted population price beats the whole finite Euler budget. Neither a
count ceiling, occupied-bin ceiling nor opposite-parity matching enters.
The original owner period and allocation remain. Literal near-owner
clips are empty when the owner scale exceeds all cofactor prime logs.
These are relative positive-supply costs, not an independent whole floor.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszDenseSmallTopFloor
open ZetaRieszParityLayerCost ZetaRieszSmallCofactorCancellation
open ZetaRieszBroadOwnerPeriodFloor ZetaRieszTinyOwnerPeriodFloor
open ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszPrimeEndpoint ZetaRieszAllowancePrimeBoxes
open ZetaRieszStaggeredFloor ZetaRieszLogShellPeriodFloor
open ZetaRieszSmallOwnerBoundary
open ZetaRieszClippedOwnerPeriodFloor

set_option maxHeartbeats 800000

/-- Keep the COUNT saving in the assembled literal signed periods.
No count/parity rank is bounded separately by a new signed hypothesis. -/
theorem retained_count_tilt_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (Q : Finset ℕ) {v y L H J M : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p∈Q,log p≤4*H)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hJ : 0<J) (hcount : ∀ k∈I,v/4≤4*J*((k : ℝ)+3))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(3848*exp (4*M-v/(32*J))/H)*(amplitude N v/v)≤
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
  have ht := sum_count_price_tilted_le I hM hJ hcount
  have hc : (481/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤3848*exp (4*M-v/(32*J))/H := by
    have hh := mul_le_mul_of_nonneg_left ht (show 0≤481/H by positivity)
    rw [show (v/4)/(8*J)=v/(32*J) by ring] at hh
    calc
      _ ≤ (481/H)*(8*exp (4*M-v/(32*J))) := hh
      _ = _ := by ring
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

/-- Literal near-owner clips cannot exist when ALL cofactor prime logs
are strictly below the original owner scale. No boundary is discarded. -/
theorem owner_clips_empty (D Q : Finset ℕ) {H J : ℝ} (hJH : 4*J<H)
    (hQ : ∀ p∈Q,log p≤4*J)
    (hD : ∀ n∈D,(n/largestPrime n).primeFactors⊆Q ∧
      ∃ q∈(n/largestPrime n).primeFactors,H≤log q) : D=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hsub,q,hq,hHq⟩ := hD n hn
  have hh := hQ q (hsub hq)
  linarith only [hJH,hHq,hh]

/-- Retain the stronger count tilt on EVERY literal near-owner boundary.
The canonical owner can change and the full allocation stays present.
This estimate does not require the boundary population to be empty. -/
theorem retained_clipped_count_tilt_norm_bound (A D Q : Finset ℕ)
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
        (12288*exp (4*M-v/(8*J))/H)*(amplitude N v/v) := by
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
      (fun p hp => (hQlog p hp).trans (by linarith only [hJH]))
    intro n hn
    obtain ⟨hn,hcnt⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2⟩
  have heq : (∑ k∈I,∑ n∈S k,f n)=∑ n∈D,f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have ht := sum_count_price_tilted_le I hM hJ0 hcount
  have hcost : (1536/H)*(∑ k∈I,(2*M)^k/(k.factorial : ℝ))≤
      12288*exp (4*M-v/(8*J))/H := by
    have hh := mul_le_mul_of_nonneg_left ht (show 0≤1536/H by positivity)
    calc
      _ ≤ (1536/H)*(8*exp (4*M-v/(8*J))) := hh
      _ = _ := by ring
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

/-- BOTH missed sign selections spend just ONE original boundary atom.
The varying allocation family is kept; this is a boundary inequality,
not a norm estimate for the signed main or the selected resonance. -/
theorem missed_parts_floor (A : ℕ→Finset ℕ) (D P Q : Finset ℕ)
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

/-- The complete signed main AND the actual nonempty ownership clips
retain a common cofactor-count saving. The strict owner-gap requirement
of `owner_clips_empty` is unnecessary here. -/
theorem count_tilt_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
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
    -(16136*exp (4*M-v/(32*J))/H)*(amplitude N v/v)≤
      (∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\P,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  have hv : 0<v := by linarith [hNv,Nat.cast_nonneg (α := ℝ) N]
  have hJ0 : 0<J := by linarith only [hJ]
  have hmain := retained_count_tilt_floor I N e A S U hI he (by linarith only [hH])
    hNv hy hL hM hUmass (fun p hp => (hUlog p hp).trans (by linarith only [hJH]))
    hS hJ0 hcount hP howner hA hpeak hsign
  have hn := retained_clipped_count_tilt_norm_bound ∅ D U y N hH hv
    (by linarith only [hNv]) hL hM hUmass hJ hJH hUlog hD
  have hscale : v/(32*J)≤v/(8*J) := div_le_div_of_nonneg_left hv.le
    (by positivity : 0<8*J) (by nlinarith only [hJ0])
  have he := exp_le_exp.mpr (show 4*M-v/(8*J)≤4*M-v/(32*J) by linarith only [hscale])
  have hbound := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ)≤12288))
      (by linarith only [hH] : 0≤H))
    (show 0≤amplitude N v/v by positivity [amplitude_nonneg N hv.le])
  have ha := (Finset.sum_le_sum (fun n (_hn : n∈D) =>
    allocation_family_atom_norm_le (fun n => A∩{largestPrime n}) L y N n)).trans (hn.trans hbound)
  have hh := add_le_add hmain ((neg_le_neg ha).trans
    (missed_parts_floor (fun n => A∩{largestPrime n}) D P Q L y N))
  convert! hh using 1 <;> ring

/-- A finite prime universe has the leading-one whole mass bound.
No sparse count, occupied-bin or prime-density premise is introduced. -/
theorem whole_mass_log_bound (Q : Finset ℕ) {x J : ℝ}
    (hx : 1≤x) (hJ : 5000≤J) (hJx : J≤4*x)
    (hQ : ∀ p∈Q,p.Prime ∧ log p≤4*J) :
    (∑ p∈Q,(p : ℝ)⁻¹)≤ smallPrimeHeadMass+log 16+1/5000+log x := by
  have hh := whole_prime_mass_le Q hJ hQ
  have hx0 : 0<x := (by norm_num : (0 : ℝ)<1).trans_le hx
  have hl := log_le_log (show 0<4*J/5000 by positivity)
    (show 4*J/5000≤16*x by nlinarith)
  rw [log_mul (by norm_num : (16 : ℝ)≠0) hx0.ne'] at hl
  linarith only [hh,hl]

/-- If the largest cofactor log is at most `v/(128 log x)`, the retained
count tilt pays the WHOLE Euler mass. The saving is kept at source
carrier level only as a relative positive-supply price. -/
theorem small_top_rate_bound {x v J H M C : ℝ} (_hx : 1≤x) (hJ : 0<J)
    (hH : 1≤H) (hM : M≤C+log x) (hscale : 512*J*log x≤v) :
    3848*exp (4*M-v/(32*J))/H≤3848*exp (4*C-12*log x) := by
  have htilt : 16*log x≤v/(32*J) := (le_div_iff₀ (show 0<32*J by positivity)).mpr
    (by nlinarith only [hscale])
  have hh := exp_le_exp.mpr (show 4*M-v/(32*J)≤4*C-12*log x by
    linarith only [hM,htilt])
  have hd := div_le_self (show 0≤3848*exp (4*M-v/(32*J)) by positivity) hH
  exact hd.trans (mul_le_mul_of_nonneg_left hh (by norm_num))

/-- The SAME small-top saving pays the joined signed main and nonempty
boundary. Only the fixed constant changes; the `N^-12` saving remains. -/
theorem small_top_boundary_rate_bound {x v J H M C : ℝ} (hJ : 0<J)
    (hH : 1≤H) (hM : M≤C+log x) (hscale : 512*J*log x≤v) :
    16136*exp (4*M-v/(32*J))/H≤16136*exp (4*C-12*log x) := by
  have htilt : 16*log x≤v/(32*J) := (le_div_iff₀ (show 0<32*J by positivity)).mpr
    (by nlinarith only [hscale])
  have hh := exp_le_exp.mpr (show 4*M-v/(32*J)≤4*C-12*log x by
    linarith only [hM,htilt])
  have hd := div_le_self (show 0≤16136*exp (4*M-v/(32*J)) by positivity) hH
  exact hd.trans (mul_le_mul_of_nonneg_left hh (by norm_num))

/-- The small-top condition forces at least `32 log x` cofactor factors.
Thus this is a GROWING dense-count population, not a fixed-count slice. -/
theorem small_top_count_lower {a : ℕ} (hs : Squarefree a) {x v J : ℝ}
    (hJ : 0<J) (hlog : ∀ p∈a.primeFactors,log p≤4*J)
    (hcore : v/4≤log a) (hscale : 512*J*log x≤v) :
    32*log x≤(a.primeFactors.card : ℝ) := by
  have hh := cofactor_log_le_count hs hlog
  nlinarith only [hh,hcore,hscale,hJ]

/-- All count ranks and reinforcing parity layers on the small-top
population have this literal signed prime-period floor. The original
allocation and both exact Riesz hinges are retained. -/
theorem small_top_period_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (Q : Finset ℕ) {v y L H J : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hJ : 5000≤J) (hJx : J≤4*((N : ℝ)+1)) (hJH : J≤H)
    (hQ : ∀ p∈Q,p.Prime ∧ log p≤4*J)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆Q)
    (hcount : ∀ k∈I,v/4≤4*J*((k : ℝ)+3))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hscale : 512*J*log ((N : ℝ)+1)≤v) :
    -(3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N v/v)≤
      ∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
  let M := smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1)
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmass : (∑ p∈Q,(p : ℝ)⁻¹)≤M := whole_mass_log_bound Q hx hJ hJx hQ
  have hM : 0≤M := (Finset.sum_nonneg (fun _ _ => by positivity)).trans hmass
  have hh := retained_count_tilt_floor I N e A S Q hI he hH hNv hy hL hM hmass
    (fun p hp => (hQ p hp).2.trans (by linarith only [hJH]))
    hS (by linarith only [hJ]) hcount hP howner hA hpeak hsign
  have hc := small_top_rate_bound hx (by linarith only [hJ])
    (by linarith only [hH] : 1≤H) (show M≤ smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1) from le_rfl) hscale
  have hf : 0≤amplitude N v/v := by
    have hv : 0<v := by linarith [hNv,Nat.cast_nonneg (α := ℝ) N]
    exact div_nonneg (amplitude_nonneg N hv.le) hv.le
  simpa only [neg_mul] using (neg_le_neg (mul_le_mul_of_nonneg_right hc hf)).trans
    (by simpa only [neg_mul] using hh)

/-- A literal small-top period WITH both original missed sign selections.
The canonical owner need not be separated from its second prime. -/
theorem small_top_with_boundary_period_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ→Finset ℕ) (D P Q U : Finset ℕ) {v y L H J : ℝ}
    (hI : ∀ k∈I,2≤k) (he : |e|=1) (hH : 10000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hJ : 5000≤J) (hJx : J≤4*((N : ℝ)+1)) (hJH : J≤H)
    (hU : ∀ p∈U,p.Prime ∧ log p≤4*J)
    (hS : ∀ k∈I,∀ a∈S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆U)
    (hcount : ∀ k∈I,v/4≤4*J*((k : ℝ)+3))
    (hP : ∀ k∈I,∀ a∈S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k∈I,∀ a∈S k,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ k∈I,∀ a∈S k,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hscale : 512*J*log ((N : ℝ)+1)≤v) :
    -(16136*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N v/v)≤
      (∑ k∈I,∑ a∈S k,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\P,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  let M := smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1)
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmass : (∑ p∈U,(p : ℝ)⁻¹)≤M := whole_mass_log_bound U hx hJ hJx hU
  have hM : 0≤M := (Finset.sum_nonneg (fun _ _ => by positivity)).trans hmass
  have hh := count_tilt_with_boundary_floor I N e A S D P Q U hI he hH hNv hy hL hM hmass
    (by linarith only [hJ]) hJH (fun p hp => (hU p hp).2) hS hcount hP howner hA hD hpeak hsign
  have hc := small_top_boundary_rate_bound (by linarith only [hJ])
    (by linarith only [hH] : 1≤H)
    (show M≤ smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1) from le_rfl) hscale
  have hf : 0≤amplitude N v/v := by
    have hv : 0<v := by linarith [hNv,Nat.cast_nonneg (α := ℝ) N]
    exact div_nonneg (amplitude_nonneg N hv.le) hv.le
  simpa only [neg_mul] using (neg_le_neg (mul_le_mul_of_nonneg_right hc hf)).trans
    (by simpa only [neg_mul] using hh)

/-- One relative price for all selected owner scales and radial periods. -/
def smallTopSupplyPrice (N : ℕ) : ℝ :=
  3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1))*
    (1+log (4*((N : ℝ)+1))/log 2)

/-- Sum the retained small-top price over EVERY selected dyadic owner
scale and radial period, in the correct `amplitude/v` supply units. -/
theorem global_small_top_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v : ℕ→ℝ) {H : ℝ} (hH : 1≤H)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i) :
    (∑ i∈V,∑ _j∈O i,
      (3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N (v i)/v i))≤ smallTopSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hrow i (hi : i∈V) :
      (∑ _j∈O i,
        (3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
          (amplitude N (v i)/v i))≤ smallTopSupplyPrice N*(amplitude N (v i)/v i) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hc := dyadic_owner_card_le (O i) hH
      (by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N] : 1≤v i) (hO i hi)
    have hlg := div_le_div_of_nonneg_right (log_le_log hv (hvG i hi))
      (log_pos (by norm_num : (1 : ℝ)<2)).le
    have hcg : ((O i).card : ℝ)≤1+log (4*((N : ℝ)+1))/log 2 := by linarith only [hc,hlg]
    have hh := mul_le_mul_of_nonneg_right hcg
      (show 0≤(3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N (v i)/v i) by positivity [amplitude_nonneg N hv.le])
    simpa only [Finset.sum_const,nsmul_eq_mul,smallTopSupplyPrice,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh := Finset.sum_le_sum hrow
  simpa only [Finset.mul_sum] using hh

/-- A global signed floor for the dense small-top population, joining
ALL counts, owner scales and radial periods. The literal ownership
clips are proved empty from their support, not hidden in a payment.
Original fibre and mask premises remain explicit. -/
theorem global_small_top_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v e : ℕ→ℝ) (I : ℕ→ℕ→Finset ℕ) (J : ℕ→ℕ→ℝ)
    (S : ℕ→ℕ→ℕ→Finset ℕ) (D Pplus Pminus U : ℕ→ℕ→Finset ℕ) (A : Finset ℕ)
    {H y L : ℝ} (hH : 10000≤H) (hy : 54≤y)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (he : ∀ i∈V,|e i|=1) (hL : ∀ i∈V,v i/2≤L)
    (hJ : ∀ i∈V,∀ j∈O i,5000≤J i j ∧ J i j≤4*((N : ℝ)+1))
    (hscale : ∀ i∈V,∀ j∈O i,512*J i j*log ((N : ℝ)+1)≤v i)
    (hgap : ∀ i∈V,∀ j∈O i,4*J i j<H*(2 : ℝ)^j)
    (hU : ∀ i∈V,∀ j∈O i,∀ p∈U i j,p.Prime ∧ log p≤4*J i j)
    (hI : ∀ i∈V,∀ j∈O i,∀ k∈I i j,2≤k)
    (hS : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆U i j)
    (hcount : ∀ i∈V,∀ j∈O i,∀ k∈I i j,v i/4≤4*J i j*((k : ℝ)+3))
    (hP : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ n∈D i j,(n/largestPrime n).primeFactors⊆U i j ∧
      ∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -smallTopSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
         (∑ n∈D i j\Pplus i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
         (∑ n∈D i j\Pminus i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) :
      -(3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N (v i)/v i)≤
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
         (∑ n∈D i j\Pplus i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
         (∑ n∈D i j\Pminus i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hHj : 5000≤H*(2 : ℝ)^j := by
      have hp := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hH,hp]
    have hz := owner_clips_empty (D i j) (U i j) (hgap i hi j hj)
      (fun p hp => (hU i hi j hj p hp).2) (hD i hi j hj)
    have ht := small_top_period_floor (I i j) N (e i) A (S i j) (U i j)
      (hI i hi j hj) (he i hi) hHj (hNv i hi) hy (hL i hi)
      (hJ i hi j hj).1 (hJ i hi j hj).2
      (by linarith [(hJ i hi j hj).1,hgap i hi j hj]) (hU i hi j hj)
      (hS i hi j hj) (hcount i hi j hj) (hP i hi j hj) (howner i hi j hj)
      (hA i hi j hj) (hpeak i hi) (hsign i hi) (hscale i hi j hj)
    simpa only [hz,Finset.empty_sdiff,Finset.sum_empty,add_zero] using ht
  have ht := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  simp only [neg_mul,Finset.sum_neg_distrib] at ht
  have hc := global_small_top_cost_le V O N v (by linarith only [hH]) hNv hvG hO
  simpa only [neg_mul] using (neg_le_neg hc).trans ht

/-- The full dense small-top price is `O(log(N)/N^12)` in actual supply
units. No effective starting order or arithmetic-head evaluation follows. -/
theorem tendsto_smallTopSupplyPrice : Tendsto smallTopSupplyPrice atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := tendsto_log_atTop.comp hn
  have h₀ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 12 (by norm_num)).comp hl
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 12 (by norm_num)).comp hl
  simp only [Function.comp_def,rpow_zero,rpow_one,one_mul] at h₀ h₁
  have ht := ((h₀.const_mul (1+log 4/log 2)).add
    (h₁.const_mul (log 2)⁻¹)).const_mul (3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)))
  convert ht using 1
  · funext N
    unfold smallTopSupplyPrice
    rw [log_mul (by norm_num : (4 : ℝ)≠0) (by positivity : (N : ℝ)+1≠0),exp_sub]
    rw [div_eq_mul_inv,← exp_neg]
    simp only [div_eq_mul_inv,neg_mul]
    ring
  · ring

/-- The nonempty-boundary price differs only by a fixed constant. -/
def smallTopBoundarySupplyPrice (N : ℕ) : ℝ := (16136/3848 : ℝ)*smallTopSupplyPrice N

/-- The count-tilted global boundary price sums all owner/radial scales. -/
theorem global_small_top_with_boundary_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v : ℕ→ℝ) {H : ℝ} (hH : 1≤H)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i) :
    (∑ i∈V,∑ _j∈O i,
      (16136*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N (v i)/v i))≤ smallTopBoundarySupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hh := mul_le_mul_of_nonneg_left
    (global_small_top_cost_le V O N v hH hNv hvG hO) (by norm_num : (0 : ℝ)≤16136/3848)
  simp_rw [Finset.mul_sum] at hh
  calc
    _ = ∑ i∈V,∑ _j∈O i,(16136/3848 : ℝ)*
        ((3848*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
          (amplitude N (v i)/v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i∈V,(16136/3848 : ℝ)*(smallTopSupplyPrice N*(amplitude N (v i)/v i)) := hh
    _ = _ := by
      unfold smallTopBoundarySupplyPrice
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Remove the strict owner-gap restriction from the global dense
small-top signed floor. ALL actual ownership clips are paid once by the
retained count tilt, at the same `O(log(N)/N^12)` relative supply rate. -/
theorem global_small_top_with_boundary_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v e : ℕ→ℝ) (I : ℕ→ℕ→Finset ℕ) (J : ℕ→ℕ→ℝ)
    (S : ℕ→ℕ→ℕ→Finset ℕ) (D Pplus Pminus U : ℕ→ℕ→Finset ℕ) (A : Finset ℕ)
    {H y L : ℝ} (hH : 10000≤H) (hy : 54≤y)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (he : ∀ i∈V,|e i|=1) (hL : ∀ i∈V,v i/2≤L)
    (hJ : ∀ i∈V,∀ j∈O i,5000≤J i j ∧ J i j≤4*((N : ℝ)+1))
    (hscale : ∀ i∈V,∀ j∈O i,512*J i j*log ((N : ℝ)+1)≤v i)
    (hJH : ∀ i∈V,∀ j∈O i,J i j≤H*(2 : ℝ)^j)
    (hU : ∀ i∈V,∀ j∈O i,∀ p∈U i j,p.Prime ∧ log p≤4*J i j)
    (hI : ∀ i∈V,∀ j∈O i,∀ k∈I i j,2≤k)
    (hS : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors⊆U i j)
    (hcount : ∀ i∈V,∀ j∈O i,∀ k∈I i j,v i/4≤4*J i j*((k : ℝ)+3))
    (hP : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ k∈I i j,∀ a∈S i j k,
      ∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ n∈D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧
        log (largestPrime n)-log q≤1/8) ∧ (n/largestPrime n).primeFactors⊆U i j)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -smallTopBoundarySupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
         (∑ n∈D i j\Pplus i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
         (∑ n∈D i j\Pminus i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) :
      -(16136*exp (4*(smallPrimeHeadMass+log 16+1/5000)-12*log ((N : ℝ)+1)))*
        (amplitude N (v i)/v i)≤
        ((∑ k∈I i j,∑ a∈S i j k,
          ∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
         (∑ n∈D i j\Pplus i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
         (∑ n∈D i j\Pminus i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hHj : 10000≤H*(2 : ℝ)^j := by
      have hp := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hH,hp]
    exact small_top_with_boundary_period_floor (I i j) N (e i) A (S i j) (D i j)
      (Pplus i j) (Pminus i j) (U i j) (hI i hi j hj) (he i hi) hHj (hNv i hi) hy (hL i hi)
      (hJ i hi j hj).1 (hJ i hi j hj).2 (hJH i hi j hj) (hU i hi j hj)
      (hS i hi j hj) (hcount i hi j hj) (hP i hi j hj) (howner i hi j hj)
      (hA i hi j hj) (hD i hi j hj) (hpeak i hi) (hsign i hi) (hscale i hi j hj)
  have ht := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  simp only [neg_mul,Finset.sum_neg_distrib] at ht
  have hc := global_small_top_with_boundary_cost_le V O N v (by linarith only [hH]) hNv hvG hO
  simpa only [neg_mul] using (neg_le_neg hc).trans ht

/-- The newly paid nonempty-boundary population has the SAME vanishing
relative supply rate. This does not imply absolute source-scale decay. -/
theorem tendsto_smallTopBoundarySupplyPrice :
    Tendsto smallTopBoundarySupplyPrice atTop (𝓝 0) := by
  change Tendsto (fun N => (16136/3848 : ℝ)*smallTopSupplyPrice N) atTop (𝓝 0)
  simpa only [mul_zero] using
    tendsto_smallTopSupplyPrice.const_mul (16136/3848 : ℝ)

end RiemannGaussian.ZetaRieszDenseSmallTopFloor
