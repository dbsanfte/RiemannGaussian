/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallCofactorCancellation

/-!
# Keep the least-prime saving through literal ownership clips

Deleting the two nearly tied large owner primes cannot delete a strictly
smaller least prime. The remaining cofactor therefore retains the small
least-prime response bound, while both owner-prime reciprocals remain in
the boundary payment. Counts are joined before this price is compared
with the signed complete-period price. No whole-core floor is asserted.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSmallOwnerBoundary
open ZetaRieszSmallCofactorCancellation ZetaRieszBroadOwnerPeriodFloor
open ZetaRieszClippedOwnerPeriodFloor ZetaRieszTinyOwnerPeriodFloor
open ZetaRieszLogShellPeriodFloor ZetaRieszSymmetricPeriodPayment
open ZetaRieszStaggeredFloor ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszAllowancePrimeBoxes ZetaRieszQuantitativePrimePeriod
open ZetaRieszOwnerCurvatureFloor ZetaRieszJointOwnerFibreFloor
open ZetaRieszPrimeEndpoint ZetaRieszMacroPrimeWindows
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszMultiPeriodSix

set_option maxHeartbeats 800000

/-- Removing two primes larger than the original least prime preserves
its upper logarithmic bound in the remaining literal cofactor. -/
theorem least_prime_survives_pair {n p q b : ℕ} {B : ℝ}
    (hn : n ≠ 1) (he : n=p*(q*b)) (hp : p.Prime) (hq : q.Prime)
    (hmin : log n.minFac ≤ B) (hpB : B < log p) (hqB : B < log q) :
    log b.minFac ≤ B := by
  have hr := Nat.minFac_prime hn
  have hrd : n.minFac ∣ p*(q*b) := he ▸ Nat.minFac_dvd n
  have hrp : ¬ n.minFac ∣ p := by
    intro hd
    have hh : p=n.minFac := (hp.dvd_iff_eq hr.ne_one).mp hd
    rw [hh] at hpB
    linarith
  have hrq : ¬ n.minFac ∣ q := by
    intro hd
    have hh : q=n.minFac := (hq.dvd_iff_eq hr.ne_one).mp hd
    rw [hh] at hqB
    linarith
  have hrb := (hr.dvd_mul.mp ((hr.dvd_mul.mp hrd).resolve_left hrp)).resolve_left hrq
  exact (log_le_log (by exact_mod_cast Nat.minFac_pos b)
    (by exact_mod_cast Nat.minFac_le_of_dvd hr.two_le hrb)).trans hmin

/-- The actual near-tied owner cover preserves a small least prime.
No artificial lower cutoff is imposed on any remaining cofactor prime. -/
theorem small_clipped_cofactor_cover {k n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card=k+2) (hk : 0<k) {v H B : ℝ} (Q : Finset ℕ)
    (hBH : B+1≤H) (hmin : log n.minFac≤B)
    (hT : v-1/16<log n ∧ log n≤v+1/16)
    (hclip : ∃ q ∈ (n/largestPrime n).primeFactors,
      H≤log q ∧ log (largestPrime n)-log q≤1/8)
    (hQ : (n/largestPrime n).primeFactors ⊆ Q) :
    ∃ b q : ℕ,n=largestPrime n*(q*b) ∧ Squarefree b ∧
      b.primeFactors.card=k ∧ b.primeFactors ⊆ Q ∧
      (log b≤v-2*H+1/16 ∧ log b.minFac≤B) ∧
      largestPrime n ∈ ZetaRieszOwnerTieFloor.pairWindow v b ∧
      q ∈ ZetaRieszOwnerTieFloor.pairWindow v b := by
  obtain ⟨b,q,he,hb,hbc,hbsub,hcap,hpw,hqw⟩ :=
    broad_clipped_cofactor_cover hn hc hk Q hT hclip hQ
  have hp := logPrimes_bounds hpw
  have hq := logPrimes_bounds hqw
  have hplo : (v-log b)/2-1/8<log (largestPrime n) := hp.2.1
  have hqlo : (v-log b)/2-1/8<log q := hq.2.1
  have hn1 : n≠1 := by intro hh; simp [hh] at hc
  have hm := least_prime_survives_pair hn1 he hp.1 hq.1 hmin
    (by linarith) (by linarith)
  exact ⟨b,q,he,hb,hbc,hbsub,⟨hcap,hm⟩,hpw,hqw⟩

/-- A divisor-layer gap pays the ENTIRE original allocated complex atom
by exact zero. No prime period, phase, factorial or support mask is removed. -/
theorem literal_atom_zero_of_spectrum_gap (A : Finset ℕ) (y : ℝ) (N : ℕ)
    {R B : ℕ} (hs : Squarefree R) (hc : 2≤R.primeFactors.card)
    (hcop : B.Coprime R) {L : ℝ}
    (hgap : ∀ d ∈ B.divisors,L≤log d ∨ log d+log R≤L) :
    ZetaRieszJointAllocation.residualCoefficient A L N (B*R)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (B*R)=0 := by
  have hz := spectrum_gap_cutoff_zero hs hc hcop hgap
  simp [ZetaRieszJointAllocation.residualCoefficient,SquarefreeVaughanLogSource.coefficient,hz]

/-- For two distinct owner primes, the SAME small divisor block pays all
four translated cutoffs before any norm. This includes original owner
clipping atoms at arbitrary growing counts, when these gaps hold. -/
theorem owner_pair_atom_zero_of_spectrum_gaps (A : Finset ℕ) (y : ℝ) (N : ℕ)
    {p q R B : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hpBR : ¬p∣B*R) (hqBR : ¬q∣B*R)
    (hs : Squarefree R) (hc : 2≤R.primeFactors.card) (hcop : B.Coprime R) {L : ℝ}
    (hgap : ∀ D ∈ ({L,L-log p,L-log q,L-log p-log q} : Finset ℝ),
      ∀ d ∈ B.divisors,D≤log d ∨ log d+log R≤D) :
    ZetaRieszJointAllocation.residualCoefficient A L N (p*(q*(B*R)))*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(B*R)))=0 := by
  have hpqBR : ¬p∣q*(B*R) := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpq ((Nat.dvd_prime_two_le hq hp.two_le).mp h)
    · exact hpBR h
  have hz₀ := spectrum_gap_cutoff_zero hs hc hcop (hgap L (by simp))
  have hz₁ := spectrum_gap_cutoff_zero hs hc hcop (hgap (L-log p) (by simp))
  have hz₂ := spectrum_gap_cutoff_zero hs hc hcop (hgap (L-log q) (by simp))
  have hz₃ := spectrum_gap_cutoff_zero hs hc hcop (hgap (L-log p-log q) (by simp))
  have hz : VaughanLogAverage.riesz L (p*(q*(B*R)))=0 := by
    rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpqBR,
      ZetaSquarefreeRieszWindows.riesz_prime_mul L hq hqBR,
      ZetaSquarefreeRieszWindows.riesz_prime_mul (L-log p) hq hqBR,
      hz₀,hz₁,hz₂,hz₃]
    ring
  simp [ZetaRieszJointAllocation.residualCoefficient,SquarefreeVaughanLogSource.coefficient,hz]

/-- Any original ownership-boundary subpopulation satisfying the joint
four-cutoff test has exactly zero payment, including both missing phase
selections and its actual allocation. The masks remain in `D`. -/
theorem owner_boundary_norm_zero_of_spectrum_gaps (A D : Finset ℕ) (L y : ℝ) (N : ℕ)
    (hD : ∀ n ∈ D,∃ p q B R : ℕ,n=p*(q*(B*R)) ∧ p.Prime ∧ q.Prime ∧ p≠q ∧
      ¬p∣B*R ∧ ¬q∣B*R ∧ Squarefree R ∧ 2≤R.primeFactors.card ∧ B.Coprime R ∧
      ∀ T ∈ ({L,L-log p,L-log q,L-log p-log q} : Finset ℝ),
        ∀ d ∈ B.divisors,T≤log d ∨ log d+log R≤T) :
    (∑ n ∈ D,‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)=0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨p,q,B,R,he,hp,hq,hpq,hpBR,hqBR,hs,hc,hcop,hgap⟩ := hD n hn
  rw [he,owner_pair_atom_zero_of_spectrum_gaps A y N hp hq hpq hpBR hqBR hs hc hcop hgap,
    norm_zero]

private theorem response_constant_bound (k : ℕ) : responseConstant k≤6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ)≤(2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    exact_mod_cast hh.trans (Nat.pow_le_pow_right (by norm_num : 1≤(2 : ℕ)) (by omega : k-2≤k))
  have h0 := hp 0
  have h1 := hp 1
  unfold responseConstant
  nlinarith only [h0,h1,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := k)]

/-- The literal ownership boundary keeps its least-prime factor. The
remaining count symmetry and both near-tied prime reciprocals are paid
only after this improvement, replacing the old `1/H` boundary by
`B₀/H²`. Every original allocation and phase remains in the atom. -/
theorem small_clipped_count_norm_bound {k N : ℕ} (hk : 0 < k)
    (A D Q : Finset ℕ) (y : ℝ) {v L H M B₀ : ℝ} (hH : 10000 ≤ H)
    (hv : 0 < v) (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hM : 0≤M) (hQmass : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p ∈ Q,log p≤4*H)
    (hB₀ : 0≤B₀) (hBH : B₀+1≤H) (hsmall : ∀ n ∈ D,log n.minFac≤B₀)
    (hD : ∀ n ∈ D, Squarefree n ∧ n.primeFactors.card=k+2 ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
        (n/largestPrime n).primeFactors ⊆ Q) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      ((384*B₀*(2*M)^k/(k.factorial : ℝ))/H^2)*(amplitude N v/v) := by
  have hH0 : 0 < H := by linarith
  let R := (ZetaRieszCofactorMass.products k (4*H)).filter (fun b : ℕ =>
    Squarefree b ∧ b.primeFactors.card=k ∧ b.primeFactors ⊆ Q ∧
      log b ≤ v-2*H+1/16 ∧ log b.minFac≤B₀)
  let V := R.sigma (fun b => (ZetaRieszOwnerTieFloor.pairWindow v b).product
    (ZetaRieszOwnerTieFloor.pairWindow v b))
  let label := fun x : Σ _ : ℕ, ℕ×ℕ => x.2.1*(x.2.2*x.1)
  let f := fun n => if n ∈ D then
    ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ else 0
  let B := 2*amplitude N v*responseConstant (k+2)/L
  have hL0 : 0 < L := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)]
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hcover : D ⊆ V.image label := by
    intro n hn
    obtain ⟨hs,hc,hT,htie,hshell⟩ := hD n hn
    obtain ⟨b,q,he,hb,hbc,hbsub,hcap,hpw,hqw⟩ :=
      small_clipped_cofactor_cover hs hc hk Q hBH (hsmall n hn) hT htie hshell
    have hbm : b ∈ ZetaRieszCofactorMass.products k (4*H) :=
      ZetaRieszCofactorMass.mem_products_of_squarefree hb hbc
        (fun r hr => hQlog r (hbsub hr))
    exact Finset.mem_image.mpr ⟨⟨b,(largestPrime n,q)⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨hbm,hb,hbc,hbsub,hcap⟩,
        Finset.mem_product.mpr ⟨hpw,hqw⟩⟩,he.symm⟩
  have hfirst : (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤ ∑ x ∈ V, f (label x) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans
      (Finset.sum_image_le_of_nonneg (fun n _ => hf n))
    simpa only [f,ite_true,Finset.sum_congr rfl (fun n hn => if_pos hn)] using hh
  have hpoint (b : ℕ) (hb : b ∈ R) (p q : ℕ) :
      f (p*(q*b)) ≤ B*(B₀*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹ := by
    obtain ⟨_,_,hbc,_,hcap,hmin⟩ := Finset.mem_filter.mp hb
    have hb1 : b ≠ 1 := by intro hh; simp [hh] at hbc; omega
    have hm : log b.minFac ≤ B₀ := hmin
    by_cases hn : p*(q*b) ∈ D
    · have hd := hD _ hn
      have hT : |log (p*(q*b) : ℕ)-v| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hd.2.2.1.1],by linarith [hd.2.2.1.2]⟩
      have hh := ZetaRieszOwnerTieFloor.boundary_atom_norm A y hv hNv hL0 hd.1 hd.2.1
        hb1 (dvd_mul_of_dvd_right (dvd_mul_left b q) p) hT
      dsimp only [f]
      rw [if_pos hn]
      have hle := mul_le_mul_of_nonneg_left hm (by positivity :
        0 ≤ B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)
      have heq : B*(log b.minFac/(p*(q*b) : ℕ)) =
          (B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)*log b.minFac := by
        simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
        ring
      change _ ≤ B*(log b.minFac/(p*(q*b) : ℕ)) at hh
      rw [heq] at hh
      exact hh.trans (by convert hle using 1; ring)
    · dsimp only [f]
      rw [if_neg hn]
      positivity
  have hrec := interval_cofactor_mass_le R Q k hQmass (by
    intro b hb
    have hh := (Finset.mem_filter.mp hb).2
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩)
  have hsum : (∑ x ∈ V, f (label x)) ≤
      B*B₀*(4/H^2)*(M^k/(k.factorial : ℝ)) := by
    change (∑ x ∈ R.sigma _, f (label x)) ≤ _
    rw [Finset.sum_sigma]
    have hrow (b : ℕ) (hb : b ∈ R) :
        (∑ pq ∈ (ZetaRieszOwnerTieFloor.pairWindow v b).product
          (ZetaRieszOwnerTieFloor.pairWindow v b), f (pq.1*(pq.2*b))) ≤
        B*B₀*(4/H^2)*(b : ℝ)⁻¹ := by
      rw [Finset.product_eq_sprod,Finset.sum_product]
      have hh := Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
        (fun p _ => Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
          (fun q _ => hpoint b hb p q))
      have hm := shell_pairWindow_mass hH (Finset.mem_filter.mp hb).2.2.2.2.1
      have hsq := pow_le_pow_left₀ (by positivity) hm 2
      have heq : (∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
          ∑ q ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
            B*(B₀*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹) =
          (B*(B₀*(b : ℝ)⁻¹))*(∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,(p : ℝ)⁻¹)^2 := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,← Finset.mul_sum,pow_two]
        ring
      rw [heq] at hh
      have hpay := mul_le_mul_of_nonneg_left hsq
        (by positivity : 0 ≤ B*(B₀*(b : ℝ)⁻¹))
      exact hh.trans (by convert hpay using 1; field_simp; ring)
    have hh := Finset.sum_le_sum hrow
    rw [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hrec (by positivity))
  have hpre : B ≤ 4*(amplitude N v/v)*responseConstant (k+2) := by
    have hh := div_le_div_of_nonneg_left
      (by positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)] :
        0 ≤ 2*amplitude N v*responseConstant (k+2))
      (by positivity : 0 < v/2) hL
    convert hh using 1
    all_goals first | rfl | ring
  have hcost := mul_le_mul_of_nonneg_right hpre
    (by positivity [hM] : 0 ≤ B₀*(4/H^2)*(M^k/(k.factorial : ℝ)))
  have heq : (4*(amplitude N v/v)*responseConstant (k+2))*
      (B₀*(4/H^2)*(M^k/(k.factorial : ℝ))) =
      (16*B₀*(amplitude N v/v)*responseConstant (k+2)*(M^k/(k.factorial : ℝ)))*(1/H^2) := by
    field_simp
    ring
  rw [heq] at hcost
  have hr : responseConstant (k+2) ≤ 24*(2 : ℝ)^k := by
    have hh := response_constant_bound (k+2)
    norm_num [pow_add] at hh
    convert hh using 1
    ring
  have hpay := mul_le_mul_of_nonneg_left hr (by positivity [hM,amplitude_nonneg N hv.le] :
    0 ≤ 16*B₀*(amplitude N v/v)*(M^k/(k.factorial : ℝ))*(1/H^2))
  have hpaid : (16*B₀*(amplitude N v/v)*responseConstant (k+2)*
      (M^k/(k.factorial : ℝ)))*(1/H^2) ≤
        ((384*B₀*(2*M)^k/(k.factorial : ℝ))/H^2)*(amplitude N v/v) := by
    simp only [mul_pow,div_eq_mul_inv] at hpay ⊢
    nlinarith only [hpay]
  exact hfirst.trans (hsum.trans (by simpa only [mul_assoc] using hcost.trans hpaid))

/-- One ownership-boundary price over every selected count. A least
prime need only be small relative to the deleted owner pair; every other
cofactor prime may be arbitrarily small. -/
theorem small_clipped_all_counts_norm_bound (A D Q : Finset ℕ) (y : ℝ) (N : ℕ)
    {v L H M B : ℝ} (hH : 10000≤H) (hv : 0<v) (hNv : (N : ℝ)+1≤v) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p ∈ Q,log p≤4*H)
    (hB : 0≤B) (hBH : B+1≤H) (hsmall : ∀ n ∈ D,log n.minFac≤B)
    (hD : ∀ n ∈ D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ Q) :
    (∑ n ∈ D,‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
        (384*B*exp (2*M)/H^2)*(amplitude N v/v) := by
  let I := D.image (fun n => n.primeFactors.card-2)
  let S := fun k => D.filter (fun n => n.primeFactors.card-2=k)
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hI k (hk : k ∈ I) : 0<k := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have := (hD n hn).2.1
    omega
  have hrow k (hk : k ∈ I) :
      (∑ n ∈ S k,f n)≤((384*B*(2*M)^k/(k.factorial : ℝ))/H^2)*(amplitude N v/v) := by
    apply small_clipped_count_norm_bound (hI k hk) A (S k) Q y hH hv hNv hL hM hQmass hQlog hB hBH
      (fun n hn => hsmall n (Finset.mem_filter.mp hn).1)
    intro n hn
    obtain ⟨hn,hcnt⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2⟩
  have heq : (∑ k ∈ I,∑ n ∈ S k,f n)=∑ n ∈ D,f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have hh := Finset.sum_le_sum hrow
  rw [heq,← Finset.sum_mul,← Finset.sum_div] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_count_price_le I hM (show 0≤384*B by positivity))
      (sq_nonneg H)) (div_nonneg (amplitude_nonneg N hv.le) hv.le))

/-- Restore all small cofactor primes in the literal ownership-boundary
population. Its price depends only on the least-prime upper bound, not
on an exponential prime-count or owner-log loss. -/
theorem whole_small_boundary_norm_bound (A D Q : Finset ℕ) (y : ℝ) (N : ℕ)
    {v L H B : ℝ} (hH : 10000≤H) (hv : 0<v) (hNv : (N : ℝ)+1≤v) (hL : v/2≤L)
    (hQ : ∀ p ∈ Q,p.Prime ∧ log p≤4*H)
    (hB : 0≤B) (hBH : B+1≤H) (hsmall : ∀ n ∈ D,log n.minFac≤B)
    (hD : ∀ n ∈ D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ Q) :
    (∑ n ∈ D,‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
        (384*smallPrimeHeadCost*B)*(amplitude N v/v) := by
  have hH0 : 0<H := by linarith
  have hh := small_clipped_all_counts_norm_bound A D Q y N hH hv hNv hL
    (Finset.sum_nonneg (fun p _ => by positivity)) (le_refl _)
    (fun p hp => (hQ p hp).2) hB hBH hsmall hD
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (whole_count_exponential_le Q (by linarith) hQ)
      (show 0≤384*B by positivity)) (sq_nonneg H)
  have heq : 384*B*(smallPrimeHeadCost*H^2)/H^2=384*smallPrimeHeadCost*B := by
    field_simp
  rw [heq] at hc
  exact hh.trans (mul_le_mul_of_nonneg_right hc
    (div_nonneg (amplitude_nonneg N hv.le) hv.le))

/-- The signed flat-response population and its ACTUAL ownership clips
share the same least-prime price. Both missed sign selections spend ONE
boundary atom. Counts and small cofactor primes are all joined first. -/
theorem whole_small_flat_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) (D P Q U : Finset ℕ) {v y L H B : ℝ}
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hH : 10000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L) (hB : 0≤B) (hBH : B+1≤H)
    (hU : ∀ p ∈ U,p.Prime ∧ log p≤4*H)
    (hS : ∀ k ∈ I,∀ a ∈ S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ U)
    (hmin : ∀ k ∈ I,∀ a ∈ S k,log a.minFac≤B)
    (hP : ∀ k ∈ I,∀ a ∈ S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k ∈ I,∀ a ∈ S k,∀ q ∈ a.primeFactors,log q≤v-Real.pi/y-log a)
    (hsmall : ∀ n ∈ D,log n.minFac≤B)
    (hD : ∀ n ∈ D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ U)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hflat : ∀ k ∈ I,∀ a ∈ S k,∀ T ∈ Set.Icc (v-Real.pi/y) (v+Real.pi/y),
      response L T a=response L v a) :
    -(504*smallPrimeHeadCost*B)*(amplitude N v/v)≤
      (∑ k ∈ I,∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a))+
      (∑ n ∈ D\P,signedPart 1 ∅ L y N n)+
      (∑ n ∈ D\Q,signedPart (-1) ∅ L y N n) := by
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmain := whole_small_flat_floor I N e S U hI he (by linarith) hNv hy hL
    hB hU hS hmin hP howner hpeak hsign hflat
  have hnorm := whole_small_boundary_norm_bound ∅ D U y N hH hv (by linarith) hL
    hU hB hBH hsmall hD
  have hparts := ZetaRieszOwnerTieFloor.missed_parts_floor ∅ D P Q L y N
  have hh := add_le_add hmain ((neg_le_neg hnorm).trans hparts)
  convert! hh using 1 <;> ring

/-- Every dyadic owner scale below a radial endpoint is counted once.
The count is logarithmic even when all cofactor counts are growing. -/
theorem dyadic_owner_card_le (J : Finset ℕ) {H v : ℝ} (hH : 1≤H) (hv : 1≤v)
    (hJ : ∀ j ∈ J,H*(2 : ℝ)^j≤v) :
    (J.card : ℝ)≤1+log v/log 2 := by
  have hlog : 0≤log v/log 2 := div_nonneg (log_nonneg hv) (log_pos (by norm_num)).le
  have hsub : J ⊆ Finset.range (⌊log v/log 2⌋₊+1) := by
    intro j hj
    have hp : (2 : ℝ)^j≤v := by
      have hh := mul_le_mul_of_nonneg_right hH (by positivity : 0≤(2 : ℝ)^j)
      simpa only [one_mul] using hh.trans (hJ j hj)
    have hl := log_le_log (by positivity : (0 : ℝ)<(2 : ℝ)^j) hp
    rw [log_pow] at hl
    have hc : (j : ℝ)≤log v/log 2 := (le_div_iff₀ (log_pos (by norm_num))).mpr hl
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hc))
  have hh : (J.card : ℝ)≤⌊log v/log 2⌋₊+1 := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le hlog
  linarith only [hh,hf]

/-- Joined small-prime main and ownership clips over EVERY owner scale
and radial period, in the ACTUAL positive supply units `amplitude/v`.
The literal support and complete-fibre cover remain explicit premises.
No claim that this price tends to zero is made. -/
theorem small_flat_radial_supply_floor (V : Finset ℕ) (J : ℕ → Finset ℕ)
    (I : ℕ → ℕ → Finset ℕ) (N : ℕ) (e v : ℕ → ℝ)
    (S : ℕ → ℕ → ℕ → Finset ℕ) (D P Q U : ℕ → ℕ → Finset ℕ)
    {y L H B G : ℝ} (hH : 10000≤H) (hB : 0≤B) (hBH : B+1≤H)
    (hy : 54≤y)
    (hv : ∀ i ∈ V,v i≤G)
    (hJ : ∀ i ∈ V,∀ j ∈ J i,H*(2 : ℝ)^j≤v i)
    (hI : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,2≤k)
    (he : ∀ i ∈ V,|e i|=1) (hNv : ∀ i ∈ V,(N : ℝ)+2≤v i)
    (hL : ∀ i ∈ V,v i/2≤L)
    (hU : ∀ i ∈ V,∀ j ∈ J i,∀ p ∈ U i j,p.Prime ∧ log p≤4*(H*(2 : ℝ)^j))
    (hS : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ a ∈ S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ U i j)
    (hmin : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ a ∈ S i j k,log a.minFac≤B)
    (hP : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ a ∈ S i j k,
      H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ a ∈ S i j k,
      ∀ q ∈ a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hsmall : ∀ i ∈ V,∀ j ∈ J i,∀ n ∈ D i j,log n.minFac≤B)
    (hD : ∀ i ∈ V,∀ j ∈ J i,∀ n ∈ D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ U i j)
    (hpeak : ∀ i ∈ V,sin (y*v i)=0) (hsign : ∀ i ∈ V,e i*cos (y*v i)≤0)
    (hflat : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ a ∈ S i j k,
      ∀ T ∈ Set.Icc (v i-Real.pi/y) (v i+Real.pi/y),response L T a=response L (v i) a) :
    -(504*smallPrimeHeadCost*B*(1+log G/log 2))*(∑ i ∈ V,amplitude N (v i)/v i)≤
      ∑ i ∈ V,∑ j ∈ J i,
        ((∑ k ∈ I i j,∑ a ∈ S i j k,
          ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) ∅ L y N (p*a))+
          (∑ n ∈ D i j\P i j,signedPart 1 ∅ L y N n)+
          (∑ n ∈ D i j\Q i j,signedPart (-1) ∅ L y N n)) := by
  have hH0 : 0<H := by linarith
  have hC : 0≤504*smallPrimeHeadCost*B := by positivity [smallPrimeHeadCost_pos]
  have hpaid i (hi : i ∈ V) := Finset.sum_le_sum (fun j (hj : j ∈ J i) =>
    whole_small_flat_with_boundary_floor (I i j) N (e i) (S i j) (D i j) (P i j) (Q i j) (U i j)
      (hI i hi j hj) (he i hi)
      (hH.trans (by nlinarith only [hH0,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)]))
      (hNv i hi) hy (hL i hi) hB
      (hBH.trans (by nlinarith only [hH0,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)]))
      (hU i hi j hj) (hS i hi j hj) (hmin i hi j hj) (hP i hi j hj)
      (howner i hi j hj) (hsmall i hi j hj) (hD i hi j hj)
      (hpeak i hi) (hsign i hi) (hflat i hi j hj))
  have hrow i (hi : i ∈ V) :
      -(504*smallPrimeHeadCost*B*(1+log G/log 2))*(amplitude N (v i)/v i)≤
        ∑ j ∈ J i,
          ((∑ k ∈ I i j,∑ a ∈ S i j k,
            ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
              signedPart (e i) ∅ L y N (p*a))+
            (∑ n ∈ D i j\P i j,signedPart 1 ∅ L y N n)+
            (∑ n ∈ D i j\Q i j,signedPart (-1) ∅ L y N n)) := by
    have hvi : 1≤v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hlg := div_le_div_of_nonneg_right (log_le_log (by linarith) (hv i hi))
      (log_pos (by norm_num : (1 : ℝ)<2)).le
    have hc : ((J i).card : ℝ)≤1+log G/log 2 := by
      linarith only [dyadic_owner_card_le (J i) (by linarith) hvi (hJ i hi),hlg]
    have hf : 0≤amplitude N (v i)/v i :=
      div_nonneg (amplitude_nonneg N (by linarith)) (by linarith)
    have hcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hC) hf
    have hh := hpaid i hi
    simp only [neg_mul] at hh
    rw [Finset.sum_neg_distrib,Finset.sum_const,nsmul_eq_mul] at hh
    calc
      _ = -(504*smallPrimeHeadCost*B*(1+log G/log 2)*(amplitude N (v i)/v i)) := by ring
      _ ≤ -(504*smallPrimeHeadCost*B*((J i).card : ℝ)*(amplitude N (v i)/v i)) :=
        neg_le_neg hcost
      _ = -(((J i).card : ℝ)*(504*smallPrimeHeadCost*B*(amplitude N (v i)/v i))) := by ring
      _ ≤ _ := hh
  have hh := Finset.sum_le_sum hrow
  simpa only [← Finset.mul_sum] using hh

/-- Price relative to `amplitude`, ONE degree above the actual supply
unit `amplitude/v`. Its decay alone is not a positive supply payment. -/
def smallFlatRadialPrice (N : ℕ) : ℝ :=
  504*smallPrimeHeadCost*log ((N : ℝ)+1)*
    (1+log (4*((N : ℝ)+1))/log 2)/((N : ℝ)+1)

/-- This coefficient is `O(log²(N+1)/(N+1))` in the one-degree-higher
`amplitude` units. The corresponding ACTUAL supply price is audited below;
this limit by itself does not pay any literal packet. -/
theorem tendsto_smallFlatRadialPrice :
    Tendsto smallFlatRadialPrice atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₁ : Tendsto (fun N : ℕ => log ((N : ℝ)+1)/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero,pow_one] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hn
  have h₂ : Tendsto (fun N : ℕ => (log ((N : ℝ)+1))^2/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hn
  have ht := ((h₁.const_mul (1+log 4/log 2)).add (h₂.const_mul (log 2)⁻¹)).const_mul
    (504*smallPrimeHeadCost)
  convert ht using 1
  · funext N
    unfold smallFlatRadialPrice
    rw [log_mul (by norm_num : (4 : ℝ)≠0) (by positivity : (N : ℝ)+1≠0)]
    simp only [div_eq_mul_inv]
    ring
  · ring

/-- The actual supply-unit price corresponding to the preceding
one-degree-higher coefficient. It is NOT claimed to decay. -/
def smallFlatSupplyPrice (N : ℕ) : ℝ :=
  504*smallPrimeHeadCost*log ((N : ℝ)+1)*(1+log (4*((N : ℝ)+1))/log 2)

/-- Restoring the missing radial power is an exact normalization
identity, not an asymptotic or a comparison of different supplies. -/
theorem smallFlatRadialPrice_mul_eq_supplyPrice (N : ℕ) :
    smallFlatRadialPrice N*((N : ℝ)+1)=smallFlatSupplyPrice N := by
  unfold smallFlatRadialPrice smallFlatSupplyPrice
  rw [div_mul_cancel₀ _ (by positivity : (N : ℝ)+1≠0)]

/-- The boundary/count majorant still grows in the ACTUAL supply units.
The cheaper least-prime bound is a saving, not the whole floor. -/
theorem tendsto_smallFlatSupplyPrice_atTop :
    Tendsto smallFlatSupplyPrice atTop atTop := by
  have hl := tendsto_log_atTop.comp
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hC : 0<504*smallPrimeHeadCost := by positivity [smallPrimeHeadCost_pos]
  have ht : Tendsto (fun N : ℕ => (504*smallPrimeHeadCost)*log ((N : ℝ)+1)) atTop atTop :=
    hl.const_mul_atTop hC
  apply tendsto_atTop_mono (fun N => ?_) ht
  have hn : (1 : ℝ)≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hlog : 0≤log (4*((N : ℝ)+1))/log 2 :=
    div_nonneg (log_nonneg (by linarith : (1 : ℝ)≤4*((N : ℝ)+1)))
      (log_pos (by norm_num)).le
  unfold smallFlatSupplyPrice
  nlinarith only [mul_nonneg (mul_nonneg hC.le (log_nonneg hn)) hlog]

/-- The current joined positive price cannot fit any fixed supply
fraction eventually. This audits the majorant, not impossibility of a
stronger signed arithmetic floor. -/
theorem not_eventually_smallFlatSupplyPrice_le (c : ℝ) :
    ¬ ∀ᶠ N : ℕ in atTop,smallFlatSupplyPrice N≤c := by
  intro h
  obtain ⟨N,hN,hlt⟩ := (h.and (tendsto_smallFlatSupplyPrice_atTop.eventually_gt_atTop c)).exists
  exact (not_lt_of_ge hN) hlt

/-- The older broad all-radial theorem is stated in `amplitude` units,
whereas its standalone supply theorem uses `amplitude/v`. This is the
exact extra factor needed before those theorems could be joined. -/
theorem broad_price_in_supply_units (N : ℕ) {v a : ℝ} (hv : v≠0) :
    (129088/a^2)*amplitude N v=(129088*v/a^2)*(amplitude N v/v) := by
  field_simp

end RiemannGaussian.ZetaRieszSmallOwnerBoundary
