/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSeparatedParityFloor
import RiemannGaussian.ZetaRieszDenseCountCoverFloor
import RiemannGaussian.ZetaRieszGlobalDebitAudit

set_option autoImplicit false

/-!
# Exponential divisor-packing saving for the separated signed crossing cost

Uniformly separated background divisor logs fit inside [0, log B]. Their
exact number is 2^omega(B). This bounds the joined two-hinge debit by
|Re w| log B / (2^omega(B)-1), before summing original labels. The actual
phase, allocation and retained divisor sum are unchanged. No bound for
the resulting complete population cost is assumed or asserted.
-/

noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSeparatedPackingFloor
open Filter Topology
open ZetaRieszSeparatedParityFloor ZetaRieszPrimeEndpoint
open ZetaRieszParityPacket ZetaRieszSmallCofactorCancellation
open ZetaRieszShortDivisorOrbits ZetaRieszSignedConvolution
open ZetaRieszShortDivisorCancellation
open ZetaRieszJointAllocation

set_option maxHeartbeats 800000

/-- Pack every background divisor, rather than only active translates.
The gap cannot exceed log B divided by the exact number of gaps. -/
theorem divisor_log_gap_packing {B : ℕ} (hB : Squarefree B) {ℓ : ℝ}
    (hsep : ∀ e ∈ B.divisors, ∀ f ∈ B.divisors, e ≠ f → ℓ ≤ |log e-log f|) :
    ((2 : ℝ)^B.primeFactors.card-1)*ℓ ≤ log B := by
  let D := B.divisors
  have hc : 0 < D.card := Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hB.ne_zero⟩
  let a := D.orderEmbOfFin rfl
  have hamem (i : Fin D.card) : a i ∈ B.divisors := D.orderEmbOfFin_mem rfl i
  have hchain : ∀ i : ℕ, ∀ hi : i < D.card, (i : ℝ)*ℓ ≤ log (a ⟨i,hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; simpa only [Nat.cast_zero,zero_mul] using log_natCast_nonneg (a ⟨0,hi⟩)
    | succ i ih =>
      intro hi
      have hip : i < D.card := by omega
      have hab : a ⟨i,hip⟩ < a ⟨i+1,hi⟩ := a.strictMono (by simp)
      have hpos : (0 : ℝ) < a ⟨i,hip⟩ := by
        exact_mod_cast Nat.pos_of_mem_divisors (hamem ⟨i,hip⟩)
      have hm : log (a ⟨i,hip⟩ : ℕ) ≤ log (a ⟨i+1,hi⟩ : ℕ) :=
        log_le_log hpos (by exact_mod_cast hab.le)
      have hg := hsep _ (hamem ⟨i+1,hi⟩) _ (hamem ⟨i,hip⟩) hab.ne'
      rw [abs_of_nonneg (sub_nonneg.mpr hm)] at hg
      have hp := ih hip
      push_cast
      linarith only [hg,hp]
  have hlast : D.card-1 < D.card := by omega
  have ht := hchain (D.card-1) hlast
  have haB : a ⟨D.card-1,hlast⟩ ≤ B := Nat.le_of_dvd
    (Nat.pos_of_ne_zero hB.ne_zero) (Nat.dvd_of_mem_divisors (hamem _))
  have hlog : log (a ⟨D.card-1,hlast⟩ : ℕ) ≤ log B := log_le_log
    (by exact_mod_cast Nat.pos_of_mem_divisors (hamem ⟨D.card-1,hlast⟩))
    (by exact_mod_cast haB)
  have hcard : ((D.card-1 : ℕ) : ℝ)= (2 : ℝ)^B.primeFactors.card-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ D.card),Nat.cast_one]
    dsimp only [D]
    rw [ZetaRieszSmoothHead.card_divisors_of_squarefree hB,Nat.cast_pow,Nat.cast_ofNat]
  rw [hcard] at ht
  exact ht.trans hlog

theorem divisor_log_gap_le {B : ℕ} (hB : Squarefree B) (hc : 0 < B.primeFactors.card)
    {ℓ : ℝ}
    (hsep : ∀ e ∈ B.divisors, ∀ f ∈ B.divisors, e ≠ f → ℓ ≤ |log e-log f|) :
    ℓ ≤ log B/((2 : ℝ)^B.primeFactors.card-1) := by
  have hp : 1 < (2 : ℝ)^B.primeFactors.card := one_lt_pow₀ (by norm_num) (by omega)
  apply (le_div_iff₀ (by linarith : 0 < (2 : ℝ)^B.primeFactors.card-1)).mpr
  simpa only [mul_comm] using divisor_log_gap_packing hB hsep

/-- Both signed tents are assembled before the packing inequality.
All low-count parity ranks and the common complex weight remain literal. -/
theorem separated_two_hinge_packing_floor {B : ℕ} (hB : Squarefree B)
    (hc : 0 < B.primeFactors.card) (σ : ℕ → ℤ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (D₁ D₀ : ℝ) (w : ℂ)
    (hσ : ∀ e ∈ B.divisors, |(σ e : ℝ)| ≤ 1)
    (hsep : ∀ e ∈ B.divisors, ∀ f ∈ B.divisors, e ≠ f → a+b ≤ |log e-log f|) :
    -|w.re| *(log B/((2 : ℝ)^B.primeFactors.card-1)) ≤
      (∑ e ∈ B.divisors,w*(σ e : ℂ)*
        ((ZetaSquarefreeRieszWindows.primePairTent a b (D₁-log e)-
          ZetaSquarefreeRieszWindows.primePairTent a b (D₀-log e) : ℝ) : ℂ)).re := by
  have hpack := divisor_log_gap_le hB hc hsep
  have hmin : 2*min a b ≤ log B/((2 : ℝ)^B.primeFactors.card-1) :=
    (by linarith [min_le_left a b,min_le_right a b] : 2*min a b ≤ a+b).trans hpack
  have hw := mul_le_mul_of_nonneg_left hmin (abs_nonneg w.re)
  have h := separated_two_hinge_floor B.divisors σ ha hb D₁ D₀ w hσ hsep
  linarith only [h,hw]

/-- The packing debit is at most 2^-m times four logarithms, whenever
there are at least m background primes. -/
theorem packing_cost_le {B m : ℕ} (hm : 1 ≤ m) (hcount : m ≤ B.primeFactors.card) :
    log B/((2 : ℝ)^B.primeFactors.card-1) ≤ 2*log B/(2 : ℝ)^m := by
  have hp : (2 : ℝ)^m ≤ (2 : ℝ)^B.primeFactors.card :=
    pow_le_pow_right₀ (by norm_num) hcount
  have hp2 : (2 : ℝ) ≤ (2 : ℝ)^m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hden : (2 : ℝ)^m/2 ≤ (2 : ℝ)^B.primeFactors.card-1 := by linarith
  have hsmall : 0 < (2 : ℝ)^m/2 := by positivity
  calc
    _ ≤ log B/((2 : ℝ)^m/2) := div_le_div_of_nonneg_left (log_natCast_nonneg B) hsmall hden
    _ = _ := by ring

/-- For every separated background with at least53 primes, the entire
joined two-hinge cost is below 1/10^15 of its weighted background log.
This is a coefficient saving, not a bound for the population log mass. -/
theorem packing_cost_le_one_quadrillion {B : ℕ} (hc : 53 ≤ B.primeFactors.card) :
    log B/((2 : ℝ)^B.primeFactors.card-1) ≤ log B/1000000000000000 := by
  have h := packing_cost_le (by norm_num : 1 ≤ (53 : ℕ)) hc
  have h2 : 2/(2 : ℝ)^53 ≤ 1/1000000000000000 := by norm_num
  have hh := mul_le_mul_of_nonneg_right h2 (log_natCast_nonneg B)
  calc
    _ ≤ 2*log B/(2 : ℝ)^53 := h
    _ ≤ _ := by nlinarith only [hh]

/-- Deleting the unique owner and its canonical least-prime pair removes
exactly three primes. This derives the packing rank from the original
label, rather than assuming a large background independently. -/
theorem canonical_background_count {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    n.primeFactors.card=
      ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).primeFactors.card+3 := by
  have howner := ZetaRieszClippedOwnerPeriodFloor.canonical_owner_data hs
    (ZetaRieszJointPrimeEnergy.core_count hn)
  have hb := canonical_block_data hn hs
  let a := n/largestPrime n
  let R := leastPairBlock a
  have hRsf : Squarefree R := howner.2.2.1.squarefree_of_dvd hb.1
  have hBsf : Squarefree (a/R) :=
    howner.2.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hb.1)
  have he := Nat.mul_div_cancel' hb.1
  change R*(a/R)=a at he
  have hcard : a.primeFactors.card=R.primeFactors.card+(a/R).primeFactors.card := by
    conv_lhs => rw [←he,Nat.primeFactors_mul hRsf.ne_zero hBsf.ne_zero,
      Finset.card_union_of_disjoint hb.2.2.disjoint_primeFactors]
  have hpair : R.primeFactors.card=2 := hb.2.1
  have hoc : n.primeFactors.card=a.primeFactors.card+1 := howner.2.2.2.1
  change n.primeFactors.card=(a/R).primeFactors.card+3
  omega

theorem canonical_background_count_ge_fiftyThree {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (hc : 56 ≤ n.primeFactors.card) :
    53 ≤ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).primeFactors.card := by
  have he := canonical_background_count hn hs
  omega

/-- Apply packing to the exact retained original divisor response.
No ownership, allocation, radial, prime-count or phase mask is relaxed. -/
theorem retained_separated_packing_floor {u : ℝ} {N K n r s : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s)
    (hc : 0 < ((n/largestPrime n)/(r*s)).primeFactors.card) (w : ℂ)
    (hsep : ∀ e ∈ ((n/largestPrime n)/(r*s)).divisors,
      ∀ f ∈ ((n/largestPrime n)/(r*s)).divisors,e ≠ f → log r+log s ≤ |log e-log f|) :
    -|w.re| *(log ((n/largestPrime n)/(r*s) : ℕ)/
      ((2 : ℝ)^((n/largestPrime n)/(r*s)).primeFactors.card-1)) ≤
      (∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w*(μ db.2 : ℂ)*(pairHinge
          (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  have hdata := core_data hn hsf
  have hB : Squarefree ((n/largestPrime n)/(r*s)) :=
    hdata.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd
      (hcanonical ▸ (canonical_block_data hn hsf).1))
  have hpack := divisor_log_gap_le hB hc hsep
  have hmin : 2*min (log r) (log s) ≤ log ((n/largestPrime n)/(r*s) : ℕ)/
      ((2 : ℝ)^((n/largestPrime n)/(r*s)).primeFactors.card-1) := by
    linarith only [hpack,min_le_left (log r) (log s),min_le_right (log r) (log s)]
  have hw := mul_le_mul_of_nonneg_left hmin (abs_nonneg w.re)
  have h := retained_separated_floor hn hsf hr hs hrs hcanonical w hsep
  linarith only [h,hw]

/-- The total ACTUAL weighted separated cost gets the count-dependent
packing saving, over all labels/counts/radial periods at once. The signed
divisor response is retained; the final weighted log population is open. -/
theorem global_retained_separated_packing_floor (u y : ℝ) (N K : ℕ)
    (S : Finset ℕ) (hS : S ⊆ coreBand u N K) (hSF : ∀ n ∈ S,Squarefree n)
    (r s : ℕ → ℕ) (hprime : ∀ n ∈ S,(r n).Prime ∧ (s n).Prime ∧ r n ≠ s n)
    (hcanonical : ∀ n ∈ S,leastPairBlock (n/largestPrime n)=r n*s n)
    (hc : ∀ n ∈ S,0 < ((n/largestPrime n)/(r n*s n)).primeFactors.card)
    (hsep : ∀ n ∈ S,∀ e ∈ ((n/largestPrime n)/(r n*s n)).divisors,
      ∀ f ∈ ((n/largestPrime n)/(r n*s n)).divisors,
        e ≠ f → log (r n)+log (s n) ≤ |log e-log f|) :
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n);
    -(∑ n ∈ S,|(w n).re| *(log ((n/largestPrime n)/(r n*s n) : ℕ)/
      ((2 : ℝ)^((n/largestPrime n)/(r n*s n)).primeFactors.card-1))) ≤
      (∑ n ∈ S,∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w n*(μ db.2 : ℂ)*(pairHinge
          (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  dsimp only
  have hh := Finset.sum_le_sum (fun n hn => retained_separated_packing_floor (hS hn) (hSF n hn)
    (hprime n hn).1 (hprime n hn).2.1 (hprime n hn).2.2 (hcanonical n hn) (hc n hn)
    (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)) (hsep n hn))
  simpa only [neg_mul,Finset.sum_neg_distrib,Complex.re_sum] using hh

/-- The complete separated cost over the current count56+ population is
at most10^-15 times its ACTUAL weighted background logarithm. Every
original weight remains in that population sum; it is not replaced by a
source-scale numerical constant. -/
theorem global_current_separated_floor (u y : ℝ) (N K : ℕ)
    (S : Finset ℕ) (hS : S ⊆ coreBand u N K)
    (hSF : ∀ n ∈ S,Squarefree n) (hcount : ∀ n ∈ S,56 ≤ n.primeFactors.card)
    (hsep : ∀ n ∈ S,
      let a := n/largestPrime n
      let R := leastPairBlock a
      ∀ e ∈ (a/R).divisors,∀ f ∈ (a/R).divisors,e ≠ f → log R ≤ |log e-log f|) :
    let B := fun n => (n/largestPrime n)/leastPairBlock (n/largestPrime n)
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n);
    -(∑ n ∈ S,|(w n).re| * (log (B n)/1000000000000000)) ≤
      (∑ n ∈ S,∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w n*(μ db.2 : ℂ)*(pairHinge
          (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  dsimp only
  rw [Complex.re_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n hn
  let a := n/largestPrime n
  let R := leastPairBlock a
  let B := a/R
  have hd := core_data (hS hn) (hSF n hn)
  have haSF : Squarefree a := hd.2.1
  have haC : 2 ≤ a.primeFactors.card := hd.2.2
  have hc := canonical_background_count_ge_fiftyThree (hS hn) (hSF n hn) (hcount n hn)
  have hp := packing_cost_le_one_quadrillion hc
  change 53 ≤ B.primeFactors.card at hc
  let r := a.minFac
  let s := (a/r).minFac
  have ha1 : a ≠ 1 := by intro h; simp [h] at haC
  have hr : r.Prime := Nat.minFac_prime ha1
  have he : r*(a/r)=a := Nat.mul_div_cancel' (Nat.minFac_dvd a)
  have hquot : a/r ≠ 1 := by
    intro h
    have har : a=r := by rw [h,mul_one] at he; exact he.symm
    have hc' := hd.2.2
    change 2 ≤ a.primeFactors.card at hc'
    rw [har,hr.primeFactors,Finset.card_singleton] at hc'
    omega
  have hs : s.Prime := Nat.minFac_prime hquot
  have hrs : r ≠ s := by
    have hcop := Nat.coprime_of_squarefree_mul (he.symm ▸ haSF)
    intro heq
    have hsd : s ∣ a/r := Nat.minFac_dvd _
    rw [←heq] at hsd
    exact (hr.coprime_iff_not_dvd.mp hcop) hsd
  have hRs : leastPairBlock a=r*s := rfl
  have hlogs : log R=log r+log s := by
    change log (leastPairBlock a)=log r+log s
    rw [hRs,Nat.cast_mul,log_mul (by exact_mod_cast hr.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hg := retained_separated_packing_floor (hS hn) (hSF n hn) hr hs hrs hRs
    (by simpa only [←hRs] using (by omega : 0 < B.primeFactors.card))
    (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n))
    (by simpa only [←hRs,←hlogs] using hsep n hn)
  have hmul := mul_le_mul_of_nonneg_left hp
    (abs_nonneg (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)).re)
  rw [←hRs] at hg
  have hneg := neg_le_neg hmul
  simp only [neg_mul] at hg
  exact hneg.trans hg

/-- The packing saving applies to the ORIGINAL residual-coefficient
packet at source scale, paying the already proved SINGLE nonowner error.
It is a literal signed inequality, not a completed profile or a bound on
an auxiliary unweighted incidence count. The total logarithmic mass on
the left remains an explicit arithmetic quantity. -/
theorem source_scaled_current_separated_floor {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N K : ℕ)
    (S : Finset ℕ) (hS : S ⊆ coreBand u N K)
    (hSF : ∀ n ∈ S,Squarefree n) (hcount : ∀ n ∈ S,56 ≤ n.primeFactors.card)
    (hsep : ∀ n ∈ S,
      let a := n/largestPrime n
      let R := leastPairBlock a
      ∀ e ∈ (a/R).divisors,∀ f ∈ (a/R).divisors,e ≠ f → log R ≤ |log e-log f|) :
    let B := fun n => (n/largestPrime n)/leastPairBlock (n/largestPrime n)
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n);
    -u^(N+1)*(∑ n ∈ S,|(w n).re| * (log (B n)/1000000000000000))-
        ZetaRieszDenseCountCoverFloor.ownerPaymentError N ≤
      ((u : ℂ)^(N+1)*∑ n ∈ S,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  dsimp only
  have hfloor := global_current_separated_floor u y N K S hS hSF hcount hsep
  dsimp only at hfloor
  have heq := congrArg Complex.re (Finset.sum_congr rfl (fun n hn =>
    ZetaRieszCrossingOrbitCancellation.owner_atom_eq_affine_sdiff (hS hn) (hSF n hn) y))
  rw [←heq] at hfloor
  have hs := mul_le_mul_of_nonneg_left hfloor (pow_nonneg hu (N+1))
  have ho := (ZetaRieszNonownerAllocation.signed_owner_bounds
    (fun _ => ZetaRieszAnnulusJoint.intermediatePrimes u N) S (fun _ => 1)
    (SquarefreeVaughanLogSource.length_pos u N) N
    (hS.trans (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))
    (by intros; simp) y hu (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)).1
  simp only [one_mul] at ho
  rw [←Complex.ofReal_pow,Complex.re_ofReal_mul] at ho
  change u^(N+1)*(∑ n ∈ S,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      ZetaRieszDenseCountCoverFloor.ownerPaymentError N ≤ _ at ho
  rw [←Complex.ofReal_pow]
  nlinarith only [hs,ho]

/-- On the remaining logarithmic count range the divisor-packing factor
is at most polynomial in the total order. This is an exponent audit, not
an upper or lower bound for the ACTUAL weighted separated population. -/
theorem logarithmic_count_pow_le {N k : ℕ}
    (hk : (k : ℝ) ≤ 5*log ((N : ℝ)+1)+2) :
    (2 : ℝ)^k ≤ 4*((N : ℝ)+1)^4 := by
  have hx : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have hl : 0 ≤ log ((N : ℝ)+1) :=
    log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hl2u : log (2 : ℝ) ≤ 4/5 := by linarith [log_two_lt_d9]
  have hprod := mul_le_mul_of_nonneg_right hk hl2
  have hsmall := mul_le_mul_of_nonneg_left hl2u
    (show 0 ≤ 5*log ((N : ℝ)+1) by positivity)
  have hlog : (k : ℝ)*log 2 ≤ 4*log ((N : ℝ)+1)+2*log 2 := by
    nlinarith only [hprod,hsmall]
  have hleft : exp ((k : ℝ)*log 2)=(2 : ℝ)^k := by
    rw [← log_pow,exp_log (by positivity : (0 : ℝ) < 2^k)]
  have hfour : exp (4*log ((N : ℝ)+1))=((N : ℝ)+1)^4 := by
    rw [show (4 : ℝ)=(4 : ℕ) by norm_num,← log_pow,exp_log (pow_pos hx 4)]
  have htwo : exp (2*log 2)=(4 : ℝ) := by
    rw [show (2 : ℝ)=(2 : ℕ) by norm_num,← log_pow,exp_log (by positivity)]
    norm_num
  calc
    _ = exp ((k : ℝ)*log 2) := hleft.symm
    _ ≤ exp (4*log ((N : ℝ)+1)+2*log 2) := exp_le_exp.mpr hlog
    _ = _ := by rw [exp_add,hfour,htwo]; ring

/-- Even the strongest packing price on this logarithmic rank range is
bounded below by an inverse polynomial. This does NOT assert a lower
bound for the signed carrier or for its weighted population mass. -/
theorem packing_factor_lower_of_logarithmic_count {N k : ℕ} (hk0 : 1 ≤ k)
    (hk : (k : ℝ) ≤ 5*log ((N : ℝ)+1)+2) :
    1/(4*((N : ℝ)+1)^4) ≤ 1/((2 : ℝ)^k-1) := by
  have hp : 1 < (2 : ℝ)^k := one_lt_pow₀ (by norm_num) (by omega)
  exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 < (2 : ℝ)^k-1)
    (by linarith [logarithmic_count_pow_le hk])

/-- The background of an original count56+ label has exactly the rank
used in the audit. No count, owner, phase or allocation is replaced. -/
theorem canonical_packing_factor_lower {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hc : 56 ≤ n.primeFactors.card)
    (hupper : (n.primeFactors.card : ℝ) < 5*log ((N : ℝ)+1)+2) :
    1/(4*((N : ℝ)+1)^4) ≤
      1/((2 : ℝ)^((n/largestPrime n)/leastPairBlock (n/largestPrime n)).primeFactors.card-1) := by
  have hbg := canonical_background_count_ge_fiftyThree hn hs hc
  have he := canonical_background_count hn hs
  have hlo : ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).primeFactors.card ≤
      n.primeFactors.card := by omega
  have hlr : (((n/largestPrime n)/leastPairBlock (n/largestPrime n)).primeFactors.card : ℝ) ≤
      n.primeFactors.card := by exact_mod_cast hlo
  exact packing_factor_lower_of_logarithmic_count (by omega) (hlr.trans hupper.le)

/-- Pricing the packing factor against the common positive period
envelope cannot pay it at source scale, even with a MOVING logarithmic
rank. The actual weighted separated population is NOT that envelope.
A signed population bound is still required. -/
theorem logarithmic_packing_periodDebit_tendsto {u y : ℝ}
    (hu : 1/2 < u) (hy : 54 ≤ y) (rank : ℕ → ℕ)
    (hrank : ∀ᶠ N : ℕ in atTop, 1 ≤ rank N ∧
      (rank N : ℝ) ≤ 5*log ((N : ℝ)+1)+2) :
    Tendsto (fun N : ℕ => u^(N+1)*ZetaRieszHighSignCoverFloor.periodUnits N y/
      ((2 : ℝ)^rank N-1)) atTop atTop := by
  have ht := ZetaRieszGlobalDebitAudit.polynomial_periodDebit_tendsto hu hy
    (by norm_num : (0 : ℝ) < 1/4) 4
  apply Filter.tendsto_atTop_mono' _ ?_ ht
  filter_upwards [hrank,eventually_ge_atTop (4000 : ℕ)] with N hr hN
  have hnon : 0 ≤ u^(N+1)*ZetaRieszHighSignCoverFloor.periodUnits N y :=
    (by positivity : 0 ≤ (u*exp (-1)/3)*((2*u)^N/((N : ℝ)+1))).trans
      (ZetaRieszGlobalDebitAudit.source_periodUnits_lower hN hy (by linarith : 0 ≤ u))
  have hh := mul_le_mul_of_nonneg_left
    (packing_factor_lower_of_logarithmic_count hr.1 hr.2) hnon
  calc
    _ = u^(N+1)*ZetaRieszHighSignCoverFloor.periodUnits N y*
        (1/(4*((N : ℝ)+1)^4)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hh
    _ = _ := by ring

end RiemannGaussian.ZetaRieszSeparatedPackingFloor
