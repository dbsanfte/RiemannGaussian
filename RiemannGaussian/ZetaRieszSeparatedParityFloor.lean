/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDenseShellCost

/-!
# A count-free signed floor for separated divisor-translation windows

For dense populations spread over many prime-log scales, the canonical
two-prime tents need not overlap. At most one background divisor can pay
each original hinge. The entire signed sum therefore costs two tent
heights, independently of the cofactor count, instead of one height per
background divisor. Both exact zero deletions and every original complex
weight remain. A population price for all overlapping configurations is
still open.
-/

noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius symmDiff
namespace RiemannGaussian.ZetaRieszSeparatedParityFloor
open ZetaSquarefreeRieszWindows ZetaRieszCrossCountTransport
open ZetaRieszShortDivisorOrbits ZetaRieszShortDivisorCancellation
open ZetaRieszSmallCofactorCancellation ZetaRieszPrimeEndpoint
open ZetaRieszParityPacket ZetaRieszFixedCountPeriod
open ZetaRieszSignedConvolution

set_option maxHeartbeats 800000

/-- Separated translates have at most one nonzero supported response.
All signed ranks are summed first; their number is absent from the bound. -/
theorem separated_supported_signed_sum (E : Finset ℕ) (σ : ℕ→ℤ)
    (F : ℝ→ℝ) (D ℓ C : ℝ)
    (hσ : ∀ e∈E,|(σ e : ℝ)|≤1)
    (hF : ∀ x,F x≠0→0<x ∧ x<ℓ) (hC : ∀ x,|F x|≤C)
    (hsep : ∀ e∈E,∀ f∈E,e≠f→ℓ≤|log e-log f|) :
    |∑ e∈E,(σ e : ℝ)*F (D-log e)|≤C := by
  have hC0 : 0≤C := (abs_nonneg (F 0)).trans (hC 0)
  have honly e (he : e∈E) (ha : F (D-log e)≠0) f (hf : f∈E) (hef : f≠e) :
      F (D-log f)=0 := by
    by_contra h
    have h₁ := hF _ ha
    have h₂ := hF _ h
    have hd := hsep f hf e he hef
    have hh : |log f-log e|<ℓ := by
      apply abs_lt.mpr
      constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]
    linarith only [hd,hh]
  by_cases hex : ∃ e∈E,F (D-log e)≠0
  · obtain ⟨e,he,ha⟩ := hex
    rw [Finset.sum_eq_single e]
    · rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hσ e he) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hC (D-log e))
    · intro f hf hef
      rw [honly e he ha f hf hef,mul_zero]
    · exact fun h => False.elim (h he)
  · have hz : ∑ e∈E,(σ e : ℝ)*F (D-log e)=0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hh : F (D-log e)=0 := by
        by_contra h
        exact hex ⟨e,he,h⟩
      rw [hh,mul_zero]
    rw [hz,abs_zero]
    exact hC0

/-- An explicit prime-log certificate for separated divisor translations.
The largest prime at which two squarefree divisors differ dominates ALL
smaller differences. No divisor-count bound or phase approximation enters. -/
theorem superincreasing_divisor_log_gap {B : ℕ} (hB : Squarefree B) (ℓ : ℝ)
    (hchain : ∀ p∈B.primeFactors,
      ℓ+∑ q∈B.primeFactors.filter (fun q => q<p),log q≤log p)
    {d e : ℕ} (hd : d∈B.divisors) (he : e∈B.divisors) (hde : d≠e) :
    ℓ≤|log d-log e| := by
  have hds := hB.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hes := hB.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  have hdB := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hB.ne_zero
  have heB := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors he) hB.ne_zero
  have hneq : d.primeFactors≠e.primeFactors := by
    intro h
    apply hde
    rw [← Nat.prod_primeFactors_of_squarefree hds,
      ← Nat.prod_primeFactors_of_squarefree hes,h]
  let T := d.primeFactors ∆ e.primeFactors
  have hT : T.Nonempty := Finset.symmDiff_nonempty.mpr hneq
  let p := T.max' hT
  have hp : p∈T := Finset.max'_mem _ _
  have hmax q (hq : q∈T) : q≤p := Finset.le_max' _ _ hq
  have hside (A D : Finset ℕ) (hA : A⊆B.primeFactors) (hD : D⊆B.primeFactors)
      (hpA : p∈A\D) (hsmaller : ∀ q∈D\A,q<p) :
      ℓ≤(∑ q∈A,log q)-(∑ q∈D,log q) := by
    have hsub : D\A⊆B.primeFactors.filter (fun q => q<p) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨hD (Finset.mem_sdiff.mp hq).1,hsmaller q hq⟩
    have hright := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun q _ _ => log_natCast_nonneg q)
    have hleft := Finset.single_le_sum
      (fun q (_hq : q∈A\D) => log_natCast_nonneg q) hpA
    have hc := hchain p (hA (Finset.mem_sdiff.mp hpA).1)
    have hi₁ := Finset.sum_inter_add_sum_sdiff A D (fun q : ℕ => log q)
    have hi₀ := Finset.sum_inter_add_sum_sdiff D A (fun q : ℕ => log q)
    rw [Finset.inter_comm D A] at hi₀
    linarith only [hright,hleft,hc,hi₁,hi₀]
  rcases Finset.mem_symmDiff.mp hp with hp | hp
  · have hh := hside d.primeFactors e.primeFactors hdB heB
      (Finset.mem_sdiff.mpr hp) (by
        intro q hq
        have hqT : q∈T := Finset.mem_symmDiff.mpr (Or.inr (Finset.mem_sdiff.mp hq))
        exact lt_of_le_of_ne (hmax q hqT) (by
          intro hqp
          exact (Finset.mem_sdiff.mp hq).2 (hqp ▸ hp.1)))
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hds,
      ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hes] at hh
    exact hh.trans (le_abs_self _)
  · have hh := hside e.primeFactors d.primeFactors heB hdB
      (Finset.mem_sdiff.mpr hp) (by
        intro q hq
        have hqT : q∈T := Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hq))
        exact lt_of_le_of_ne (hmax q hqT) (by
          intro hqp
          exact (Finset.mem_sdiff.mp hq).2 (hqp ▸ hp.1)))
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hes,
      ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hds] at hh
    exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)

/-- The joined two-hinge real contribution retains the entire common
complex weight. It costs TWO heights at every count, without an absolute
Fourier or complete-prime phase replacement. -/
theorem separated_two_hinge_floor (E : Finset ℕ) (σ : ℕ→ℤ)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (D₁ D₀ : ℝ) (w : ℂ)
    (hσ : ∀ e∈E,|(σ e : ℝ)|≤1)
    (hsep : ∀ e∈E,∀ f∈E,e≠f→a+b≤|log e-log f|) :
    -2*|w.re| * min a b≤
      (∑ e∈E,w*(σ e : ℂ)*
        ((primePairTent a b (D₁-log e)-primePairTent a b (D₀-log e) : ℝ) : ℂ)).re := by
  have hsupport x (hx : primePairTent a b x≠0) : 0<x ∧ x<a+b := by
    constructor
    · by_contra h
      exact hx (primePairTent_eq_zero_of_outside ha hb (Or.inl (le_of_not_gt h)))
    · by_contra h
      exact hx (primePairTent_eq_zero_of_outside ha hb (Or.inr (le_of_not_gt h)))
  have hbound x : |primePairTent a b x|≤ min a b := by
    rw [abs_of_nonneg (primePairTent_bounds ha hb x).1]
    exact (primePairTent_bounds ha hb x).2
  have h₁ := separated_supported_signed_sum E σ (primePairTent a b) D₁ (a+b) (min a b)
    hσ hsupport hbound hsep
  have h₀ := separated_supported_signed_sum E σ (primePairTent a b) D₀ (a+b) (min a b)
    hσ hsupport hbound hsep
  let B := ∑ e∈E,(σ e : ℝ)*(primePairTent a b (D₁-log e)-primePairTent a b (D₀-log e))
  have hB : |B|≤2*min a b := by
    dsimp [B]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact (abs_sub _ _).trans (by linarith only [h₁,h₀])
  have heq : (∑ e∈E,w*(σ e : ℂ)*
      ((primePairTent a b (D₁-log e)-primePairTent a b (D₀-log e) : ℝ) : ℂ)).re=w.re*B := by
    rw [Complex.re_sum]
    dsimp [B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp [Complex.mul_re]
    ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hB (abs_nonneg w.re)
  rw [← abs_mul] at hh
  have hl := (neg_le_neg hh).trans (neg_abs_le (w.re*B))
  convert hl using 1 <;> first | rfl | ring

private theorem two_prime_riesz {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r≠s) (D : ℝ) :
    VaughanLogAverage.riesz D (r*s)=primePairTent (log r) (log s) D := by
  simpa only [mul_one,Nat.divisors_one,Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,Nat.cast_one,log_one,sub_zero,one_mul] using
      riesz_two_primes_eq_tent D hr hs hrs hr.not_dvd_one hs.not_dvd_one

/-- A floor for the ENTIRE original retained divisor sum of one label.
The two previous exact-zero deletions commute with this cancellation.
The common weight can be the original phase/factorial/owner allocation. -/
theorem retained_separated_floor {u : ℝ} {N K n r s : ℕ}
    (hn : n∈coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hrs : r≠s)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s) (w : ℂ)
    (hsep : ∀ e∈((n/largestPrime n)/(r*s)).divisors,
      ∀ f∈((n/largestPrime n)/(r*s)).divisors,e≠f→log r+log s≤|log e-log f|) :
    -2*|w.re| * min (log r) (log s)≤
      (∑ db∈(n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  have hdata := core_data hn hsf
  have hRa : r*s ∣ n/largestPrime n := hcanonical ▸ (canonical_block_data hn hsf).1
  have he := retained_group_eq_sum hn hsf hRa (hcanonical ▸ dvd_refl _)
    (((n/largestPrime n)/(r*s)).divisors) (Finset.Subset.refl _) w
  dsimp only at he
  rw [← divisorsAntidiagonal_eq_orbits (Nat.pos_of_ne_zero hdata.2.1.ne_zero) hRa,
    Finset.inter_eq_left.mpr (Finset.sdiff_subset)] at he
  rw [he]
  have hh := separated_two_hinge_floor (((n/largestPrime n)/(r*s)).divisors)
    (fun e => μ ((n/largestPrime n)/e)) (log_natCast_nonneg r) (log_natCast_nonneg s)
    (log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N)
    (log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N) w
    (by intro e _; exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hsep
  simpa only [basedResponse,two_prime_riesz hr hs hrs] using hh

/-- Apply the explicit lacunary prime-log certificate to the literal
retained floor. Arbitrarily many background factors are permitted. -/
theorem retained_lacunary_floor {u : ℝ} {N K n r s : ℕ}
    (hn : n∈coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hrs : r≠s)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s) (w : ℂ)
    (hchain : ∀ p∈((n/largestPrime n)/(r*s)).primeFactors,
      log r+log s+∑ q∈((n/largestPrime n)/(r*s)).primeFactors.filter (fun q => q<p),
        log q≤log p) :
    -2*|w.re| * min (log r) (log s)≤
      (∑ db∈(n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  have hdata := core_data hn hsf
  have hB : Squarefree ((n/largestPrime n)/(r*s)) :=
    hdata.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd
      (hcanonical ▸ (canonical_block_data hn hsf).1))
  exact retained_separated_floor hn hsf hr hs hrs hcanonical w
    (fun _ he _ hf hef => superincreasing_divisor_log_gap hB (log r+log s) hchain he hf hef)

/-- Apply the count-free separated-window price across ALL selected
original labels, counts and radial periods. Its remaining population
cost is explicit; this theorem does not assert that cost is source-small. -/
theorem global_retained_separated_floor (u y : ℝ) (N K : ℕ)
    (S : Finset ℕ) (hS : S⊆coreBand u N K) (hSF : ∀ n∈S,Squarefree n)
    (r s : ℕ→ℕ) (hprime : ∀ n∈S,(r n).Prime ∧ (s n).Prime ∧ r n≠s n)
    (hcanonical : ∀ n∈S,leastPairBlock (n/largestPrime n)=r n*s n)
    (hsep : ∀ n∈S,∀ e∈((n/largestPrime n)/(r n*s n)).divisors,
      ∀ f∈((n/largestPrime n)/(r n*s n)).divisors,e≠f→log (r n)+log (s n)≤|log e-log f|) :
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n);
    -(∑ n∈S,2*|(w n).re| * min (log (r n)) (log (s n)))≤
      (∑ n∈S,∑ db∈(n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w n*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  dsimp only
  have hh := Finset.sum_le_sum (fun n hn => retained_separated_floor (hS hn) (hSF n hn)
    (hprime n hn).1 (hprime n hn).2.1 (hprime n hn).2.2 (hcanonical n hn)
    (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)) (hsep n hn))
  simpa only [neg_mul,Finset.sum_neg_distrib,Complex.re_sum] using hh

/-- A global literal signed floor under prime-log inequalities, with
no background count ceiling. The explicit remaining population price
must still be funded; this is not the independent whole-carrier floor. -/
theorem global_retained_lacunary_floor (u y : ℝ) (N K : ℕ)
    (S : Finset ℕ) (hS : S⊆coreBand u N K) (hSF : ∀ n∈S,Squarefree n)
    (r s : ℕ→ℕ) (hprime : ∀ n∈S,(r n).Prime ∧ (s n).Prime ∧ r n≠s n)
    (hcanonical : ∀ n∈S,leastPairBlock (n/largestPrime n)=r n*s n)
    (hchain : ∀ n∈S,∀ p∈((n/largestPrime n)/(r n*s n)).primeFactors,
      log (r n)+log (s n)+
        ∑ q∈((n/largestPrime n)/(r n*s n)).primeFactors.filter (fun q => q<p),
          log q≤log p) :
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n);
    -(∑ n∈S,2*|(w n).re| * min (log (r n)) (log (s n)))≤
      (∑ n∈S,∑ db∈(n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
        w n*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re := by
  apply global_retained_separated_floor u y N K S hS hSF r s hprime hcanonical
  intro n hn e he f hf hef
  have hdata := core_data (hS hn) (hSF n hn)
  have hB : Squarefree ((n/largestPrime n)/(r n*s n)) :=
    hdata.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd
      (hcanonical n hn ▸ (canonical_block_data (hS hn) (hSF n hn)).1))
  exact superincreasing_divisor_log_gap hB (log (r n)+log (s n)) (hchain n hn) he hf hef

end RiemannGaussian.ZetaRieszSeparatedParityFloor
