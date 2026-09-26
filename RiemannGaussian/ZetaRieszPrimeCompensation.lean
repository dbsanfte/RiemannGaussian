/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCutoffProfile

/-!
# Quantitative opposing coefficients from two small prime factors

After retaining two small primes, pair separation among the remaining
primes removes every composite divisor exactly. The response is a negative
sum of prime-pair tents, at every prime count. A literal prime window gives
a lower bound for its negative magnitude. No phase or population estimate
is inferred from these coefficient bounds.
-/

namespace RiemannGaussian.ZetaRieszPrimeCompensation
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows

/-- Pair separation suffices to exclude every composite divisor below
the cutoff; individual primes need not exceed half the cutoff. -/
theorem composite_divisor_log_ge_of_pairs {b d : ℕ} (hb : Squarefree b)
    (hd : d ∈ b.divisors) (hd1 : d ≠ 1) (hdp : ¬d.Prime) {D : ℝ}
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) : D ≤ Real.log d := by
  have hs := hb.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hk : 1 < d.primeFactors.card := by
    by_contra h
    have hc : d.primeFactors.card = 0 ∨ d.primeFactors.card = 1 := by omega
    rcases hc with hc | hc
    · apply hd1
      rw [← Nat.prod_primeFactors_of_squarefree hs, Finset.card_eq_zero.mp hc,
        Finset.prod_empty]
    · obtain ⟨p, he⟩ := Finset.card_eq_one.mp hc
      have heq : d = p := by
        rw [← Nat.prod_primeFactors_of_squarefree hs, he, Finset.prod_singleton]
      exact hdp (heq ▸ Nat.prime_of_mem_primeFactors (by rw [he]; simp))
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hk
  have hsub := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hb.ne_zero
  have hpqsub : ({p,q} : Finset ℕ) ⊆ d.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hpqsub
    (fun x _ _ => Real.log_natCast_nonneg x)
  rw [Finset.sum_pair hpq, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hsum
  exact (hpairs p (hsub hp) q (hsub hq) hpq).trans hsum

/-- Pair separation removes the composite divisors before estimation.
The unit tent and all opposing prime tents retain their exact weights.
This also includes the three/four-prime cases b=1 and b prime. -/
theorem riesz_eq_unit_sub_prime_tents {r a b : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hra : r ≠ a)
    (hrb : ¬r ∣ b) (hab : ¬a ∣ b) (hb : Squarefree b) {D : ℝ}
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) :
    VaughanLogAverage.riesz D (r*(a*b)) =
      primePairTent (Real.log r) (Real.log a) D-∑ p ∈ b.primeFactors,
        primePairTent (Real.log r) (Real.log a) (D-Real.log p) := by
  rw [riesz_two_primes_eq_tent D hr ha hra hrb hab]
  let f := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)*
    primePairTent (Real.log r) (Real.log a) (D-Real.log d)
  have h1 : 1 ∉ b.primeFactors := fun h => Nat.not_prime_one (Nat.prime_of_mem_primeFactors h)
  have hsub : insert 1 b.primeFactors ⊆ b.divisors := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, hb.ne_zero⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hd, hb.ne_zero⟩
  have he : (∑ d ∈ insert 1 b.primeFactors, f d) = ∑ d ∈ b.divisors, f d := by
    apply Finset.sum_subset hsub
    intro d hd hout
    have hd1 : d ≠ 1 := fun h => hout (by simp [h])
    have hdp : ¬d.Prime := fun h => hout (Finset.mem_insert_of_mem
      (h.mem_primeFactors (Nat.dvd_of_mem_divisors hd) hb.ne_zero))
    have hlog := composite_divisor_log_ge_of_pairs hb hd hd1 hdp hpairs
    dsimp [f]
    rw [primePairTent_eq_zero_of_outside (Real.log_natCast_nonneg r)
      (Real.log_natCast_nonneg a) (Or.inl (by linarith)), mul_zero]
  change (∑ d ∈ b.divisors, f d) = _
  rw [← he, Finset.sum_insert h1]
  have hf1 : f 1 = primePairTent (Real.log r) (Real.log a) D := by
    simp only [f, ArithmeticFunction.moebius_apply_one, Int.cast_one,
      Nat.cast_one, Real.log_one, sub_zero, one_mul]
  rw [hf1, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  simp [f, ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]

/-- Once the unit tent is saturated, every surviving term has one common
negative sign, for arbitrarily many distinct prime factors in b. -/
theorem riesz_eq_neg_prime_tents {r a b : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hra : r ≠ a)
    (hrb : ¬r ∣ b) (hab : ¬a ∣ b) (hb : Squarefree b) {D : ℝ}
    (hsmall : Real.log r+Real.log a ≤ D)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) :
    VaughanLogAverage.riesz D (r*(a*b)) =
      -∑ p ∈ b.primeFactors,
        primePairTent (Real.log r) (Real.log a) (D-Real.log p) := by
  rw [riesz_eq_unit_sub_prime_tents hr ha hra hrb hab hb hpairs,
    primePairTent_eq_zero_of_outside (Real.log_natCast_nonneg r)
      (Real.log_natCast_nonneg a) (Or.inr hsmall), zero_sub]

/-- The exact response is nonpositive throughout the pair-separated
class. This statement keeps all prime counts and cutoff endpoints. -/
theorem riesz_nonpos {r a b : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hra : r ≠ a)
    (hrb : ¬r ∣ b) (hab : ¬a ∣ b) (hb : Squarefree b) {D : ℝ}
    (hsmall : Real.log r+Real.log a ≤ D)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) :
    VaughanLogAverage.riesz D (r*(a*b)) ≤ 0 := by
  rw [riesz_eq_neg_prime_tents hr ha hra hrb hab hb hsmall hpairs]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ =>
    (primePairTent_bounds (Real.log_natCast_nonneg r) (Real.log_natCast_nonneg a) _).1))

/-- The entire common-sign response costs one least-prime logarithm per
remaining prime, rather than one allowance per signed divisor. -/
theorem neg_riesz_le_prime_count {r a b : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hra : r ≠ a)
    (hrb : ¬r ∣ b) (hab : ¬a ∣ b) (hb : Squarefree b) {D : ℝ}
    (hsmall : Real.log r+Real.log a ≤ D)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) :
    -VaughanLogAverage.riesz D (r*(a*b)) ≤ b.primeFactors.card*Real.log r := by
  rw [riesz_eq_neg_prime_tents hr ha hra hrb hab hb hsmall hpairs, neg_neg]
  calc
    _ ≤ ∑ _p ∈ b.primeFactors, Real.log r := Finset.sum_le_sum (fun _ _ =>
      (primePairTent_bounds (Real.log_natCast_nonneg r) (Real.log_natCast_nonneg a) _).2.trans
        (min_le_left _ _))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Every prime in this literal logarithmic interval supplies a full
least-prime logarithm of opposing coefficient, not merely a sign. -/
def plateauPrimes (D : ℝ) (r a b : ℕ) : Finset ℕ :=
  b.primeFactors.filter (fun p => D-Real.log a ≤ Real.log p ∧ Real.log p ≤ D-Real.log r)

/-- The central part of the exact pair tent has its full least width. -/
theorem primePairTent_plateau {r a t : ℝ} (hr : 0 ≤ r)
    (hrt : r ≤ t) (hta : t ≤ a) : primePairTent r a t = r := by
  simp only [primePairTent, max_eq_right (by linarith : 0 ≤ t),
    max_eq_right (by linarith : 0 ≤ t-r),
    max_eq_left (by linarith : t-a ≤ 0),
    max_eq_left (by linarith : t-r-a ≤ 0)]
  ring

/-- A quantitative one-sided bound for the actual Riesz coefficient,
using the number of genuine primes in the full-overlap interval. -/
theorem riesz_le_neg_plateau_count {r a b : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hra : r ≠ a)
    (hrb : ¬r ∣ b) (hab : ¬a ∣ b) (hb : Squarefree b) {D : ℝ}
    (hsmall : Real.log r+Real.log a ≤ D)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) :
    VaughanLogAverage.riesz D (r*(a*b)) ≤
      -(plateauPrimes D r a b).card*Real.log r := by
  rw [riesz_eq_neg_prime_tents hr ha hra hrb hab hb hsmall hpairs]
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (show plateauPrimes D r a b ⊆ b.primeFactors from Finset.filter_subset _ _)
    (fun p _ _ => (primePairTent_bounds (Real.log_natCast_nonneg r)
      (Real.log_natCast_nonneg a) (D-Real.log p)).1)
  have he : (∑ p ∈ plateauPrimes D r a b,
      primePairTent (Real.log r) (Real.log a) (D-Real.log p)) =
      (plateauPrimes D r a b).card*Real.log r := by
    calc
      _ = ∑ _p ∈ plateauPrimes D r a b, Real.log r := by
        apply Finset.sum_congr rfl
        intro p hp
        have h := (Finset.mem_filter.mp hp).2
        exact primePairTent_plateau (Real.log_natCast_nonneg r) (by linarith) (by linarith)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [he] at hsub
  linarith

/-- Saturated largest-prime deletion carries the exact negative tent sum
into the original arithmetic coefficient. No prime, phase, or weight is
completed or replaced. -/
theorem coefficient_eq_neg_prime_tents {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ}
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hsmall : Real.log r+Real.log a ≤ L-Real.log P)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) :
    SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b))) =
      ((-(Real.log (P*(r*(a*b)) : ℕ)/L)*
        ∑ p ∈ b.primeFactors,
          primePairTent (Real.log r) (Real.log a) (L-Real.log P-Real.log p) : ℝ) : ℂ) := by
  have hc := hs.of_mul_right
  have hab := hc.of_mul_right
  have hPr : ¬P ∣ r*(a*b) :=
    hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hrab : ¬r ∣ a*b := hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hc)
  have hrb : ¬r ∣ b := fun h => hrab (dvd_mul_of_dvd_right h _)
  have ha_b : ¬a ∣ b := ha.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hab)
  have hra : r ≠ a := fun h => hrab (by rw [h]; exact dvd_mul_right _ _)
  have hab1 : a*b ≠ 1 := fun h => ha.ne_one (mul_eq_one.mp h).1
  have hc1 : r*(a*b) ≠ 1 := fun h => hr.ne_one (mul_eq_one.mp h).1
  have hcp : ¬(r*(a*b)).Prime := by
    rw [Nat.prime_mul_iff]
    simp [hr.ne_one, hab1]
  have hnp : ¬(P*(r*(a*b))).Prime := by
    rw [Nat.prime_mul_iff]
    simp [hP.ne_one, hc1]
  rw [ZetaRieszContinuumCascade.coefficient_saturated_prime hP hPr hc hc1 hcp
    ⟨hs,hnp⟩ hsat, ZetaRieszContinuumCascade.kernel_primeFactors hc,
    riesz_eq_neg_prime_tents hr ha hra hrb ha_b hab.of_mul_right hsmall hpairs]
  push_cast
  ring

/-- Each actual plateau prime supplies the full quantitative opposing
coefficient, on the same literal saturated label. This real coefficient
bound does not assert a sign for its complex prime-phase atom. -/
theorem coefficient_le_neg_plateau_count {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hsmall : Real.log r+Real.log a ≤ L-Real.log P)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) :
    (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))).re ≤
      -(Real.log (P*(r*(a*b)) : ℕ)/L)*
        ((plateauPrimes (L-Real.log P) r a b).card*Real.log r) := by
  rw [coefficient_eq_neg_prime_tents hP hr ha hs hsat hsmall hpairs, Complex.ofReal_re]
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr
    (div_nonneg (Real.log_natCast_nonneg _) hL.le))
  have hc := hs.of_mul_right
  have hab := hc.of_mul_right
  have hrab : ¬r ∣ a*b := hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hc)
  have hrb : ¬r ∣ b := fun h => hrab (dvd_mul_of_dvd_right h _)
  have ha_b : ¬a ∣ b := ha.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hab)
  have hra : r ≠ a := fun h => hrab (by rw [h]; exact dvd_mul_right _ _)
  have he := riesz_eq_neg_prime_tents hr ha hra hrb ha_b hab.of_mul_right hsmall hpairs
  have hb := riesz_le_neg_plateau_count hr ha hra hrb ha_b hab.of_mul_right hsmall hpairs
  rw [he] at hb
  linarith

/-- This magnitude estimate already concerns the original coefficient.
All height dependence remains in its unchanged complex kernel downstream. -/
theorem norm_coefficient_le_prime_count {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hsmall : Real.log r+Real.log a ≤ L-Real.log P)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) :
    ‖SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))‖ ≤
      (Real.log (P*(r*(a*b)) : ℕ)/L)*(b.primeFactors.card*Real.log r) := by
  rw [coefficient_eq_neg_prime_tents hP hr ha hs hsat hsmall hpairs,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (div_nonneg (Real.log_natCast_nonneg _) hL.le),
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ =>
      (primePairTent_bounds (Real.log_natCast_nonneg r) (Real.log_natCast_nonneg a) _).1))]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.log_natCast_nonneg _) hL.le)
  calc
    _ ≤ ∑ _p ∈ b.primeFactors, Real.log r := Finset.sum_le_sum (fun _ _ =>
      (primePairTent_bounds (Real.log_natCast_nonneg r) (Real.log_natCast_nonneg a) _).2.trans
        (min_le_left _ _))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- On the unchanged retained support, saturation and primality of the
canonical largest/least factors are automatic. The only extra tests are
the small-pair and remaining-pair cutoffs; no prime-count class is fixed. -/
theorem coefficient_le_neg_plateau_count_lowSupport {u : ℝ} {N K n a b : ℕ}
    (hn : n ∈ ZetaRieszLeastVariation.lowSupport u N K) (ha : a.Prime)
    (he : n = ZetaRieszPrimeEndpoint.largestPrime n*(n.minFac*(a*b)))
    (hsmall : Real.log n.minFac+Real.log a ≤
      SquarefreeVaughanLogSource.length u N-Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors, p ≠ q →
      SquarefreeVaughanLogSource.length u N-Real.log (ZetaRieszPrimeEndpoint.largestPrime n) ≤
        Real.log p+Real.log q) :
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re ≤
      -(Real.log n/SquarefreeVaughanLogSource.length u N)*
        ((plateauPrimes (SquarefreeVaughanLogSource.length u N-
          Real.log (ZetaRieszPrimeEndpoint.largestPrime n)) n.minFac a b).card*
          Real.log n.minFac) := by
  obtain ⟨hnI,_⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnB,hI⟩ := Finset.mem_filter.mp hnI
  obtain ⟨_hnC,hs,hn1,_,hp,hprimes⟩ := Finset.mem_filter.mp hnB
  have hP := Nat.prime_of_mem_primeFactors hp
  have hr := Nat.minFac_prime hn1.ne'
  have hs' : Squarefree (ZetaRieszPrimeEndpoint.largestPrime n*(n.minFac*(a*b))) := he ▸ hs
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have howner := (lt_div_iff₀ ht).mp hI.1.1
  have hphysical := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp (hprimes _ hp)
  have hlogP : Real.log (ZetaRieszPrimeEndpoint.largestPrime n) ≤
      SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast hphysical.1.pos)
    exact_mod_cast hphysical.2.2.le
  have hlog : Real.log n = Real.log (ZetaRieszPrimeEndpoint.largestPrime n)+
      Real.log (n.minFac*(a*b) : ℕ) := by
    conv_lhs => rw [he]
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hP.ne_zero)
      (by exact_mod_cast hs'.of_mul_right.ne_zero)]
  have h := coefficient_le_neg_plateau_count hP hr ha hs'
    (SquarefreeVaughanLogSource.length_pos u N) (by linarith) hsmall hpairs
  simpa only [← he] using h

end
end RiemannGaussian.ZetaRieszPrimeCompensation
