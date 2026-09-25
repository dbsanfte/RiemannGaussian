/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastVariation
import RiemannGaussian.ZetaRieszTriplePrime
import RiemannGaussian.ZetaRieszExtremePrimeProfile

/-!
# Signed cutoff profiles in the current large-prime interior

The numerical profile audit distinguishes within-label cancellation from
compensation across prime counts. Four-prime labels on the current core
have a nonnegative arithmetic coefficient, before the full complex phase.
A rough middle factor can leave an exactly positive plateau at any count.
Neither fact is a signed floor for the oscillatory carrier.
-/

namespace RiemannGaussian.ZetaRieszCutoffProfile
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- On the lower half of its support the three-factor cofactor response
is nonnegative. All clipped hinge endpoints are retained. -/
theorem tripleDifference_nonneg_below_midpoint {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL : 2*L ≤ a+b+c) : 0 ≤ tripleDifference a b c L := by
  simp only [tripleDifference, primePairTent, max_def]
  split_ifs <;> linarith

/-- An actual squarefree three-prime cofactor has the same sign, without
an exposed-zero, density or phase hypothesis. -/
theorem riesz_three_nonneg_below_midpoint {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card = 3) {D : ℝ} (hD : 2*D ≤ Real.log a) :
    0 ≤ VaughanLogAverage.riesz D a := by
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩ := exists_three_primes ha hc
  have he : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log q+Real.log r := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  rw [he] at hD
  rw [riesz_three_primes_eq_difference D hp hq hr hpq hpr hqr]
  exact tripleDifference_nonneg_below_midpoint (Real.log_natCast_nonneg p)
    (Real.log_natCast_nonneg q) (Real.log_natCast_nonneg r) hD

/-- Exact positive plateaux survive every middle prime whose logarithm
is beyond the reflected cutoff. The middle factor is never completed. -/
theorem riesz_reflected_plateau {r b : ℕ} (hr : r.Prime)
    (hs : Squarefree (b*r)) {D : ℝ} (hrD : Real.log r ≤ D)
    (hb : ∀ p ∈ b.primeFactors, D ≤ Real.log p) :
    VaughanLogAverage.riesz D (b*r) = Real.log r := by
  rw [ZetaRieszExtremePrimeProfile.riesz_mul_eq_of_extreme_rough hs hb]
  exact ZetaRieszExtremePrimeProfile.riesz_prime_of_saturated hr hrD

/-- Past its least middle-prime threshold, the exact three-factor
profile has two decreasing pieces, until the opposite pair endpoint. -/
theorem tripleDifference_eq_after_min {a b c t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hat : a ≤ t) (ht : t ≤ a+c) :
    tripleDifference a b c t = a-min a (max 0 (t-b))-max 0 (t-c) := by
  have hclip : max 0 (t-b)-max 0 (t-a-b) = min a (max 0 (t-b)) := by
    simp only [max_def, min_def]
    split_ifs <;> linarith
  simp only [tripleDifference, primePairTent]
  rw [max_eq_right (show 0 ≤ t by linarith),
    max_eq_right (show 0 ≤ t-a by linarith),
    max_eq_left (show t-c-a ≤ 0 by linarith),
    max_eq_left (show t-c-b ≤ 0 by linarith),
    max_eq_left (show t-c-a-b ≤ 0 by linarith)]
  linarith

/-- The middle three-factor profile cannot increase after its smallest
prime and before its midpoint. No absolute value is used. -/
theorem tripleDifference_antitone_after_min {a b c x y : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hax : a ≤ x) (hxy : x ≤ y) (hy : 2*y ≤ a+b+c) :
    tripleDifference a b c y ≤ tripleDifference a b c x := by
  rw [tripleDifference_eq_after_min ha hab (hax.trans hxy) (by linarith),
    tripleDifference_eq_after_min ha hab hax (by linarith)]
  have hb' := min_le_min_left a (max_le_max_left 0 (sub_le_sub_right hxy b))
  have hc' := max_le_max_left 0 (sub_le_sub_right hxy c)
  linarith

/-- A literal four-prime reflected cofactor has a nonpositive response
once its least marked pair lies below the cutoff and the remaining three
prime logs are still below their midpoint. This is the favorable arithmetic
sign for a five-prime label after saturated largest-prime deletion. -/
theorem riesz_four_nonpos_small_pair {r a b c : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (r*(a*(b*c))))
    {D : ℝ} (hpair : Real.log r+Real.log a ≤ D)
    (hmid : 2*D ≤ Real.log a+Real.log b+Real.log c) :
    VaughanLogAverage.riesz D (r*(a*(b*c))) ≤ 0 := by
  have hrm : ¬ r ∣ a*(b*c) :=
    hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  rw [riesz_prime_mul D hr hrm,
    riesz_three_primes_eq_difference D ha hb hc hab.ne (hab.trans hbc).ne hbc.ne,
    riesz_three_primes_eq_difference (D-Real.log r) ha hb hc
      hab.ne (hab.trans hbc).ne hbc.ne]
  exact sub_nonpos.mpr (tripleDifference_antitone_after_min (Real.log_natCast_nonneg a)
    (Real.log_le_log (by exact_mod_cast ha.pos) (by exact_mod_cast hab.le))
    (Real.log_le_log (by exact_mod_cast hb.pos) (by exact_mod_cast hbc.le))
    (by linarith) (by linarith [Real.log_natCast_nonneg r]) hmid)

/-- A sign-certified five-prime family in the original coefficient. Its
test is a small-pair cutoff, not a prescribed numerical factor shape.
Saturation and the reflected midpoint are explicit hypotheses. -/
theorem five_coefficient_nonpos_small_pair {P r a b c : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (P*(r*(a*(b*c)))))
    {L : ℝ} (hL : 0 < L) (hsat : Real.log (r*(a*(b*c)) : ℕ) ≤ L)
    (hpair : Real.log r+Real.log a ≤ L-Real.log P)
    (hmid : 2*(L-Real.log P) ≤ Real.log a+Real.log b+Real.log c) :
    (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*(b*c))))).re ≤ 0 := by
  have ham : a*(b*c) ≠ 1 := fun he => ha.ne_one (mul_eq_one.mp he).1
  have hrm : r*(a*(b*c)) ≠ 1 := fun he => hr.ne_one (mul_eq_one.mp he).1
  have hnp : ¬(r*(a*(b*c))).Prime := Nat.not_prime_mul hr.ne_one ham
  have hcut := riesz_four_nonpos_small_pair hr ha hb hc hab hbc hs.of_mul_right hpair hmid
  have hpa : ¬P ∣ r*(a*(b*c)) :=
    hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs.of_mul_right hrm hnp hsat
  have hn : 0 ≤ VaughanLogAverage.riesz L (P*(r*(a*(b*c)))) := by
    rw [riesz_prime_mul L hP hpa, hz, zero_sub]
    exact neg_nonneg.mpr hcut
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs <;> simp only [Complex.ofReal_re, Complex.zero_re]
  · exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.log_natCast_nonneg _)) hn) hL.le
  · exact le_rfl

/-- The core size and physical endpoint discharge saturation and midpoint
for this five-prime sign test. In the literal ordered factorization, r and
a can be taken to be the two smallest primes. The only extra arithmetic
test is log(P*r*a)<=L; the full phase is still present downstream. -/
theorem five_coefficient_nonpos_core {u : ℝ} (hu : 1/2 ≤ u)
    {N P r a b c : ℕ} (hN : 2 ≤ N)
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (P*(r*(a*(b*c)))))
    (howner : Real.log (P*(r*(a*(b*c))) : ℕ)/2 ≤ Real.log P)
    (hleast : Real.log r ≤ (3/50 : ℝ)*Real.log (P*(r*(a*(b*c))) : ℕ))
    (hphysical : Real.log P ≤ SquarefreeVaughanLogSource.length u N)
    (hcore : (39/20 : ℝ)*N ≤ Real.log (P*(r*(a*(b*c))) : ℕ))
    (hpair : Real.log P+Real.log r+Real.log a ≤ SquarefreeVaughanLogSource.length u N) :
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)
      (P*(r*(a*(b*c))))).re ≤ 0 := by
  have hlog : Real.log (P*(r*(a*(b*c))) : ℕ) =
      Real.log P+Real.log (r*(a*(b*c)) : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hP.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hmiddle : Real.log (r*(a*(b*c)) : ℕ) =
      Real.log r+Real.log a+Real.log b+Real.log c := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hr.ne_zero)
      (by exact_mod_cast hs.of_mul_right.of_mul_right.ne_zero), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast ha.ne_zero)
        (by exact_mod_cast (Nat.mul_ne_zero hb.ne_zero hc.ne_zero)), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hb.ne_zero) (by exact_mod_cast hc.ne_zero)]
    ring
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have hlog2 : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlen' : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply five_coefficient_nonpos_small_pair hP hr ha hb hc hab hbc hs
    (SquarefreeVaughanLogSource.length_pos u N)
  · linarith
  · linarith
  · linarith

/-- Extracting the large prime leaves a saturated composite at the
original cutoff and a below-midpoint triple at the reflected cutoff. -/
theorem coefficient_large_prime_triple_nonneg {P a : ℕ} (hP : P.Prime)
    (hs : Squarefree (P*a)) (hc : a.primeFactors.card = 3)
    {L : ℝ} (hL : 0 < L) (haL : Real.log a ≤ L)
    (hmid : 2*(L-Real.log P) ≤ Real.log a) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient L (P*a)).re := by
  have ha := hs.of_mul_right
  have ha1 : a ≠ 1 := by intro he; simp [he] at hc
  have hnp : ¬a.Prime := by
    intro hp
    rw [hp.primeFactors, Finset.card_singleton] at hc
    omega
  have hpa : ¬P ∣ a := hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hnp haL
  have hn : VaughanLogAverage.riesz L (P*a) ≤ 0 := by
    rw [riesz_prime_mul L hP hpa, hz, zero_sub]
    exact neg_nonpos.mpr (riesz_three_nonneg_below_midpoint ha hc hmid)
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs <;> simp only [Complex.ofReal_re, Complex.zero_re]
  · exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (Real.log_natCast_nonneg _)) hn) hL.le
  · exact le_rfl

/-- The literal physical length and lower core endpoint force this
sign for every squarefree four-prime label with a prime above sqrt(n).
The conclusion concerns its coefficient, not its real oscillatory atom. -/
theorem four_coefficient_nonneg_core {u : ℝ} (hu : 1/2 ≤ u)
    {N n P : ℕ} (hN : 2 ≤ N) (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (howner : Real.log n/2 ≤ Real.log P)
    (hphysical : Real.log P ≤ SquarefreeVaughanLogSource.length u N)
    (hcore : (39/20 : ℝ)*N ≤ Real.log n) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) n).re := by
  let a := ∏ p ∈ n.primeFactors.erase P, p
  have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
  have hac : a.primeFactors.card = 3 := by
    rw [hfa, Finset.card_erase_of_mem hP, hc]
  have he : n = P*a := by
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact (Finset.mul_prod_erase _ _ hP).symm
  have hsp : Squarefree (P*a) := he ▸ hs
  have hp := Nat.prime_of_mem_primeFactors hP
  have hlog : Real.log n = Real.log P+Real.log a := by
    rw [he, Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hsp.of_mul_right.ne_zero)]
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have hlog2 : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlen' : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right hlog2 hN0]
  rw [he]
  apply coefficient_large_prime_triple_nonneg hp hsp hac
    (SquarefreeVaughanLogSource.length_pos u N)
  · linarith
  · linarith

/-- The sign applies directly to the current unchanged retained support;
no additional share, count, physical or factorial mask is imposed. -/
theorem four_coefficient_nonneg_lowSupport {u : ℝ} (hu : 1/2 ≤ u)
    {N K n : ℕ} (hN : 2 ≤ N)
    (hn : n ∈ ZetaRieszLeastVariation.lowSupport u N K)
    (hc : n.primeFactors.card = 4) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) n).re := by
  obtain ⟨hnI,_⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnB,hI⟩ := Finset.mem_filter.mp hnI
  obtain ⟨hnC,hs,hn1,_,hp,hprimes⟩ := Finset.mem_filter.mp hnB
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have howner := (lt_div_iff₀ ht).mp hI.1.1
  have hphysical := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp
    (hprimes _ hp)
  have hlogP : Real.log (ZetaRieszPrimeEndpoint.largestPrime n) ≤
      SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast hphysical.1.pos)
    exact_mod_cast hphysical.2.2.le
  have hcore := (Finset.mem_filter.mp hnC).2.1
  apply four_coefficient_nonneg_core hu hN hs hc hp ?_ hlogP hcore.le
  linarith

end
end RiemannGaussian.ZetaRieszCutoffProfile
