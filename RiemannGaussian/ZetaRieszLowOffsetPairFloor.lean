/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReducedCountPayment

/-!
# A joined floor on the low-offset side of the literal hinge

The two old four-divisor blocks have opposite signs before their common
original observation is applied. This region includes near-balanced
seven-prime labels and is disjoint from the earlier overlap selector.
Joining the blocks costs at most two thirds of their separate real-part
allowance when their positive amplitudes differ by at most a factor five.

The prime row keeps its signed constant and logarithmic moments together.
All original phases and masks remain. No aggregate numerical floor or
source-scale population payment is asserted for this sector.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical Pointwise ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszLowOffsetPairFloor
open ZetaRieszHingePairCancellation ZetaRieszShortDivisorOrbits
open ZetaRieszSignedConvolution ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszTriplePrime ZetaSquarefreeRieszWindows
open ZetaRieszShortDivisorCancellation

private theorem low_tent {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hx : 0 ≤ x) (hxa : x ≤ a) : primePairTent a b x=x := by
  unfold primePairTent
  rw [max_eq_right hx,max_eq_left (by linarith : x-a ≤ 0),
    max_eq_left (by linarith : x-b ≤ 0),
    max_eq_left (by linarith : x-a-b ≤ 0)]
  ring

private theorem high_tent {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbx : b ≤ x) (hhi : x ≤ a+b) : primePairTent a b x=a+b-x := by
  unfold primePairTent
  rw [max_eq_right (by linarith : 0 ≤ x),
    max_eq_right (by linarith : 0 ≤ x-a),
    max_eq_right (by linarith : 0 ≤ x-b),
    max_eq_left (by linarith : x-a-b ≤ 0)]
  ring

/-- Both original hinges are retained. Here the second old block crosses
the first hinge even though it lies below the cofactor hinge. -/
theorem low_offset_difference {a b c P D : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcP : c ≤ P)
    (hD : 0 ≤ D) (hDa : D ≤ a) (hhi : P+D ≤ a+b) :
    tripleDifference a b c (P+D)-tripleDifference a b c D =
      a+b+c-2*P-3*D := by
  have hfirst := high_tent ha hab (show b ≤ P+D by linarith) hhi
  have hsecond := low_tent ha hab hD hDa
  have hthird := low_tent ha hab (show 0 ≤ P+D-c by linarith)
    (show P+D-c ≤ a by linarith)
  have hfourth := primePairTent_eq_zero_of_outside ha (show 0 ≤ b by linarith)
    (Or.inl (show D-c ≤ 0 by linarith))
  rw [tripleDifference,tripleDifference,hfirst,hsecond,hthird,hfourth]
  ring

/-- An exact independent saving after joining two opposite arithmetic
amplitudes, rather than assigning an allowance to each count separately. -/
theorem opposite_amplitudes_two_thirds {x y : ℝ}
    (hxy : x ≤ 5*y) (hyx : y ≤ 5*x) :
    |x-y| ≤ (2/3 : ℝ)*(x+y) := by
  apply abs_le.mpr
  constructor <;> linarith only [hxy,hyx]

/-- The balance conditions themselves force both amplitudes to be
nonnegative. No positivity of the original complex phase is required. -/
theorem balanced_amplitudes_nonneg {x y : ℝ}
    (hxy : x ≤ 5*y) (hyx : y ≤ 5*x) : 0 ≤ x ∧ 0 ≤ y := by
  constructor <;> linarith only [hxy,hyx]

/-- The actual low-offset response has the two-thirds allowance. -/
theorem low_offset_two_thirds {a b c P D : ℝ}
    (hxy : a+b-P-2*D ≤ 5*(P+D-c))
    (hyx : P+D-c ≤ 5*(a+b-P-2*D)) :
    |a+b+c-2*P-3*D| ≤ (2/3 : ℝ)*(a+b-c-D) := by
  have heq : a+b+c-2*P-3*D=(a+b-P-2*D)-(P+D-c) := by ring
  have heq' : a+b-c-D=(a+b-P-2*D)+(P+D-c) := by ring
  rw [heq,heq']
  exact opposite_amplitudes_two_thirds hxy hyx

/-- Exact low-offset formula for the original eight incidences. The
phase, factorial kernel and allocation may be any common original weight. -/
theorem weighted_low_offset_pair_eq {a p r s q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqp : log q ≤ log p)
    (hlo : 0 ≤ log (a/e : ℕ)-L) (hsmall : log (a/e : ℕ)-L ≤ log r)
    (hhi : log p+(log (a/e : ℕ)-L) ≤ log r+log s) (w : ℂ) :
    (∑ db ∈ orbitDivisors a (r*s*q) e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*
        ((log r+log s+log q-2*log p-3*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
  have hb := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hRa he))
  have hl : log (p*(a/e) : ℕ)=log p+log (a/e : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hb.ne_zero)]
  have hv (x : ℝ) : VaughanLogAverage.riesz x (r*s*q)=
      tripleDifference (log r) (log s) (log q) x := by
    rw [mul_assoc]
    exact riesz_three_primes_eq_difference x hr hs hq hrs hrq hsq
  rw [weighted_orbit_eq_riesz_difference ha hp hRa he L w,hv,hv,hl]
  rw [show log p+log (a/e : ℕ)-L=log p+(log (a/e : ℕ)-L) by ring,
    low_offset_difference (log_natCast_nonneg r) hrsle hsqle hqp hlo hsmall hhi]

private theorem adjacent_bases {a R q e : ℕ} (hRa : R*q ∣ a)
    (he : e ∣ a/(R*q)) : e ∣ a/R ∧ e*q ∣ a/R := by
  have hR : R ∣ a := (dvd_mul_right R q).trans hRa
  have hq : q ∣ a/R := (Nat.dvd_div_iff_mul_dvd hR).mpr (by
    simpa only [mul_comm] using hRa)
  have he' : e ∣ (a/R)/q := by simpa only [Nat.div_div_eq_div_mul] using he
  exact ⟨base_dvd hq he',by
    simpa only [mul_comm] using (Nat.dvd_div_iff_mul_dvd hq).mp he'⟩

/-- The first old block has a positive arithmetic amplitude times the
common original Möbius observation. Neither hinge was normed separately. -/
theorem weighted_low_offset_first_eq {a p r s q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsp : log s ≤ log p)
    (hlo : 0 ≤ log (a/e : ℕ)-L) (hsmall : log (a/e : ℕ)-L ≤ log r)
    (hhi : log p+(log (a/e : ℕ)-L) ≤ log r+log s) (w : ℂ) :
    (∑ db ∈ orbitDivisors a (r*s) e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*((log r+log s-log p-2*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
  have hR : r*s ∣ a := (dvd_mul_right (r*s) q).trans hRa
  have hbases := adjacent_bases hRa he
  have hb := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hR hbases.1))
  have hl : log (p*(a/e) : ℕ)=log p+log (a/e : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hb.ne_zero)]
  have hv (x : ℝ) : VaughanLogAverage.riesz x (r*s)=
      primePairTent (log r) (log s) x := by
    simpa using riesz_two_primes_eq_tent x hr hs hrs hr.not_dvd_one hs.not_dvd_one
  rw [weighted_orbit_eq_riesz_difference ha hp hR hbases.1 L w,hv,hv,hl]
  rw [show log p+log (a/e : ℕ)-L=log p+(log (a/e : ℕ)-L) by ring,
    high_tent (log_natCast_nonneg r) hrsle (by linarith : log s ≤ log p+(log (a/e : ℕ)-L)) hhi,
    low_tent (log_natCast_nonneg r) hrsle hlo hsmall]
  congr 2
  ring

/-- The adjacent old block has the OPPOSITE common observation. This
is a crossing of the first hinge, not a zero/affine discarded block. -/
theorem weighted_low_offset_second_eq {a p r s q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqp : log q ≤ log p)
    (hlo : 0 ≤ log (a/e : ℕ)-L) (hsmall : log (a/e : ℕ)-L ≤ log r)
    (hhi : log p+(log (a/e : ℕ)-L) ≤ log r+log s) (w : ℂ) :
    (∑ db ∈ orbitDivisors a (r*s) (e*q),
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -w*(μ (a/e) : ℂ)*((log p+(log (a/e : ℕ)-L)-log q : ℝ) : ℂ) := by
  have hj := weighted_low_offset_pair_eq ha hp hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hqp hlo hsmall hhi w
  rw [paired_orbit_eq_union _ _ _ hq,
    Finset.sum_union (paired_orbits_disjoint ha hq hRa he),
    weighted_low_offset_first_eq ha hp hr hs hrs hRa he hrsle
      (hsqle.trans hqp) hlo hsmall hhi w] at hj
  apply add_left_cancel (a := w*(μ (a/e) : ℂ)*
    ((log r+log s-log p-2*(log (a/e : ℕ)-L) : ℝ) : ℂ))
  rw [hj]
  push_cast
  ring

/-- Join two opposite original blocks before observing their real part.
Their separate allowances lose at least one third, for EVERY phase. -/
theorem opposite_real_floor {x y : ℝ} (hxy : x ≤ 5*y) (hyx : y ≤ 5*x) (z : ℂ) :
    -(2/3 : ℝ)*(|(z*(x : ℂ)).re|+|(-z*(y : ℂ)).re|) ≤
      (z*((x-y : ℝ) : ℂ)).re := by
  have hn := balanced_amplitudes_nonneg hxy hyx
  have hb := mul_le_mul_of_nonneg_left (opposite_amplitudes_two_thirds hxy hyx)
    (abs_nonneg z.re)
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.neg_re] at ⊢
  rw [abs_mul,abs_mul,abs_of_nonneg hn.1,abs_of_nonneg hn.2,abs_neg]
  have hr := neg_abs_le (z.re*(x-y))
  rw [abs_mul] at hr
  nlinarith only [hb,hr]

/-- The original eight-incidence sector has an independent floor at
two thirds of its old two-block real allowance. The common observation
can include the full source power and every literal factorial mask. -/
theorem re_low_offset_pair_floor {a p r s q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqp : log q ≤ log p)
    (hlo : 0 ≤ log (a/e : ℕ)-L) (hsmall : log (a/e : ℕ)-L ≤ log r)
    (hhi : log p+(log (a/e : ℕ)-L) ≤ log r+log s)
    (hxy : log r+log s-log p-2*(log (a/e : ℕ)-L) ≤
      5*(log p+(log (a/e : ℕ)-L)-log q))
    (hyx : log p+(log (a/e : ℕ)-L)-log q ≤
      5*(log r+log s-log p-2*(log (a/e : ℕ)-L))) (w : ℂ) :
    -(2/3 : ℝ)*
      (|(∑ db ∈ orbitDivisors a (r*s) e,
          w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re|+
       |(∑ db ∈ orbitDivisors a (r*s) (e*q),
          w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re|) ≤
      (∑ db ∈ orbitDivisors a (r*s*q) e,
        w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re := by
  rw [weighted_low_offset_pair_eq ha hp hr hs hq hrs hrq hsq hRa he
      hrsle hsqle hqp hlo hsmall hhi,
    weighted_low_offset_first_eq ha hp hr hs hrs hRa he hrsle
      (hsqle.trans hqp) hlo hsmall hhi,
    weighted_low_offset_second_eq ha hp hr hs hq hrs hrq hsq hRa he
      hrsle hsqle hqp hlo hsmall hhi]
  have heq : log r+log s+log q-2*log p-3*(log (a/e : ℕ)-L)=
      (log r+log s-log p-2*(log (a/e : ℕ)-L))-
        (log p+(log (a/e : ℕ)-L)-log q) := by ring
  rw [heq]
  simpa only [mul_assoc,neg_mul] using opposite_real_floor hxy hyx (w*(μ (a/e) : ℂ))

/-- The low-offset prime row keeps its EXACT signed constant and log
moments. No clipped moment, absolute prime observation or count debit is
introduced by this affine formula. -/
theorem low_offset_prime_row_eq (Pset : Finset ℕ) {a r s q e : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : 0 ≤ log (a/e : ℕ)-L) (hsmall : log (a/e : ℕ)-L ≤ log r)
    (hP : ∀ p ∈ Pset, p.Prime ∧ log q ≤ log p ∧
      log p+(log (a/e : ℕ)-L) ≤ log r+log s) (w : ℕ → ℂ) :
    (∑ p ∈ Pset, ∑ db ∈ orbitDivisors a (r*s*q) e,
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      (μ (a/e) : ℂ)*
        (((log r+log s+log q-3*(log (a/e : ℕ)-L) : ℝ) : ℂ)*
          (∑ p ∈ Pset, w p)-2*(∑ p ∈ Pset, ((log p : ℝ) : ℂ)*w p)) := by
  simp only [mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [weighted_low_offset_pair_eq ha (hP p hp).1 hr hs hq hrs hrq hsq hRa he
    hrsle hsqle (hP p hp).2.1 hlo hsmall (hP p hp).2.2]
  push_cast
  ring

/-- A canonical block crossing the first hinge has not been deleted by
either earlier affine-zero selector. This includes the low-offset region
where the other block lies below the second hinge. -/
theorem first_hinge_orbit_disjoint {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hcut : log (largestPrime n*(n/largestPrime n) : ℕ)-
      SquarefreeVaughanLogSource.length u N-log e < log (leastPairBlock (n/largestPrime n))) :
    Disjoint (orbitDivisors (n/largestPrime n) (leastPairBlock (n/largestPrime n)) e)
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n) := by
  have hb := canonical_block_data hn hs
  apply Finset.disjoint_left.mpr
  intro db hdb hpaid
  have hsame {f : ℕ}
      (hf : f ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
      (hmatch : db ∈ orbitDivisors (n/largestPrime n) (leastPairBlock (n/largestPrime n)) f) :
      f=e := by
    by_contra hne
    exact Finset.disjoint_left.mp (orbitDivisors_disjoint hb.2.2 hf he hne) hmatch hdb
  rcases Finset.mem_union.mp hpaid with hpaid | hpaid
  · unfold cancelledOrbitDivisors at hpaid
    dsimp only at hpaid
    rw [if_pos ⟨hb.1,by omega⟩] at hpaid
    obtain ⟨f,hf,hmatch⟩ := Finset.mem_biUnion.mp hpaid
    have hgeom := (Finset.mem_filter.mp hf).2
    rw [hsame (Finset.mem_filter.mp hf).1 hmatch] at hgeom
    linarith [hgeom.2.1]
  · unfold ZetaRieszCrossingOrbitCancellation.affineDivisors at hpaid
    dsimp only at hpaid
    rw [if_pos ⟨hb.1,by omega⟩] at hpaid
    obtain ⟨f,hf,hmatch⟩ := Finset.mem_biUnion.mp hpaid
    have hgeom := (Finset.mem_filter.mp hf).2
    rw [hsame (Finset.mem_filter.mp hf).1 hmatch] at hgeom
    linarith [hgeom.1]

/-- The new saving is on CURRENT retained original incidences, not on
an already-paid affine block. No count/radial/physical mask is completed. -/
theorem low_offset_pair_subset_retained {u : ℝ} {N K n r s q e : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s)
    (hRa : r*s*q ∣ n/largestPrime n) (he : e ∣ (n/largestPrime n)/(r*s*q))
    (hhi : log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
      SquarefreeVaughanLogSource.length u N) < log r+log s) :
    orbitDivisors (n/largestPrime n) (r*s*q) e ⊆
      (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n) := by
  have hd := core_data hn hsf
  have hb := adjacent_bases hRa he
  have hR : r*s ∣ n/largestPrime n := (dvd_mul_right (r*s) q).trans hRa
  have hzero : (n/largestPrime n)/(r*s) ≠ 0 :=
    (hd.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hR)).ne_zero
  have he' : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors := by
    rw [hcanonical]
    exact Nat.mem_divisors.mpr ⟨hb.1,hzero⟩
  have heq' : e*q ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors := by
    rw [hcanonical]
    exact Nat.mem_divisors.mpr ⟨hb.2,hzero⟩
  have hlogR : log (leastPairBlock (n/largestPrime n))=log r+log s := by
    rw [hcanonical,Nat.cast_mul,log_mul (by exact_mod_cast hr.ne_zero)
      (by exact_mod_cast hs.ne_zero)]
  have hl := base_log hd.2.1 hd.1 (base_dvd hR hb.1)
  have hB := hd.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hR hb.1))
  have hlB : log (largestPrime n*((n/largestPrime n)/e) : ℕ)=
      log (largestPrime n)+log ((n/largestPrime n)/e : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero) (by exact_mod_cast hB.ne_zero)]
  have hcut : log (largestPrime n*(n/largestPrime n) : ℕ)-
      SquarefreeVaughanLogSource.length u N-log e < log (leastPairBlock (n/largestPrime n)) := by
    rw [hlogR]
    rw [hlB] at hl
    linarith only [hl,hhi]
  have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he').ne'
  have hlogeq : log (e*q : ℕ)=log e+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast he0) (by exact_mod_cast hq.ne_zero)]
  have hcutq : log (largestPrime n*(n/largestPrime n) : ℕ)-
      SquarefreeVaughanLogSource.length u N-log (e*q : ℕ) <
        log (leastPairBlock (n/largestPrime n)) := by
    rw [hlogeq]
    linarith [log_natCast_nonneg q]
  have hecancel := first_hinge_orbit_disjoint hn hsf he' hcut
  have heqcancel := first_hinge_orbit_disjoint hn hsf heq' hcutq
  rw [hcanonical] at hecancel heqcancel
  intro db hdb
  apply Finset.mem_sdiff.mpr
  refine ⟨orbitDivisors_subset (Nat.pos_of_ne_zero hd.2.1.ne_zero) hRa he hdb,?_⟩
  rw [paired_orbit_eq_union _ _ _ hq] at hdb
  rcases Finset.mem_union.mp hdb with hdb | hdb
  · exact fun hh => Finset.disjoint_left.mp hecancel hdb hh
  · exact fun hh => Finset.disjoint_left.mp heqcancel hdb hh

/-- Direct floor for one retained original label: the new pair is joined
once, and every unselected incidence remains signed in the same ledger. -/
theorem retained_low_offset_floor {u : ℝ} {N K n r s q e : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s)
    (hRa : r*s*q ∣ n/largestPrime n) (he : e ∣ (n/largestPrime n)/(r*s*q))
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqp : log q ≤ log (largestPrime n))
    (hlo : 0 ≤ log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N)
    (hsmall : log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N ≤ log r)
    (hhi : log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
      SquarefreeVaughanLogSource.length u N) < log r+log s)
    (hxy : log r+log s-log (largestPrime n)-
        2*(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N) ≤
      5*(log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
        SquarefreeVaughanLogSource.length u N)-log q))
    (hyx : log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
        SquarefreeVaughanLogSource.length u N)-log q ≤
      5*(log r+log s-log (largestPrime n)-
        2*(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N))) (w : ℂ) :
    let D := (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db ∈ D \ orbitDivisors (n/largestPrime n) (r*s*q) e, f db).re-
      (2/3 : ℝ)*(|(∑ db ∈ orbitDivisors (n/largestPrime n) (r*s) e, f db).re|+
        |(∑ db ∈ orbitDivisors (n/largestPrime n) (r*s) (e*q), f db).re|) ≤
      (∑ db ∈ D, f db).re := by
  dsimp only
  have hp := re_low_offset_pair_floor (core_data hn hsf).2.1 (core_data hn hsf).1
    hr hs hq hrs hrq hsq hRa he hrsle hsqle hqp hlo hsmall hhi.le hxy hyx w
  have heq := Finset.sum_sdiff (f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ))
    (low_offset_pair_subset_retained hn hsf hr hs hq hcanonical hRa he hhi)
  have hreal := congrArg Complex.re heq
  simp only [Complex.add_re] at hreal
  linarith only [hp,hreal]

/-- Finite arithmetic witnesses for this specific signed floor. There
is no prime-discrepancy or cancellation estimate among these hypotheses. -/
structure LowOffsetData (u : ℝ) (N n r s q e : ℕ) : Prop where
  r_prime : r.Prime
  s_prime : s.Prime
  q_prime : q.Prime
  rs_ne : r ≠ s
  rq_ne : r ≠ q
  sq_ne : s ≠ q
  canonical : leastPairBlock (n/largestPrime n)=r*s
  block_dvd : r*s*q ∣ n/largestPrime n
  base_dvd : e ∣ (n/largestPrime n)/(r*s*q)
  rs_log : log r ≤ log s
  sq_log : log s ≤ log q
  qp_log : log q ≤ log (largestPrime n)
  offset_nonneg : 0 ≤ log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N
  offset_small : log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N ≤ log r
  first_crossing : log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
    SquarefreeVaughanLogSource.length u N) < log r+log s
  first_balance : log r+log s-log (largestPrime n)-
      2*(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N) ≤
    5*(log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
      SquarefreeVaughanLogSource.length u N)-log q)
  second_balance : log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
      SquarefreeVaughanLogSource.length u N)-log q ≤
    5*(log r+log s-log (largestPrime n)-
      2*(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N))

/-- Join this sector over ALL selected labels/counts/radial periods.
Every unselected label and incidence stays signed. The separate old
two-block allowance is reduced by one third, never spent twice. -/
theorem global_retained_low_offset_floor {u : ℝ} {N K : ℕ} (C H : Finset ℕ)
    (hH : H ⊆ C) (hC : ∀ n ∈ C, n ∈ coreBand u N K ∧ Squarefree n)
    (r s q e : ℕ → ℕ) (hdata : ∀ n ∈ H, LowOffsetData u N n (r n) (s n) (q n) (e n))
    (w : ℕ → ℂ) :
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun n (db : ℕ×ℕ) => w n*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ n ∈ C \ H, ∑ db ∈ D n, f n db).re+
      (∑ n ∈ H, (∑ db ∈ D n \ orbitDivisors (n/largestPrime n) (r n*s n*q n) (e n), f n db).re)-
      (2/3 : ℝ)*(∑ n ∈ H,
        (|(∑ db ∈ orbitDivisors (n/largestPrime n) (r n*s n) (e n), f n db).re|+
        |(∑ db ∈ orbitDivisors (n/largestPrime n) (r n*s n) (e n*q n), f n db).re|)) ≤
      (∑ n ∈ C, ∑ db ∈ D n, f n db).re := by
  dsimp only
  have hs := Finset.sum_le_sum (s := H) (fun n hn =>
    retained_low_offset_floor (hC n (hH hn)).1 (hC n (hH hn)).2
      (hdata n hn).r_prime (hdata n hn).s_prime (hdata n hn).q_prime
      (hdata n hn).rs_ne (hdata n hn).rq_ne (hdata n hn).sq_ne
      (hdata n hn).canonical (hdata n hn).block_dvd (hdata n hn).base_dvd
      (hdata n hn).rs_log (hdata n hn).sq_log (hdata n hn).qp_log
      (hdata n hn).offset_nonneg (hdata n hn).offset_small (hdata n hn).first_crossing
      (hdata n hn).first_balance (hdata n hn).second_balance (w n))
  dsimp only at hs
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at hs
  have heq := congrArg Complex.re (Finset.sum_sdiff hH (f := fun n =>
    ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
      w n*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)))
  simp only [Complex.add_re,Complex.re_sum] at heq
  simp only [Complex.re_sum] at hs ⊢
  linarith only [hs,heq]

/-- Direct current floor-ledger comparison. The old credits and both
geometric error budgets remain unchanged and occur once. Only the chosen
low-offset pairs get the independent one-third allowance saving. -/
theorem eventually_remaining_low_offset_floor {u : ℝ} (hu : 1/2<u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j : ℕ in atTop,
    let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
    let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
    let C := ((((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree) \
      ZetaRieszReducedCountPayment.reducedCountLabels u N K)
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let w := fun n => (u : ℂ)^(N+1)*phaseWeight
      (if n ∈ ZetaRieszHingeAllocationPayment.hingeLabels u N K then ∅ else
        ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)
    let f := fun n (db : ℕ×ℕ) => w n*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    let B := (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re+
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)+
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*
      ZetaRieszHingeAllocationPayment.hingeAllocationRate^N+
      ((203/50 : ℝ)*(10001/20000))*((N : ℝ)+1)*ZetaRieszReducedCountPayment.paidCountRate^N
    ∀ (H : Finset ℕ) (r s q e : ℕ → ℕ), H ⊆ C →
      (∀ n ∈ H, LowOffsetData u N n (r n) (s n) (q n) (e n)) →
      (∑ n ∈ C \ H, ∑ db ∈ D n, f n db).re+
        (∑ n ∈ H, (∑ db ∈ D n \ orbitDivisors (n/largestPrime n) (r n*s n*q n) (e n), f n db).re)-
        (2/3 : ℝ)*(∑ n ∈ H,
          (|(∑ db ∈ orbitDivisors (n/largestPrime n) (r n*s n) (e n), f n db).re|+
          |(∑ db ∈ orbitDivisors (n/largestPrime n) (r n*s n) (e n*q n), f n db).re|))-
        u^(N+1)*B-E ≤
          u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j := by
  filter_upwards [ZetaRieszReducedCountPayment.eventually_remaining_reducedCount_bounds hu hU y]
    with j hJ
  dsimp only at hJ ⊢
  intro H r s q e hH hdata
  have hC : ∀ n ∈ ((((coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).filter
      (fun n : ℕ => (197/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j<log n)).filter Squarefree) \
      ZetaRieszReducedCountPayment.reducedCountLabels u
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)),
        n ∈ coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) ∧ Squarefree n := by
    intro n hn
    have hm := Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1
    exact ⟨(Finset.mem_filter.mp hm.1).1,hm.2⟩
  have hp := global_retained_low_offset_floor _ H hH hC r s q e hdata
    (fun n => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*phaseWeight
      (if n ∈ ZetaRieszHingeAllocationPayment.hingeLabels u
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
        then ∅ else ZetaRieszAnnulusJoint.intermediatePrimes u
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) y (n/largestPrime n) (largestPrime n))
  dsimp only at hp
  conv at hp =>
    rhs
    simp only [mul_assoc,← Finset.mul_sum,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
    simp only [Finset.mul_sum,← mul_assoc]
  nlinarith only [hp,hJ.1]

end RiemannGaussian.ZetaRieszLowOffsetPairFloor
