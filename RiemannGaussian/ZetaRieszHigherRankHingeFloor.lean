/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowOffsetPairFloor
import RiemannGaussian.ZetaRieszReflectedLinear
import RiemannGaussian.ZetaRieszPairBoundary

/-!
# Join every based divisor block in the low-offset hinge

When the two literal cutoffs see respectively only the unit divisor and
the unit/single-prime divisors, a full higher-rank block is evaluated
exactly. Its original phase, factorial and label masks are unchanged.
The canonical first block and all its other incidences are joined BEFORE
pricing: balanced opposite amplitudes cost at most one quarter of their
separate real-part allowance.

Both previous affine-zero populations are unions of complete canonical
orbits. A based divisibility filter cannot clip these orbits, so the new
floor applies after the current zero deletions without spending them again.
The aggregate numerical floor remains open.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical Pointwise ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszHigherRankHingeFloor
open ZetaRieszShortDivisorOrbits ZetaRieszShortDivisorCancellation
open ZetaRieszHingePairCancellation ZetaRieszSignedConvolution
open ZetaRieszPrimeEndpoint ZetaRieszParityPacket

/-- The maximal based block is exactly the original antidiagonal with
unsigned divisor divisible by its base. No physical label is changed. -/
theorem based_orbit_eq_filter {a e : ℕ} (ha : 0 < a) (he : e ∣ a) :
    orbitDivisors a (a/e) e = a.divisorsAntidiagonal.filter (fun db => e ∣ db.1) := by
  have he0 := Nat.pos_of_dvd_of_pos he ha
  have hRa : a/e ∣ a := Nat.div_dvd_of_dvd he
  have he' : e ∣ a/(a/e) := by
    apply (Nat.dvd_div_iff_mul_dvd hRa).mpr
    exact ⟨1,by simpa only [mul_one,mul_comm] using (Nat.mul_div_cancel' he).symm⟩
  apply Finset.ext
  intro db
  constructor
  · intro hdb
    obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp hdb
    apply Finset.mem_filter.mpr
    refine ⟨orbitDivisors_subset ha hRa he' hdb,?_⟩
    rw [← hde]
    exact dvd_mul_right e d
  · intro hdb
    obtain ⟨hanti,hd⟩ := Finset.mem_filter.mp hdb
    have hmem := Nat.mem_divisorsAntidiagonal.mp hanti
    have hda : db.1 ∣ a := ⟨db.2,hmem.1.symm⟩
    obtain ⟨d,hde⟩ := hd
    have hdq : d ∣ a/e := (Nat.dvd_div_iff_mul_dvd he).mpr (hde ▸ hda)
    apply Finset.mem_image.mpr
    refine ⟨d,Nat.mem_divisors.mpr ⟨hdq,(Nat.pos_of_dvd_of_pos hRa ha).ne'⟩,?_⟩
    apply Prod.ext
    · exact hde.symm
    · change a/(e*d)=db.2
      rw [← hde,← hmem.1]
      exact Nat.mul_div_cancel_left db.2 (Nat.pos_of_dvd_of_pos hda ha)

/-- A base coprime to the canonical pair either retains its ENTIRE
orbit or none of it. It never creates a clipped old zero block. -/
theorem filter_canonical_orbit {a Q e f : ℕ} (hcop : e.Coprime Q) :
    (orbitDivisors a Q f).filter (fun db => e ∣ db.1) =
      if e ∣ f then orbitDivisors a Q f else ∅ := by
  have hconstant : ∀ db ∈ orbitDivisors a Q f, (e ∣ db.1 ↔ e ∣ f) := by
    intro db hdb
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
    exact (hcop.of_dvd_right (Nat.dvd_of_mem_divisors hd)).dvd_mul_right
  by_cases hef : e ∣ f
  · rw [if_pos hef]
    exact Finset.filter_eq_self.mpr (fun db hdb => (hconstant db hdb).mpr hef)
  · rw [if_neg hef]
    apply Finset.filter_eq_empty_iff.mpr
    intro db hdb hh
    exact hef ((hconstant db hdb).mp hh)

private theorem filtered_union_zero {a Q e : ℕ}
    (hcop : Q.Coprime (a/Q)) (he : e ∣ a/Q)
    (E : Finset ℕ) (hE : E ⊆ (a/Q).divisors) (f : (ℕ×ℕ) → ℂ)
    (hz : ∀ b ∈ E, (∑ db ∈ orbitDivisors a Q b, f db)=0) :
    (∑ db ∈ (E.biUnion (orbitDivisors a Q)).filter (fun db => e ∣ db.1), f db)=0 := by
  have heQ : e.Coprime Q := (hcop.of_dvd_right he).symm
  rw [Finset.filter_biUnion]
  rw [Finset.sum_biUnion (by
    intro b hb c hc hbc
    exact (orbitDivisors_disjoint hcop (hE hb) (hE hc) hbc).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  apply Finset.sum_eq_zero
  intro b hb
  rw [filter_canonical_orbit heQ]
  split_ifs
  · exact hz b hb
  · exact Finset.sum_empty

/-- Each old zero credit remains exactly zero inside the selected
based population, for any common original complex observation. -/
theorem filtered_old_zero {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∣ (n/largestPrime n)/leastPairBlock (n/largestPrime n)) (w : ℂ) :
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db ∈ (cancelledOrbitDivisors u N n).filter (fun db => e ∣ db.1), f db)=0 ∧
    (∑ db ∈ (ZetaRieszCrossingOrbitCancellation.affineDivisors u N n).filter
      (fun db => e ∣ db.1), f db)=0 := by
  have hb := canonical_block_data hn hs
  have hd := core_data hn hs
  dsimp only
  constructor
  · unfold cancelledOrbitDivisors
    dsimp only
    rw [if_pos ⟨hb.1,by omega⟩]
    apply filtered_union_zero hb.2.2 he _ (Finset.filter_subset _ _)
    intro b hbmem
    have hg := (Finset.mem_filter.mp hbmem).2
    exact weighted_orbit_eq_zero hd.2.1 hd.1 hb.1
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hbmem).1)
      (by omega) (by linarith [hg.2.1]) hg.2.2.1 w
  · unfold ZetaRieszCrossingOrbitCancellation.affineDivisors
    dsimp only
    rw [if_pos ⟨hb.1,by omega⟩]
    apply filtered_union_zero hb.2.2 he _ (Finset.filter_subset _ _)
    intro b hbmem
    have hg := (Finset.mem_filter.mp hbmem).2
    exact weighted_orbit_eq_zero hd.2.1 hd.1 hb.1
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hbmem).1)
      (by omega) (by linarith [hg.1]) hg.2.1 w

/-- The higher-rank response is unchanged by BOTH previous affine-zero
deletions. Their costs are not added to the new sector a second time. -/
theorem retained_based_sum_eq_full {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∣ (n/largestPrime n)/leastPairBlock (n/largestPrime n)) (w : ℂ) :
    let a := n/largestPrime n
    let O := orbitDivisors a (a/e) e
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db ∈ D ∩ O, f db)=(∑ db ∈ O, f db) := by
  dsimp only
  let a := n/largestPrime n
  let O := orbitDivisors a (a/e) e
  let B := cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n
  let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
    (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
  have hb := canonical_block_data hn hs
  have ha := (core_data hn hs).2.1
  have hea : e ∣ a := he.trans (Nat.div_dvd_of_dvd hb.1)
  have hO : O = a.divisorsAntidiagonal.filter (fun db => e ∣ db.1) :=
    based_orbit_eq_filter (Nat.pos_of_ne_zero ha.ne_zero) hea
  have hB : B ⊆ a.divisorsAntidiagonal := Finset.union_subset
    (cancelledOrbitDivisors_subset hn hs)
    (ZetaRieszCrossingOrbitCancellation.affineDivisors_subset hn hs)
  have hfilter : O ∩ B = B.filter (fun db => e ∣ db.1) := by
    rw [hO]
    ext db
    simp only [Finset.mem_inter,Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨hB h.1,h.2⟩,h.1⟩
  have hzero : (∑ db ∈ O ∩ B, f db)=0 := by
    rw [hfilter,Finset.filter_union,Finset.sum_union (by
      exact (ZetaRieszCrossingOrbitCancellation.affine_disjoint_old_cancelled hn hs).symm.mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hz := filtered_old_zero hn hs he w
    dsimp only at hz
    rw [hz.1,hz.2,add_zero]
  have hset : (a.divisorsAntidiagonal \ B) ∩ O = O \ (O ∩ B) := by
    have hsub : O ⊆ a.divisorsAntidiagonal := hO ▸ Finset.filter_subset _ _
    ext db
    simp only [Finset.mem_inter,Finset.mem_sdiff]
    constructor
    · exact fun h => ⟨h.2,fun hh => h.1.2 hh.2⟩
    · exact fun h => ⟨⟨hsub h.1,fun hh => h.2 ⟨h.1,hh⟩⟩,h.1⟩
  have hh := Finset.sum_sdiff (Finset.inter_subset_left : O ∩ B ⊆ O) (f := f)
  rw [hzero,add_zero] at hh
  change (∑ db ∈ (a.divisorsAntidiagonal \ B) ∩ O, f db)=∑ db ∈ O, f db
  rw [hset,hh]

/-- All divisor ranks are summed before estimation. When the lower
cutoff sees only the unit and the upper sees only unit/single primes,
the original block is a count-LINEAR signed coefficient. -/
theorem weighted_linear_orbit_eq {a p R e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (he : e ∣ a/R) {L : ℝ}
    (hD : 0 ≤ log (a/e : ℕ)-L)
    (hsmall : log (a/e : ℕ)-L ≤ log R.minFac)
    (hprimes : ∀ q ∈ R.primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q ∧ log q ≤ log p) (w : ℂ) :
    (∑ db ∈ orbitDivisors a R e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*
        ((log R-((R.primeFactors.card : ℝ)-1)*log p-
          (R.primeFactors.card : ℝ)*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
  have hR := ha.squarefree_of_dvd hRa
  have hB := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hRa he))
  have hl : log (p*(a/e) : ℕ)=log p+log (a/e : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hB.ne_zero)]
  rw [weighted_orbit_eq_riesz_difference ha hp hRa he L w,hl]
  rw [show log p+log (a/e : ℕ)-L=log p+(log (a/e : ℕ)-L) by ring,
    ZetaRieszReflectedLinear.riesz_eq_linear hR
      (add_nonneg (log_natCast_nonneg p) hD)
      (fun q hq => ⟨(hprimes q hq).1,by linarith [(hprimes q hq).2]⟩),
    ZetaRieszTypeII.riesz_eq_cutoff_below_minFac hR.ne_zero hD hsmall]
  congr 2
  ring

private theorem maximal_base {a e : ℕ} (he : e ∣ a) : e ∣ a/(a/e) := by
  apply (Nat.dvd_div_iff_mul_dvd (Nat.div_dvd_of_dvd he)).mpr
  exact ⟨1,by simpa only [mul_one,mul_comm] using (Nat.mul_div_cancel' he).symm⟩

/-- The canonical first pair block remains a literal part of the full
based population. The other ranks are its original complementary incidences. -/
theorem canonical_orbit_subset_based {a Q e : ℕ} (ha : 0 < a)
    (hQa : Q ∣ a) (he : e ∣ a/Q) :
    orbitDivisors a Q e ⊆ orbitDivisors a (a/e) e := by
  rw [based_orbit_eq_filter ha (base_dvd hQa he)]
  intro db hdb
  refine Finset.mem_filter.mpr ⟨orbitDivisors_subset ha hQa he hdb,?_⟩
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
  exact dvd_mul_right e d

/-- The first canonical block is the positive amplitude; the full
unremoved block retains every middle-prime rank with its original sign. -/
theorem canonical_first_eq {a p Q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hQa : Q ∣ a) (hQ : Q.primeFactors.card=2)
    (he : e ∣ a/Q) {L : ℝ} (hD : 0 ≤ log (a/e : ℕ)-L)
    (hsmall : log (a/e : ℕ)-L ≤ log (a/e : ℕ).minFac)
    (hprimes : ∀ q ∈ (a/e).primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q ∧ log q ≤ log p) (w : ℂ) :
    (∑ db ∈ orbitDivisors a Q e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*((log Q-log p-2*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
  have hQR := block_dvd_quotient hQa he
  have hB := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hQa he))
  have hQ1 : Q ≠ 1 := by intro hh; rw [hh] at hQ; simp at hQ
  have hmf := Nat.minFac_prime hQ1
  have hmin : (a/e).minFac ≤ Q.minFac :=
    Nat.minFac_le_of_dvd hmf.two_le ((Nat.minFac_dvd Q).trans hQR)
  have hsmallQ : log (a/e : ℕ)-L ≤ log Q.minFac := hsmall.trans
    (log_le_log (by exact_mod_cast Nat.minFac_pos (a/e)) (by exact_mod_cast hmin))
  rw [weighted_linear_orbit_eq ha hp hQa he hD hsmallQ
    (fun q hq => hprimes q (Nat.primeFactors_mono hQR hB.ne_zero hq)) w,hQ]
  norm_num

/-- Join ALL other based ranks, rather than pairing only one adjacent
prime. Their single signed amplitude opposes the canonical first block. -/
theorem based_rest_eq {a p Q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hQa : Q ∣ a) (hQ : Q.primeFactors.card=2)
    (he : e ∣ a/Q) {L : ℝ} (hD : 0 ≤ log (a/e : ℕ)-L)
    (hsmall : log (a/e : ℕ)-L ≤ log (a/e : ℕ).minFac)
    (hprimes : ∀ q ∈ (a/e).primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q ∧ log q ≤ log p) (w : ℂ) :
    (∑ db ∈ orbitDivisors a (a/e) e \ orbitDivisors a Q e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -w*(μ (a/e) : ℂ)*
        ((((a/e).primeFactors.card : ℝ)-2)*(log p+(log (a/e : ℕ)-L))-
          (log (a/e : ℕ)-log Q) : ℝ) := by
  have hea := base_dvd hQa he
  have hfull := weighted_linear_orbit_eq ha hp (Nat.div_dvd_of_dvd hea)
    (maximal_base hea) hD hsmall hprimes w
  have hfirst := canonical_first_eq ha hp hQa hQ he hD hsmall hprimes w
  have hsum := Finset.sum_sdiff (canonical_orbit_subset_based
    (Nat.pos_of_ne_zero ha.ne_zero) hQa he) (f := fun db : ℕ×ℕ =>
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))
  rw [← hsum,hfirst] at hfull
  push_cast at hfull ⊢
  linear_combination hfull

/-- Explicit quarter-cost cancellation of opposite joined amplitudes.
The balance inequalities also imply their nonnegativity. -/
theorem opposite_quarter {x y : ℝ} (hxy : 3*x ≤ 5*y) (hyx : 3*y ≤ 5*x) :
    0 ≤ x ∧ 0 ≤ y ∧ |x-y| ≤ (1/4 : ℝ)*(x+y) := by
  refine ⟨by linarith only [hxy,hyx],by linarith only [hxy,hyx],?_⟩
  apply abs_le.mpr
  constructor <;> linarith only [hxy,hyx]

/-- The arbitrary original complex phase does not affect the relative
saving: it is applied only AFTER the opposite arithmetic ranks are joined. -/
theorem opposite_quarter_real_floor {x y : ℝ}
    (hxy : 3*x ≤ 5*y) (hyx : 3*y ≤ 5*x) (z : ℂ) :
    -(1/4 : ℝ)*(|(z*(x : ℂ)).re|+|(-z*(y : ℂ)).re|) ≤
      (z*((x-y : ℝ) : ℂ)).re := by
  have hh := opposite_quarter hxy hyx
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.neg_re]
  rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hh.1,abs_of_nonneg hh.2.1]
  have hb := mul_le_mul_of_nonneg_left hh.2.2 (abs_nonneg z.re)
  have hz := neg_abs_le (z.re*(x-y))
  rw [abs_mul] at hz
  nlinarith only [hb,hz]

/-- The full original higher-rank block costs only one quarter of the
separate first-block/ALL-other-ranks real allowance. This is an independent
signed inequality for the unchanged finite arithmetic population. -/
theorem higher_rank_quarter_floor {a p Q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hQa : Q ∣ a) (hQ : Q.primeFactors.card=2)
    (he : e ∣ a/Q) {L : ℝ} (hD : 0 ≤ log (a/e : ℕ)-L)
    (hsmall : log (a/e : ℕ)-L ≤ log (a/e : ℕ).minFac)
    (hprimes : ∀ q ∈ (a/e).primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q ∧ log q ≤ log p)
    (hxy : 3*(log Q-log p-2*(log (a/e : ℕ)-L)) ≤
      5*((((a/e).primeFactors.card : ℝ)-2)*(log p+(log (a/e : ℕ)-L))-
        (log (a/e : ℕ)-log Q)))
    (hyx : 3*((((a/e).primeFactors.card : ℝ)-2)*(log p+(log (a/e : ℕ)-L))-
        (log (a/e : ℕ)-log Q)) ≤
      5*(log Q-log p-2*(log (a/e : ℕ)-L))) (w : ℂ) :
    let O := orbitDivisors a (a/e) e
    let H := orbitDivisors a Q e
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ);
    -(1/4 : ℝ)*(|(∑ db ∈ H, f db).re|+|(∑ db ∈ O \ H, f db).re|) ≤
      (∑ db ∈ O, f db).re := by
  dsimp only
  rw [canonical_first_eq ha hp hQa hQ he hD hsmall hprimes w,
    based_rest_eq ha hp hQa hQ he hD hsmall hprimes w,
    weighted_linear_orbit_eq ha hp (Nat.div_dvd_of_dvd (base_dvd hQa he))
      (maximal_base (base_dvd hQa he)) hD hsmall hprimes w]
  have heq : log (a/e : ℕ)-(((a/e).primeFactors.card : ℝ)-1)*log p-
      ((a/e).primeFactors.card : ℝ)*(log (a/e : ℕ)-L) =
        (log Q-log p-2*(log (a/e : ℕ)-L))-
          ((((a/e).primeFactors.card : ℝ)-2)*(log p+(log (a/e : ℕ)-L))-
            (log (a/e : ℕ)-log Q)) := by ring
  rw [heq]
  simpa only [mul_assoc,neg_mul] using opposite_quarter_real_floor hxy hyx (w*(μ (a/e) : ℂ))

/-- Only literal prime-log geometry and explicit amplitude balance enter
this selector. No signed moment, prime-density or Type-II estimate is assumed. -/
structure HigherRankData (u : ℝ) (N n e : ℕ) : Prop where
  base_dvd : e ∣ (n/largestPrime n)/leastPairBlock (n/largestPrime n)
  offset_nonneg : 0 ≤ log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N
  offset_small : log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N ≤
    log ((n/largestPrime n)/e : ℕ).minFac
  single_layer : ∀ q ∈ ((n/largestPrime n)/e).primeFactors,
    (log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-
      SquarefreeVaughanLogSource.length u N))/2 ≤ log q ∧ log q ≤ log (largestPrime n)
  first_balance : 3*(log (leastPairBlock (n/largestPrime n))-log (largestPrime n)-
      2*(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N)) ≤
    5*(((((n/largestPrime n)/e).primeFactors.card : ℝ)-2)*
      (log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N))-
        (log ((n/largestPrime n)/e : ℕ)-log (leastPairBlock (n/largestPrime n))))
  rest_balance : 3*(((((n/largestPrime n)/e).primeFactors.card : ℝ)-2)*
      (log (largestPrime n)+(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N))-
        (log ((n/largestPrime n)/e : ℕ)-log (leastPairBlock (n/largestPrime n)))) ≤
    5*(log (leastPairBlock (n/largestPrime n))-log (largestPrime n)-
      2*(log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N))

/-- The signed inequality acts on the CURRENT retained antidiagonal.
Every other incidence remains signed, and old zero deletions are spent once. -/
theorem retained_higher_rank_floor {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdata : HigherRankData u N n e) (w : ℂ) :
    let a := n/largestPrime n
    let O := orbitDivisors a (a/e) e
    let H := orbitDivisors a (leastPairBlock a) e
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db ∈ D \ O, f db).re-
      (1/4 : ℝ)*(|(∑ db ∈ H, f db).re|+|(∑ db ∈ O \ H, f db).re|) ≤
        (∑ db ∈ D, f db).re := by
  have hd := core_data hn hs
  have hb := canonical_block_data hn hs
  have hp := higher_rank_quarter_floor hd.2.1 hd.1 hb.1 hb.2.1 hdata.base_dvd
    hdata.offset_nonneg hdata.offset_small hdata.single_layer
    hdata.first_balance hdata.rest_balance w
  have hr := retained_based_sum_eq_full hn hs hdata.base_dvd w
  dsimp only at hp hr ⊢
  have hh := congrArg Complex.re (Finset.sum_inter_add_sum_sdiff
    ((n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n))
    (orbitDivisors (n/largestPrime n) ((n/largestPrime n)/e) e)
    (fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)))
  rw [hr] at hh
  simp only [Complex.add_re] at hh
  linarith only [hp,hh]

/-- The higher-rank prime row remains ONE signed constant/log moment
on its actual prime set, with every original phase and hole retained. -/
theorem higher_rank_prime_row_eq (Pset : Finset ℕ) {a R e : ℕ}
    (ha : Squarefree a) (hRa : R ∣ a) (he : e ∣ a/R) {L : ℝ}
    (hD : 0 ≤ log (a/e : ℕ)-L) (hsmall : log (a/e : ℕ)-L ≤ log R.minFac)
    (hP : ∀ p ∈ Pset, p.Prime ∧ ∀ q ∈ R.primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q ∧ log q ≤ log p) (w : ℕ → ℂ) :
    (∑ p ∈ Pset, ∑ db ∈ orbitDivisors a R e,
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      (μ (a/e) : ℂ)*
        (((log R-(R.primeFactors.card : ℝ)*(log (a/e : ℕ)-L) : ℝ) : ℂ)*
          (∑ p ∈ Pset, w p)-
            (((R.primeFactors.card : ℝ)-1 : ℝ) : ℂ)*
              (∑ p ∈ Pset, ((log p : ℝ) : ℂ)*w p)) := by
  simp only [mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [weighted_linear_orbit_eq ha (hP p hp).1 hRa he hD hsmall (hP p hp).2 (w p)]
  push_cast
  ring

/-- The root cancellation principle is independent of primes: an
alternating Boolean-cube difference of two clipped linear functions
reduces to its empty/singleton faces whenever all higher faces miss both
cutoffs. It applies to ANY finite family of positive increments. -/
theorem subset_single_layer_difference {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {P D : ℝ} (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hx : ∀ i ∈ S, D ≤ x i ∧ (P+D)/2 ≤ x i ∧ x i ≤ P) :
    (∑ U ∈ S.powerset, (-1 : ℝ)^U.card*
      (max 0 (P+D-∑ i ∈ U, x i)-max 0 (D-∑ i ∈ U, x i))) =
      (∑ i ∈ S, x i)-((S.card : ℝ)-1)*P-(S.card : ℝ)*D := by
  let f := fun U : Finset ι => (-1 : ℝ)^U.card*
    (max 0 (P+D-∑ i ∈ U, x i)-max 0 (D-∑ i ∈ U, x i))
  let B := insert ∅ (S.image (fun i => ({i} : Finset ι)))
  have hB : B ⊆ S.powerset := by
    intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact Finset.mem_powerset.mpr (Finset.empty_subset _)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hU
      exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi)
  have hzero : ∀ U ∈ S.powerset, U ∉ B → f U=0 := by
    intro U hU hnot
    have hsub := Finset.mem_powerset.mp hU
    have hc : 2 ≤ U.card := by
      by_contra hh
      have hcases : U.card=0 ∨ U.card=1 := by omega
      rcases hcases with hh | hh
      · have hz := Finset.card_eq_zero.mp hh
        exact hnot (by rw [hz]; exact Finset.mem_insert_self _ _)
      · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hh
        exact hnot (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨i,hsub (by rw [hi]; exact Finset.mem_singleton_self _),hi.symm⟩))
    have hm : (∑ _i ∈ U, (P+D)/2) ≤ ∑ i ∈ U, x i :=
      Finset.sum_le_sum (fun i hi => (hx i (hsub hi)).2.1)
    rw [Finset.sum_const,nsmul_eq_mul] at hm
    have hcR : (2 : ℝ) ≤ U.card := by exact_mod_cast hc
    have hsum : P+D ≤ ∑ i ∈ U, x i := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcR) (add_nonneg hP hD)]
    simp only [f,max_eq_left (by linarith : P+D-∑ i ∈ U, x i ≤ 0),
      max_eq_left (by linarith : D-∑ i ∈ U, x i ≤ 0),sub_self,mul_zero]
  have heq := Finset.sum_subset hB hzero
  change (∑ U ∈ S.powerset, f U)=_
  rw [← heq]
  have hempty : (∅ : Finset ι) ∉ S.image (fun i => ({i} : Finset ι)) := by simp
  rw [show B=insert ∅ (S.image (fun i => ({i} : Finset ι))) from rfl,
    Finset.sum_insert hempty,Finset.sum_image (by
      intro i _ j _ hij
      exact Finset.singleton_inj.mp hij)]
  have hfempty : f ∅=P := by
    simp only [f,Finset.card_empty,pow_zero,Finset.sum_empty,sub_zero,
      max_eq_right (add_nonneg hP hD),max_eq_right hD,one_mul]
    ring
  have hf : ∀ i ∈ S, f {i}=x i-P-D := by
    intro i hi
    simp only [f,Finset.card_singleton,pow_one,Finset.sum_singleton,
      max_eq_right (by linarith [(hx i hi).2.2] : 0 ≤ P+D-x i),
      max_eq_left (by linarith [(hx i hi).1] : D-x i ≤ 0)]
    ring
  rw [hfempty,Finset.sum_congr rfl hf,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.sum_const,nsmul_eq_mul,nsmul_eq_mul]
  ring

/-- Equal increments expose the exact rank/offset law. It explains
both the cancellations near D=P/k and reinforcing populations elsewhere. -/
theorem equal_increment_response {ι : Type*} (S : Finset ι) {P D : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hDP : D ≤ P) :
    (∑ U ∈ S.powerset, (-1 : ℝ)^U.card*
      (max 0 (P+D-∑ _i ∈ U, P)-max 0 (D-∑ _i ∈ U, P))) =
        P-(S.card : ℝ)*D := by
  rw [subset_single_layer_difference S (fun _ => P) hP hD
    (fun _ _ => ⟨hDP,by linarith,le_rfl⟩),Finset.sum_const,nsmul_eq_mul]
  ring

/-- The general count-linear price is sharp: a different admissible
offset makes all remaining ranks reinforce. The cancellation principle
therefore does NOT license a uniform zero cost or a constant rank price. -/
theorem reinforcing_endpoint_response {ι : Type*} (S : Finset ι) {P : ℝ}
    (hP : 0 ≤ P) :
    (∑ U ∈ S.powerset, (-1 : ℝ)^U.card*
      (max 0 (2*P-∑ _i ∈ U, P)-max 0 (P-∑ _i ∈ U, P))) =
        -((S.card : ℝ)-1)*P := by
  have he := equal_increment_response S hP hP le_rfl
  rw [show P+P=2*P by ring] at he
  rw [he]
  ring

/-- The cancellation centre scales with rank. With equal increments P
it is D=P/k; the observed narrow low-offset balance is not an accident
specific to seven- or ten-prime labels. -/
theorem linear_rank_center {k : ℝ} (hk : k ≠ 0) (S P D : ℝ) :
    S-(k-1)*P-k*D = -k*(D-(S-(k-1)*P)/k) := by
  field_simp
  ring

/-- A rank-dependent interval gives the same quarter saving for every
count. With equal increments S=kP and Q=2P its endpoints reduce to
3P/(5k-4) and 5P/(3k+4). No fixed prime-count list is needed. -/
theorem rank_quarter_of_band {k S Q P D : ℝ} (hk : 2 ≤ k)
    (hlo : (5*S-2*Q-(5*k-7)*P)/(5*k-4) ≤ D)
    (hhi : D ≤ (3*S+2*Q-(3*k-1)*P)/(3*k+4)) :
    |S-(k-1)*P-k*D| ≤
      (1/4 : ℝ)*(2*Q-S+(k-3)*P+(k-4)*D) := by
  have hl := (div_le_iff₀ (by linarith : 0<5*k-4)).mp hlo
  have hh := (le_div_iff₀ (by linarith : 0<3*k+4)).mp hhi
  have hxy : 3*(Q-P-2*D) ≤ 5*((k-2)*(P+D)-(S-Q)) := by nlinarith only [hl]
  have hyx : 3*((k-2)*(P+D)-(S-Q)) ≤ 5*(Q-P-2*D) := by nlinarith only [hh]
  have hp := (opposite_quarter hxy hyx).2.2
  convert hp using 1 <;> congr 1 <;> ring

/-- Even away from the balanced centre, the complete single-layer
response has a LINEAR rank cost, replacing the exponential unsigned
divisor cover. This bound keeps both clipped functions joined. -/
theorem linear_rank_cost_le {k S P D : ℝ} (hk : 2 ≤ k) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hDP : D ≤ P)
    (hlo : k*((P+D)/2) ≤ S) (hhi : S ≤ k*P) :
    |S-(k-1)*P-k*D| ≤ (k-1)*P := by
  apply abs_le.mpr
  constructor
  · nlinarith only [hlo,mul_nonneg (by linarith : 0≤k) (sub_nonneg.mpr hDP)]
  · nlinarith only [hhi,mul_nonneg (by linarith : 0≤k) hD,
      mul_nonneg (by linarith : 0≤k-2) hP]

/-- The count-linear estimate applies to the unchanged original
arithmetic block with its full complex observation. No separate divisor
or cofactor-count norm is used to derive it. -/
theorem norm_linear_orbit_le {a p R e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (he : e ∣ a/R) (hk : 2 ≤ R.primeFactors.card)
    {L : ℝ} (hD : 0 ≤ log (a/e : ℕ)-L)
    (hsmall : log (a/e : ℕ)-L ≤ log R.minFac)
    (hprimes : ∀ q ∈ R.primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q ∧ log q ≤ log p) (w : ℂ) :
    ‖∑ db ∈ orbitDivisors a R e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)‖ ≤
        ‖w‖*(((R.primeFactors.card : ℝ)-1)*log p) := by
  have hR := ha.squarefree_of_dvd hRa
  have hR1 : R ≠ 1 := by intro hh; rw [hh] at hk; simp at hk
  have hmf : R.minFac ∈ R.primeFactors :=
    (Nat.minFac_prime hR1).mem_primeFactors (Nat.minFac_dvd R) hR.ne_zero
  have hDP := hsmall.trans (hprimes R.minFac hmf).2
  have hl : (∑ _q ∈ R.primeFactors, (log p+(log (a/e : ℕ)-L))/2) ≤
      ∑ q ∈ R.primeFactors, log q := Finset.sum_le_sum (fun q hq => (hprimes q hq).1)
  have hh : (∑ q ∈ R.primeFactors, log q) ≤ ∑ _q ∈ R.primeFactors, log p :=
    Finset.sum_le_sum (fun q hq => (hprimes q hq).2)
  rw [Finset.sum_const,nsmul_eq_mul,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hR] at hl
  rw [Finset.sum_const,nsmul_eq_mul,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hR] at hh
  have hc := linear_rank_cost_le (by exact_mod_cast hk) (log_natCast_nonneg p) hD hDP hl hh
  have hm : ‖(μ (a/e) : ℂ)‖ ≤ 1 := by
    have h : |(μ (a/e) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e)
    simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using h
  rw [weighted_linear_orbit_eq ha hp hRa he hD hsmall hprimes w,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖w‖*|log R-((R.primeFactors.card : ℝ)-1)*log p-
        (R.primeFactors.card : ℝ)*(log (a/e : ℕ)-L)| :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) hm) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)

/-- A direct signed floor on the original global population: counts,
labels and radial periods may vary, but each selected physical label is
spent once and every other incidence remains signed. -/
theorem global_retained_higher_rank_floor {u : ℝ} {N K : ℕ} (C H : Finset ℕ)
    (hH : H ⊆ C) (hC : ∀ n ∈ C, n ∈ coreBand u N K ∧ Squarefree n)
    (e : ℕ → ℕ) (hdata : ∀ n ∈ H, HigherRankData u N n (e n)) (w : ℕ → ℂ) :
    let a := fun n => n/largestPrime n
    let O := fun n => orbitDivisors (a n) (a n/e n) (e n)
    let H0 := fun n => orbitDivisors (a n) (leastPairBlock (a n)) (e n)
    let D := fun n => (a n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun n (db : ℕ×ℕ) => w n*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ n ∈ C \ H, ∑ db ∈ D n, f n db).re+
      (∑ n ∈ H, (∑ db ∈ D n \ O n, f n db).re)-
      (1/4 : ℝ)*(∑ n ∈ H,
        (|(∑ db ∈ H0 n, f n db).re|+|(∑ db ∈ O n \ H0 n, f n db).re|)) ≤
      (∑ n ∈ C, ∑ db ∈ D n, f n db).re := by
  dsimp only
  have hs := Finset.sum_le_sum (s := H) (fun n hn =>
    retained_higher_rank_floor (hC n (hH hn)).1 (hC n (hH hn)).2 (hdata n hn) (w n))
  dsimp only at hs
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at hs
  have heq := congrArg Complex.re (Finset.sum_sdiff hH (f := fun n =>
    ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
      w n*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)))
  simp only [Complex.add_re,Complex.re_sum] at heq
  simp only [Complex.re_sum] at hs ⊢
  linarith only [hs,heq]

/-- The new quarter-cost saving enters the SAME authoritative floor
ledger after global allocation/count payments. All earlier credits and
both geometric errors are unchanged and occur once. -/
theorem eventually_remaining_higher_rank_floor {u : ℝ} (hu : 1/2<u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j : ℕ in atTop,
    let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
    let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
    let C := ((((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree) \
      ZetaRieszReducedCountPayment.reducedCountLabels u N K)
    let a := fun n => n/largestPrime n
    let O := fun n e => orbitDivisors (a n) (a n/e) e
    let H0 := fun n e => orbitDivisors (a n) (leastPairBlock (a n)) e
    let D := fun n => (a n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let w := fun n => (u : ℂ)^(N+1)*phaseWeight
      (if n ∈ ZetaRieszHingeAllocationPayment.hingeLabels u N K then ∅ else
        ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (a n) (largestPrime n)
    let f := fun n (db : ℕ×ℕ) => w n*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    let B := (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re+
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)+
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*
      ZetaRieszHingeAllocationPayment.hingeAllocationRate^N+
      ((203/50 : ℝ)*(10001/20000))*((N : ℝ)+1)*ZetaRieszReducedCountPayment.paidCountRate^N
    ∀ (H : Finset ℕ) (e : ℕ → ℕ), H ⊆ C → (∀ n ∈ H, HigherRankData u N n (e n)) →
      (∑ n ∈ C \ H, ∑ db ∈ D n, f n db).re+
        (∑ n ∈ H, (∑ db ∈ D n \ O n (e n), f n db).re)-
        (1/4 : ℝ)*(∑ n ∈ H,
          (|(∑ db ∈ H0 n (e n), f n db).re|+|(∑ db ∈ O n (e n) \ H0 n (e n), f n db).re|))-
        u^(N+1)*B-E ≤
          u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j := by
  filter_upwards [ZetaRieszReducedCountPayment.eventually_remaining_reducedCount_bounds hu hU y]
    with j hJ
  dsimp only at hJ ⊢
  intro H e hH hdata
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
  have hp := global_retained_higher_rank_floor _ H hH hC e hdata
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

end RiemannGaussian.ZetaRieszHigherRankHingeFloor
