/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShortDivisorCancellation

/-!
# Zero cost for the full short-divisor interior

The squarefree divisor antidiagonal splits into disjoint blocks `d=e*delta`,
where `delta` runs through one composite small block and `e` divides its
coprime complement. Every complete block missing both hinge crossings
cancels exactly with the ORIGINAL common phase and factorial allocation.
The selected blocks lie in the unpaid short boundary. No separate prime
count, divisor or Fourier norm is used to remove them. The surviving
cutoff and reflected-hinge crossings are retained, not claimed small.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical Pointwise ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszShortDivisorOrbits
open ZetaRieszSignedConvolution ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszOwnerGapRows ZetaRieszShortDivisorCancellation

/-- A based block of original unsigned/signed cofactor incidences. -/
def orbitDivisors (a R e : ℕ) : Finset (ℕ×ℕ) :=
  R.divisors.image (fun d => (e*d,a/(e*d)))

/-- A based cofactor incidence divides the complete original cofactor. -/
theorem base_dvd {a R e : ℕ} (hRa : R ∣ a) (he : e ∣ a/R) :
    e ∣ a := he.trans (Nat.div_dvd_of_dvd hRa)

/-- The canonical block remains in every based surviving cofactor. -/
theorem block_dvd_quotient {a R e : ℕ} (hRa : R ∣ a) (he : e ∣ a/R) :
    R ∣ a/e := by
  apply (Nat.dvd_div_iff_mul_dvd (base_dvd hRa he)).mpr
  have h := Nat.mul_dvd_mul_left R he
  rw [Nat.mul_div_cancel' hRa] at h
  simpa only [mul_comm] using h

/-- Exact logarithmic geometry on the original based incidence. -/
theorem base_log {a p e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (he : e ∣ a) :
    log (p*(a/e) : ℕ) = log (p*a : ℕ)-log e := by
  have he0 : e ≠ 0 := (Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero ha.ne_zero)).ne'
  have hb0 : a/e ≠ 0 := by
    intro hz
    have h := Nat.mul_div_cancel' he
    rw [hz,mul_zero] at h
    exact ha.ne_zero h.symm
  have hl : log a = log e+log (a/e : ℕ) := by
    conv_lhs => rw [← Nat.mul_div_cancel' he]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast he0) (by exact_mod_cast hb0)]
  rw [Nat.cast_mul,Nat.cast_mul,
    log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hb0),
    log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero),hl]
  ring

/-- Every orbit uses literal original antidiagonal members. -/
theorem orbitDivisors_subset {a R e : ℕ} (ha : 0 < a)
    (hRa : R ∣ a) (he : e ∣ a/R) :
    orbitDivisors a R e ⊆ a.divisorsAntidiagonal := by
  intro db hdb
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
  have hdq := (Nat.dvd_of_mem_divisors hd).trans (block_dvd_quotient hRa he)
  have hed : e*d ∣ a := (Nat.dvd_div_iff_mul_dvd (base_dvd hRa he)).mp hdq
  exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hed,ha.ne'⟩

/-- Coprimality makes the based divisor blocks disjoint, so cancellation
credits cannot count the same original incidence twice. -/
theorem orbitDivisors_disjoint {a R e f : ℕ}
    (hcop : R.Coprime (a/R)) (he : e ∈ (a/R).divisors)
    (hf : f ∈ (a/R).divisors) (hef : e ≠ f) :
    Disjoint (orbitDivisors a R e) (orbitDivisors a R f) := by
  apply Finset.disjoint_left.mpr
  intro db hde hdf
  obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp hde
  obtain ⟨c,hc,hdf⟩ := Finset.mem_image.mp hdf
  have hprod : e*d=f*c := (congrArg Prod.fst hde).trans (congrArg Prod.fst hdf).symm
  have hge : Nat.gcd (e*d) (a/R)=e := by
    rw [mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd
      (hcop.of_dvd_left (Nat.dvd_of_mem_divisors hd)) (Nat.dvd_of_mem_divisors he)
  have hgf : Nat.gcd (f*c) (a/R)=f := by
    rw [mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd
      (hcop.of_dvd_left (Nat.dvd_of_mem_divisors hc)) (Nat.dvd_of_mem_divisors hf)
  exact hef (hge.symm.trans ((congrArg (fun d => Nat.gcd d (a/R)) hprod).trans hgf))

/-- The based blocks partition the entire original divisor antidiagonal.
This does not complete a prime sum or change any label mask. -/
theorem divisorsAntidiagonal_eq_orbits {a R : ℕ} (ha : 0 < a) (hRa : R ∣ a) :
    a.divisorsAntidiagonal = (a/R).divisors.biUnion (orbitDivisors a R) := by
  apply Finset.ext
  intro db
  constructor
  · intro hdb
    have hanti := Nat.mem_divisorsAntidiagonal.mp hdb
    have hd : db.1 ∈ R.divisors*(a/R).divisors := by
      rw [← Nat.divisors_mul,Nat.mul_div_cancel' hRa]
      exact Nat.mem_divisors.mpr ⟨⟨db.2,hanti.1.symm⟩,ha.ne'⟩
    rw [Finset.mul_def] at hd
    obtain ⟨⟨d,e⟩,hde,hprod⟩ := Finset.mem_image.mp hd
    obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
    apply Finset.mem_biUnion.mpr
    refine ⟨e,he,Finset.mem_image.mpr ⟨d,hd,?_⟩⟩
    have heq : e*d=db.1 := (mul_comm e d).trans hprod
    apply Prod.ext
    · exact heq
    · change a/(e*d)=db.2
      rw [heq,← hanti.1]
      exact Nat.mul_div_cancel_left db.2 (Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hdb).1)
  · intro hdb
    obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    exact orbitDivisors_subset ha hRa (Nat.dvd_of_mem_divisors he) hdb

/-- A full based interior block has ZERO signed complex cost. The weight
is still evaluated at `p*a`, not at the smaller auxiliary cofactor `a/e`. -/
theorem weighted_orbit_eq_zero {a p R e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (he : e ∣ a/R)
    (hc : 2 ≤ R.primeFactors.card) {L : ℝ}
    (hR : log R ≤ log (p*a : ℕ)-L-log e)
    (hside : log (p*a : ℕ)-L-log e ≤ log p ∨
      log p+log e+log R ≤ log (p*a : ℕ)-L) (w : ℂ) :
    (∑ db ∈ orbitDivisors a R e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) = 0 := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos (base_dvd hRa he)
    (Nat.pos_of_ne_zero ha.ne_zero)
  rw [orbitDivisors,Finset.sum_image (by
    intro d _ f _ h
    exact Nat.mul_left_cancel he0 (congrArg Prod.fst h))]
  have haq := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hRa he))
  have hl := base_log ha hp (base_dvd hRa he)
  have hhR : log R ≤ log (p*(a/e) : ℕ)-L := by rw [hl]; linarith
  have hhside : log (p*(a/e) : ℕ)-L ≤ log p ∨
      log p+log R ≤ log (p*(a/e) : ℕ)-L := by
    rw [hl]
    rcases hside with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hh := weighted_block_eq_zero haq hp (block_dvd_quotient hRa he) hc hhR hhside w
  simpa only [Nat.div_div_eq_div_mul] using hh

/-- Literal geometry for a complete short-boundary orbit. Both original
hinges and the paid-row cutoff retain their exact endpoints. -/
def ShortOrbit (u : ℝ) (N n R e : ℕ) : Prop :=
  let p := largestPrime n
  let a := n/p
  let T := log (p*a : ℕ)
  let L := SquarefreeVaughanLogSource.length u N
  log e+log R < T-(3899/2000 : ℝ)*N ∧
    log e+log R ≤ T-L ∧
    (T-L-log e ≤ log p ∨ log p+log e+log R ≤ T-L) ∧
    log p < (243/200 : ℝ)*N

/-- All cancelling based orbits, selected inside the original label. -/
def cancelledOrbitDivisors (u : ℝ) (N n : ℕ) : Finset (ℕ×ℕ) :=
  let a := n/largestPrime n
  let R := leastPairBlock a
  if R ∣ a ∧ 2 ≤ R.primeFactors.card then
    ((a/R).divisors.filter (ShortOrbit u N n R)).biUnion (orbitDivisors a R)
  else ∅

/-- The literal core supplies a prime owner and a squarefree composite cofactor. -/
theorem core_data {u : ℝ} {N K n : ℕ} (hn : n ∈ coreBand u N K)
    (hs : Squarefree n) :
    (largestPrime n).Prime ∧ Squarefree (n/largestPrime n) ∧
      2 ≤ (n/largestPrime n).primeFactors.card := by
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hcnt : n.primeFactors.card=(n/largestPrime n).primeFactors.card+1 := by
    conv_lhs => rw [← he,Nat.primeFactors_mul hpp.ne_zero hd.1.ne_zero,
      hpp.primeFactors,Finset.singleton_union,Finset.card_insert_of_notMem
        (show largestPrime n ∉ (n/largestPrime n).primeFactors from
          fun h => hd.2.2.2 (Nat.dvd_of_mem_primeFactors h))]
  exact ⟨hpp,hd.1,by omega⟩

/-- The canonical orbit block and its complement are genuinely coprime,
with exactly two distinct cofactor primes in the block. -/
theorem canonical_block_data {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    let a := n/largestPrime n
    let R := leastPairBlock a
    R ∣ a ∧ R.primeFactors.card=2 ∧ R.Coprime (a/R) := by
  have hd := core_data hn hs
  have hR := leastPairBlock_data hd.2.1 hd.2.2
  have he := Nat.mul_div_cancel' hR.1
  exact ⟨hR.1,hR.2,Nat.coprime_of_squarefree_mul (he.symm ▸ hd.2.1)⟩

/-- The selected union is a suballocation of the actual core label. -/
theorem cancelledOrbitDivisors_subset {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    cancelledOrbitDivisors u N n ⊆ (n/largestPrime n).divisorsAntidiagonal := by
  unfold cancelledOrbitDivisors
  dsimp only
  split_ifs with h
  · intro db hdb
    obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    exact orbitDivisors_subset (Nat.pos_of_ne_zero (core_data hn hs).2.1.ne_zero) h.1
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1) hdb
  · exact Finset.empty_subset _

/-- The enlarged population replaces the previous unit-based blocks.
Their incidences are included once, rather than credited a second time. -/
theorem previous_cancelled_subset {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    cancelledDivisors u N n ⊆ cancelledOrbitDivisors u N n := by
  intro db hdb
  unfold cancelledDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · unfold cancelledOrbitDivisors
    dsimp only
    rw [if_pos ⟨h.1,h.2.1⟩]
    apply Finset.mem_biUnion.mpr
    refine ⟨1,Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,
        ((core_data hn hs).2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd h.1)).ne_zero⟩
    · simpa only [ShortOrbit,Nat.cast_one,log_one,zero_add,sub_zero,add_zero] using
        ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
    · simpa only [orbitDivisors,blockDivisors,one_mul] using hdb
  · simp only [Finset.notMem_empty] at hdb

/-- All complete affine orbits in the original short boundary cancel
jointly at any finite order, height and count cutoff. -/
theorem cancelled_orbit_literal_sum_eq_zero {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    (∑ db ∈ cancelledOrbitDivisors u N n,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ)) = 0 := by
  unfold cancelledOrbitDivisors
  dsimp only
  split_ifs with h
  · have hcop := (canonical_block_data hn hs).2.2
    rw [Finset.sum_biUnion (by
      intro e he f hf hef
      exact orbitDivisors_disjoint hcop (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hef)]
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    exact weighted_orbit_eq_zero (core_data hn hs).2.1 (core_data hn hs).1 h.1
      (Nat.dvd_of_mem_divisors he) h.2 (by linarith [hgeom.2.1]) hgeom.2.2.1 _
  · exact Finset.sum_empty

/-- Every selected orbit stays strictly outside the already paid
owner-gap rows. No geometric error credit is reused. -/
theorem cancelled_orbit_outer_log_gt {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ cancelledOrbitDivisors u N n) :
    (3899/2000 : ℝ)*N < log (largestPrime n*b : ℕ) := by
  unfold cancelledOrbitDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    obtain ⟨delta,hdelta,hpair⟩ := Finset.mem_image.mp hdb
    have hed : e*delta ∣ n/largestPrime n := by
      apply (Nat.dvd_div_iff_mul_dvd (base_dvd h.1 (Nat.dvd_of_mem_divisors he))).mp
      exact (Nat.dvd_of_mem_divisors hdelta).trans
        (block_dvd_quotient h.1 (Nat.dvd_of_mem_divisors he))
    have he0 := Nat.pos_of_mem_divisors he
    have hd0 := Nat.pos_of_mem_divisors hdelta
    have hnatle := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hdelta).2)
      (Nat.dvd_of_mem_divisors hdelta)
    have hle : log delta ≤ log (leastPairBlock (n/largestPrime n)) := log_le_log
      (by exact_mod_cast hd0) (by exact_mod_cast hnatle)
    have hl := base_log (core_data hn hs).2.1 (core_data hn hs).1 hed
    have heb : (n/largestPrime n)/(e*delta)=b := congrArg Prod.snd hpair
    rw [heb] at hl
    have hloged : log (e*delta : ℕ)=log e+log delta := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne') (by exact_mod_cast hd0.ne')]
    rw [hloged] at hl
    linarith [hgeom.1]
  · simp only [Finset.notMem_empty] at hdb

/-- The zero-cost orbits cannot overlap any paid owner-gap row. -/
theorem cancelled_orbit_not_ownerGapRows {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ cancelledOrbitDivisors u N n) :
    (largestPrime n,b) ∉ ownerGapRows u N := by
  intro h
  have hcut := (Finset.mem_filter.mp h).2.2.2.2.2.1
  linarith [cancelled_orbit_outer_log_gt hn hs hdb]

/-- The zero-cost orbits cannot overlap the whole large-owner payment. -/
theorem cancelled_orbit_not_largeOwner {u : ℝ} {N K n d b : ℕ}
    (hdb : (d,b) ∈ cancelledOrbitDivisors u N n) :
    n ∉ ZetaRieszUnifiedSignedRows.largeOwnerLabels u N K := by
  unfold cancelledOrbitDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,_⟩ := Finset.mem_biUnion.mp hdb
    have hP := (Finset.mem_filter.mp he).2.2.2.2
    intro hlarge
    have hcut := (Finset.mem_filter.mp hlarge).2.2.2.2.1
    linarith
  · simp only [Finset.notMem_empty] at hdb

/-- Exact deletion of the full zero-cost interior from the existing
whole carrier; every other original incidence remains signed. -/
theorem coreConvolution_eq_sum_sdiff (u y : ℝ) (N K : ℕ) :
    coreConvolution u y N K =
      ∑ n ∈ (coreBand u N K).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \ cancelledOrbitDivisors u N n,
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
              (largestPrime n) db.2 : ℂ) := by
  unfold coreConvolution
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hcore,hs⟩ := Finset.mem_filter.mp hn
  have he := Finset.sum_sdiff (f := fun db : ℕ×ℕ =>
    phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
      (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ)) (cancelledOrbitDivisors_subset hcore hs)
  rw [cancelled_orbit_literal_sum_eq_zero hcore hs y,add_zero] at he
  exact he.symm

/-- The enlarged ORIGINAL unpaid population costs exactly zero at
source scale, uniformly in every retained height, count and moment order. -/
theorem source_scaled_cancelled_orbits_norm_eq_zero (u y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*
      (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ cancelledOrbitDivisors u N n,
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ))‖ = 0 := by
  have he : (∑ n ∈ (coreBand u N K).filter Squarefree,
      ∑ db ∈ cancelledOrbitDivisors u N n,
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact cancelled_orbit_literal_sum_eq_zero (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2 y
  rw [he,mul_zero,norm_zero]

/-- Any surviving SHORT incidence belongs to an orbit meeting one of
only two boundaries: the paid-row cutoff or the reflected cofactor hinge.
All interior based blocks have already been removed at zero cost. -/
theorem uncancelled_short_orbit_geometry {u : ℝ} {N K n e delta : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hdelta : delta ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (hP : log (largestPrime n) < (243/200 : ℝ)*N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ (3899/2000 : ℝ)*N)
    (hshort : log (e*delta : ℕ) < log n-(3899/2000 : ℝ)*N)
    (hnot : (e*delta,(n/largestPrime n)/(e*delta)) ∉ cancelledOrbitDivisors u N n) :
    (log n-(3899/2000 : ℝ)*N-log (leastPairBlock (n/largestPrime n)) ≤ log e ∧
        log e < log n-(3899/2000 : ℝ)*N) ∨
      (log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-
          log (leastPairBlock (n/largestPrime n)) < log e ∧
        log e < log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N) := by
  have hd := core_data hn hs
  have hblock := canonical_block_data hn hs
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have hc := ZetaRieszJointPrimeEnergy.core_count hn; omega : 2 ≤ n.primeFactors.card)
  have hpa : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hT : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hpa]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast hd.2.1.ne_zero)]
  have hloged : log (e*delta : ℕ)=log e+log delta := by
    rw [Nat.cast_mul,log_mul
      (by exact_mod_cast (Nat.pos_of_mem_divisors he).ne')
      (by exact_mod_cast (Nat.pos_of_mem_divisors hdelta).ne')]
  have heH : log e < log n-(3899/2000 : ℝ)*N := by
    rw [hloged] at hshort
    linarith [log_natCast_nonneg delta]
  by_cases hcut : log e+log (leastPairBlock (n/largestPrime n)) <
      log n-(3899/2000 : ℝ)*N
  · have hcomp : log e+log (leastPairBlock (n/largestPrime n)) ≤
        log n-SquarefreeVaughanLogSource.length u N := by linarith
    have hside : ¬(log n-SquarefreeVaughanLogSource.length u N-log e ≤
        log (largestPrime n) ∨
        log (largestPrime n)+log e+log (leastPairBlock (n/largestPrime n)) ≤
          log n-SquarefreeVaughanLogSource.length u N) := by
      intro hside
      apply hnot
      unfold cancelledOrbitDivisors
      dsimp only
      rw [if_pos ⟨hblock.1,by omega⟩]
      apply Finset.mem_biUnion.mpr
      refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩,Finset.mem_image.mpr ⟨delta,hdelta,rfl⟩⟩
      simpa only [ShortOrbit,hpa] using ⟨hcut,hcomp,hside,hP⟩
    push Not at hside
    right
    exact ⟨by linarith [hside.2],by linarith [hside.1]⟩
  · left
    exact ⟨by linarith [not_lt.mp hcut],heH⟩

/-- The boundary classification applies to EVERY original short
incidence, not just the orbit containing the unsigned unit. -/
theorem uncancelled_short_incidence_geometry {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ (n/largestPrime n).divisorsAntidiagonal)
    (hP : log (largestPrime n) < (243/200 : ℝ)*N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ (3899/2000 : ℝ)*N)
    (hshort : log d < log n-(3899/2000 : ℝ)*N)
    (hnot : (d,b) ∉ cancelledOrbitDivisors u N n) :
    ∃ e delta : ℕ,
      e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors ∧
      delta ∈ (leastPairBlock (n/largestPrime n)).divisors ∧ d=e*delta ∧
      b=(n/largestPrime n)/(e*delta) ∧
      ((log n-(3899/2000 : ℝ)*N-log (leastPairBlock (n/largestPrime n)) ≤ log e ∧
          log e < log n-(3899/2000 : ℝ)*N) ∨
        (log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-
            log (leastPairBlock (n/largestPrime n)) < log e ∧
          log e < log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N)) := by
  have hblock := canonical_block_data hn hs
  rw [divisorsAntidiagonal_eq_orbits
    (Nat.pos_of_ne_zero (core_data hn hs).2.1.ne_zero) hblock.1] at hdb
  obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
  obtain ⟨delta,hdelta,hpair⟩ := Finset.mem_image.mp hdb
  have hde : d=e*delta := (congrArg Prod.fst hpair).symm
  have hbe : b=(n/largestPrime n)/(e*delta) := (congrArg Prod.snd hpair).symm
  have hgeom := uncancelled_short_orbit_geometry hn hs he hdelta hP hL
    (by simpa only [← hde] using hshort) (by rw [← hbe,← hde]; exact hnot)
  exact ⟨e,delta,he,hdelta,hde,hbe,hgeom⟩

/-- When the small block is polynomial, the surviving based crossings
have logarithmic width. This support statement makes no density or
population-norm assertion for either remaining strip. -/
theorem uncancelled_short_orbit_logarithmic_strips {u B : ℝ} {N K n e delta : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hdelta : delta ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (hP : log (largestPrime n) < (243/200 : ℝ)*N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ (3899/2000 : ℝ)*N)
    (hshort : log (e*delta : ℕ) < log n-(3899/2000 : ℝ)*N)
    (hnot : (e*delta,(n/largestPrime n)/(e*delta)) ∉ cancelledOrbitDivisors u N n)
    (hB : log (leastPairBlock (n/largestPrime n)) ≤ B*log ((N : ℝ)+1)) :
    (log n-(3899/2000 : ℝ)*N-B*log ((N : ℝ)+1) ≤ log e ∧
        log e < log n-(3899/2000 : ℝ)*N) ∨
      (log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-
          B*log ((N : ℝ)+1) < log e ∧
        log e < log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N) := by
  rcases uncancelled_short_orbit_geometry hn hs he hdelta hP hL hshort hnot with h | h
  · exact Or.inl ⟨by linarith [h.1],h.2⟩
  · exact Or.inr ⟨by linarith [h.1],h.2⟩

/-- A polynomially small reflected crossing can survive only in this
strict central owner band. The unsigned unit and all other bases obey the
same statement; no arithmetic density assertion enters. -/
theorem reflected_short_owner_bounds {u : ℝ} (hu : 1/2 ≤ u) {N K n e : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hR : log (leastPairBlock (n/largestPrime n)) < (N : ℝ)/2000)
    (he : log e < log n-(3899/2000 : ℝ)*N)
    (hcross : log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-
        log (leastPairBlock (n/largestPrime n)) < log e ∧
      log e < log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N) :
    (9/16 : ℝ)*N < log (largestPrime n) ∧
      log (largestPrime n) < (131/200 : ℝ)*N := by
  have hd := core_data hn hs
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have hc := ZetaRieszJointPrimeEnergy.core_count hn; omega : 2 ≤ n.primeFactors.card)
  have hpa := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hT : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hpa]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast hd.2.1.ne_zero)]
  have hupper : log n ≤ (203/100 : ℝ)*N := (Finset.mem_filter.mp hn).2.2
  have hlength := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : 2*log 2 ≤ (13863/10000 : ℝ) := by linarith [log_two_lt_d9]
  have hLupper := hlength.trans (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg N))
  exact ⟨by linarith [hcross.1,Nat.cast_nonneg (α := ℝ) N],
    by linarith [hcross.2,log_natCast_nonneg e]⟩

/-- The central-band restriction is eventually available from the
original moving length on the whole requested radius interval. Its
starting order is unevaluated, and the central signed cost remains open. -/
theorem eventually_reflected_short_owner_bounds {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ K n e : ℕ, n ∈ coreBand u N K → Squarefree n →
      log (leastPairBlock (n/largestPrime n)) ≤ B*log ((N : ℝ)+1) →
      log e < log n-(3899/2000 : ℝ)*N →
      (log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-
          log (leastPairBlock (n/largestPrime n)) < log e ∧
        log e < log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N) →
      (9/16 : ℝ)*N < log (largestPrime n) ∧
        log (largestPrime n) < (131/200 : ℝ)*N := by
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hl,eventually_logarithmic_block_short B,eventually_ge_atTop 2]
    with N hL hR hN
  intro K n e hn hs hB he hcross
  exact reflected_short_owner_bounds hu hN hn hs (by nlinarith only [hL])
    (hB.trans_lt hR) he hcross

/-- The current exact floor ledger loses no additional budget after
deleting the full cancelling short interior. No new carrier is introduced. -/
theorem ownerGapRemaining_eq_sum_sdiff (u y : ℝ) (j : ℕ) :
    ownerGapRemaining u y j =
      (∑ n ∈ (coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \ cancelledOrbitDivisors u
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n,
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u
              (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge
              (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
              (largestPrime n) db.2 : ℂ)).re-
        (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re-
        (ownerGapLiteralRows u y j+ownerGapEndpointRows u y j) := by
  rw [ownerGapRemaining,coreConvolution_eq_sum_sdiff]

end RiemannGaussian.ZetaRieszShortDivisorOrbits
