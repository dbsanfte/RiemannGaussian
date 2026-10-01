/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPolynomialCutoffRows

/-!
# Restore complete signed blocks across the artificial row cutoff

When the based owner fails the whole-window ownership gap, every member
of its canonical two-prime orbit also fails that gap. The original Riesz
hinges are then saturated, including the members beyond the artificial
short cutoff. Restoring the full orbit cancels exactly. No original phase,
label, allocation, count or physical mask is changed.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCrossingOrbitCancellation
open ZetaRieszSignedConvolution ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszJointAllocation
open ZetaRieszShortDivisorCancellation ZetaRieszShortDivisorOrbits

/-- Every canonical cofactor-prime log is bounded by the original owner
log. No small-prime or polynomial-pair hypothesis is needed. -/
theorem canonical_pair_log_le_twice_owner {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    log (leastPairBlock (n/largestPrime n)) ≤ 2*log (largestPrime n) := by
  have hd := core_data hn hs
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hn; omega : 2 ≤ n.primeFactors.card)
  have hne : n.primeFactors.Nonempty := ⟨largestPrime n,hp⟩
  have hm : n.primeFactors.max' hne=largestPrime n := by
    simp only [largestPrime,dif_pos hne]
  have hmax q (hq : q ∈ (n/largestPrime n).primeFactors) : q ≤ largestPrime n :=
    (Finset.le_max' _ q (Nat.primeFactors_mono
      (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) hs.ne_zero hq)).trans_eq hm
  have hx := ZetaRieszRoughCutoffRows.second_prime_data hd.2.1 hd.2.2
  have hr := hx.2.2.1
  have ht := hx.2.2.2.1
  have hrmem : (n/largestPrime n).minFac ∈ (n/largestPrime n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr,Nat.minFac_dvd _,hd.2.1.ne_zero⟩
  have htmem : ZetaRieszRoughCutoffRows.secondPrime (n/largestPrime n) ∈
      (n/largestPrime n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨ht,
      (Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd _)),hd.2.1.ne_zero⟩
  have hrl : log ((n/largestPrime n).minFac : ℝ) ≤ log (largestPrime n) :=
    log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hmax _ hrmem)
  have htl : log (ZetaRieszRoughCutoffRows.secondPrime (n/largestPrime n)) ≤
      log (largestPrime n) :=
    log_le_log (by exact_mod_cast ht.pos) (by exact_mod_cast hmax _ htmem)
  have hlog : log (leastPairBlock (n/largestPrime n))=
      log (n/largestPrime n).minFac+
        log (ZetaRieszRoughCutoffRows.secondPrime (n/largestPrime n)) := by
    unfold leastPairBlock
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hr.ne_zero) (by exact_mod_cast ht.ne_zero)]
    rfl
  linarith

/-- The based orbit crosses the artificial cutoff and fails the whole
window owner condition. The entire orbit, not its clipped part, is selected. -/
def CrossingOrbit (N n R e : ℕ) : Prop :=
  let p := largestPrime n
  let T := log (p*(n/p) : ℕ)
  log e < T-(3899/2000 : ℝ)*N ∧
    T-(3899/2000 : ℝ)*N ≤ log e+log R ∧
    T-log e+log p ≤ (203/100 : ℝ)*N

/-- Failure of the whole-window ownership gap forces a small owner on
every selected crossing, independently of prime count or roughness. -/
theorem crossing_owner_log_small {N n R e : ℕ} (h : CrossingOrbit N n R e) :
    log (largestPrime n) < (161/2000 : ℝ)*N := by
  dsimp only [CrossingOrbit] at h
  linarith [h.1,h.2.2]

/-- The original two hinges saturate on ALL four members, including
the ones beyond the artificial short cutoff. This is exact geometry. -/
theorem crossing_hinges_saturated {u : ℝ} (hu : 1/2 ≤ u) {N K n e : ℕ}
    (hN : 32 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (h : CrossingOrbit N n (leastPairBlock (n/largestPrime n)) e) :
    log (largestPrime n)+log e+log (leastPairBlock (n/largestPrime n)) ≤
      log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N := by
  have hP := crossing_owner_log_small h
  have hR := canonical_pair_log_le_twice_owner hn hs
  have hL := ZetaRieszCentralPair.length_le_central_lower hu (by omega : 20 ≤ N)
  have he := h.1
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Literal canonical orbits restored across the artificial row cutoff. -/
def crossingDivisors (N n : ℕ) : Finset (ℕ×ℕ) :=
  let a := n/largestPrime n
  let R := leastPairBlock a
  if R ∣ a ∧ 2 ≤ R.primeFactors.card then
    ((a/R).divisors.filter (CrossingOrbit N n R)).biUnion (orbitDivisors a R)
  else ∅

/-- The restored members are actual original cofactor incidences. -/
theorem crossingDivisors_subset {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    crossingDivisors N n ⊆ (n/largestPrime n).divisorsAntidiagonal := by
  unfold crossingDivisors
  dsimp only
  split_ifs with h
  · intro db hdb
    obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    exact orbitDivisors_subset (Nat.pos_of_ne_zero (core_data hn hs).2.1.ne_zero) h.1
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1) hdb
  · exact Finset.empty_subset _

/-- All original masks and the full common complex weight survive this
independent exact cancellation. Orders, heights and counts are unrestricted. -/
theorem crossing_literal_sum_eq_zero {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 32 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n) (w : ℂ) :
    (∑ db ∈ crossingDivisors N n,
      w*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ))=0 := by
  unfold crossingDivisors
  dsimp only
  split_ifs with h
  · rw [Finset.sum_biUnion (by
      intro e he f hf hef
      exact orbitDivisors_disjoint (canonical_block_data hn hs).2.2
        (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef)]
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    have hsat := crossing_hinges_saturated hu hN hn hs hgeom
    exact weighted_orbit_eq_zero (core_data hn hs).2.1 (core_data hn hs).1 h.1
      (Nat.dvd_of_mem_divisors he) h.2
      (by linarith [log_natCast_nonneg (largestPrime n)]) (Or.inr hsat) w
  · exact Finset.sum_empty

/-- Every restored member still fails the previous whole-row owner
condition. Passing the artificial short cutoff creates no paid row overlap. -/
theorem crossing_outer_owner_le {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ crossingDivisors N n) :
    log (largestPrime n*b : ℕ)+log (largestPrime n) ≤ (203/100 : ℝ)*N := by
  unfold crossingDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    obtain ⟨δ,hδ,hpair⟩ := Finset.mem_image.mp hdb
    have hed : e*δ ∣ n/largestPrime n := by
      apply (Nat.dvd_div_iff_mul_dvd (base_dvd h.1 (Nat.dvd_of_mem_divisors he))).mp
      exact (Nat.dvd_of_mem_divisors hδ).trans
        (block_dvd_quotient h.1 (Nat.dvd_of_mem_divisors he))
    have hl := base_log (core_data hn hs).2.1 (core_data hn hs).1 hed
    have hbe : (n/largestPrime n)/(e*δ)=b := congrArg Prod.snd hpair
    rw [hbe] at hl
    have he0 := Nat.pos_of_mem_divisors he
    have hδ0 := Nat.pos_of_mem_divisors hδ
    have hlog : log (e*δ : ℕ)=log e+log δ := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne') (by exact_mod_cast hδ0.ne')]
    rw [hlog] at hl
    linarith [hgeom.2.2,log_natCast_nonneg δ]
  · simp only [Finset.notMem_empty] at hdb

/-- No restored incidence spends a previous closed-row payment. -/
theorem crossing_not_ownerGapRows {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ crossingDivisors N n) :
    (largestPrime n,b) ∉ ZetaRieszOwnerGapRows.ownerGapRows u N := by
  intro hpaid
  have hgap := (Finset.mem_filter.mp hpaid).2.2.2.2.2.2.2.1
  linarith [crossing_outer_owner_le hn hs hdb]

/-- A restored crossing cannot belong to the whole large-owner credit. -/
theorem crossing_not_largeOwner {u : ℝ} {N K n d b : ℕ}
    (hdb : (d,b) ∈ crossingDivisors N n) :
    n ∉ ZetaRieszUnifiedSignedRows.largeOwnerLabels u N K := by
  unfold crossingDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,_⟩ := Finset.mem_biUnion.mp hdb
    have hP := crossing_owner_log_small (Finset.mem_filter.mp he).2
    intro hlarge
    have hcut := (Finset.mem_filter.mp hlarge).2.2.2.2.1
    linarith [Nat.cast_nonneg (α := ℝ) N]
  · simp only [Finset.notMem_empty] at hdb

/-- A crossing with the failed based-owner gap restores every canonical
member. This includes both previously surviving clipped edges. -/
theorem crossing_orbit_membership {u : ℝ} {N K n e δ : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hδ : δ ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (h : CrossingOrbit N n (leastPairBlock (n/largestPrime n)) e) :
    (e*δ,(n/largestPrime n)/(e*δ)) ∈ crossingDivisors N n := by
  have hblock := canonical_block_data hn hs
  unfold crossingDivisors
  dsimp only
  rw [if_pos ⟨hblock.1,by omega⟩]
  exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_filter.mpr ⟨he,h⟩,
    Finset.mem_image.mpr ⟨δ,hδ,rfl⟩⟩

/-- The newly restored crossings and the old short-interior zero blocks
are disjoint original incidence populations, not repeated zero credits. -/
theorem crossing_disjoint_old_cancelled {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    Disjoint (crossingDivisors N n) (cancelledOrbitDivisors u N n) := by
  have hblock := canonical_block_data hn hs
  unfold crossingDivisors cancelledOrbitDivisors
  dsimp only
  rw [if_pos ⟨hblock.1,by omega⟩,if_pos ⟨hblock.1,by omega⟩]
  apply Finset.disjoint_left.mpr
  intro db hnew hold
  obtain ⟨e,he,hnew⟩ := Finset.mem_biUnion.mp hnew
  obtain ⟨f,hf,hold⟩ := Finset.mem_biUnion.mp hold
  by_cases hef : e=f
  · have hc := (Finset.mem_filter.mp he).2.2.1
    have ho := (Finset.mem_filter.mp hf).2.1
    rw [hef] at hc
    linarith
  · exact Finset.disjoint_left.mp
      (orbitDivisors_disjoint hblock.2.2 (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hef) hnew hold

/-- The complete ORIGINAL restored-crossing population has zero norm
at source scale. No count-by-count allowance, zero premise or height
bound enters; every complex observation is still at its original label. -/
theorem source_scaled_crossing_population_norm_eq_zero {u : ℝ} (hu : 1/2 ≤ u)
    {N : ℕ} (hN : 32 ≤ N) (K : ℕ) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*
      (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ crossingDivisors N n,
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ))‖=0 := by
  have hz : (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ crossingDivisors N n,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact crossing_literal_sum_eq_zero hu hN (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2 _
  rw [hz,mul_zero,norm_zero]

/-- No based short-cutoff crossing can remain with a failed whole-row
owner gap after exact restoration. This applies even to rough pairs. -/
theorem uncancelled_cutoff_owner_gap {u : ℝ} {N K n e δ : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hδ : δ ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (hshort : log e < log (largestPrime n*(n/largestPrime n) : ℕ)-(3899/2000 : ℝ)*N)
    (hcross : log (largestPrime n*(n/largestPrime n) : ℕ)-(3899/2000 : ℝ)*N ≤
      log e+log (leastPairBlock (n/largestPrime n)))
    (hnot : (e*δ,(n/largestPrime n)/(e*δ)) ∉ crossingDivisors N n) :
    (203/100 : ℝ)*N < log (largestPrime n*(n/largestPrime n) : ℕ)-log e+
      log (largestPrime n) := by
  by_contra hgap
  exact hnot (crossing_orbit_membership hn hs he hδ
    ⟨hshort,hcross,le_of_not_gt hgap⟩)

/-- Any cutoff crossing surviving restoration has a fixed positive
owner-log share, even for arbitrary rough pairs. This is support only. -/
theorem remaining_cutoff_owner_lower {u : ℝ} {N K n e δ : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hδ : δ ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (hshort : log e < log (largestPrime n*(n/largestPrime n) : ℕ)-(3899/2000 : ℝ)*N)
    (hcross : log (largestPrime n*(n/largestPrime n) : ℕ)-(3899/2000 : ℝ)*N ≤
      log e+log (leastPairBlock (n/largestPrime n)))
    (hnot : (e*δ,(n/largestPrime n)/(e*δ)) ∉ crossingDivisors N n) :
    (161/6000 : ℝ)*N < log (largestPrime n) := by
  have hgap := uncancelled_cutoff_owner_gap hn hs he hδ hshort hcross hnot
  have hR := canonical_pair_log_le_twice_owner hn hs
  linarith

/-- Exact incidence recovery for a based original block. No prime or
label completion enters this finite arithmetic identity. -/
theorem based_orbit_data {a B e R δ : ℕ} (ha : 0 < a) (hprod : a=B*e)
    (hRB : R ∣ B) (hδ : δ ∈ R.divisors) :
    e ∈ (a/R).divisors ∧ (e*δ,B/δ) ∈ orbitDivisors a R e := by
  have hBe : 0 < B*e := hprod ▸ ha
  have hb : 0 < B := Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hBe.ne').1
  have he : 0 < e := Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hBe.ne').2
  have hR : 0 < R := Nat.pos_of_dvd_of_pos hRB hb
  have hRa : R ∣ a := hprod ▸ hRB.trans (dvd_mul_right B e)
  have hed : e ∣ a/R := by
    apply (Nat.dvd_div_iff_mul_dvd hRa).mpr
    rw [hprod]
    exact Nat.mul_dvd_mul hRB (dvd_refl e)
  have haq : a/R ≠ 0 := (Nat.div_pos (Nat.le_of_dvd ha hRa) hR).ne'
  have hq : a/(e*δ)=B/δ := by
    rw [← Nat.div_div_eq_div_mul,hprod,mul_comm B e,Nat.mul_div_cancel_left _ he]
  exact ⟨Nat.mem_divisors.mpr ⟨hed,haq⟩,
    Finset.mem_image.mpr ⟨δ,hδ,by simp only [hq]⟩⟩

/-- Every original clipped crossing with failed whole-window ownership
is contained in a newly restored ZERO block, even for rough canonical
pairs. Its beyond-cutoff members are retained rather than norm-paid. -/
theorem original_crossing_cancelled_of_owner_gap_failure {u : ℝ} {N K p B e δ : ℕ}
    (hn : p*(B*e) ∈ coreBand u N K) (hs : Squarefree (p*(B*e)))
    (howner : largestPrime (p*(B*e))=p)
    (hR : leastPairBlock (B*e) ∣ B) (hδ : δ ∈ (leastPairBlock (B*e)).divisors)
    (hshort : log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N)
    (hcross : log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log (leastPairBlock (B*e)))
    (hgap : log (p*B : ℕ)+log p ≤ (203/100 : ℝ)*N) :
    (e*δ,B/δ) ∈ crossingDivisors N (p*(B*e)) := by
  have hd := core_data hn hs
  have hp : p.Prime := howner ▸ hd.1
  have ha : Squarefree (B*e) := (Nat.squarefree_mul_iff.mp hs).2.2
  have hdata := based_orbit_data (Nat.pos_of_ne_zero ha.ne_zero) rfl hR hδ
  have he0 := Nat.pos_of_ne_zero (mul_ne_zero_iff.mp ha.ne_zero).2
  have hb0 := Nat.pos_of_ne_zero (mul_ne_zero_iff.mp ha.ne_zero).1
  have hlog : log (p*(B*e) : ℕ)=log (p*B : ℕ)+log e := by
    rw [← mul_assoc,Nat.cast_mul,log_mul
      (by exact_mod_cast (Nat.mul_pos hp.pos hb0).ne') (by exact_mod_cast he0.ne')]
  have hlogeδ : log (e*δ : ℕ)=log e+log δ := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne')
      (by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne')]
  have hecut : log e < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N := by
    rw [hlogeδ] at hshort
    linarith [log_natCast_nonneg δ]
  have hgeom : CrossingOrbit N (p*(B*e)) (leastPairBlock (B*e)) e := by
    simpa only [CrossingOrbit,howner,Nat.mul_div_cancel_left _ hp.pos] using
      (show log e < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ∧
        log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log (leastPairBlock (B*e)) ∧
        log (p*(B*e) : ℕ)-log e+log p ≤ (203/100 : ℝ)*N from
        ⟨hecut,hcross,by rw [hlog]; linarith⟩)
  have hh := crossing_orbit_membership hn hs
    (by simpa only [howner,Nat.mul_div_cancel_left _ hp.pos] using hdata.1)
    (by simpa only [howner,Nat.mul_div_cancel_left _ hp.pos] using hδ)
    (by simpa only [howner,Nat.mul_div_cancel_left _ hp.pos] using hgeom)
  have hquot : (B*e)/(e*δ)=B/δ := by
    rw [← Nat.div_div_eq_div_mul,mul_comm B e,Nat.mul_div_cancel_left _ he0]
  simpa only [howner,Nat.mul_div_cancel_left _ hp.pos,hquot] using hh

/-- A literal incidence selected by the independently paid polynomial
packet cannot also be in a restored crossing. Canonicity identifies its
base before the contradictory whole-window owner conditions are compared. -/
theorem polynomial_paid_incidence_not_crossing {u : ℝ} {N K : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hr : pb ∈ ZetaRieszPolynomialCutoffRows.cutoffRows u N) {e δ : ℕ}
    (he : e ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))
    (hsieve : ZetaRieszUnsignedDivisorError.sieve (ZetaRieszRoughCutoffRows.forbidden pb.1 pb.2) e ≠ 0)
    (hδ : δ ∈ ZetaRieszRoughCutoffRows.cutoffDivisors N pb.1 pb.2)
    (hn : pb.1*(pb.2*e) ∈ coreBand u N K) :
    (e*δ,pb.2/δ) ∉ crossingDivisors N (pb.1*(pb.2*e)) := by
  have hi := ZetaRieszPolynomialCutoffRows.cutoff_original_incidence hN hr he hsieve hδ
  have hg := ZetaRieszPolynomialCutoffRows.cutoff_row_geometry hr
  have he0 : 0 < e := hg.2.2.2.2.2.2.1.trans_le (Finset.mem_Icc.mp he).1
  obtain ⟨_,hB,_,_,_,_,_,hgap,_,hcount,_,_,_⟩ := Finset.mem_filter.mp hr
  have htag : ZetaRieszRoughCutoffRows.roughTag pb.2 e ≠ 0 :=
    (mul_ne_zero_iff.mp ((ZetaRieszRoughCutoffRows.sieve_forbidden pb.1 pb.2 e) ▸ hsieve)).2
  have hcanon := ZetaRieszRoughCutoffRows.leastPairBlock_original hB hcount he0 htag
  have hRB : leastPairBlock (pb.2*e) ∣ pb.2 :=
    hcanon ▸ (leastPairBlock_data hB hcount).1
  have hδR : δ ∈ (leastPairBlock (pb.2*e)).divisors := by
    rw [hcanon]
    exact (Finset.mem_filter.mp hδ).1
  have hBe := (Nat.squarefree_mul_iff.mp hi.1).2.2
  have hbdata := based_orbit_data (Nat.pos_of_ne_zero hBe.ne_zero) rfl hRB hδR
  have hblock := canonical_block_data hn hi.1
  intro hnew
  unfold crossingDivisors at hnew
  dsimp only at hnew
  rw [if_pos ⟨hblock.1,by omega⟩] at hnew
  obtain ⟨f,hf,hnew⟩ := Finset.mem_biUnion.mp hnew
  have hfmem := (Finset.mem_filter.mp hf).1
  have hemost : e ∈ ((pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))/
      leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))).divisors := by
    simpa only [hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] using hbdata.1
  have heinc : (e*δ,pb.2/δ) ∈ orbitDivisors
      (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))
      (leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))) e := by
    simpa only [hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] using hbdata.2
  have hfe : f=e := by
    by_contra hne
    exact Finset.disjoint_left.mp
      (orbitDivisors_disjoint hblock.2.2 hfmem hemost hne) hnew heinc
  have hfailed := (Finset.mem_filter.mp hf).2.2.2
  rw [hfe,hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] at hfailed
  have hlog : log (pb.1*(pb.2*e) : ℕ)=log (pb.1*pb.2 : ℕ)+log e := by
    rw [← mul_assoc,Nat.cast_mul,log_mul
      (by exact_mod_cast (Nat.mul_pos hg.1.pos (Nat.pos_of_ne_zero hB.ne_zero)).ne')
      (by exact_mod_cast he0.ne')]
  linarith

/-- Every active canonical short-cutoff crossing in the polynomial cap
is now either independently paid or part of a restored exact zero block.
There is no residual tiny-owner or fixed-count exception in this dichotomy. -/
theorem eventually_polynomial_crossing_paid_or_cancelled (u : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ K p B e δ : ℕ,
      p*(B*e) ∈ coreBand u N K → Squarefree (p*(B*e)) →
      p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N → largestPrime (p*(B*e))=p →
      leastPairBlock (B*e) ∣ B → δ ∈ (leastPairBlock (B*e)).divisors →
      log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N →
      log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log (leastPairBlock (B*e)) →
      log p < (243/200 : ℝ)*N → ZetaRieszRoughCutoffRows.secondPrime B ≤ N^2 →
      pairHinge (SquarefreeVaughanLogSource.length u N) p (B/δ) ≠ 0 →
      ((p,B) ∈ ZetaRieszPolynomialCutoffRows.cutoffRows u N ∧
        e ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N p B)
          (ZetaRieszFineDivisorRows.upper N p B) ∧
        δ ∈ ZetaRieszRoughCutoffRows.cutoffDivisors N p B ∧
        ZetaRieszUnsignedDivisorError.sieve (ZetaRieszRoughCutoffRows.forbidden p B) e=1) ∨
      (e*δ,B/δ) ∈ crossingDivisors N (p*(B*e)) := by
  filter_upwards [ZetaRieszPolynomialCutoffRows.eventually_polynomial_cutoff_gap] with N hsize
  intro K p B e δ hn hs hp howner hR hδ hshort hcross hP hsmall hH
  by_cases hgap : (203/100 : ℝ)*N < log (p*B : ℕ)+log p
  · exact Or.inl (ZetaRieszPolynomialCutoffRows.cutoff_crossing_covered
      hn hs hp howner hR hδ hshort hcross hgap hP hsmall hsize hH)
  · exact Or.inr (original_crossing_cancelled_of_owner_gap_failure
      hn hs howner hR hδ hshort hcross (le_of_not_gt hgap))

/-- Both old interior and restored crossing blocks can be removed
jointly from the ORIGINAL sum at exactly zero cost. -/
theorem literal_union_sum_eq_zero {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 32 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    (∑ db ∈ cancelledOrbitDivisors u N n ∪ crossingDivisors N n,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ))=0 := by
  rw [Finset.sum_union (crossing_disjoint_old_cancelled hn hs).symm,
    cancelled_orbit_literal_sum_eq_zero hn hs y,
    crossing_literal_sum_eq_zero hu hN hn hs,add_zero]

/-- Literal owner atom after exact joint zero-block deletion. Every
factor is still evaluated at the same original physical label. -/
theorem owner_atom_eq_sum_sdiff {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 32 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
          (cancelledOrbitDivisors u N n ∪ crossingDivisors N n),
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ) := by
  have hd := core_data hn hs
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hco := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have hpa : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hr := residual_atom_eq_convolution hd.2.1 hd.2.2 hd.1 hco.2.2.2
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
    (SquarefreeVaughanLogSource.length u N) y N
  rw [hpa] at hr
  rw [hr]
  have hsub : cancelledOrbitDivisors u N n ∪ crossingDivisors N n ⊆
      (n/largestPrime n).divisorsAntidiagonal :=
    Finset.union_subset (cancelledOrbitDivisors_subset hn hs) (crossingDivisors_subset hn hs)
  have he := Finset.sum_sdiff (f := fun db : ℕ×ℕ =>
    phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
      (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ)) hsub
  rw [literal_union_sum_eq_zero hu hN hn hs y,add_zero] at he
  exact he.symm

/-- The CURRENT central main loses the new population at zero cost,
before any real-part bound and with its exact original count/radial masks. -/
theorem centralConvolution_eq_sum_sdiff {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ}
    (hN : 32 ≤ N) (K : ℕ) (y : ℝ) :
    ZetaRieszLowerRadialPayment.centralConvolution u y N K =
      ∑ n ∈ ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
            (cancelledOrbitDivisors u N n ∪ crossingDivisors N n),
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
              (largestPrime n) db.2 : ℂ) := by
  have hf : (∑ n ∈ ((coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ZetaRieszLowerRadialPayment.centralConvolution u y N K := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n _ hnot
    have hns : ¬Squarefree n := fun h => hnot (Finset.mem_filter.mpr ⟨by assumption,h⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hns]
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hcore,hs⟩ := Finset.mem_filter.mp hn
  exact owner_atom_eq_sum_sdiff hu hN (Finset.mem_filter.mp hcore).1 hs y

/-- Exact deletion in the present floor ledger. All previous comparison
credits keep their original supports and budget, without a new allowance. -/
theorem polynomialCentralRemaining_eq_sum_sdiff {u : ℝ} (hu : 1/2 ≤ u)
    (y : ℝ) (j : ℕ) (hN : 32 ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :
    let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
    let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
    ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j =
      (∑ n ∈ ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
            (cancelledOrbitDivisors u N n ∪ crossingDivisors N n),
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
              (largestPrime n) db.2 : ℂ)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+
        ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j := by
  dsimp only
  rw [ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining_eq,
    centralConvolution_eq_sum_sdiff hu hN]

/-- Complete affine blocks outside the earlier short-interior selector,
whose based owner fails the whole-window condition. There is no artificial
cutoff condition and no restriction on the sizes of the two block primes. -/
def UnpaidAffineOrbit (u : ℝ) (N n R e : ℕ) : Prop :=
  let p := largestPrime n
  let T := log (p*(n/p) : ℕ)
  let L := SquarefreeVaughanLogSource.length u N
  log e+log R ≤ T-L ∧
    (T-L-log e ≤ log p ∨ log p+log e+log R ≤ T-L) ∧
    log p < (243/200 : ℝ)*N ∧
    T-log e+log p ≤ (203/100 : ℝ)*N ∧
    ¬ShortOrbit u N n R e

/-- The enlarged zero population consists only of original incidences. -/
def affineDivisors (u : ℝ) (N n : ℕ) : Finset (ℕ×ℕ) :=
  let a := n/largestPrime n
  let R := leastPairBlock a
  if R ∣ a ∧ 2 ≤ R.primeFactors.card then
    ((a/R).divisors.filter (UnpaidAffineOrbit u N n R)).biUnion (orbitDivisors a R)
  else ∅

/-- Every newly selected affine member remains in the original antidiagonal. -/
theorem affineDivisors_subset {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    affineDivisors u N n ⊆ (n/largestPrime n).divisorsAntidiagonal := by
  unfold affineDivisors
  dsimp only
  split_ifs with h
  · intro db hdb
    obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    exact orbitDivisors_subset (Nat.pos_of_ne_zero (core_data hn hs).2.1.ne_zero) h.1
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1) hdb
  · exact Finset.empty_subset _

/-- The enlarged signed population cancels at exactly zero cost, with
any common original complex weight. No radius, order or zero premise enters. -/
theorem affine_literal_sum_eq_zero {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (w : ℂ) :
    (∑ db ∈ affineDivisors u N n,
      w*(μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ))=0 := by
  unfold affineDivisors
  dsimp only
  split_ifs with h
  · rw [Finset.sum_biUnion (by
      intro e he f hf hef
      exact orbitDivisors_disjoint (canonical_block_data hn hs).2.2
        (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef)]
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    exact weighted_orbit_eq_zero (core_data hn hs).2.1 (core_data hn hs).1 h.1
      (Nat.dvd_of_mem_divisors he) h.2 (by linarith [hgeom.1]) hgeom.2.1 w
  · exact Finset.sum_empty

/-- The new affine selector excludes every previously deleted interior
block, so enlarging the zero population never counts a credit twice. -/
theorem affine_disjoint_old_cancelled {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    Disjoint (affineDivisors u N n) (cancelledOrbitDivisors u N n) := by
  have hblock := canonical_block_data hn hs
  unfold affineDivisors cancelledOrbitDivisors
  dsimp only
  rw [if_pos ⟨hblock.1,by omega⟩,if_pos ⟨hblock.1,by omega⟩]
  apply Finset.disjoint_left.mpr
  intro db hnew hold
  obtain ⟨e,he,hnew⟩ := Finset.mem_biUnion.mp hnew
  obtain ⟨f,hf,hold⟩ := Finset.mem_biUnion.mp hold
  by_cases hef : e=f
  · have hnot := (Finset.mem_filter.mp he).2.2.2.2.2
    rw [hef] at hnot
    exact hnot (Finset.mem_filter.mp hf).2
  · exact Finset.disjoint_left.mp
      (orbitDivisors_disjoint hblock.2.2 (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hef) hnew hold

/-- Restored artificial-cutoff crossings are included in the enlarged
affine population. The previous exact zero credit is replaced, not added. -/
theorem crossingDivisors_subset_affine {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 32 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    crossingDivisors N n ⊆ affineDivisors u N n := by
  have hblock := canonical_block_data hn hs
  unfold crossingDivisors affineDivisors
  dsimp only
  rw [if_pos ⟨hblock.1,by omega⟩,if_pos ⟨hblock.1,by omega⟩]
  intro db hdb
  obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
  obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
  apply Finset.mem_biUnion.mpr
  refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩,hdb⟩
  have hsat := crossing_hinges_saturated hu hN hn hs hgeom
  have hP := crossing_owner_log_small hgeom
  have hnot : ¬ShortOrbit u N n (leastPairBlock (n/largestPrime n)) e := by
    intro hold
    linarith [hold.1,hgeom.2.1]
  exact ⟨by linarith [log_natCast_nonneg (largestPrime n)],Or.inr hsat,
    by linarith [Nat.cast_nonneg (α := ℝ) N],hgeom.2.2,hnot⟩

/-- Every restored long member also fails the whole-window owner
condition; it cannot spend any closed-row comparison payment. -/
theorem affine_outer_owner_le {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ affineDivisors u N n) :
    log (largestPrime n*b : ℕ)+log (largestPrime n) ≤ (203/100 : ℝ)*N := by
  unfold affineDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,hdb⟩ := Finset.mem_biUnion.mp hdb
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    obtain ⟨δ,hδ,hpair⟩ := Finset.mem_image.mp hdb
    have hed : e*δ ∣ n/largestPrime n := by
      apply (Nat.dvd_div_iff_mul_dvd (base_dvd h.1 (Nat.dvd_of_mem_divisors he))).mp
      exact (Nat.dvd_of_mem_divisors hδ).trans
        (block_dvd_quotient h.1 (Nat.dvd_of_mem_divisors he))
    have hl := base_log (core_data hn hs).2.1 (core_data hn hs).1 hed
    have hbe : (n/largestPrime n)/(e*δ)=b := congrArg Prod.snd hpair
    rw [hbe] at hl
    have he0 := Nat.pos_of_mem_divisors he
    have hδ0 := Nat.pos_of_mem_divisors hδ
    have hlog : log (e*δ : ℕ)=log e+log δ := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne') (by exact_mod_cast hδ0.ne')]
    rw [hlog] at hl
    linarith [hgeom.2.2.2.1,log_natCast_nonneg δ]
  · simp only [Finset.notMem_empty] at hdb

/-- The enlarged zero population is disjoint from the existing owner-gap credit. -/
theorem affine_not_ownerGapRows {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ affineDivisors u N n) :
    (largestPrime n,b) ∉ ZetaRieszOwnerGapRows.ownerGapRows u N := by
  intro hpaid
  have hgap := (Finset.mem_filter.mp hpaid).2.2.2.2.2.2.2.1
  linarith [affine_outer_owner_le hn hs hdb]

/-- The whole large-owner payment is also disjoint from every new affine block. -/
theorem affine_not_largeOwner {u : ℝ} {N K n d b : ℕ}
    (hdb : (d,b) ∈ affineDivisors u N n) :
    n ∉ ZetaRieszUnifiedSignedRows.largeOwnerLabels u N K := by
  unfold affineDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,_⟩ := Finset.mem_biUnion.mp hdb
    have hP := (Finset.mem_filter.mp he).2.2.2.1
    intro hlarge
    have hcut := (Finset.mem_filter.mp hlarge).2.2.2.2.1
    linarith
  · simp only [Finset.notMem_empty] at hdb

/-- A paid canonical polynomial-cutoff incidence cannot belong to an
unpaid affine block. The original canonical base is identified exactly
before comparing the opposite whole-window owner inequalities. -/
theorem polynomial_paid_incidence_not_affine {u : ℝ} {N K : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hr : pb ∈ ZetaRieszPolynomialCutoffRows.cutoffRows u N) {e δ : ℕ}
    (he : e ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))
    (hsieve : ZetaRieszUnsignedDivisorError.sieve (ZetaRieszRoughCutoffRows.forbidden pb.1 pb.2) e ≠ 0)
    (hδ : δ ∈ ZetaRieszRoughCutoffRows.cutoffDivisors N pb.1 pb.2)
    (hn : pb.1*(pb.2*e) ∈ coreBand u N K) :
    (e*δ,pb.2/δ) ∉ affineDivisors u N (pb.1*(pb.2*e)) := by
  have hi := ZetaRieszPolynomialCutoffRows.cutoff_original_incidence hN hr he hsieve hδ
  have hg := ZetaRieszPolynomialCutoffRows.cutoff_row_geometry hr
  have he0 : 0 < e := hg.2.2.2.2.2.2.1.trans_le (Finset.mem_Icc.mp he).1
  obtain ⟨_,hB,_,_,_,_,_,hgap,_,hcount,_,_,_⟩ := Finset.mem_filter.mp hr
  have htag : ZetaRieszRoughCutoffRows.roughTag pb.2 e ≠ 0 :=
    (mul_ne_zero_iff.mp ((ZetaRieszRoughCutoffRows.sieve_forbidden pb.1 pb.2 e) ▸ hsieve)).2
  have hcanon := ZetaRieszRoughCutoffRows.leastPairBlock_original hB hcount he0 htag
  have hRB : leastPairBlock (pb.2*e) ∣ pb.2 :=
    hcanon ▸ (leastPairBlock_data hB hcount).1
  have hδR : δ ∈ (leastPairBlock (pb.2*e)).divisors := by
    rw [hcanon]
    exact (Finset.mem_filter.mp hδ).1
  have hBe := (Nat.squarefree_mul_iff.mp hi.1).2.2
  have hbdata := based_orbit_data (Nat.pos_of_ne_zero hBe.ne_zero) rfl hRB hδR
  have hblock := canonical_block_data hn hi.1
  intro hnew
  unfold affineDivisors at hnew
  dsimp only at hnew
  rw [if_pos ⟨hblock.1,by omega⟩] at hnew
  obtain ⟨f,hf,hnew⟩ := Finset.mem_biUnion.mp hnew
  have hfmem := (Finset.mem_filter.mp hf).1
  have hemost : e ∈ ((pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))/
      leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))).divisors := by
    simpa only [hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] using hbdata.1
  have heinc : (e*δ,pb.2/δ) ∈ orbitDivisors
      (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))
      (leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))) e := by
    simpa only [hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] using hbdata.2
  have hfe : f=e := by
    by_contra hne
    exact Finset.disjoint_left.mp
      (orbitDivisors_disjoint hblock.2.2 hfmem hemost hne) hnew heinc
  have hfailed := (Finset.mem_filter.mp hf).2.2.2.2.1
  rw [hfe,hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] at hfailed
  have hlog : log (pb.1*(pb.2*e) : ℕ)=log (pb.1*pb.2 : ℕ)+log e := by
    rw [← mul_assoc,Nat.cast_mul,log_mul
      (by exact_mod_cast (Nat.mul_pos hg.1.pos (Nat.pos_of_ne_zero hB.ne_zero)).ne')
      (by exact_mod_cast he0.ne')]
  linarith

/-- The complete enlarged ORIGINAL population has zero source-scaled
norm at every height, order and count cutoff, without a zero hypothesis. -/
theorem source_scaled_affine_population_norm_eq_zero (u y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*
      (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ affineDivisors u N n,
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ))‖=0 := by
  have hz : (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ affineDivisors u N n,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact affine_literal_sum_eq_zero (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2 _
  rw [hz,mul_zero,norm_zero]

/-- Every affine orbit with a failed based owner gap is removed, even
when it lies far beyond the artificial short cutoff. -/
theorem affine_membership_or_old {u : ℝ} {N K n e δ : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hδ : δ ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (hR : log e+log (leastPairBlock (n/largestPrime n)) ≤
      log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N)
    (hside : log (largestPrime n*(n/largestPrime n) : ℕ)-
        SquarefreeVaughanLogSource.length u N-log e ≤ log (largestPrime n) ∨
      log (largestPrime n)+log e+log (leastPairBlock (n/largestPrime n)) ≤
        log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N)
    (hP : log (largestPrime n) < (243/200 : ℝ)*N)
    (hgap : log (largestPrime n*(n/largestPrime n) : ℕ)-log e+log (largestPrime n) ≤
      (203/100 : ℝ)*N) :
    (e*δ,(n/largestPrime n)/(e*δ)) ∈
      cancelledOrbitDivisors u N n ∪ affineDivisors u N n := by
  have hblock := canonical_block_data hn hs
  by_cases hshort : ShortOrbit u N n (leastPairBlock (n/largestPrime n)) e
  · apply Finset.mem_union_left
    unfold cancelledOrbitDivisors
    dsimp only
    rw [if_pos ⟨hblock.1,by omega⟩]
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hshort⟩,
      Finset.mem_image.mpr ⟨δ,hδ,rfl⟩⟩
  · apply Finset.mem_union_right
    unfold affineDivisors
    dsimp only
    rw [if_pos ⟨hblock.1,by omega⟩]
    exact Finset.mem_biUnion.mpr ⟨e,
      Finset.mem_filter.mpr ⟨he,⟨hR,hside,hP,hgap,hshort⟩⟩,
      Finset.mem_image.mpr ⟨δ,hδ,rfl⟩⟩

/-- A surviving complete nonzero-hinge block with the failed owner gap
must now meet the actual Riesz hinge. This is support, not a floor claim. -/
theorem remaining_affine_hinge_crossing {u : ℝ} {N K n e δ : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hδ : δ ∈ (leastPairBlock (n/largestPrime n)).divisors)
    (hR : log e+log (leastPairBlock (n/largestPrime n)) ≤
      log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N)
    (hP : log (largestPrime n) < (243/200 : ℝ)*N)
    (hgap : log (largestPrime n*(n/largestPrime n) : ℕ)-log e+log (largestPrime n) ≤
      (203/100 : ℝ)*N)
    (hnot : (e*δ,(n/largestPrime n)/(e*δ)) ∉
      cancelledOrbitDivisors u N n ∪ affineDivisors u N n) :
    log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N-
        log (largestPrime n)-log (leastPairBlock (n/largestPrime n)) < log e ∧
      log e < log (largestPrime n*(n/largestPrime n) : ℕ)-
        SquarefreeVaughanLogSource.length u N-log (largestPrime n) := by
  have hside : ¬(log (largestPrime n*(n/largestPrime n) : ℕ)-
        SquarefreeVaughanLogSource.length u N-log e ≤ log (largestPrime n) ∨
      log (largestPrime n)+log e+log (leastPairBlock (n/largestPrime n)) ≤
        log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N) := by
    intro hside
    exact hnot (affine_membership_or_old hn hs he hδ hR hside hP hgap)
  push Not at hside
  constructor <;> linarith [hside.1,hside.2]

/-- The enlarged zero population and old interior cancel jointly before
any real-part or norm estimate. -/
theorem affine_union_sum_eq_zero {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    (∑ db ∈ cancelledOrbitDivisors u N n ∪ affineDivisors u N n,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ))=0 := by
  rw [Finset.sum_union (affine_disjoint_old_cancelled hn hs).symm,
    cancelled_orbit_literal_sum_eq_zero hn hs y,
    affine_literal_sum_eq_zero hn hs,add_zero]

/-- Exact enlargement of zero deletion in the SAME current central
owner atom, retaining the common phase and every literal mask. -/
theorem owner_atom_eq_affine_sdiff {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
          (cancelledOrbitDivisors u N n ∪ affineDivisors u N n),
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ) := by
  have hd := core_data hn hs
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hco := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have hpa : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hr := residual_atom_eq_convolution hd.2.1 hd.2.2 hd.1 hco.2.2.2
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
    (SquarefreeVaughanLogSource.length u N) y N
  rw [hpa] at hr
  rw [hr]
  have hsub : cancelledOrbitDivisors u N n ∪ affineDivisors u N n ⊆
      (n/largestPrime n).divisorsAntidiagonal :=
    Finset.union_subset (cancelledOrbitDivisors_subset hn hs) (affineDivisors_subset hn hs)
  have he := Finset.sum_sdiff (f := fun db : ℕ×ℕ =>
    phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
      (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ)) hsub
  rw [affine_union_sum_eq_zero hn hs y,add_zero] at he
  exact he.symm

/-- The whole current central carrier omits ALL these affine populations
at zero cost. No selected prime count or radial period is estimated alone. -/
theorem centralConvolution_eq_affine_sdiff (u y : ℝ) (N K : ℕ) :
    ZetaRieszLowerRadialPayment.centralConvolution u y N K =
      ∑ n ∈ ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
            (cancelledOrbitDivisors u N n ∪ affineDivisors u N n),
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
              (largestPrime n) db.2 : ℂ) := by
  have hf : (∑ n ∈ ((coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ZetaRieszLowerRadialPayment.centralConvolution u y N K := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n _ hnot
    have hns : ¬Squarefree n := fun h => hnot (Finset.mem_filter.mpr ⟨by assumption,h⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hns]
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hcore,hs⟩ := Finset.mem_filter.mp hn
  exact owner_atom_eq_affine_sdiff (Finset.mem_filter.mp hcore).1 hs y

/-- Direct zero-cost saving in the existing floor ledger, with no new
carrier or error allowance and no change to previous whole-row supports. -/
theorem polynomialCentralRemaining_eq_affine_sdiff (u y : ℝ) (j : ℕ) :
    let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
    let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
    ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j =
      (∑ n ∈ ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
            (cancelledOrbitDivisors u N n ∪ affineDivisors u N n),
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
              (largestPrime n) db.2 : ℂ)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+
        ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j := by
  dsimp only
  rw [ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining_eq,
    centralConvolution_eq_affine_sdiff]

end RiemannGaussian.ZetaRieszCrossingOrbitCancellation
