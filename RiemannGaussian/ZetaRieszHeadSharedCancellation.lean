/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeHeadPolePayment
import RiemannGaussian.ZetaRieszSignedConvolution
import RiemannGaussian.ZetaRieszPostHingeEnergy

/-!
# Shared-prime cancellation in the whole balanced main/head comparison

The smaller prime in every literal head pair has log greater than `7N/10`.
Two such primes in a central balanced label saturate the remaining composite
cofactor and give an exact zero, at EVERY count at least four. Consequently
a nonzero higher-count label can share a head prime only as its unique
largest prime. The full signed shared-incidence sum reduces to that owner
profile without a count multiplicity, completion, phase loss or error.

This is an exact cancellation in the actual unpaid population. It does not
bound the surviving owner profile or prove the cofinal floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszHeadSharedCancellation
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint
open ZetaRieszBalancedOwnerFloor ZetaRieszBalancedRadialPayment
open ZetaRieszPrimeHeadTransport ZetaRieszPrimeHeadPolePayment
open ZetaRieszSmallTagNativeFloor (owners)

/-- The same genuine cofactor primes from the full literal head intervals.
The actual allocation and sieve remain in the head; this support set does
not replace either weight by a density. -/
def headCofactors (u : ℝ) (N : ℕ) : Finset ℕ :=
  (owners u N).biUnion (fun p => (pairInterval N p).filter Nat.Prime)

theorem headCofactor_log {u : ℝ} {N q : ℕ} (hq : q∈headCofactors u N) :
    (7/10 : ℝ)*N<log q := by
  obtain ⟨p,hp,hq⟩ := Finset.mem_biUnion.mp hq
  exact (head_prime_logs hp (Finset.mem_filter.mp hq).1).2

private theorem log_mul_nat {a b : ℕ} (ha : a≠0) (hb : b≠0) :
    log (a*b : ℕ)=log a+log b := by
  rw [Nat.cast_mul,log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]

/-- Both deletion cutoffs are saturated, while the last cutoff is
nonpositive. The remaining cofactor is composite, so all signs cancel. -/
theorem coefficient_two_large_zero {p q a : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p≠q) (hpa : ¬p∣a) (hqa : ¬q∣a)
    (hs : Squarefree (p*(q*a))) (hc : 4≤(p*(q*a)).primeFactors.card)
    {L : ℝ} (hpL : log (q*a : ℕ)≤L) (hqL : log (p*a : ℕ)≤L)
    (hpair : L≤log p+log q) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*a))=0 := by
  have ha := hs.of_mul_right.of_mul_right
  have ha0 := ha.ne_zero
  have hac : 2≤a.primeFactors.card := by
    have he : (p*(q*a)).primeFactors={p}∪({q}∪a.primeFactors) := by
      rw [Nat.primeFactors_mul hp.ne_zero hs.of_mul_right.ne_zero,
        Nat.primeFactors_mul hq.ne_zero ha0,hp.primeFactors,hq.primeFactors]
    have h1 := Finset.card_union_le ({p} : Finset ℕ) ({q}∪a.primeFactors)
    have h2 := Finset.card_union_le ({q} : Finset ℕ) a.primeFactors
    simp only [Finset.card_singleton] at h1 h2
    rw [he] at hc
    omega
  have ha1 : a≠1 := by intro he; simp [he] at hac
  have hlp : log a≤L-log p := by
    rw [log_mul_nat hp.ne_zero ha0] at hqL
    linarith only [hqL]
  have hlq : log a≤L-log q := by
    rw [log_mul_nat hq.ne_zero ha0] at hpL
    linarith only [hpL]
  rw [ZetaRieszTypeII.coefficient_prime_minus_hinge hp hq hpq hpa hqa hs
    ha0 ha1 L hlp hlq,
    ZetaRieszSignedConvolution.vonMangoldt_zero_of_squarefree_count ha hac]
  have hz : L-log (p*q : ℕ)≤0 := by
    rw [log_mul_nat hp.ne_zero hq.ne_zero]
    linarith only [hpair]
  rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos hz]
  simp

/-- A uniform all-count cancellation on the ACTUAL central native labels.
Only the two indicated prime incidences are used; every other mask stays. -/
theorem central_two_large_zero {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n p q : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (hn : n∈centralLabels u j)
    (hc : 4≤n.primeFactors.card) (hp : p∈n.primeFactors)
    (hq : q∈n.primeFactors) (hpq : p≠q)
    (hlp : (7/10 : ℝ)*dyadicMomentOrder j<log p)
    (hlq : (7/10 : ℝ)*dyadicMomentOrder j<log q) :
    SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n=0 := by
  have hs : Squarefree n :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (mem_centralLabels.mp hn).1).1).2
  have hmem : (p,q)∈ZetaRieszTypeII.primePairs n :=
    Finset.mem_offDiag.mpr ⟨hp,hq,hpq⟩
  obtain ⟨hpp,hqp,hne,he,hpa,hqa⟩ := ZetaRieszTypeII.primePair_data hs hmem
  have hsf : Squarefree (p*(q*(n/(p*q)))) := he.symm ▸ hs
  have ha0 := hsf.of_mul_right.of_mul_right.ne_zero
  have hl := ZetaRieszPostHingeEnergy.length_ge_rational hN
    (by linarith : 0<u) hU
  have hhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤dyadicMomentOrder j)
  have ht := (mem_centralLabels.mp hn).2.2
  have hlog : log n=log p+log q+log (n/(p*q) : ℕ) := by
    conv_lhs => rw [← he]
    rw [log_mul_nat hpp.ne_zero hsf.of_mul_right.ne_zero,
      log_mul_nat hqp.ne_zero ha0]
    ring
  have hNr : (0 : ℝ)<dyadicMomentOrder j := by exact_mod_cast (by omega : 0<dyadicMomentOrder j)
  have hpc : log (q*(n/(p*q)) : ℕ)≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
    rw [log_mul_nat hqp.ne_zero ha0]
    nlinarith only [hl,ht,hlog,hlp,hNr]
  have hqc : log (p*(n/(p*q)) : ℕ)≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
    rw [log_mul_nat hpp.ne_zero ha0]
    nlinarith only [hl,ht,hlog,hlq,hNr]
  have hpair : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)≤log p+log q := by
    nlinarith only [hhi,hlp,hlq,hNr]
  have hz := coefficient_two_large_zero hpp hqp hne hpa hqa hsf
    (by simpa only [he] using hc) hpc hqc hpair
  simpa only [he] using hz

/-- A higher-count head-prime incidence below the owner has zero ORIGINAL
coefficient. The sieve, allocation and phase cannot restore that atom. -/
theorem central_nonowner_head_zero {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n q : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (hn : n∈centralLabels u j)
    (hc : 4≤n.primeFactors.card)
    (hqH : q∈headCofactors u (dyadicMomentOrder j))
    (hq : q∈n.primeFactors.erase (largestPrime n)) :
    SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n=0 := by
  obtain ⟨hne,hq⟩ := Finset.mem_erase.mp hq
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)
  have hmax : q≤largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨q,hq⟩)]
    exact Finset.le_max' _ _ hq
  have hlog := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos : (0 : ℝ)<q)
    (by exact_mod_cast hmax : (q : ℝ)≤largestPrime n)
  exact central_two_large_zero hu hU hN hn hc hp hq hne.symm
    ((headCofactor_log hqH).trans_le hlog) (headCofactor_log hqH)

/-- Before taking any real part or norm, ALL higher-count shared-prime
incidences reduce to the unique owner. Arbitrary correlated prime weights
and an arbitrary complex weight on the original label are retained. -/
theorem central_shared_incidence_eq_owner {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (hn : n∈centralLabels u j)
    (hc : 4≤n.primeFactors.card) (c : ℕ→ℂ) (w : ℂ) :
    (∑ q∈n.primeFactors∩headCofactors u (dyadicMomentOrder j),c q)*
      (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*w)=
    (if largestPrime n∈headCofactors u (dyadicMomentOrder j)
      then c (largestPrime n) else 0)*
      (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*w) := by
  let S := n.primeFactors∩headCofactors u (dyadicMomentOrder j)
  let a := SquarefreeVaughanLogSource.coefficient
    (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*w
  have hz (q : ℕ) (hq : q∈S) (hne : q≠largestPrime n) : c q*a=0 := by
    have hm := Finset.mem_inter.mp hq
    have he := central_nonowner_head_zero hu hU hN hn hc hm.2
      (Finset.mem_erase.mpr ⟨hne,hm.1⟩)
    dsimp [a]
    rw [he,zero_mul,mul_zero]
  rw [Finset.sum_mul]
  change (∑ q∈S,c q*a)=_
  by_cases hpH : largestPrime n∈headCofactors u (dyadicMomentOrder j)
  · rw [if_pos hpH]
    have hpS : largestPrime n∈S := Finset.mem_inter.mpr
      ⟨ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega),hpH⟩
    exact Finset.sum_eq_single (largestPrime n) (fun q hq hne => hz q hq hne)
      (fun h => (h hpS).elim)
  · rw [if_neg hpH,zero_mul]
    apply Finset.sum_eq_zero
    intro q hq
    apply hz q hq
    intro he
    subst q
    exact hpH (Finset.mem_inter.mp hq).2

/-- The whole higher-count signed incidence profile has ONE owner slot
per nonzero label. No incidence normalization or absolute count price is
introduced. The original factorial product phase can be used as `w`. -/
theorem higher_count_profile_eq_owner {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (c : ℕ→ℂ) (w : ℕ→ℂ) :
    (∑ n∈(centralLabels u j).filter (fun n=>4≤n.primeFactors.card),
      (∑ q∈n.primeFactors∩headCofactors u (dyadicMomentOrder j),c q)*
        (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*w n))=
    ∑ n∈(centralLabels u j).filter (fun n=>4≤n.primeFactors.card),
      (if largestPrime n∈headCofactors u (dyadicMomentOrder j)
        then c (largestPrime n) else 0)*
        (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*w n) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hd := Finset.mem_filter.mp hn
  exact central_shared_incidence_eq_owner hu hU hN hd.1 hd.2 c (w n)

/-- The full native labels cancelled by a NONOWNER head-prime incidence.
This is a subset of the original central population, at unrestricted count. -/
def nonownerShared (u : ℝ) (j : ℕ) : Finset ℕ :=
  (centralLabels u j).filter (fun n=>4≤n.primeFactors.card ∧
    ∃ q∈headCofactors u (dyadicMomentOrder j),q∈n.primeFactors.erase (largestPrime n))

/-- An independent exact payment of this ENTIRE literal signed sector.
Arbitrary original factorial, allocation and complex phase weights remain. -/
theorem nonownerShared_sum_eq_zero {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (w : ℕ→ℂ) :
    (∑ n∈nonownerShared u j,
      SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*w n)=0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn,hc,q,hqH,hq⟩ := Finset.mem_filter.mp hn
  rw [central_nonowner_head_zero hu hU hN hn hc hqH hq,zero_mul]

/-- This signed subpopulation has floor zero, independently of any zero
hypothesis. No favorable observation, factor or count has been discarded. -/
theorem nonownerShared_source_floor {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (y : ℝ) :
    0≤((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈nonownerShared u j,
      SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  rw [nonownerShared_sum_eq_zero hu hU hN,mul_zero]
  simp

/-- Exact whole-floor deletion, with the same full signed prime correction
still available. The surviving main has not acquired an independent floor. -/
theorem centralRest_eq_without_nonownerShared {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (y : ℝ) :
    centralRest u y j=(u : ℂ)^(dyadicMomentOrder j+1)*
      ∑ n∈centralLabels u j\nonownerShared u j,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n := by
  unfold centralRest
  congr 1
  symm
  apply Finset.sum_subset Finset.sdiff_subset
  intro n hn hnot
  have hmem : n∈nonownerShared u j := by
    by_contra hh
    exact hnot (Finset.mem_sdiff.mpr ⟨hn,hh⟩)
  obtain ⟨_,hc,q,hqH,hq⟩ := Finset.mem_filter.mp hmem
  rw [central_nonowner_head_zero hu hU hN hn hc hqH hq,zero_mul]

end RiemannGaussian.ZetaRieszHeadSharedCancellation
