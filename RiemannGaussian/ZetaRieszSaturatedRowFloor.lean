/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnsignedDivisorError

/-!
# A signed comparison floor for literal saturated owner rows

The squarefree counting payment is applied to original core incidences,
with the actual prime-count cutoff left in their finite definition.
Only its comparison error is estimated. The density main, the smaller
unsigned divisor rows and the unsaturated rows remain signed and unpaid.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSaturatedRowFloor
open ZetaRieszSignedConvolution ZetaRieszUnsignedDivisorError
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- Explicit geometry of a saturated interval, before applying any
counting theorem. The inequalities at the two integer endpoints check
the original total-log window, saturation and nondominant share. -/
def RowGeometry (N : ℕ) (L : ℝ) (p b M X : ℕ) : Prop :=
  p.Prime ∧ 1 < b ∧ Squarefree b ∧ ¬p ∣ b ∧
    (∀ q ∈ b.primeFactors, q < p) ∧ pairHinge L p b ≠ 0 ∧
    0 < M ∧
    (39/20 : ℝ)*N ≤ log (p*b : ℕ)+log M ∧
    log (p*b : ℕ)+log X ≤ (203/100 : ℝ)*N ∧
    log b+log X ≤ L ∧
    log p ≤ (13/20 : ℝ)*(log (p*b : ℕ)+log M)

private theorem squarefree_outer {N p b M X : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) : Squarefree (p*b) := by
  exact Nat.squarefree_mul_iff.mpr
    ⟨hg.1.coprime_iff_not_dvd.mpr hg.2.2.2.1,hg.1.squarefree,hg.2.2.1⟩

/-- The original cofactor is squarefree, has at least two distinct
primes and lies below the owner prime. This is deduced from saturation
and the exact squarefree product sieve, not supplied as a phase premise. -/
theorem row_cofactor_geometry {N p b M X d : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) (hd : d ∈ Finset.Ioc M X)
    (hsieve : sieve (p*b).primeFactors d ≠ 0) :
    Squarefree (b*d) ∧ 2 ≤ (b*d).primeFactors.card ∧
      ∀ q ∈ (b*d).primeFactors, q < p := by
  have hgeom := hg
  obtain ⟨hp,hb,hbs,hpb,hbmax,hactive,hM,hlo,hhi,hsat,hshare⟩ := hg
  have hd1 : 1 < d := by have := Finset.mem_Ioc.mp hd; omega
  have hd0 : 0 < d := by omega
  have hb0 : 0 < b := by omega
  have hn : Squarefree ((p*b)*d) := by
    rw [sieve_eq_product_squarefree (squarefree_outer hgeom)] at hsieve
    split_ifs at hsieve with h
    · exact h
    · contradiction
  have hbd : Squarefree (b*d) := by
    rw [show (p*b)*d=p*(b*d) by ac_rfl] at hn
    exact (Nat.squarefree_mul_iff.mp hn).2.2
  have hdc := (Nat.squarefree_mul_iff.mp hbd).1
  have hdis : Disjoint b.primeFactors d.primeFactors := by
    apply Finset.disjoint_left.mpr
    intro q hq hqd
    have hqprime := Nat.prime_of_mem_primeFactors hq
    exact (hqprime.coprime_iff_not_dvd.mp
      (hdc.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq)))
        (Nat.dvd_of_mem_primeFactors hqd)
  have hc : 2 ≤ (b*d).primeFactors.card := by
    rw [Nat.primeFactors_mul (by omega) (by omega),Finset.card_union_of_disjoint hdis]
    have hbcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hb)
    have hdcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hd1)
    omega
  have hdX : log d ≤ log X := log_le_log
    (by exact_mod_cast hd0) (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
  have hsatd : log (b*d : ℕ) ≤ L := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hb0.ne') (by exact_mod_cast hd0.ne')]
    linarith
  have hdp := active_unsigned_lt_owner hp.pos hb0 hd0 hsatd hactive
  refine ⟨hbd,hc,?_⟩
  intro q hq
  rw [Nat.primeFactors_mul (by omega) (by omega),Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact hbmax q hq
  · exact (Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hq)).trans_lt hdp

/-- Full canonical ownership also holds at a rounded lower endpoint.
The unsigned divisor must be nonunit; no length or arithmetic atom is
changed and no new count or phase allowance is introduced. -/
theorem closed_row_cofactor_geometry {N p b M X d : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) (hd : d ∈ Finset.Icc M X) (hd1 : 1 < d)
    (hsieve : sieve (p*b).primeFactors d ≠ 0) :
    Squarefree (b*d) ∧ 2 ≤ (b*d).primeFactors.card ∧
      ∀ q ∈ (b*d).primeFactors, q < p := by
  have hgeom := hg
  obtain ⟨hp,hb,hbs,hpb,hbmax,hactive,hM,hlo,hhi,hsat,hshare⟩ := hg
  have hd0 : 0 < d := by omega
  have hb0 : 0 < b := by omega
  have hn : Squarefree ((p*b)*d) := by
    rw [sieve_eq_product_squarefree (squarefree_outer hgeom)] at hsieve
    split_ifs at hsieve with h
    · exact h
    · contradiction
  have hbd : Squarefree (b*d) := by
    rw [show (p*b)*d=p*(b*d) by ac_rfl] at hn
    exact (Nat.squarefree_mul_iff.mp hn).2.2
  have hdc := (Nat.squarefree_mul_iff.mp hbd).1
  have hdis : Disjoint b.primeFactors d.primeFactors := by
    apply Finset.disjoint_left.mpr
    intro q hq hqd
    have hqprime := Nat.prime_of_mem_primeFactors hq
    exact (hqprime.coprime_iff_not_dvd.mp
      (hdc.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq)))
        (Nat.dvd_of_mem_primeFactors hqd)
  have hc : 2 ≤ (b*d).primeFactors.card := by
    rw [Nat.primeFactors_mul (by omega) (by omega),Finset.card_union_of_disjoint hdis]
    have hbcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hb)
    have hdcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hd1)
    omega
  have hdX : log d ≤ log X := log_le_log
    (by exact_mod_cast hd0) (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
  have hsatd : log (b*d : ℕ) ≤ L := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hb0.ne') (by exact_mod_cast hd0.ne')]
    linarith
  have hdp := active_unsigned_lt_owner hp.pos hb0 hd0 hsatd hactive
  refine ⟨hbd,hc,?_⟩
  intro q hq
  rw [Nat.primeFactors_mul (by omega) (by omega),Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact hbmax q hq
  · exact (Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hq)).trans_lt hdp

/-- On the selected literal rows, the only remaining core membership
condition is its original count cutoff. All other original masks are
checked from the actual endpoint geometry. -/
theorem row_mem_core_iff (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {p b M X d : ℕ}
    (hg : RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) p b M X)
    (hd : d ∈ Finset.Ioc M X) (hsieve : sieve (p*b).primeFactors d ≠ 0) :
    p*(b*d) ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ↔
      (p*(b*d)).primeFactors.card < dyadicPrimeCount j := by
  have hgeom := hg
  obtain ⟨hp,hb,hbs,hpb,hbmax,hactive,hM,hlo,hhi,hsat,hshare⟩ := hg
  have hco := row_cofactor_geometry hgeom hd hsieve
  have hd0 : 0 < d := by have := Finset.mem_Ioc.mp hd; omega
  have hb0 : 0 < b := by omega
  have hn : Squarefree (p*(b*d)) := by
    have hh := hsieve
    rw [sieve_eq_product_squarefree (squarefree_outer hgeom)] at hh
    split_ifs at hh with h
    · simpa only [mul_assoc] using h
    · contradiction
  have hcnt : (p*(b*d)).primeFactors.card=(b*d).primeFactors.card+1 := by
    rw [Nat.primeFactors_mul hp.ne_zero hco.1.ne_zero,hp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem]
    intro hh
    exact (lt_irrefl p) (hco.2.2 p hh)
  have ht : log (p*(b*d) : ℕ)=log (p*b : ℕ)+log d := by
    rw [show p*(b*d)=(p*b)*d by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hb0).ne') (by exact_mod_cast hd0.ne')]
  have hdM : log M < log d := (log_lt_log_iff
    (by exact_mod_cast hM) (by exact_mod_cast hd0)).mpr
      (by exact_mod_cast (Finset.mem_Ioc.mp hd).1)
  have hdX : log d ≤ log X := log_le_log
    (by exact_mod_cast hd0) (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
  constructor
  · intro hncore
    have hnar := (Finset.mem_filter.mp hncore).1
    have hnd := (Finset.mem_filter.mp hnar).1
    have hret := (Finset.mem_sdiff.mp hnd).1
    have hmask := (Finset.mem_sdiff.mp hret).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmask).1).2.2
  · intro hK
    apply mem_core_of_strict_prime_share j hj hu hU hL hn (by omega) hK
      (by rw [ht]; linarith) (by rw [ht]; linarith)
    intro q hq
    have hqp : q ≤ p := by
      rw [Nat.primeFactors_mul hp.ne_zero hco.1.ne_zero,hp.primeFactors,
        Finset.mem_union,Finset.mem_singleton] at hq
      exact hq.elim (fun h => h ▸ le_rfl) (fun h => (hco.2.2 q h).le)
    have hlogqp : log q ≤ log p := log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast hqp)
    rw [ht]
    linarith

/-- One original complemented-divisor incidence. The full phase and
allocation remain those of the original product, not of either factor. -/
def rowAtom (A : Finset ℕ) (N : ℕ) (L y : ℝ) (p b d : ℕ) : ℝ :=
  (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*(b*d))})
    L N y (b*d) p).re*(μ b : ℝ)*pairHinge L p b*sieve (p*b).primeFactors d

/-- The literal core selection, including its original count cutoff. -/
def coreRow (u y : ℝ) (j p b M X : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  ∑ d ∈ Finset.Ioc M X,
    if p*(b*d) ∈ coreBand u N (dyadicPrimeCount j) then rowAtom A N L y p b d else 0

/-- The exact high-count extension of the same original incidence.
It contains no completed prime cofactor and no altered factorial weight. -/
def overflowRow (u y : ℝ) (j p b M X : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  ∑ d ∈ Finset.Ioc M X,
    if dyadicPrimeCount j ≤ (p*(b*d)).primeFactors.card then rowAtom A N L y p b d else 0

/-- One signed arithmetic density row. Its Möbius sign, joined hinge,
allocation, factorial kernel and phase are all retained. -/
def densityRow (N : ℕ) (L y : ℝ) (p b M X : ℕ) : ℝ :=
  ((μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ)))*density (p*b).primeFactors*
    (∑ d ∈ Finset.Icc 1 X, ZetaRieszCofactorDiscrepancy.shellWeight M X
      (ownedAmplitude N (log p) (log (p*b : ℕ))) y (log (p*b : ℕ)) d)

/-- The counting discrepancy is now applied to LITERAL core rows.
No window, allocation, prime support or count cutoff is discarded: the
only extension is the explicit, independently payable high-count row. -/
theorem coreRow_add_overflow (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {p b M X : ℕ}
    (hg : RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) p b M X)
    (hpA : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)) :
    coreRow u y j p b M X+overflowRow u y j p b M X =
      densityRow (dyadicMomentOrder j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b M X+
      ownedShellDiscrepancy (dyadicMomentOrder j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b M X := by
  have he := ownedShellDiscrepancy_eq_literal
    (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y
    hg.1 (by have := hg.2.1; omega) hg.2.2.2.2.2.2.1 hpA
    (fun d hd hs => row_cofactor_geometry hg hd hs)
  rw [he]
  unfold coreRow overflowRow densityRow
  dsimp only
  rw [← Finset.sum_add_distrib]
  have hrows : (∑ d ∈ Finset.Ioc M X,
      ((if p*(b*d) ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b d
        else 0)+
      (if dyadicPrimeCount j ≤ (p*(b*d)).primeFactors.card then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b d
        else 0))) =
      ∑ d ∈ Finset.Ioc M X,
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b d := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hz : sieve (p*b).primeFactors d=0
    · simp [rowAtom,hz]
    have hc := row_mem_core_iff j hj hu hU hL hg hd hz
    by_cases hk : (p*(b*d)).primeFactors.card < dyadicPrimeCount j
    · rw [if_pos (hc.mpr hk),if_neg (by omega),add_zero]
    · rw [if_neg (fun h => hk (hc.mp h)),if_pos (by omega),zero_add]
  rw [hrows]
  simp only [rowAtom]
  ring

/-- Join all selected original core rows before estimating their
counting error. This is a signed comparison floor, not a positive
allowance for the density main or the remaining literal carrier. -/
theorem source_scaled_rows_floor {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) (M X : ι → ℕ×ℕ → ℕ)
    (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hN : 32 ≤ dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hI : I.card ≤ dyadicMomentOrder j+1)
    (hg : ∀ i ∈ I, ∀ pb ∈ B i, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
        pb.1 pb.2 (M i pb) (X i pb))
    (hpA : ∀ i ∈ I, ∀ pb ∈ B i,
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (hMX : ∀ i ∈ I, ∀ pb ∈ B i, M i pb < X i pb)
    (hXM : ∀ i ∈ I, ∀ pb ∈ B i, X i pb ≤ 2*M i pb)
    (hlarge : ∀ i ∈ I, ∀ pb ∈ B i, exp ((dyadicMomentOrder j : ℝ)/10) ≤ M i pb) :
    u^(dyadicMomentOrder j+1)*
      (∑ i ∈ I, ∑ pb ∈ B i,
        (densityRow (dyadicMomentOrder j)
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y pb.1 pb.2
            (M i pb) (X i pb)-overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)))-
      errorConstant*(8+|y|)*((dyadicMomentOrder j : ℝ)+1)^3*(49/50 : ℝ)^(dyadicMomentOrder j) ≤
        u^(dyadicMomentOrder j+1)*∑ i ∈ I, ∑ pb ∈ B i,
          coreRow u y j pb.1 pb.2 (M i pb) (X i pb) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hloN : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hLL : 0 < L := by dsimp [L,N]; nlinarith
  have hB i (hi : i ∈ I) pb (hpb : pb ∈ B i) :
      pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 :=
    ⟨(hg i hi pb hpb).1,(hg i hi pb hpb).2.2.1,(hg i hi pb hpb).2.2.2.1⟩
  have hM i (hi : i ∈ I) pb (hpb : pb ∈ B i) : 0 < M i pb :=
    (hg i hi pb hpb).2.2.2.2.2.2.1
  have hlog i (hi : i ∈ I) pb (hpb : pb ∈ B i) :
      log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N := by
    have hh := (hg i hi pb hpb).2.2.2.2.2.2.2.2.1
    change _ ≤ (203/100 : ℝ)*N at hh
    linarith [log_natCast_nonneg (X i pb)]
  have hPL i (hi : i ∈ I) pb (hpb : pb ∈ B i) : log pb.1 ≤ L := by
    obtain ⟨_,_,_,_,_,_,_,_,hh,_,hp⟩ := hg i hi pb hpb
    have hmX : log (M i pb) ≤ log (X i pb) := log_le_log (by exact_mod_cast hM i hi pb hpb)
      (by exact_mod_cast (hMX i hi pb hpb).le)
    change (11/8 : ℝ)*N ≤ L at hL
    change _ ≤ (203/100 : ℝ)*N at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hT i (hi : i ∈ I) pb (hpb : pb ∈ B i) d
      (hd : d ∈ Finset.Icc (M i pb+1) (X i pb)) :
      1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    obtain ⟨_,_,_,_,_,_,_,hh,_,_,_⟩ := hg i hi pb hpb
    have hMd : M i pb ≤ d := by have := Finset.mem_Icc.mp hd; omega
    have hmD : log (M i pb) ≤ log d := log_le_log (by exact_mod_cast hM i hi pb hpb)
      (by exact_mod_cast hMd)
    change (39/20 : ℝ)*N ≤ _ at hh
    linarith
  have herr := source_scaled_shells_error I B hN M X hLL (by linarith : 0 ≤ u) hU y
    hI hB hlog hM hMX hXM hlarge hPL hT
  have heq : (∑ i ∈ I, ∑ pb ∈ B i, coreRow u y j pb.1 pb.2 (M i pb) (X i pb)) =
      (∑ i ∈ I, ∑ pb ∈ B i,
        (densityRow N L y pb.1 pb.2 (M i pb) (X i pb)-
          overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)))+
      ∑ i ∈ I, ∑ pb ∈ B i, ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pb hpb
    have h := coreRow_add_overflow (y := y) j hj hu hU hL (hg i hi pb hpb) (hpA i hi pb hpb)
    change _+_=densityRow N L y _ _ _ _+ownedShellDiscrepancy N L y _ _ _ _ at h
    linarith
  rw [heq,mul_add]
  have hl := neg_abs_le (u^(N+1)*∑ i ∈ I, ∑ pb ∈ B i,
    ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb))
  change |u^(N+1)*_| ≤ _ at herr
  linarith

/-- Actual owner-divisor incidences selected by the row intervals.
The pair `(n,(d,b))` records its ORIGINAL label and divisor allocation. -/
def incidences (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ) : Finset (ℕ×(ℕ×ℕ)) :=
  B.biUnion (fun pb => ((Finset.Ioc (M pb) (X pb)).filter
    (fun d => sieve (pb.1*pb.2).primeFactors d ≠ 0)).image
      (fun d => (pb.1*(pb.2*d),(d,pb.2))))

/-- The exact selected divisor set of each original label. -/
def selectedDivisors (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ) (n : ℕ) : Finset (ℕ×ℕ) :=
  ((incidences B M X).filter (fun v => v.1=n)).image Prod.snd

private theorem mem_incidences {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ}
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    ∃ pb ∈ B, ∃ d ∈ Finset.Ioc (M pb) (X pb),
      sieve (pb.1*pb.2).primeFactors d ≠ 0 ∧ v=(pb.1*(pb.2*d),(d,pb.2)) := by
  obtain ⟨pb,hpb,hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hv
  exact ⟨pb,hpb,d,(Finset.mem_filter.mp hd).1,(Finset.mem_filter.mp hd).2,he.symm⟩

/-- A row incidence has the genuine canonical owner and an original
squarefree product label. No owner multiplicity is introduced. -/
theorem incidence_owner {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ} {N : ℕ} {L : ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N L pb.1 pb.2 (M pb) (X pb))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    Squarefree v.1 ∧
      ZetaRieszPrimeEndpoint.largestPrime v.1*(v.2.2*v.2.1)=v.1 ∧
      v.2.1*v.2.2=v.1/ZetaRieszPrimeEndpoint.largestPrime v.1 := by
  obtain ⟨pb,hpb,d,hd,hs,rfl⟩ := mem_incidences hv
  have hgeom := hg pb hpb
  have hco := row_cofactor_geometry hgeom hd hs
  have howner := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
    hgeom.1 hco.1.ne_zero hco.2.2
  have hn : Squarefree (pb.1*(pb.2*d)) := by
    rw [sieve_eq_product_squarefree (squarefree_outer hgeom)] at hs
    split_ifs at hs with h
    · simpa only [mul_assoc] using h
    · contradiction
  refine ⟨hn,?_,?_⟩
  · rw [howner]
  · simp only [howner,Nat.mul_div_cancel_left _ hgeom.1.pos]
    ac_rfl

/-- Every selected set is a literal subset of the original cofactor
antidiagonal. This prevents spending a duplicate incidence credit. -/
theorem selectedDivisors_subset {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ} {N : ℕ} {L : ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N L pb.1 pb.2 (M pb) (X pb)) (n : ℕ) :
    selectedDivisors B M X n ⊆ (n/ZetaRieszPrimeEndpoint.largestPrime n).divisorsAntidiagonal := by
  intro db hdb
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hdb
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have ho := incidence_owner hg hv
  apply Nat.mem_divisorsAntidiagonal.mpr
  rw [← he]
  refine ⟨ho.2.2,?_⟩
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  have ho := row_cofactor_geometry (hg pb hpb) hd (by assumption)
  rw [ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) (hg pb hpb).1
    ho.1.ne_zero ho.2.2,Nat.mul_div_cancel_left _ (hg pb hpb).1.pos]
  exact ho.1.ne_zero

/-- Original row selections with distinct outer pairs cannot overlap
as divisor incidences, even when several divisors have the same label. -/
theorem sum_rows_eq_incidences (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ) {N : ℕ} {L : ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N L pb.1 pb.2 (M pb) (X pb))
    (f : ℕ → (ℕ×ℕ) → ℝ) :
    (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0) =
      ∑ v ∈ incidences B M X, f v.1 v.2 := by
  have hdis : Set.Pairwise (↑B) (fun pb pc => Disjoint
      (((Finset.Ioc (M pb) (X pb)).filter (fun d => sieve (pb.1*pb.2).primeFactors d ≠ 0)).image
        (fun d => (pb.1*(pb.2*d),(d,pb.2))))
      (((Finset.Ioc (M pc) (X pc)).filter (fun d => sieve (pc.1*pc.2).primeFactors d ≠ 0)).image
        (fun d => (pc.1*(pc.2*d),(d,pc.2))))) := by
    intro pb hpb pc hpc hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hw
    have hd' := Finset.mem_filter.mp hd
    have he' := Finset.mem_filter.mp he
    have hdco := row_cofactor_geometry (hg pb hpb) hd'.1 hd'.2
    have heco := row_cofactor_geometry (hg pc hpc) he'.1 he'.2
    have hownerd := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
      (hg pb hpb).1 hdco.1.ne_zero hdco.2.2
    have hownere := ZetaRieszPrimeIntervals.largestPrime_mul pc.1 (pc.2*e)
      (hg pc hpc).1 heco.1.ne_zero heco.2.2
    have hpe : pc.1=pb.1 := by
      have hh := congrArg ZetaRieszPrimeEndpoint.largestPrime (congrArg Prod.fst heq)
      simpa only [hownerd,hownere] using hh
    have hbe : pc.2=pb.2 := by simpa using congrArg (fun v : ℕ×(ℕ×ℕ) => v.2.2) heq
    exact hne (Prod.ext hpe.symm hbe.symm)
  rw [incidences,Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro pb hpb
  rw [Finset.sum_image (fun d _ e _ he => by simpa using congrArg (fun v : ℕ×(ℕ×ℕ) => v.2.1) he)]
  simp only [Finset.sum_filter]

private theorem sum_incidences_eq_fibers (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (f : ℕ → (ℕ×ℕ) → ℝ) :
    (∑ v ∈ incidences B M X, f v.1 v.2) =
      ∑ n ∈ (incidences B M X).image Prod.fst,
        ∑ db ∈ selectedDivisors B M X n, f n db := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (t := (incidences B M X).image Prod.fst) (g := Prod.fst)
    (fun v (hv : v ∈ incidences B M X) => Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    (fun v : ℕ×(ℕ×ℕ) => f v.1 v.2)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n _
  rw [selectedDivisors,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  · intro v hv w hw he
    exact Prod.ext ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) he

private def incidenceWeight (A : Finset ℕ) (N : ℕ) (L y : ℝ) (n : ℕ) (db : ℕ×ℕ) : ℝ :=
  (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L N y
    (n/ZetaRieszPrimeEndpoint.largestPrime n) (ZetaRieszPrimeEndpoint.largestPrime n)).re*
      (μ db.2 : ℝ)*pairHinge L (ZetaRieszPrimeEndpoint.largestPrime n) db.2

private theorem rowAtom_eq_incidenceWeight (A : Finset ℕ) {N p b M X d : ℕ} {L : ℝ}
    (y : ℝ) (hg : RowGeometry N L p b M X) (hd : d ∈ Finset.Ioc M X)
    (hs : sieve (p*b).primeFactors d ≠ 0) :
    rowAtom A N L y p b d = incidenceWeight A N L y (p*(b*d)) (d,b) := by
  have hc := row_cofactor_geometry hg hd hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul p (b*d) hg.1 hc.1.ne_zero hc.2.2
  have hs1 : sieve (p*b).primeFactors d=1 := by
    unfold sieve at *
    split_ifs at * <;> simp_all
  simp only [rowAtom,incidenceWeight,ho,Nat.mul_div_cancel_left _ hg.1.pos,hs1,mul_one]

private theorem sum_incidenceWeight_eq_partial (A : Finset ℕ) (N n : ℕ) (L y : ℝ)
    (D : Finset (ℕ×ℕ))
    (he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n) :
    (∑ db ∈ D, incidenceWeight A N L y n db) =
      (partialCoefficient (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L N
        (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n) D*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  simp only [incidenceWeight,phaseWeight,partialCoefficient,he,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro db _
  ring

/-- Reindex any ORIGINAL product mask through the selected incidences.
No mask is completed or included in an absolute variation estimate. -/
theorem sum_maskedRows_eq_partial (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (χ : ℕ → Prop)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        χ,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n db => if χ n then
    incidenceWeight A N L y n db else 0
  have hrows : (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then rowAtom A N L y pb.1 pb.2 d else 0) =
      ∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
        if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0 := by
    apply Finset.sum_congr rfl
    intro pb hpb
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : sieve (pb.1*pb.2).primeFactors d=0
    · simp [rowAtom,hs]
    rw [if_pos hs,rowAtom_eq_incidenceWeight A y (hg pb hpb) hd hs]
  rw [hrows,sum_rows_eq_incidences B M X hg f,sum_incidences_eq_fibers]
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : χ n
  · simp only [f,if_pos hk]
    have he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      obtain ⟨v,hv,hnv⟩ := Finset.mem_image.mp hn
      have ho := incidence_owner hg hv
      rw [← hnv,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    exact sum_incidenceWeight_eq_partial A N n L y _ he
  · simp only [f,if_neg hk,Finset.sum_const_zero]

/-- The literal high-count row sum is the original factorial kernel
times a partial divisor coefficient, on its original product labels.
This gives the exact bridge to the checked high-count payment. -/
theorem sum_overflow_eq_partial (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, overflowRow u y j pb.1 pb.2 (M pb) (X pb)) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        (fun n => dyadicPrimeCount j ≤ n.primeFactors.card),
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  convert sum_maskedRows_eq_partial B M X u y j
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card) hg using 1
  · apply Finset.sum_congr rfl
    intro pb _
    unfold overflowRow
    dsimp only
    apply Finset.sum_congr rfl
    intro d _
    by_cases hk : dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card <;> simp [hk]
  · congr 1
    apply Finset.sum_congr
    · ext n; simp
    · intro n _; rfl

private theorem row_window {N p b M X d : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) (hd : d ∈ Finset.Ioc M X) :
    (39/20 : ℝ)*N < log (p*(b*d) : ℕ) ∧
      log (p*(b*d) : ℕ) ≤ (203/100 : ℝ)*N := by
  have hgeom := hg
  obtain ⟨hp,hb,_,_,_,_,hM,hlo,hhi,_,_⟩ := hg
  have hd0 : 0 < d := by have := Finset.mem_Ioc.mp hd; omega
  have hb0 : 0 < b := by omega
  have ht : log (p*(b*d) : ℕ)=log (p*b : ℕ)+log d := by
    rw [show p*(b*d)=(p*b)*d by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hb0).ne') (by exact_mod_cast hd0.ne')]
  have hMd : log M < log d := (log_lt_log_iff
    (by exact_mod_cast hM) (by exact_mod_cast hd0)).mpr
      (by exact_mod_cast (Finset.mem_Ioc.mp hd).1)
  have hdX : log d ≤ log X := log_le_log (by exact_mod_cast hd0)
    (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
  rw [ht]
  constructor <;> linarith

private theorem incidence_band {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ} {N : ℕ} {L : ℝ}
    (hN : 0 < N) (hg : ∀ pb ∈ B, RowGeometry N L pb.1 pb.2 (M pb) (X pb))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) : v.1 ∈ zetaPrimeLogBand N := by
  have hn := (incidence_owner hg hv).1
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  have hw := row_window (hg pb hpb) hd
  by_contra hnot
  have hc := zetaPrimeLogBand_complement N hn.ne_zero hnot
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  rcases hc with hlo | hhi
  · nlinarith [log_two_lt_d9]
  · nlinarith [log_two_gt_d9]

private theorem incidence_log_le_twice_length {u : ℝ} {j : ℕ}
    {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ}
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M pb) (X pb))
    (hpA : ∀ pb ∈ B, pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    log v.1 ≤ 2*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  obtain ⟨hp,hb,_,_,_,_,hM,_,_,hsat,_⟩ := hg pb hpb
  obtain ⟨_,_,hpX⟩ := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp (hpA pb hpb)
  have hpL : log pb.1 ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) :=
    (log_lt_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpX)).le
  have hd0 : 0 < d := by have := Finset.mem_Ioc.mp hd; omega
  have hdX : log d ≤ log (X pb) := log_le_log (by exact_mod_cast hd0)
    (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
  rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by positivity : ((pb.2*d : ℕ) : ℝ) ≠ 0),
    Nat.cast_mul,log_mul (by exact_mod_cast (show pb.2≠0 by omega)) (by exact_mod_cast hd0.ne')]
  linarith

/-- The exact row extension beyond the ORIGINAL count cutoff is
independently source-o(1). Squarefreeness, product labels and every
selected divisor incidence are retained in the high-count theorem. -/
theorem tendsto_overflowRows (B : ℕ → Finset (ℕ×ℕ)) (M X : ℕ → ℕ×ℕ → ℕ)
    (y : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hg : ∀ j, ∀ pb ∈ B j, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M j pb) (X j pb))
    (hpA : ∀ j, ∀ pb ∈ B j,
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ∑ pb ∈ B j, overflowRow u (y j) j pb.1 pb.2 (M j pb) (X j pb)) atTop (𝓝 0) := by
  let S := fun j => ((incidences (B j) (M j) (X j)).image Prod.fst).filter
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card)
  let p := fun (_ : ℕ) n => ZetaRieszPrimeEndpoint.largestPrime n
  let a := fun (_ : ℕ) n => n/ZetaRieszPrimeEndpoint.largestPrime n
  have hn j n (h : n ∈ S j) :
      ∃ v ∈ incidences (B j) (M j) (X j), v.1=n :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).1
  have hS j n (h : n ∈ S j) : Squarefree n ∧
      n ∈ zetaPrimeLogBand (dyadicMomentOrder j) ∧ dyadicPrimeCount j ≤ n.primeFactors.card := by
    obtain ⟨v,hv,he⟩ := hn j n h
    rw [← he]
    exact ⟨(incidence_owner (hg j) hv).1,
      incidence_band (by unfold dyadicMomentOrder dyadicPrimeCount; positivity) (hg j) hv,
      by simpa only [he] using (Finset.mem_filter.mp h).2⟩
  have he j n (h : n ∈ S j) : p j n*a j n=n := by
    obtain ⟨v,hv,he⟩ := hn j n h
    have ho := incidence_owner (hg j) hv
    dsimp [p,a]
    rw [← he,← ho.2.2]
    simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
  have hp j n (h : n ∈ S j) : 0 < p j n := by
    have hn0 := (hS j n h).1.ne_zero
    have he := he j n h
    by_contra hh
    have hp0 : p j n=0 := by omega
    rw [hp0,zero_mul] at he
    exact hn0 he.symm
  have ha j n (h : n ∈ S j) : 0 < a j n := by
    have hn0 := (hS j n h).1.ne_zero
    have he := he j n h
    by_contra hh
    have ha0 : a j n=0 := by omega
    rw [ha0,mul_zero] at he
    exact hn0 he.symm
  have ht := tendsto_high_count_partial_incidence S
    (fun j n => ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
      {ZetaRieszPrimeEndpoint.largestPrime n})
    (fun j n => selectedDivisors (B j) (M j) (X j) n) p a
    (fun j => SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y hu hU
    (fun j => SquarefreeVaughanLogSource.length_pos u _) hS hp ha he
    (fun j n _ => selectedDivisors_subset (hg j) n)
    (fun j n h => by
      obtain ⟨v,hv,he⟩ := hn j n h
      simpa only [he] using incidence_log_le_twice_length (hg j) (hpA j) hv)
  have hr := Complex.continuous_re.tendsto _ |>.comp ht
  simp only [Complex.zero_re] at hr
  convert hr using 1
  ext j
  rw [sum_overflow_eq_partial (B j) (M j) (X j) u (y j) j (hg j)]
  simp only [Function.comp_apply,S,p,a,← Complex.ofReal_pow,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- A fixed high-count envelope, used only for the comparison extension. -/
def highCountConstant : ℝ := 64*ZetaRieszWideOwnerAudit.radiusCeiling*log 2

theorem highCountConstant_nonneg : 0 ≤ highCountConstant := by
  unfold highCountConstant ZetaRieszWideOwnerAudit.radiusCeiling
  positivity [log_pos (by norm_num : (1 : ℝ)<2)]

/-- A quantitative count-boundary payment uniform over every selected
outer pair and every height. The fixed count tilt has rate at most 97/100;
its remaining count exponential is subgeometric on the original schedule. -/
theorem overflowRows_bound (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M pb) (X pb))
    (hpA : ∀ pb ∈ B,
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*∑ pb ∈ B,
      overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
        highCountConstant*(dyadicMomentOrder j : ℝ)*(97/100 : ℝ)^(dyadicMomentOrder j)*
          exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ((incidences B M X).image Prod.fst).filter
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card)
  let c := fun n => partialCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
        (selectedDivisors B M X n)/2
  have hn n (h : n ∈ S) : ∃ v ∈ incidences B M X, v.1=n :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).1
  have hsf n (h : n ∈ S) : Squarefree n := by
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using (incidence_owner hg hv).1
  have hband : S ⊆ zetaPrimeLogBand N := by
    intro n h
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using incidence_band
      (by dsimp [N,dyadicMomentOrder,dyadicPrimeCount]; positivity) hg hv
  have hc n (h : n ∈ S) : ‖c n‖ ≤ zetaMoebiusLogMajorant n := by
    obtain ⟨v,hv,he⟩ := hn n h
    have ho := incidence_owner hg hv
    have hpn : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      rw [← he,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    have hp : 0 < ZetaRieszPrimeEndpoint.largestPrime n := by
      by_contra hh
      have h0 : ZetaRieszPrimeEndpoint.largestPrime n=0 := by omega
      rw [h0,zero_mul] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have ha : (0 : ℕ) < n/ZetaRieszPrimeEndpoint.largestPrime n := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0,mul_zero] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have hT : log n ≤ 2*L := by
      simpa only [he] using incidence_log_le_twice_length hg hpA hv
    have hdom := partialCoefficient_bound
      (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      N hp ha (selectedDivisors B M X n) (selectedDivisors_subset hg n)
      (SquarefreeVaughanLogSource.length_pos u N) (by simpa only [hpn] using hT)
    rw [hpn] at hdom
    dsimp [c]
    rw [norm_div]
    norm_num
    linarith
  have hnorm := ZetaRieszWeightedCount.norm_normalized_many_dyadic_le S c hc 1 j y hu hU
    (by norm_num : (0 : ℝ)<49/100) (by norm_num : (49/100 : ℝ)<1/2) hsf hband
    (fun n h => (Finset.mem_filter.mp h).2)
  have hP : (∑ k ∈ (1 : Polynomial ℂ).support,
      ‖(1 : Polynomial ℂ).coeff k‖*(49/100 : ℝ)⁻¹^k)=1 := by
    rw [← Polynomial.C_1,Polynomial.support_C (by norm_num : (1 : ℂ)≠0)]
    simp
  rw [hP,mul_one,show (3/2 : ℝ)-49/100=101/100 by norm_num] at hnorm
  have hreal : |u^(N+1)*∑ pb ∈ B, overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
      2*‖(u : ℂ)^(N+1)*∑ n ∈ S,
        c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
    rw [sum_overflow_eq_partial B M X u y j hg]
    have heq : (u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
        2*((u : ℂ)^(N+1)*∑ n ∈ S,
          c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
      calc
        _ = (u : ℂ)^(N+1)*(2*∑ n ∈ S,
            c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [ZetaRieszJointAllocation.filter_one_eq]
          dsimp [c]
          ring
        _ = _ := by ring
    have hre := Complex.abs_re_le_norm
      ((u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    have hrhs : ‖(u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
        2*‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
      rw [heq,norm_mul]
      norm_num
    simpa only [S,L,N,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre.trans_eq hrhs
  apply hreal.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ)≤2)).trans _)
  have hr : 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) ≤ 97/100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hr0 : 0 ≤ 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  dsimp [highCountConstant]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr N)
    (by dsimp [ZetaRieszWideOwnerAudit.radiusCeiling]
        positivity [log_pos (by norm_num : (1 : ℝ)<2)] : 0 ≤ 64*ZetaRieszWideOwnerAudit.radiusCeiling*log 2*N)
  have he := mul_le_mul_of_nonneg_right hp
    (exp_pos (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))).le
  convert he using 1
  ring

/-- All selected count boundaries may be joined over a growing number
of shells. Their total cost still has an explicit geometric rate. -/
theorem eventually_overflowShells_bound {ι : Type*} (I : ℕ → Finset ι)
    (B : ℕ → ι → Finset (ℕ×ℕ)) (M X : ℕ → ι → ℕ×ℕ → ℕ)
    (y : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hI : ∀ j, (I j).card ≤ dyadicMomentOrder j+1)
    (hg : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M j i pb) (X j i pb))
    (hpA : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i,
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*∑ i ∈ I j, ∑ pb ∈ B j i,
        overflowRow u (y j) j pb.1 pb.2 (M j i pb) (X j i pb)| ≤
          highCountConstant*((dyadicMomentOrder j : ℝ)+1)^2*(49/50 : ℝ)^(dyadicMomentOrder j) := by
  have hcount := ZetaRieszPrimeCountMass.eventually_exp_count_le_geometric
    (2*ZetaRieszPrimeCountMass.countMass (101/100)) (by norm_num : (1 : ℝ)<101/100)
  filter_upwards [hcount] with j hj
  let N := dyadicMomentOrder j
  let C := highCountConstant*(N : ℝ)*(97/100 : ℝ)^N*
    exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))
  have hC : 0 ≤ C := by dsimp [C]; positivity [highCountConstant_nonneg]
  calc
    _ ≤ ∑ i ∈ I j, |u^(N+1)*∑ pb ∈ B j i,
        overflowRow u (y j) j pb.1 pb.2 (M j i pb) (X j i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I j, C := Finset.sum_le_sum (fun i hi =>
      overflowRows_bound (B j i) (M j i) (X j i) j hu hU (y j) (hg j i hi) (hpA j i hi))
    _ = ((I j).card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hI j) hC
    _ ≤ highCountConstant*((N : ℝ)+1)^2*
        ((97/100 : ℝ)^N*(101/100 : ℝ)^N) := by
      have hex : exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) ≤
          (101/100 : ℝ)^N := by simpa only [mul_assoc,mul_comm,mul_left_comm] using hj
      have hp := mul_le_mul_of_nonneg_left hex
        (by positivity [highCountConstant_nonneg] : 0 ≤ ((N : ℝ)+1)*highCountConstant*N*(97/100 : ℝ)^N)
      have hn : ((N : ℝ)+1)*N ≤ ((N : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hpoly := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn highCountConstant_nonneg)
        (by positivity : 0 ≤ (97/100 : ℝ)^N*(101/100 : ℝ)^N)
      dsimp [C]
      nlinarith only [hp,hpoly]
    _ ≤ _ := by
      rw [← mul_pow]
      gcongr
      all_goals first | positivity [highCountConstant_nonneg] | norm_num

/-- This budget pays only the two comparison errors: squarefree
counting and the literal count-cutoff extension. It does not pay a
positive allowance for any retained signed main contribution. -/
def rowErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  (errorConstant*(8+|y|)*((N : ℝ)+1)^3+
    highCountConstant*((N : ℝ)+1)^2)*(49/50 : ℝ)^N

theorem tendsto_rowErrorBudget (y : ℝ) :
    Tendsto (rowErrorBudget y) atTop (𝓝 0) := by
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (by norm_num : (0 : ℝ)<49/50) (by norm_num : (49/50 : ℝ)<1)).const_mul highCountConstant
  have he := (tendsto_shell_error_budget y).add ht
  have he' : Tendsto (fun N : ℕ =>
      errorConstant*(8+|y|)*((N : ℝ)+1)^3*(49/50 : ℝ)^N+
        highCountConstant*(((N : ℝ)+1)^2*(49/50 : ℝ)^N)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using he
  convert he' using 1
  ext N
  unfold rowErrorBudget
  ring

/-- A source-geometric signed floor on ORIGINAL core rows, after both
counting and count-boundary errors have been paid. All counts and shell
contributions in the density main stay joined, with their actual signs.
The independent numerical floor for that signed main remains open. -/
theorem eventually_signed_rows_floor {ι : Type*} (I : ℕ → Finset ι)
    (B : ℕ → ι → Finset (ℕ×ℕ)) (M X : ℕ → ι → ℕ×ℕ → ℕ)
    {u : ℝ} (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hI : ∀ j, (I j).card ≤ dyadicMomentOrder j+1)
    (hg : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M j i pb) (X j i pb))
    (hpA : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i,
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (hMX : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i, M j i pb < X j i pb)
    (hXM : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i, X j i pb ≤ 2*M j i pb)
    (hlarge : ∀ j, ∀ i ∈ I j, ∀ pb ∈ B j i,
      exp ((dyadicMomentOrder j : ℝ)/10) ≤ M j i pb) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*
        (∑ i ∈ I j, ∑ pb ∈ B j i,
          densityRow (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y pb.1 pb.2
              (M j i pb) (X j i pb))-rowErrorBudget y (dyadicMomentOrder j) ≤
        u^(dyadicMomentOrder j+1)*∑ i ∈ I j, ∑ pb ∈ B j i,
          coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb) := by
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  have hlength : ∀ᶠ j in atTop, (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
    simpa only [show (2 : ℝ)*(11/16)=11/8 by norm_num] using
      tendsto_dyadicMomentOrder.eventually hl
  have hhigh := eventually_overflowShells_bound I B M X (fun _ => y)
    (by linarith : 0 ≤ u) hU hI hg hpA
  filter_upwards [hlength,hhigh,eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ))]
    with j hL hh hj hN
  have hf := source_scaled_rows_floor (I j) (B j) (M j) (X j) j hj hu hU y hN hL
    (hI j) (hg j) (hpA j) (hMX j) (hXM j) (hlarge j)
  simp only [Finset.sum_sub_distrib,mul_sub] at hf
  have hupper := (le_abs_self (u^(dyadicMomentOrder j+1)*∑ i ∈ I j, ∑ pb ∈ B j i,
    overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb))).trans hh
  unfold rowErrorBudget
  rw [add_mul]
  linarith

/-- Every unselected ORIGINAL core incidence, with its sign and phase.
In particular, small unsigned divisors and unsaturated rows remain here;
they are neither completed nor assigned separate positive budgets. -/
def remainingIncidences (u y : ℝ) (j : ℕ) (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ n ∈ (coreBand u N (dyadicPrimeCount j)).filter Squarefree,
    ∑ db ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).divisorsAntidiagonal\
      selectedDivisors B M X n, incidenceWeight A N L y n db

/-- The row floor is a genuine suballocation of the existing whole
core, not a model appended to it. The signed remainder is explicit and
contains every unselected divisor incidence exactly once. -/
theorem coreConvolution_eq_remaining_rows (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M pb) (X pb)) :
    (coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re =
      remainingIncidences u y j B M X+∑ pb ∈ B, coreRow u y j pb.1 pb.2 (M pb) (X pb) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let F := (coreBand u N (dyadicPrimeCount j)).filter Squarefree
  let S := ((incidences B M X).image Prod.fst).filter
    (fun n => n ∈ coreBand u N (dyadicPrimeCount j))
  have hSF : S ⊆ F := by
    intro n hn
    obtain ⟨himage,hcore⟩ := Finset.mem_filter.mp hn
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp himage
    exact Finset.mem_filter.mpr ⟨hcore,by simpa only [he] using (incidence_owner hg hv).1⟩
  have hrows : (∑ pb ∈ B, coreRow u y j pb.1 pb.2 (M pb) (X pb)) =
      ∑ n ∈ F, ∑ db ∈ selectedDivisors B M X n, incidenceWeight A N L y n db := by
    have hmask := sum_maskedRows_eq_partial B M X u y j
      (fun n => n ∈ coreBand u N (dyadicPrimeCount j)) hg
    have hmask' : (∑ pb ∈ B, coreRow u y j pb.1 pb.2 (M pb) (X pb)) =
        (∑ n ∈ S,
          partialCoefficient (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L N
            (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
            (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
      convert hmask using 1
      · apply Finset.sum_congr rfl
        intro pb _
        unfold coreRow
        dsimp only
        apply Finset.sum_congr rfl
        intro d _
        by_cases hk : pb.1*(pb.2*d) ∈ coreBand u N (dyadicPrimeCount j)
        · simp only [N] at hk ⊢; simp only [if_pos hk]
        · simp only [N] at hk ⊢; simp only [if_neg hk]
      · congr 1
        apply Finset.sum_congr
        · ext n; simp [S,N]
        · intro n _; rfl
    rw [hmask',Complex.re_sum]
    calc
      _ = ∑ n ∈ S, ∑ db ∈ selectedDivisors B M X n, incidenceWeight A N L y n db := by
        apply Finset.sum_congr rfl
        intro n hn
        obtain ⟨v,hv,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hn).1
        have ho := incidence_owner hg hv
        have hpn : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
          rw [← he,← ho.2.2]
          simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
        exact (sum_incidenceWeight_eq_partial A N n L y _ hpn).symm
      _ = _ := by
        apply Finset.sum_subset hSF
        intro n hn hnot
        have hD : selectedDivisors B M X n=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro db hdb
          obtain ⟨v,hv,_⟩ := Finset.mem_image.mp hdb
          have hv' := Finset.mem_filter.mp hv
          exact hnot (Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨v,hv'.1,hv'.2⟩,(Finset.mem_filter.mp hn).1⟩)
        simp only [hD,Finset.sum_empty]
  have hfull : (coreConvolution u y N (dyadicPrimeCount j)).re =
      ∑ n ∈ F, ∑ db ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).divisorsAntidiagonal,
        incidenceWeight A N L y n db := by
    rw [coreConvolution,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro db _
    simp [incidenceWeight,A,L,Complex.mul_re]
  rw [hrows,hfull,remainingIncidences]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact (Finset.sum_sdiff (selectedDivisors_subset hg n)).symm

/-- The row comparison budget plus the TWO already-paid whole-carrier
differences. The nonowner allocation payment occurs exactly once. -/
def joinedRowErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  rowErrorBudget y N+
    2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256)+
      (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))

theorem tendsto_joinedRowErrorBudget (y : ℝ) :
    Tendsto (joinedRowErrorBudget y) atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ)≤19/20) (by norm_num : (19/20 : ℝ)<1)).mul_const
      (2*zetaMoebiusLogMajorantMass (1+1/256))
  have hfirst : Tendsto (fun N : ℕ =>
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256)) atTop (𝓝 0) := by
    simp only [zero_mul] at hp
    convert hp using 1
    ext N
    ring
  have hr : 0 < ZetaRieszNonownerAllocation.nonownerRate := by
    unfold ZetaRieszNonownerAllocation.nonownerRate
    positivity
  have hn := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    1 hr (ZetaRieszNonownerAllocation.nonownerRate_bounds.2.trans (by norm_num))).mul_const
      ((4/3 : ℝ)*((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
  have hsecond : Tendsto (fun N : ℕ =>
      (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) atTop (𝓝 0) := by
    simp only [pow_one,zero_mul] at hn
    convert hn using 1
    ext N
    ring
  have hsum := ((tendsto_rowErrorBudget y).add hfirst).add hsecond
  simp only [zero_add] at hsum
  change Tendsto (fun N => joinedRowErrorBudget y N) atTop (𝓝 0)
  exact hsum

/-- A whole-carrier signed floor after paying the ORIGINAL selected
row discrepancies. The remaining incidences and the density rows must
still be bounded JOINTLY; this theorem does not assert their numerical
-79/1000 floor, or discard either of their signs. -/
theorem eventually_joined_floor_with_signed_rows
    (B : ℕ → Finset (ℕ×ℕ)) (M X : ℕ → ℕ×ℕ → ℕ)
    {u : ℝ} (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hg : ∀ j, ∀ pb ∈ B j, RowGeometry (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2 (M j pb) (X j pb))
    (hpA : ∀ j, ∀ pb ∈ B j,
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (hMX : ∀ j, ∀ pb ∈ B j, M j pb < X j pb)
    (hXM : ∀ j, ∀ pb ∈ B j, X j pb ≤ 2*M j pb)
    (hlarge : ∀ j, ∀ pb ∈ B j, exp ((dyadicMomentOrder j : ℝ)/10) ≤ M j pb) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*
        (remainingIncidences u y j (B j) (M j) (X j)+
          ∑ pb ∈ B j, densityRow (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y pb.1 pb.2 (M j pb) (X j pb))-
        joinedRowErrorBudget y (dyadicMomentOrder j) ≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*
            ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have hrows := eventually_signed_rows_floor (fun _ => ({()}: Finset Unit))
    (fun j (_ : Unit) => B j) (fun j (_ : Unit) => M j) (fun j (_ : Unit) => X j)
    hu hU y (fun j => by simp)
    (fun j _ _ => hg j) (fun j _ _ => hpA j) (fun j _ _ => hMX j)
    (fun j _ _ => hXM j) (fun j _ _ => hlarge j)
  simp only [Finset.sum_singleton] at hrows
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hrows,tendsto_dyadicMomentOrder.eventually hl] with j hj hL
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  have hL' : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by nlinarith only [hL]
  have hc := joined_sub_convolution_bound (by linarith : 0 ≤ u) hU N K y hL'
  have hre := (Complex.abs_re_le_norm ((u : ℂ)^(N+1)*
    (ZetaRieszGammaJoint.joinedPhysical u y N K-coreConvolution u y N K))).trans hc
  have hneg := (abs_le.mp hre).1
  have heq : (((u : ℂ)^(N+1)*
      (ZetaRieszGammaJoint.joinedPhysical u y N K-coreConvolution u y N K)).re) =
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re-
        u^(N+1)*(coreConvolution u y N K).re := by
    simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.sub_re,zero_mul,sub_zero]
    ring
  rw [heq,coreConvolution_eq_remaining_rows (B j) (M j) (X j) u y j (hg j)] at hneg
  change u^(N+1)*(∑ pb ∈ B j, densityRow N
    (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (M j pb) (X j pb))-
      rowErrorBudget y N ≤ u^(N+1)*∑ pb ∈ B j, coreRow u y j pb.1 pb.2 (M j pb) (X j pb) at hj
  unfold joinedRowErrorBudget
  change u^(N+1)*_-(rowErrorBudget y N+_+_) ≤ _
  nlinarith only [hj,hneg]

/-! ## Ownership geometry independent of the actual Riesz length

The auxiliary length below is used ONLY to certify largest-prime
ownership and integer window geometry. Every arithmetic kernel, Riesz
hinge, physical-prime set, allocation, phase and count cut still uses the
original `SquarefreeVaughanLogSource.length`. These strengthened APIs
allow a concrete unsaturated row to receive the same signed payment.
-/

theorem row_mem_core_iff_of_geometry (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {ℒ : ℝ} {p b M X d : ℕ}
    (hg : RowGeometry (dyadicMomentOrder j) ℒ p b M X)
    (hd : d ∈ Finset.Ioc M X) (hsieve : sieve (p*b).primeFactors d ≠ 0) :
    p*(b*d) ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ↔
      (p*(b*d)).primeFactors.card < dyadicPrimeCount j := by
  have hgeom := hg
  obtain ⟨hp,hb,hbs,hpb,hbmax,hactive,hM,hlo,hhi,hsat,hshare⟩ := hg
  have hco := row_cofactor_geometry hgeom hd hsieve
  have hd0 : 0 < d := by have := Finset.mem_Ioc.mp hd; omega
  have hb0 : 0 < b := by omega
  have hn : Squarefree (p*(b*d)) := by
    have hh := hsieve
    rw [sieve_eq_product_squarefree (squarefree_outer hgeom)] at hh
    split_ifs at hh with h
    · simpa only [mul_assoc] using h
    · contradiction
  have hcnt : (p*(b*d)).primeFactors.card=(b*d).primeFactors.card+1 := by
    rw [Nat.primeFactors_mul hp.ne_zero hco.1.ne_zero,hp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem]
    intro hh
    exact (lt_irrefl p) (hco.2.2 p hh)
  have ht : log (p*(b*d) : ℕ)=log (p*b : ℕ)+log d := by
    rw [show p*(b*d)=(p*b)*d by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hb0).ne') (by exact_mod_cast hd0.ne')]
  have hdM : log M < log d := (log_lt_log_iff
    (by exact_mod_cast hM) (by exact_mod_cast hd0)).mpr
      (by exact_mod_cast (Finset.mem_Ioc.mp hd).1)
  have hdX : log d ≤ log X := log_le_log
    (by exact_mod_cast hd0) (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
  constructor
  · intro hncore
    have hnar := (Finset.mem_filter.mp hncore).1
    have hnd := (Finset.mem_filter.mp hnar).1
    have hret := (Finset.mem_sdiff.mp hnd).1
    have hmask := (Finset.mem_sdiff.mp hret).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmask).1).2.2
  · intro hK
    apply mem_core_of_strict_prime_share j hj hu hU hL hn (by omega) hK
      (by rw [ht]; linarith) (by rw [ht]; linarith)
    intro q hq
    have hqp : q ≤ p := by
      rw [Nat.primeFactors_mul hp.ne_zero hco.1.ne_zero,hp.primeFactors,
        Finset.mem_union,Finset.mem_singleton] at hq
      exact hq.elim (fun h => h ▸ le_rfl) (fun h => (hco.2.2 q h).le)
    have hlogqp : log q ≤ log p := log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast hqp)
    rw [ht]
    linarith

theorem coreRow_add_overflow_of_geometry (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {ℒ : ℝ} {p b M X : ℕ}
    (hg : RowGeometry (dyadicMomentOrder j) ℒ p b M X)
    (hpA : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)) :
    coreRow u y j p b M X+overflowRow u y j p b M X =
      densityRow (dyadicMomentOrder j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b M X+
      ownedShellDiscrepancy (dyadicMomentOrder j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b M X := by
  have he := ownedShellDiscrepancy_eq_literal
    (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y
    hg.1 (by have := hg.2.1; omega) hg.2.2.2.2.2.2.1 hpA
    (fun d hd hs => row_cofactor_geometry hg hd hs)
  rw [he]
  unfold coreRow overflowRow densityRow
  dsimp only
  rw [← Finset.sum_add_distrib]
  have hrows : (∑ d ∈ Finset.Ioc M X,
      ((if p*(b*d) ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b d
        else 0)+
      (if dyadicPrimeCount j ≤ (p*(b*d)).primeFactors.card then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b d
        else 0))) =
      ∑ d ∈ Finset.Ioc M X,
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y p b d := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hz : sieve (p*b).primeFactors d=0
    · simp [rowAtom,hz]
    have hc := row_mem_core_iff_of_geometry j hj hu hU hL hg hd hz
    by_cases hk : (p*(b*d)).primeFactors.card < dyadicPrimeCount j
    · rw [if_pos (hc.mpr hk),if_neg (by omega),add_zero]
    · rw [if_neg (fun h => hk (hc.mp h)),if_pos (by omega),zero_add]
  rw [hrows]
  simp only [rowAtom]
  ring

private theorem rowAtom_eq_incidenceWeight_of_geometry (A : Finset ℕ) {N p b M X d : ℕ} {L ℒ : ℝ}
    (y : ℝ) (hg : RowGeometry N ℒ p b M X) (hd : d ∈ Finset.Ioc M X)
    (hs : sieve (p*b).primeFactors d ≠ 0) :
    rowAtom A N L y p b d = incidenceWeight A N L y (p*(b*d)) (d,b) := by
  have hc := row_cofactor_geometry hg hd hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul p (b*d) hg.1 hc.1.ne_zero hc.2.2
  have hs1 : sieve (p*b).primeFactors d=1 := by
    unfold sieve at *
    split_ifs at * <;> simp_all
  simp only [rowAtom,incidenceWeight,ho,Nat.mul_div_cancel_left _ hg.1.pos,hs1,mul_one]

theorem sum_maskedRows_eq_partial_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (χ : ℕ → Prop) (ℒ : ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) ℒ pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        χ,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n db => if χ n then
    incidenceWeight A N L y n db else 0
  have hrows : (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then rowAtom A N L y pb.1 pb.2 d else 0) =
      ∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
        if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0 := by
    apply Finset.sum_congr rfl
    intro pb hpb
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : sieve (pb.1*pb.2).primeFactors d=0
    · simp [rowAtom,hs]
    rw [if_pos hs,rowAtom_eq_incidenceWeight_of_geometry A y (hg pb hpb) hd hs]
  rw [hrows,sum_rows_eq_incidences B M X hg f,sum_incidences_eq_fibers]
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : χ n
  · simp only [f,if_pos hk]
    have he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      obtain ⟨v,hv,hnv⟩ := Finset.mem_image.mp hn
      have ho := incidence_owner hg hv
      rw [← hnv,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    exact sum_incidenceWeight_eq_partial A N n L y _ he
  · simp only [f,if_neg hk,Finset.sum_const_zero]

theorem sum_overflow_eq_partial_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (ℒ : ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) ℒ pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, overflowRow u y j pb.1 pb.2 (M pb) (X pb)) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        (fun n => dyadicPrimeCount j ≤ n.primeFactors.card),
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  convert sum_maskedRows_eq_partial_of_geometry B M X u y j
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card) ℒ hg using 1
  · apply Finset.sum_congr rfl
    intro pb _
    unfold overflowRow
    dsimp only
    apply Finset.sum_congr rfl
    intro d _
    by_cases hk : dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card <;> simp [hk]
  · congr 1
    apply Finset.sum_congr
    · ext n; simp
    · intro n _; rfl

private theorem incidence_log_le_twice_actual {u ℒ : ℝ} {j : ℕ}
    {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ}
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) ℒ pb.1 pb.2 (M pb) (X pb))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    log v.1 ≤ 2*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  have h := (row_window (hg pb hpb) hd).2
  nlinarith [Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]

theorem overflowRows_bound_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y ℒ : ℝ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) ℒ pb.1 pb.2 (M pb) (X pb)) :
    |u^(dyadicMomentOrder j+1)*∑ pb ∈ B,
      overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
        highCountConstant*(dyadicMomentOrder j : ℝ)*(97/100 : ℝ)^(dyadicMomentOrder j)*
          exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ((incidences B M X).image Prod.fst).filter
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card)
  let c := fun n => partialCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
        (selectedDivisors B M X n)/2
  have hn n (h : n ∈ S) : ∃ v ∈ incidences B M X, v.1=n :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).1
  have hsf n (h : n ∈ S) : Squarefree n := by
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using (incidence_owner hg hv).1
  have hband : S ⊆ zetaPrimeLogBand N := by
    intro n h
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using incidence_band
      (by dsimp [N,dyadicMomentOrder,dyadicPrimeCount]; positivity) hg hv
  have hc n (h : n ∈ S) : ‖c n‖ ≤ zetaMoebiusLogMajorant n := by
    obtain ⟨v,hv,he⟩ := hn n h
    have ho := incidence_owner hg hv
    have hpn : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      rw [← he,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    have hp : 0 < ZetaRieszPrimeEndpoint.largestPrime n := by
      by_contra hh
      have h0 : ZetaRieszPrimeEndpoint.largestPrime n=0 := by omega
      rw [h0,zero_mul] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have ha : (0 : ℕ) < n/ZetaRieszPrimeEndpoint.largestPrime n := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0,mul_zero] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have hT : log n ≤ 2*L := by
      simpa only [he] using incidence_log_le_twice_actual hL hg hv
    have hdom := partialCoefficient_bound
      (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      N hp ha (selectedDivisors B M X n) (selectedDivisors_subset hg n)
      (SquarefreeVaughanLogSource.length_pos u N) (by simpa only [hpn] using hT)
    rw [hpn] at hdom
    dsimp [c]
    rw [norm_div]
    norm_num
    linarith
  have hnorm := ZetaRieszWeightedCount.norm_normalized_many_dyadic_le S c hc 1 j y hu hU
    (by norm_num : (0 : ℝ)<49/100) (by norm_num : (49/100 : ℝ)<1/2) hsf hband
    (fun n h => (Finset.mem_filter.mp h).2)
  have hP : (∑ k ∈ (1 : Polynomial ℂ).support,
      ‖(1 : Polynomial ℂ).coeff k‖*(49/100 : ℝ)⁻¹^k)=1 := by
    rw [← Polynomial.C_1,Polynomial.support_C (by norm_num : (1 : ℂ)≠0)]
    simp
  rw [hP,mul_one,show (3/2 : ℝ)-49/100=101/100 by norm_num] at hnorm
  have hreal : |u^(N+1)*∑ pb ∈ B, overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
      2*‖(u : ℂ)^(N+1)*∑ n ∈ S,
        c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
    rw [sum_overflow_eq_partial_of_geometry B M X u y j ℒ hg]
    have heq : (u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
        2*((u : ℂ)^(N+1)*∑ n ∈ S,
          c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
      calc
        _ = (u : ℂ)^(N+1)*(2*∑ n ∈ S,
            c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [ZetaRieszJointAllocation.filter_one_eq]
          dsimp [c]
          ring
        _ = _ := by ring
    have hre := Complex.abs_re_le_norm
      ((u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    have hrhs : ‖(u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
        2*‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
      rw [heq,norm_mul]
      norm_num
    simpa only [S,L,N,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre.trans_eq hrhs
  apply hreal.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ)≤2)).trans _)
  have hr : 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) ≤ 97/100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hr0 : 0 ≤ 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  dsimp [highCountConstant]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr N)
    (by dsimp [ZetaRieszWideOwnerAudit.radiusCeiling]
        positivity [log_pos (by norm_num : (1 : ℝ)<2)] : 0 ≤ 64*ZetaRieszWideOwnerAudit.radiusCeiling*log 2*N)
  have he := mul_le_mul_of_nonneg_right hp
    (exp_pos (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))).le
  convert he using 1
  ring

end RiemannGaussian.ZetaRieszSaturatedRowFloor
