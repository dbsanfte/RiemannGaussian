/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePhaseSumRecovery

/-!
# Linear seed targets with complete factor-sum recovery

The original denominator-one seed at the true residue has a nonnegative
quadratic-size index at every factor ratio. A bounded common seed hit
always exposes the literal factor sum, so one public candidate suffices.
Only the original linear residue cache is queried. Shared blocking gives
a subquadratic explicit coefficient/point source, with its remaining
superlinear input floor kept separate from full bit-operation complexity.
-/

namespace RiemannGaussian.SemiprimeSeedSumAcquisition

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeWideWrapCoverage SemiprimeWrapIndexRecovery SemiprimeForcedRowSeparation
open SemiprimeGlobalPhaseCancellation SemiprimePhaseSumRecovery
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeLongPowerRouting SemiprimeDensePeriodForcing SemiprimeIntervalJet
open SemiprimeSharedIntervalJet Polynomial

/-- Choose the common block width for the actual m-1 public seed targets. -/
def seedBlockWidth (m : ℕ) : ℕ := sharedWidth m (m-1)

/-- Pad one common seed interval, with no per-seed tail polynomial. -/
def seedBlockCount (m : ℕ) : ℕ := blockCount m (seedBlockWidth m)

/-- The original absolute seed indices are retained in the padded interval. -/
def seedLength (m : ℕ) : ℕ := seedBlockCount m*seedBlockWidth m

/-- The common block is positive for every public input. -/
theorem seedBlockWidth_pos (m : ℕ) : 0<seedBlockWidth m := sharedWidth_pos _ _

/-- At the actual asymptotic width, padding covers every proved original
seed index and stays below the retained local simple-root periods. -/
theorem seedLength_bounds {m : ℕ} (hm : 4≤m) :
    2*m^2+2≤seedLength m ∧ seedLength m≤4*m^2 := by
  have hw : seedBlockWidth m≤m^2 := sharedWidth_le_quadratic hm (by omega)
  have hlo := padded_contains_original (B:=m) (seedBlockWidth_pos m)
  have hhi := padded_length_le (B:=m) (m:=seedBlockWidth m)
  have hm2 : 1≤m^2 := by nlinarith only [hm]
  unfold seedLength seedBlockCount
  constructor <;> nlinarith only [hlo,hhi,hw,hm2]

/-- The full seed base uses the exact original denominator-one index. -/
def seedBase {G : Type*} [CommGroup G] (g : G) (m : ℕ) : G := g^(m^2)

/-- The rough local orders are preserved by the original seed base, so
the whole padded seed interval has simple roots in both prime fields. -/
theorem long_seed_interval_periods {p q m : ℕ} (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    seedLength m≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) ∧
    seedLength m≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) := by
  have heP : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))=
      orderOf (leftUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      ((projectedUnit g m)^(m^2)) : (ZMod p)ˣ) : ZMod p)=_
    rw [orderOf_units,map_pow]
    exact ((rough_coprime_small (by omega : 0<m) le_rfl
      hlong.2.2.2.2.2.1).pow_right 2).orderOf_pow
  have heQ : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))=
      orderOf (rightUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom)
      ((projectedUnit g m)^(m^2)) : (ZMod q)ˣ) : ZMod q)=_
    rw [orderOf_units,map_pow]
    exact ((rough_coprime_small (by omega : 0<m) le_rfl
      hlong.2.2.2.2.2.2).pow_right 2).orderOf_pow
  rw [heP,heQ]
  have hbound := (seedLength_bounds hm).2
  have hP := hlong.2.2.2.1.1
  have hQ := hlong.2.2.2.1.2
  constructor <;> nlinarith only [hP,hQ,hbound]

/-- A common seed index has an automatically integral sum signal. -/
def seedSum {G : Type*} (m : ℕ) (s : ProgressionSeed G) (r : ℕ) : ℤ :=
  1-cachedOffset m s+(m : ℤ)^2*r

/-- Every bounded common seed hit, including a false private-row tag,
has the actual factor sum. No hidden numerical order is queried. -/
theorem common_seed_sum_exact {p q m j r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hr : r<seedLength m)
    (hhit : (progressionSeed (projectedUnit g m) (p*q) m j).step=
      (seedBase (projectedUnit g m) m)^r) :
    seedSum m (progressionSeed (projectedUnit g m) (p*q) m j) r=(p : ℤ)+q := by
  let h := projectedUnit g m
  let S := seedSum m (progressionSeed h (p*q) m j) r
  have hc : j.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hh := hhit
  rw [seed_step_offset h hmprime.pos hc] at hh
  simp only [seedBase,←zpow_natCast,←zpow_mul] at hh
  have hd := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hh
  have he : ((p*q : ℕ)+seedOffset (p*q) m j)-(m^2 : ℕ)*(r : ℤ)=
      (p*q : ℕ)+1-S := by
    dsimp only [S,seedSum]
    rw [cachedOffset_seed,Nat.cast_pow]
    ring
  rw [he] at hd
  have hphi := global_order_dvd_euler hp hq hpq h
  have hphiZ : (orderOf h : ℤ)∣(((p-1)*(q-1) : ℕ) : ℤ) := by exact_mod_cast hphi
  have heuler : (((p-1)*(q-1) : ℕ) : ℤ)=(p*q : ℕ)+1-((p : ℤ)+q) := by
    simp only [Nat.cast_mul,Nat.cast_sub hp.one_le,Nat.cast_sub hq.one_le,Nat.cast_one]
    ring
  rw [heuler] at hphiZ
  have hdiff := hd.sub hphiZ
  have hid : ((p*q : ℕ)+1-S)-((p*q : ℕ)+1-((p : ℤ)+q))=(p : ℤ)+q-S := by ring
  rw [hid] at hdiff
  have hδ := seedOffset_bounds (N:=p*q) (by omega) hj hjm
  have hrZ : (r : ℤ)≤4*(m : ℤ)^2 := by
    exact_mod_cast hr.le.trans (seedLength_bounds hm).2
  have hprod := mul_le_mul_of_nonneg_left hrZ (sq_nonneg (m : ℤ))
  have hS : |S|≤5*(m : ℤ)^4 := by
    have hmZ : (4 : ℤ)≤m := by exact_mod_cast hm
    have hm2 : 3*(m : ℤ)^2+1≤(m : ℤ)^4 := by
      have hh := mul_nonneg (by nlinarith only [hmZ] : (0 : ℤ)≤(m : ℤ)^2-4)
        (by positivity : (0 : ℤ)≤(m : ℤ)^2)
      nlinarith only [hh,hmZ]
    apply abs_le.mpr
    dsimp only [S,seedSum]
    rw [cachedOffset_seed]
    constructor <;> nlinarith only [hδ.1,hδ.2,hprod,hm2,
      show (0 : ℤ)≤(m : ℤ)^2*r by positivity]
  have hsum := factor_sum_bound hp hq hmprime.pos hsize h hlong.2.2.2.1
  have hsumZ : (p : ℤ)+q≤2*(m : ℤ)^4 := by exact_mod_cast hsum
  have hbound := abs_sub ((p : ℤ)+q) S
  rw [abs_of_nonneg (by positivity : (0 : ℤ)≤(p : ℤ)+q)] at hbound
  have hab : |(p : ℤ)+q-S|<(orderOf h : ℤ) := by
    have ho : 16*(m : ℤ)^4<(orderOf h : ℤ) := by
      exact_mod_cast long_global_order_bound hp hq hpq g hlong
    nlinarith only [hbound,hS,hsumZ,ho]
  rw [←Int.natCast_natAbs] at hab
  have habN : ((p : ℤ)+q-S).natAbs<(orderOf h : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using
      (show ((p : ℤ)+q-S).natAbs<orderOf h by exact_mod_cast hab)
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiff habN
  change S=(p : ℤ)+q
  omega

/-- A public bounded seed index makes one ordinary sum candidate, then
checks its proper GCD independently. -/
def recoverSeedSum {G : Type*} (N m : ℕ) (s : ProgressionSeed G) (r : ℕ) : Option ℕ :=
  checkedSignal N (factorSumCandidate N (seedSum m s r))

/-- A seed sum guess can return only a checked proper divisor. -/
theorem recoverSeedSum_sound {G : Type*} {N m r d : ℕ} (s : ProgressionSeed G)
    (he : recoverSeedSum N m s r=some d) : ProperDivisor N d := checkedSignal_sound he

/-- Any canonical bounded common seed hit recovers the smaller prime,
even if that seed is not the exact factor's residue row. -/
theorem recoverSeedSum_common {p q m j r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hr : r<seedLength m)
    (hhit : (progressionSeed (projectedUnit g m) (p*q) m j).step=
      (seedBase (projectedUnit g m) m)^r) :
    recoverSeedSum (p*q) m (progressionSeed (projectedUnit g m) (p*q) m j) r=some p := by
  have hs := common_seed_sum_exact hp hq hpq.ne hm hmprime hsize g hlong hj hjm hr hhit
  unfold recoverSeedSum
  rw [hs,factorSumCandidate_exact hpq.le,checkedSignal,Nat.gcd_eq_right (dvd_mul_right p q),if_pos]
  exact ⟨hp.one_lt,by nlinarith only [hp.pos,hq.one_lt]⟩

/-- Read one original seed over the common padded absolute index range. -/
noncomputable def readSeed {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) : Option (ℕ⊕ℕ) :=
  recoverTaggedInterval (seedBase g m) s.step (seedLength m) (2*m)

/-- Every publicly returned common seed index is bounded and verified
against the exact original global seed equation. -/
theorem readSeed_index_sound {N m r : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (he : readSeed g m s=some (Sum.inr r)) :
    r<seedLength m ∧ s.step=(seedBase g m)^r := by
  obtain ⟨hr,hvalue⟩ := recoverTaggedInterval_index_sound _ _ he
  refine ⟨hr,?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val] using hvalue

/-- On the actual long branch, EVERY common original seed reader tag
returns the smaller factor, including tags at other public residues. -/
theorem readSeed_common_recovers {p q m r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (s : ProgressionSeed ((ZMod (p*q))ˣ))
    (hs : s∈progressionSeeds (projectedUnit g m) (p*q) m)
    (he : readSeed (projectedUnit g m) m s=some (Sum.inr r)) :
    recoverSeedSum (p*q) m s r=some p := by
  obtain ⟨hj,hjm,hseed⟩ := cached_seed_source hs
  obtain ⟨hr,hhit⟩ := readSeed_index_sound _ _ he
  rw [hseed] at hhit ⊢
  exact recoverSeedSum_common hp hq hpq hm hmprime hsize g hlong hj hjm hr hhit

/-- Exact denominator-one arithmetic forces a public seed reader
outcome at every remaining factor ratio. No denominator grid is needed. -/
theorem long_seed_reader_witness {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ s∈progressionSeeds (projectedUnit g m) (p*q) m,
      readSeed (projectedUnit g m) m s≠none := by
  let : Fact p.Prime := ⟨hp⟩
  have hm1 : 1<m := by omega
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    omega
  obtain ⟨I,hI,hindex⟩ := row_index_exists hp.pos hN
    (denseRow_relation (N:=p*q) (j:=p%m) (t:=1) (by omega) hj false)
  have hden : (denseRow (p*q) m (p%m) 1 false).t=(1 : ℤ) := rfl
  rw [hden,one_mul] at hI
  change (m : ℤ)^2*I=(seedRow (p*q) m (p%m)).a*p+
    (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q at hI
  have hbounds := seed_index_bounds hm1 hpq.le hprefix hsize hI
  let r := I.toNat
  have hrI : (r : ℤ)=I := Int.toNat_of_nonneg hbounds.1
  have hr : r<seedLength m := by
    have hl : (2*m^2+2 : ℕ)≤seedLength m := (seedLength_bounds hm).1
    have hupper := hbounds.2
    change I≤(2*m^2+1 : ℕ) at hupper
    omega
  let h := projectedUnit g m
  let s := progressionSeed h (p*q) m (p%m)
  have hs : s∈progressionSeeds h (p*q) m := progressionSeed_mem h hj₀ (Nat.mod_lt p (by omega))
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (seedRow (p*q) m (p%m)).a (seedRow (p*q) m (p%m)).b
      (seedRow (p*q) m (p%m)).c (1 : ℤ) := by
    simpa only [Nat.cast_mul,Nat.cast_one,seedRow,denseRow,liftRow] using
      (denseRow_relation (N:=p*q) (j:=p%m) (t:=1) (by omega) hj false)
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hh := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : (leftUnit h)^((p : ℤ)-1)=1 := by
    have hh := ZMod.units_pow_card_sub_one_eq_one p (leftUnit h)
    simpa only [←zpow_natCast,Nat.cast_sub hp.one_le,Nat.cast_one] using hh
  have hhit := quotient_row_power_hit (leftUnit h) hcoord hrel hindex
    (by exact_mod_cast hp.ne_zero) hperiod
  have hPu : leftUnit s.step=(leftUnit (seedBase h m))^r := by
    simp only [s,progressionSeed,leftUnit,map_zpow,seedBase,map_pow]
    rw [←zpow_natCast,←zpow_natCast,←zpow_mul,hrI]
    exact hhit
  have hProot : ZMod.castHom (dvd_mul_right p q) (ZMod p) (s.step : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q)))^r := by
    have hh := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hPu
    simpa [leftUnit,RingHom.toMonoidHom] using hh
  have hperiods := long_seed_interval_periods hm g hlong
  have hcover : seedLength m≤(2*m)^2 := by nlinarith only [(seedLength_bounds hm).2]
  have hreader := recoverTaggedInterval_preserves_root hp hq hpq (seedBase h m) s.step hr
    hcover hperiods.1 hperiods.2 hProot
  refine ⟨s,hs,?_⟩
  intro hnone
  rcases hreader with ⟨d,hd⟩|hd
  · change readSeed h m s=some (Sum.inl d) at hd
    rw [hnone] at hd
    cases hd
  · change readSeed h m s=some (Sum.inr r) at hd
    rw [hnone] at hd
    cases hd

/-- Scan only the original linear seed cache. The first reader outcome
ends the scan; every common outcome is a true sum on the actual long branch. -/
noncomputable def scanSeedSums {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ))→Option ℕ
  | [] => none
  | s::xs => match readSeed g m s with
    | none => scanSeedSums g m xs
    | some (Sum.inl d) => some d
    | some (Sum.inr r) => recoverSeedSum N m s r

/-- Every returned seed-scan factor is independently checked. -/
theorem scanSeedSums_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    (xs : List (ProgressionSeed ((ZMod N)ˣ))) (he : scanSeedSums g m xs=some d) :
    ProperDivisor N d := by
  induction xs with
  | nil => simp only [scanSeedSums] at he; cases he
  | cons s xs ih =>
    simp only [scanSeedSums] at he
    split at he
    · exact ih he
    · rename_i e hre
      cases he
      exact recoverTaggedInterval_factor_sound _ _ hre
    · exact recoverSeedSum_sound _ he

/-- Any remaining source suffix with an arithmetic reader witness
succeeds. A false earlier common seed tag also factors immediately. -/
theorem scanSeedSums_complete_of_witness {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (xs : List (ProgressionSeed ((ZMod (p*q))ˣ)))
    (hsource : ∀ s∈xs,s∈progressionSeeds (projectedUnit g m) (p*q) m)
    (hwitness : ∃ s∈xs,readSeed (projectedUnit g m) m s≠none) :
    ∃ d, scanSeedSums (projectedUnit g m) m xs=some d := by
  induction xs with
  | nil => obtain ⟨s,hs,_⟩ := hwitness; cases hs
  | cons s xs ih =>
    cases he : readSeed (projectedUnit g m) m s with
    | none =>
      obtain ⟨w,hw,hread⟩ := hwitness
      have hwtail : w∈xs := by
        rcases List.mem_cons.mp hw with heq|hmem
        · subst w
          exact False.elim (hread he)
        · exact hmem
      obtain ⟨d,hd⟩ := ih (fun w hw => hsource w (List.mem_cons_of_mem s hw)) ⟨w,hwtail,hread⟩
      exact ⟨d,by simp only [scanSeedSums,he,hd]⟩
    | some outcome =>
      cases outcome with
      | inl d => exact ⟨d,by simp only [scanSeedSums,he]⟩
      | inr r =>
        have hr := readSeed_common_recovers hp hq hpq hm hmprime hsize g hlong s
          (hsource s List.mem_cons_self) he
        exact ⟨p,by simp only [scanSeedSums,he,hr]⟩

/-- The linear original residue target list is complete for every
remaining distinct-prime ratio, without any denominator or wrap grid. -/
theorem scanSeedSums_complete {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m) (hmprime : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ d, scanSeedSums (projectedUnit g m) m
      (progressionSeeds (projectedUnit g m) (p*q) m)=some d :=
  scanSeedSums_complete_of_witness hp hq hpq hm hmprime hsize g hlong _ (fun _ hs => hs)
    (long_seed_reader_witness hp hq hpq hm hprefix hN hsize g hlong)

/-- Construct the three common block polynomials once, independently
of every seed target and absolute block index. -/
noncomputable def seedBlockPolynomials {R : Type*} [CommRing R] (alpha : R) (w : ℕ) :
    R[X]×R[X]×R[X] :=
  let P := SemiprimeCartesianCompletion.rootPolynomial (Finset.range w) (fun u => alpha^u)
  (P,P.derivative,babyBasePolynomial alpha w)

/-- Restore one original absolute block from the supplied common
polynomials, retaining both marked derivatives through zero products. -/
noncomputable def seedBlockJet {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (w j : ℕ) (P : R[X]×R[X]×R[X]) : R×R×R :=
  let z := normalizedPoint alpha x w j
  let c := (alpha : R)^(j*w)
  let h := c^w
  let v := SemiprimeMergedIndexAcquisition.evaluateMergedPolynomials P z
  (h*v.1,h*((((alpha^(j*w))⁻¹ : Rˣ) : R))*v.2.1,
    h*((j*w : ℕ)*((w : ℕ) : R)*v.1+v.2.2-((j*w : ℕ) : R)*z*v.2.1))

/-- Supplying the exact common block polynomials gives the original
block product and both absolute-index derivatives, including zeros. -/
theorem seedBlockJet_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    {w : ℕ} (hw : 0<w) (j : ℕ) :
    seedBlockJet alpha x w j (seedBlockPolynomials (alpha : R) w)=
      blockJet (alpha : R) x (j*w) w := by
  change normalizedBlockJet alpha x w j=blockJet (alpha : R) x (j*w) w
  exact normalizedBlockJet_eq alpha x hw j

/-- Compose original blocks using supplied common polynomials. Each
seed's three channels stay separate from every other seed's channels. -/
noncomputable def sharedSeedJet {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (w J : ℕ) (P : R[X]×R[X]×R[X]) : R×R×R :=
  (List.range J).foldl (fun v j => combineJets v (seedBlockJet alpha x w j P)) (1,0,0)

/-- The common-polynomial fold is exactly the entire padded original
interval's detector and both marked derivatives, over any commutative ring. -/
theorem sharedSeedJet_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    {w : ℕ} (hw : 0<w) (J : ℕ) :
    sharedSeedJet alpha x w J (seedBlockPolynomials (alpha : R) w)=
      (intervalProduct (alpha : R) x (J*w),targetDerivative (alpha : R) x (J*w),
        baseDerivative (alpha : R) x (J*w)) := by
  simp only [sharedSeedJet,seedBlockJet_exact alpha x hw]
  exact blockedJet_exact (alpha : R) x w J

/-- Acquire the original linear seed batch. The common polynomial
construction occurs outside both the seed map and every block fold. -/
noncomputable def seedBatchJets {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ)×(ZMod N×ZMod N×ZMod N)) :=
  let alpha := seedBase g m
  let w := seedBlockWidth m
  let P := seedBlockPolynomials (alpha : ZMod N) w
  (progressionSeeds g N m).map fun s =>
    (s,sharedSeedJet alpha (s.step : ZMod N) w (seedBlockCount m) P)

/-- There is one acquired triple per original residue, with no
denominator, full-wrap or interval-root target axis. -/
theorem seedBatchJets_length {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    (seedBatchJets g m).length=m-1 := by
  simp only [seedBatchJets,List.length_map,progressionSeeds_length]

/-- Read the supplied original seed scalars with the unchanged index
decoder, whose factor and global-index channels are both retained. -/
noncomputable def readSeedJet {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (jet : ZMod N×ZMod N×ZMod N) : Option (ℕ⊕ℕ) :=
  recoverTaggedJet (seedBase g m) s.step (seedLength m) (2*m) jet

/-- Shared acquisition supplies exactly the original padded seed reader. -/
theorem readSeedJet_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) :
    readSeedJet g m s
      (sharedSeedJet (seedBase g m) (s.step : ZMod N) (seedBlockWidth m)
        (seedBlockCount m) (seedBlockPolynomials
          ((seedBase g m : (ZMod N)ˣ) : ZMod N) (seedBlockWidth m)))=readSeed g m s := by
  simp only [readSeedJet,sharedSeedJet_exact _ _ (seedBlockWidth_pos m),
    readSeed,recoverTaggedInterval,seedLength]

/-- Consume the aligned original seed batch; the first reader outcome
ends the scan, so at most one sum candidate is constructed. -/
noncomputable def scanSeedJetBatch {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ)×(ZMod N×ZMod N×ZMod N))→Option ℕ
  | [] => none
  | (s,jet)::xs => match readSeedJet g m s jet with
    | none => scanSeedJetBatch g m xs
    | some (Sum.inl d) => some d
    | some (Sum.inr r) => recoverSeedSum N m s r

/-- Exact labelled acquisition preserves the complete original seed
scan for every seed list, not only a privately successful member. -/
theorem scanSeedJetBatch_map_exact {N m : ℕ} (g : (ZMod N)ˣ)
    (xs : List (ProgressionSeed ((ZMod N)ˣ))) :
    scanSeedJetBatch g m (xs.map fun s =>
      (s,sharedSeedJet (seedBase g m) (s.step : ZMod N) (seedBlockWidth m)
        (seedBlockCount m) (seedBlockPolynomials
          ((seedBase g m : (ZMod N)ˣ) : ZMod N) (seedBlockWidth m))))=
      scanSeedSums g m xs := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    simp only [List.map_cons,scanSeedJetBatch,readSeedJet_exact,scanSeedSums]
    cases he : readSeed g m s with
    | none => exact ih
    | some outcome => cases outcome <;> rfl

/-- The shared whole batch equals the complete linear original seed scan. -/
theorem seedBatch_scan_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    scanSeedJetBatch g m (seedBatchJets g m)=scanSeedSums g m (progressionSeeds g N m) :=
  scanSeedJetBatch_map_exact g _

/-- The actual public matched-width long output succeeds using ONLY
the original linear seed targets and their shared block acquisition. -/
theorem long_public_route_seed_batch_succeeds {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ d, scanSeedJetBatch h m (seedBatchJets h m)=some d ∧ ProperDivisor (p*q) d := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hmBounds.1
  have hbudget : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  have hcover : m^2<p*q := public_modulus_prefix_below_input hN hB
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hmprime : m.Prime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hmprime.pos
    (by have hh := hmprime.two_le; nlinarith only [hh] : m≤m^2)
  obtain ⟨d,hd⟩ := scanSeedSums_complete hp hq hpq hm hmprime hprefix.le hcop.symm
    hbudget g hlong
  exact ⟨hc,d,by rwa [seedBatch_scan_exact],scanSeedSums_sound _ _ hd⟩

/-- All normalized acquisition points, keeping the original seed labels
in the batch rather than pooling different seed jets. -/
def seedBatchPoints {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : List (ZMod N) :=
  sharedPoints (seedBase g m) ((progressionSeeds g N m).map fun s => (s.step : ZMod N))
    (seedBlockWidth m) (seedBlockCount m)

/-- There are exactly original seeds times common blocks normalized
points; the full quadratic interval is not materialized as targets. -/
theorem seedBatchPoints_length {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    (seedBatchPoints g m).length=(m-1)*seedBlockCount m := by
  simp only [seedBatchPoints,sharedPoints_length,List.length_map,progressionSeeds_length]

/-- Root inputs for the common block, normalized evaluation points,
original cached seeds and one constant. This is not a bit clock. -/
def seedSourceInput {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : ℕ :=
  seedBlockWidth m+(seedBatchPoints g m).length+(progressionSeeds g N m).length+1

/-- Exact construction input count of the shared original seed source. -/
theorem seedSourceInput_eq {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    seedSourceInput g m=seedBlockWidth m+(m-1)*seedBlockCount m+(m-1)+1 := by
  simp only [seedSourceInput,seedBatchPoints_length,progressionSeeds_length]

/-- The original linear cache fits the selected common block width. -/
theorem seedBlockWidth_ge_modulus {m : ℕ} (hm : 4≤m) : m≤seedBlockWidth m := by
  have hR : 1≤m-1 := by omega
  have hh := Nat.mul_le_mul_right (3*m^2+1) hR
  have hsq : m^2≤(m-1)*(3*m^2+1) := by nlinarith only [hh]
  have hs := Nat.le_sqrt'.mpr hsq
  unfold seedBlockWidth sharedWidth
  omega

/-- The complete shared root/point/cache source has subquadratic input
scale. Fast evaluation and full factorizer bit/memory costs are not priced. -/
theorem seedSourceInput_le_four_width {N m : ℕ} (g : (ZMod N)ˣ) (hm : 4≤m) :
    seedSourceInput g m≤4*seedBlockWidth m := by
  have hgroup := shared_group_input_bound (B:=m) (R:=m-1) (by omega)
  have hcache := seedBlockWidth_ge_modulus hm
  rw [seedSourceInput_eq]
  change seedBlockWidth m+(m-1)*seedBlockCount m≤3*seedBlockWidth m at hgroup
  omega

/-- The whole input count has O(m^(3/2)) scale, including the public
seed cache. This is an explicit data bound, not a factoring-rate theorem. -/
theorem seedSourceInput_squared_bound {N m : ℕ} (g : (ZMod N)ˣ) (hm : 4≤m) :
    (seedSourceInput g m)^2≤96*m^3+32*m+32 := by
  have hi := seedSourceInput_le_four_width g hm
  have hs := Nat.sqrt_le' ((m-1)*(3*m^2+1))
  have hw : (seedBlockWidth m)^2≤2*((m-1)*(3*m^2+1))+2 := by
    unfold seedBlockWidth sharedWidth
    nlinarith [sq_nonneg ((Nat.sqrt ((m-1)*(3*m^2+1)) : ℤ)-1)]
  have hR := Nat.mul_le_mul_right (3*m^2+1) (show m-1≤m by omega)
  have hii := Nat.mul_self_le_mul_self hi
  nlinarith only [hii,hw,hR]

/-- ANY explicit common-block representation retaining all m-1 seed
points has a superlinear input floor. This concerns this representation,
not all implicit acquisition algorithms or all factoring algorithms. -/
theorem explicit_seed_source_floor {m w : ℕ} (hm : 4≤m) (hw : 0<w) :
    6*m^3<(w+(m-1)*blockCount m w)^2 := by
  have hpad := padded_contains_original (B:=m) hw
  have hmul := Nat.mul_le_mul_left (m-1) hpad
  have hr : 1≤m-1 := by omega
  have hR := Nat.mul_le_mul_right (3*m^2) (show m≤2*(m-1) by omega)
  have hmulZ : ((m-1 : ℕ) : ℤ)*(3*(m : ℤ)^2+1)≤
      ((m-1 : ℕ) : ℤ)*((w : ℤ)*blockCount m w) := by exact_mod_cast hmul
  have hRZ : (m : ℤ)*(3*(m : ℤ)^2)≤2*((m-1 : ℕ) : ℤ)*(3*(m : ℤ)^2) := by
    exact_mod_cast hR
  have hrZ : (1 : ℤ)≤(m-1 : ℕ) := by exact_mod_cast hr
  have hs := sq_nonneg ((w : ℤ)-((m-1 : ℕ) : ℤ)*blockCount m w)
  have hresult : 6*(m : ℤ)^3<((w : ℤ)+((m-1 : ℕ) : ℤ)*blockCount m w)^2 := by
    nlinarith only [hmulZ,hRZ,hrZ,hs]
  exact_mod_cast hresult

/-- The actual balanced construction retains this explicit source floor;
neither common-phase recovery nor sharing makes this source linear. -/
theorem seedSourceInput_superlinear {N m : ℕ} (g : (ZMod N)ˣ) (hm : 4≤m) :
    6*m^3<(seedSourceInput g m)^2 := by
  have hf := explicit_seed_source_floor hm (seedBlockWidth_pos m)
  rw [seedSourceInput_eq]
  change 6*m^3<(seedBlockWidth m+(m-1)*seedBlockCount m)^2 at hf
  apply hf.trans_le
  simpa only [pow_two] using Nat.mul_self_le_mul_self
    (show seedBlockWidth m+(m-1)*seedBlockCount m≤
      seedBlockWidth m+(m-1)*seedBlockCount m+(m-1)+1 by omega)

/-- Count the actual visited prefix's sum candidate constructions and
candidate checks. The first reader outcome ends the original seed scan. -/
noncomputable def seedScanCandidateBudget {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ))→ℕ
  | [] => 0
  | s::xs => match readSeed g m s with
    | none => seedScanCandidateBudget g m xs
    | some (Sum.inl _) => 0
    | some (Sum.inr _) => 1

/-- The entire linear seed scan uses at most one quadratic sum candidate
and one candidate check. The interval decoder is outside this counter. -/
theorem seedScanCandidateBudget_le_one {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (xs : List (ProgressionSeed ((ZMod N)ˣ))) : seedScanCandidateBudget g m xs≤1 := by
  induction xs with
  | nil => change 0≤1; omega
  | cons s xs ih =>
    simp only [seedScanCandidateBudget]
    cases he : readSeed g m s with
    | none => exact ih
    | some outcome =>
      cases outcome with
      | inl d => change 0≤1; omega
      | inr r => change 1≤1; omega

end RiemannGaussian.SemiprimeSeedSumAcquisition
