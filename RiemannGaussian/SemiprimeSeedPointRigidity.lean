/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedSumAcquisition

/-!
# Arithmetic rigidity of normalized original seed points

The common long order rules out modular wrap between the exponents of
normalized seed points. Equal points have exactly equal integer exponents
and belong to the same quadratic offset class. The original public
residue labels and block indices are retained throughout this argument.
Every value has at most two labels across the entire source. Removing all
duplicate values therefore leaves a superlinear explicit input floor,
independently of block width. This does not price an implicit algorithm.
-/

namespace RiemannGaussian.SemiprimeSeedPointRigidity

open scoped BigOperators
open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeGlobalPhaseCancellation SemiprimeSeedSumAcquisition
open SemiprimeSharedIntervalJet SemiprimeLongPowerRouting Polynomial
open SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeWrapIndexRecovery
open SemiprimeWideWrapCoverage

/-- The exact signed exponent of a normalized original seed target. -/
def pointExponent (N m w j k : ℕ) : ℤ :=
  (N : ℤ)+seedOffset N m j-(m : ℤ)^2*w*k

/-- One original public residue/block point, before removing duplicates. -/
def seedPoint {N : ℕ} (g : (ZMod N)ˣ) (m w j k : ℕ) : ZMod N :=
  normalizedPoint (seedBase g m) (progressionSeed g N m j).step w k

/-- Normalization retains the full integer offset and absolute block index. -/
theorem seedPoint_eq_zpow {N m j : ℕ} (g : (ZMod N)ˣ)
    (hm : 0<m) (hj : j.Coprime m) (w k : ℕ) :
    seedPoint g m w j k=(g^pointExponent N m w j k : (ZMod N)ˣ) := by
  change ((((seedBase g m)^(k*w))⁻¹*(progressionSeed g N m j).step : (ZMod N)ˣ) : ZMod N)=
    ((g^pointExponent N m w j k : (ZMod N)ˣ) : ZMod N)
  apply congrArg (fun u : (ZMod N)ˣ => (u : ZMod N))
  rw [seed_step_offset g hm hj]
  simp only [seedBase,←zpow_natCast,←zpow_mul,←zpow_neg,←zpow_add]
  congr 1
  simp only [pointExponent,Nat.cast_mul,Nat.cast_pow]
  ring

/-- Every block offset is at most the padded quadratic length, for any
positive width at most m^2. -/
theorem block_offset_bound {m w k : ℕ} (hw : w≤m^2) (hk : k<blockCount m w) :
    k*w≤4*m^2 := by
  have hp := padded_length_le (B:=m) (m:=w)
  have hb := Nat.mul_le_mul_right w hk.le
  nlinarith only [hp,hb,hw]

/-- Differences of normalized point exponents are short enough that
the actual global long order cannot wrap them. -/
theorem point_exponent_difference_bound {N m w j j₀ k k₀ : ℕ}
    (hm : 4≤m) (hw : w≤m^2)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hk : k<blockCount m w) (hk₀ : k₀<blockCount m w) :
    |pointExponent N m w j k-pointExponent N m w j₀ k₀|≤
      4*(m : ℤ)^4+4*(m : ℤ)^2 := by
  have hδ := seedOffset_bounds (N:=N) (by omega) hj hjm
  have hδ₀ := seedOffset_bounds (N:=N) (by omega) hj₀ hj₀m
  have hb : (k : ℤ)*w≤4*(m : ℤ)^2 := by
    exact_mod_cast block_offset_bound hw hk
  have hb₀ : (k₀ : ℤ)*w≤4*(m : ℤ)^2 := by
    exact_mod_cast block_offset_bound hw hk₀
  have hp := mul_le_mul_of_nonneg_left hb (sq_nonneg (m : ℤ))
  have hp₀ := mul_le_mul_of_nonneg_left hb₀ (sq_nonneg (m : ℤ))
  apply abs_le.mpr
  unfold pointExponent
  constructor <;> nlinarith only [hδ.1,hδ.2,hδ₀.1,hδ₀.2,hp,hp₀,
    show (0 : ℤ)≤(m : ℤ)^2*w*k by positivity,
    show (0 : ℤ)≤(m : ℤ)^2*w*k₀ by positivity]

/-- Equal normalized points force an EXACT integer relation; large
modular order cannot create extra equality between different exponent lifts. -/
theorem seedPoint_eq_iff_offsets {p q m w j j₀ k k₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hw : w≤m^2)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hk : k<blockCount m w) (hk₀ : k₀<blockCount m w) :
    seedPoint (projectedUnit g m) m w j k=seedPoint (projectedUnit g m) m w j₀ k₀ ↔
      seedOffset (p*q) m j-seedOffset (p*q) m j₀=(m : ℤ)^2*w*((k : ℤ)-k₀) := by
  have hjcop : j.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hj₀cop : j₀.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  rw [seedPoint_eq_zpow _ hmprime.pos hjcop,seedPoint_eq_zpow _ hmprime.pos hj₀cop]
  constructor
  · intro he
    have hu := Units.ext he
    have hd := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hu
    have hb := point_exponent_difference_bound (N:=p*q) hm hw hj hjm hj₀ hj₀m hk hk₀
    have ho : 16*(m : ℤ)^4<(orderOf (projectedUnit g m) : ℤ) := by
      exact_mod_cast long_global_order_bound hp hq hpq g hlong
    have hmZ : (4 : ℤ)≤m := by exact_mod_cast hm
    have hs := mul_nonneg (by nlinarith only [hmZ] : (0 : ℤ)≤(m : ℤ)^2-1)
      (sq_nonneg (m : ℤ))
    have hab : |pointExponent (p*q) m w j k-pointExponent (p*q) m w j₀ k₀|<
        (orderOf (projectedUnit g m) : ℤ) := by nlinarith only [hb,ho,hs,hmZ]
    rw [←Int.natCast_natAbs] at hab
    have habN : (pointExponent (p*q) m w j k-pointExponent (p*q) m w j₀ k₀).natAbs<
        (orderOf (projectedUnit g m) : ℤ).natAbs := by
      simpa only [Int.natAbs_natCast] using
        (show (pointExponent (p*q) m w j k-pointExponent (p*q) m w j₀ k₀).natAbs<
          orderOf (projectedUnit g m) by exact_mod_cast hab)
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habN
    unfold pointExponent at hz
    nlinarith only [hz]
  · intro he
    have hexp : pointExponent (p*q) m w j k=pointExponent (p*q) m w j₀ k₀ := by
      unfold pointExponent
      nlinarith only [he]
    rw [hexp]

/-- Equal normalized points belong to one original offset class modulo m. -/
theorem seedPoint_phase_divisible {p q m w j j₀ k k₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hw : w≤m^2)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hk : k<blockCount m w) (hk₀ : k₀<blockCount m w)
    (he : seedPoint (projectedUnit g m) m w j k=seedPoint (projectedUnit g m) m w j₀ k₀) :
    (m : ℤ)∣seedOffset (p*q) m j-seedOffset (p*q) m j₀ := by
  have hδ := (seedPoint_eq_iff_offsets hp hq hpq hm hmprime hw g hlong
    hj hjm hj₀ hj₀m hk hk₀).mp he
  refine ⟨(m : ℤ)*w*((k : ℤ)-k₀),?_⟩
  rw [hδ]
  ring

/-- At one original residue, every retained block point is distinct. -/
theorem seedPoint_fixed_seed_injective {p q m w j k k₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hwpos : 0<w) (hw : w≤m^2)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hk : k<blockCount m w) (hk₀ : k₀<blockCount m w)
    (he : seedPoint (projectedUnit g m) m w j k=seedPoint (projectedUnit g m) m w j k₀) :
    k=k₀ := by
  have hδ := (seedPoint_eq_iff_offsets hp hq hpq hm hmprime hw g hlong
    hj hjm hj hjm hk hk₀).mp he
  have hprod : (0 : ℤ)<(m : ℤ)^2*w := by
    have hmZ : (0 : ℤ)<m := by exact_mod_cast (show 0<m by omega)
    have hwZ : (0 : ℤ)<w := by exact_mod_cast hwpos
    positivity
  have hh : (k : ℤ)=(k₀ : ℤ) := by nlinarith only [hδ,hprod]
  exact_mod_cast hh

/-- Distinct canonical residues in one offset class obey the public
Möbius partner relation j+j₀=2*j*j₀; the relation is independent of N. -/
theorem offset_class_partner_relation {N m j j₀ : ℕ}
    (hm : m.Prime) (hN : m.Coprime N)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hphase : (m : ℤ)∣seedOffset N m j-seedOffset N m j₀) :
    j=j₀ ∨ (j : ZMod m)+(j₀ : ZMod m)=2*(j : ZMod m)*j₀ := by
  let : Fact m.Prime := ⟨hm⟩
  have hjcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hj₀cop : j₀.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  have hneg : (m : ℤ)∣seedOffset N m j₀-seedOffset N m j := by
    simpa only [neg_sub] using (dvd_neg.mpr hphase)
  have he : (seedOffset N m j : ZMod m)=(seedOffset N m j₀ : ZMod m) :=
    (ZMod.intCast_eq_intCast_iff _ _ m).mpr (Int.modEq_iff_dvd.mpr hneg)
  have hfirst := offset_square_residue (N:=N) hm.pos hjcop
  have hsecond := offset_square_residue (N:=N) hm.pos hj₀cop
  rw [←he] at hsecond
  have hcross : (N : ZMod m)*((j : ZMod m)-(j₀ : ZMod m))*
      ((j : ZMod m)+(j₀ : ZMod m)-2*(j : ZMod m)*j₀)=0 := by
    linear_combination (j₀ : ZMod m)^2*hfirst-(j : ZMod m)^2*hsecond
  have hNunit : IsUnit (N : ZMod m) := (ZMod.isUnit_iff_coprime N m).mpr hN.symm
  have hpair : ((j : ZMod m)-(j₀ : ZMod m))*
      ((j : ZMod m)+(j₀ : ZMod m)-2*(j : ZMod m)*j₀)=0 := by
    apply (mul_eq_zero.mp (by simpa only [mul_assoc] using hcross)).resolve_left hNunit.ne_zero
  rcases mul_eq_zero.mp hpair with hsame|hpartner
  · left
    have hv := congrArg ZMod.val (sub_eq_zero.mp hsame)
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hjm,Nat.mod_eq_of_lt hj₀m] using hv
  · right
    exact sub_eq_zero.mp hpartner

/-- Original residue/block labels for one padded common-block source. -/
def pointDomain (m w : ℕ) : Finset (ℕ×ℕ) :=
  (Finset.range (m-1))×ˢ(Finset.range (blockCount m w))

/-- Membership keeps the original nonzero residue and absolute block bounds. -/
theorem pointDomain_mem_iff {m w r k : ℕ} :
    (r,k)∈pointDomain m w ↔ r+1<m ∧ k<blockCount m w := by
  simp only [pointDomain,Finset.mem_product,Finset.mem_range]
  omega

/-- The label domain has exactly the original seeds times common blocks. -/
theorem pointDomain_card (m w : ℕ) : (pointDomain m w).card=(m-1)*blockCount m w := by
  simp only [pointDomain,Finset.card_product,Finset.card_range]

/-- Distinct actual normalized values, with repeated labels removed. -/
noncomputable def pointValues {N : ℕ} (g : (ZMod N)ˣ) (m w : ℕ) : Finset (ZMod N) :=
  (pointDomain m w).image fun u => seedPoint g m w (u.1+1) u.2

/-- All original labels producing one actual normalized point. -/
noncomputable def pointFiber {N : ℕ} (g : (ZMod N)ˣ) (m w : ℕ) (x : ZMod N) : Finset (ℕ×ℕ) :=
  (pointDomain m w).filter fun u => seedPoint g m w (u.1+1) u.2=x

/-- Every actual point has at most TWO original labels across the ENTIRE
seed/block source. This includes reuse between different blocks. -/
theorem pointFiber_card_le_two {p q m w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (hwpos : 0<w) (hw : w≤m^2) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (x : ZMod (p*q)) : (pointFiber (projectedUnit g m) m w x).card≤2 := by
  classical
  let : Fact m.Prime := ⟨hmprime⟩
  let F := pointFiber (projectedUnit g m) m w x
  change F.card≤2
  by_cases hF : F=∅
  · rw [hF]
    simp only [Finset.card_empty,Nat.zero_le]
  obtain ⟨u₀,hu₀⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  have hb {u : ℕ×ℕ} (hu : u∈F) : u.1+1<m ∧ u.2<blockCount m w :=
    pointDomain_mem_iff.mp (Finset.mem_filter.mp hu).1
  have hv {u : ℕ×ℕ} (hu : u∈F) :
      seedPoint (projectedUnit g m) m w (u.1+1) u.2=x := (Finset.mem_filter.mp hu).2
  let P := phasePolynomial (p*q) m (seedOffset (p*q) m (u₀.1+1))
  have hP : P≠0 := phasePolynomial_ne_zero hmprime hN _
  have hmapping : Set.MapsTo (fun u : ℕ×ℕ => ((u.1+1 : ℕ) : ZMod m))
      F P.roots.toFinset := by
    intro u hu
    have hcop : (u.1+1).Coprime m :=
      (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (hb hu).1)).symm
    have hphase := seedPoint_phase_divisible hp hq hpq hm hmprime hw g hlong
      (by omega : 1≤u.1+1) (hb hu).1 (by omega : 1≤u₀.1+1) (hb hu₀).1
      (hb hu).2 (hb hu₀).2 ((hv hu).trans (hv hu₀).symm)
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr
      (phasePolynomial_root hmprime.pos hcop hphase))
  have hinj : (F : Set (ℕ×ℕ)).InjOn (fun u : ℕ×ℕ => ((u.1+1 : ℕ) : ZMod m)) := by
    intro u hu v hv₁ he
    have heval := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (hb hu).1,
      Nat.mod_eq_of_lt (hb hv₁).1] at heval
    have hres : u.1=v.1 := by omega
    have hpoint := (hv hu).trans (hv hv₁).symm
    rw [←hres] at hpoint
    have hblock := seedPoint_fixed_seed_injective hp hq hpq hm hmprime hwpos hw g hlong
      (by omega : 1≤u.1+1) (hb hu).1 (hb hu).2 (hb hv₁).2 hpoint
    exact Prod.ext hres hblock
  have hcard := Finset.card_le_card_of_injOn _ hmapping hinj
  have hroots := Multiset.toFinset_card_le P.roots
  have hdegree := (Polynomial.card_roots' P).trans (phasePolynomial_degree (p*q) m _)
  omega

/-- Removing every exact repeated value saves at most a factor of two,
including collisions between different residue and block labels. -/
theorem distinct_point_card_lower {p q m w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (hwpos : 0<w) (hw : w≤m^2) (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    (m-1)*blockCount m w≤2*(pointValues (projectedUnit g m) m w).card := by
  classical
  calc
    (m-1)*blockCount m w=(pointDomain m w).card := (pointDomain_card m w).symm
    _=∑ x∈pointValues (projectedUnit g m) m w,
        (pointFiber (projectedUnit g m) m w x).card := Finset.card_eq_sum_card_image _ _
    _≤∑ _x∈pointValues (projectedUnit g m) m w,2 :=
      Finset.sum_le_sum fun x _ => pointFiber_card_le_two hp hq hpq hm hmprime hN
        hwpos hw g hlong x
    _=2*(pointValues (projectedUnit g m) m w).card := by simp only [Finset.sum_const,
      smul_eq_mul,mul_comm]

/-- Even perfect reuse of every repeated normalized value retains a
superlinear source for EVERY positive block width on the actual long branch.
This is a common-block input floor, not a general factoring lower bound. -/
theorem distinct_source_floor {p q m w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (hwpos : 0<w) (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    3*m^3<(w+(pointValues (projectedUnit g m) m w).card)^2 := by
  by_cases hw : w≤m^2
  · have hd := distinct_point_card_lower hp hq hpq hm hmprime hN hwpos hw g hlong
    have hpadded := padded_contains_original (B:=m) hwpos
    have hpad := Nat.mul_le_mul_left (m-1) hpadded
    have hdw := Nat.mul_le_mul_left w hd
    have hr : 1≤m-1 := by omega
    have hR := Nat.mul_le_mul_right (3*m^2) (show m≤2*(m-1) by omega)
    let Q := (pointValues (projectedUnit g m) m w).card
    have hpadZ : ((m-1 : ℕ) : ℤ)*(3*(m : ℤ)^2+1)≤
        ((m-1 : ℕ) : ℤ)*((w : ℤ)*blockCount m w) := by exact_mod_cast hpad
    have hdwZ : (w : ℤ)*(((m-1 : ℕ) : ℤ)*blockCount m w)≤(w : ℤ)*(2*(Q : ℤ)) := by
      exact_mod_cast hdw
    have hRZ : (m : ℤ)*(3*(m : ℤ)^2)≤2*((m-1 : ℕ) : ℤ)*(3*(m : ℤ)^2) := by
      exact_mod_cast hR
    have hrZ : (1 : ℤ)≤(m-1 : ℕ) := by exact_mod_cast hr
    have hs := sq_nonneg ((w : ℤ)-(Q : ℤ))
    have hresult : 3*(m : ℤ)^3<((w : ℤ)+(Q : ℤ))^2 := by
      nlinarith only [hpadZ,hdwZ,hRZ,hrZ,hs]
    exact_mod_cast hresult
  · have hww := Nat.mul_self_le_mul_self (show m^2+1≤w by omega)
    have hmul := Nat.mul_le_mul_right (m^3) hm
    have hf : 3*m^3<w^2 := by nlinarith only [hww,hmul]
    apply hf.trans_le
    simpa only [pow_two] using Nat.mul_self_le_mul_self
      (show w≤w+(pointValues (projectedUnit g m) m w).card by omega)

/-- The finite value set is exactly the generic original shared-point
list after removing every repeated value; it is not an auxiliary source. -/
theorem pointValues_eq_sharedPoints {N : ℕ} (g : (ZMod N)ˣ) (m w : ℕ) :
    pointValues g m w=(sharedPoints (seedBase g m)
      ((progressionSeeds g N m).map fun s => (s.step : ZMod N)) w (blockCount m w)).toFinset := by
  classical
  ext x
  simp only [pointValues,Finset.mem_image,List.mem_toFinset,sharedPoints,List.mem_flatMap]
  constructor
  · rintro ⟨u,hu,he⟩
    have hb := pointDomain_mem_iff.mp hu
    refine ⟨((progressionSeed g N m (u.1+1)).step : ZMod N),?_ ,?_⟩
    · exact List.mem_map.mpr ⟨progressionSeed g N m (u.1+1),
        progressionSeed_mem g (by omega) hb.1,rfl⟩
    · exact List.mem_map.mpr ⟨u.2,List.mem_range.mpr hb.2,he⟩
  · rintro ⟨z,hz,hpoint⟩
    obtain ⟨s,hs,hstep⟩ := List.mem_map.mp hz
    obtain ⟨hj,hjm,hseed⟩ := cached_seed_source hs
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hpoint
    refine ⟨(s.residue-1,k),pointDomain_mem_iff.mpr ⟨by omega,List.mem_range.mp hk⟩,?_⟩
    rw [←hstep,hseed] at he
    simpa only [seedPoint,show s.residue-1+1=s.residue by omega] using he

/-- The actual acquired batch has precisely the proved finite value set. -/
theorem seedBatchPoints_values {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    pointValues g m (seedBlockWidth m)=(seedBatchPoints g m).toFinset :=
  pointValues_eq_sharedPoints g m _

/-- The most optimistic distinct-value version of the current full
source: common block roots, unique point values, original cache and a constant. -/
noncomputable def deduplicatedSeedInput {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : ℕ :=
  seedBlockWidth m+(seedBatchPoints g m).toFinset.card+(progressionSeeds g N m).length+1

/-- Exact removal of repeats never increases the previous source count. -/
theorem deduplicatedSeedInput_le {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    deduplicatedSeedInput g m≤seedSourceInput g m := by
  have hc := List.toFinset_card_le (l:=seedBatchPoints g m)
  unfold deduplicatedSeedInput seedSourceInput
  omega

/-- The optimistic source retains the same O(m^(3/2)) upper input scale. -/
theorem deduplicatedSeedInput_squared_bound {N m : ℕ} (g : (ZMod N)ˣ) (hm : 4≤m) :
    (deduplicatedSeedInput g m)^2≤96*m^3+32*m+32 := by
  have hmono : (deduplicatedSeedInput g m)^2≤(seedSourceInput g m)^2 := by
    simpa only [pow_two] using Nat.mul_self_le_mul_self (deduplicatedSeedInput_le g m)
  exact hmono.trans (seedSourceInput_squared_bound g hm)

/-- Even the actual balanced source with every repeated point removed
has a matching superlinear input floor on every remaining long branch. -/
theorem deduplicatedSeedInput_floor {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    3*m^3<(deduplicatedSeedInput (projectedUnit g m) m)^2 := by
  have hf := distinct_source_floor hp hq hpq hm hmprime hN (seedBlockWidth_pos m) g hlong
  rw [seedBatchPoints_values] at hf
  unfold deduplicatedSeedInput
  apply hf.trans_le
  simpa only [pow_two] using Nat.mul_self_le_mul_self
    (show seedBlockWidth m+(seedBatchPoints (projectedUnit g m) m).toFinset.card≤
      seedBlockWidth m+(seedBatchPoints (projectedUnit g m) m).toFinset.card+
        (progressionSeeds (projectedUnit g m) (p*q) m).length+1 by omega)

/-- The source obstruction is attached to the actual matched-width
public long output and prefix, not to a supplied private high-order unit. -/
theorem actual_public_route_deduplicated_floor {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      3*m^3<(deduplicatedSeedInput h m)^2 ∧
        (deduplicatedSeedInput h m)^2≤96*m^3+32*m+32 := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hmBounds.1
  have hcover : m^2<p*q := public_modulus_prefix_below_input hN hB
  have hmprime : m.Prime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hmprime.pos
    (by have hh := hmprime.two_le; nlinarith only [hh] : m≤m^2)
  exact ⟨hc,deduplicatedSeedInput_floor hp hq hpq.ne hm hmprime hcop.symm g hlong,
    deduplicatedSeedInput_squared_bound _ hm⟩

end RiemannGaussian.SemiprimeSeedPointRigidity
