/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedMomentPeriodGapObstruction

/-!
# Period gaps for arbitrarily placed original seed blocks

The sample may use any finite set of block positions. Its gap condition
keeps the signed differences of those positions, rather than enlarging
them to a consecutive interval. Under gaps in both actual local orders,
no pair of sampled points yields a proper factor. A gap in one component
retains half the sample mass and forces the corresponding degree floor
for the whole original positive moment carrier.

The separate classical argument in the investigation journal supplies
infinitely many actual long inputs for each predetermined sparse layout.
Its analytic density and selector counting are not formalized here. The
stronger consequence of the OpenAI prime-predecessor manuscript is kept
separate from the published Baker--Harman input and its verification.
-/

namespace RiemannGaussian.SemiprimeSparseBlockPeriodObstruction

open scoped BigOperators
open Polynomial SemiprimeSeedMomentPoleRetention SemiprimeSeedMomentPrefixRigidity
open SemiprimeSeedPointRigidity SemiprimeSeedMomentCancellationObstruction
open SemiprimeSeedSumAcquisition SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeGlobalPhaseCancellation SemiprimeSeedFiniteTransfer
open SemiprimeSharedIntervalJet SemiprimeIntervalJet

/-- The actual period avoids the windows at every signed layout distance.
The condition does not fill in unsampled block positions. -/
abbrev BlockSetPeriodGap (m : ℕ) (blocks : Finset ℕ) (R : ℕ) : Prop :=
  ∀ k∈blocks,∀ k₀∈blocks,k≠k₀ → ∀ a : ℤ,
    4*(m : ℤ)^2 < |4*(m : ℤ)^3*((k : ℤ)-k₀)-a*R|

/-- A local equality in this layout has the same block and exact offset. -/
theorem point_reduction_eq_blocks_offsets {N m j j₀ k k₀ : ℕ}
    {blocks : Finset ℕ} {R : Type*} [CommRing R]
    (f : ZMod N→+*R) (g : (ZMod N)ˣ)
    (hm : 4≤m) (hmprime : m.Prime)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hk : k∈blocks) (hk₀ : k₀∈blocks)
    (horder : 4*m^2<orderOf (Units.map f.toMonoidHom g))
    (hgap : BlockSetPeriodGap m blocks (orderOf (Units.map f.toMonoidHom g)))
    (he : f (seedPoint g m (4*m) j k)=f (seedPoint g m (4*m) j₀ k₀)) :
    k=k₀ ∧ seedOffset N m j=seedOffset N m j₀ := by
  have hjcop : j.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hj₀cop : j₀.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  have hu : Units.map f.toMonoidHom (g^pointExponent N m (4*m) j k)=
      Units.map f.toMonoidHom (g^pointExponent N m (4*m) j₀ k₀) := by
    apply Units.ext
    change f ((g^pointExponent N m (4*m) j k : (ZMod N)ˣ) : ZMod N)=
      f ((g^pointExponent N m (4*m) j₀ k₀ : (ZMod N)ˣ) : ZMod N)
    simpa only [seedPoint_eq_zpow g hmprime.pos hjcop,
      seedPoint_eq_zpow g hmprime.pos hj₀cop] using he
  rw [map_zpow,map_zpow] at hu
  obtain ⟨a,ha⟩ := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hu
  have hb := seed_offset_difference_bound (N:=N) (by omega) hj hjm hj₀ hj₀m
  have hsame : k=k₀ := by
    by_contra hn
    have hh := hgap k hk k₀ hk₀ hn (-a)
    have heq : 4*(m : ℤ)^3*((k : ℤ)-k₀)-(-a)*orderOf (Units.map f.toMonoidHom g)=
        seedOffset N m j-seedOffset N m j₀ := by
      simp only [pointExponent,Nat.cast_mul] at ha
      norm_num only [Nat.cast_ofNat] at ha
      linear_combination -ha
    rw [heq] at hh
    exact (not_lt_of_ge hb) hh
  have hdδ : (orderOf (Units.map f.toMonoidHom g) : ℤ)∣
      seedOffset N m j-seedOffset N m j₀ := by
    rw [hsame] at ha
    refine ⟨a,?_⟩
    simp only [pointExponent] at ha
    linear_combination ha
  have ho : 4*(m : ℤ)^2<(orderOf (Units.map f.toMonoidHom g) : ℤ) := by
    exact_mod_cast horder
  have hsmall : (seedOffset N m j-seedOffset N m j₀).natAbs<
      (orderOf (Units.map f.toMonoidHom g) : ℤ).natAbs := by
    rw [←Int.natCast_natAbs] at hb
    simpa only [Int.natAbs_natCast] using
      (show (seedOffset N m j-seedOffset N m j₀).natAbs<
        orderOf (Units.map f.toMonoidHom g) by exact_mod_cast hb.trans_lt ho)
  exact ⟨hsame,sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdδ hsmall)⟩

/-- These gaps prevent local-only collisions at every selected position. -/
theorem point_eq_of_period_gap_reduction {N m j j₀ k k₀ : ℕ}
    {blocks : Finset ℕ} {R : Type*} [CommRing R]
    (f : ZMod N→+*R) (g : (ZMod N)ˣ)
    (hm : 4≤m) (hmprime : m.Prime)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hk : k∈blocks) (hk₀ : k₀∈blocks)
    (horder : 4*m^2<orderOf (Units.map f.toMonoidHom g))
    (hgap : BlockSetPeriodGap m blocks (orderOf (Units.map f.toMonoidHom g)))
    (he : f (seedPoint g m (4*m) j k)=f (seedPoint g m (4*m) j₀ k₀)) :
    seedPoint g m (4*m) j k=seedPoint g m (4*m) j₀ k₀ := by
  obtain ⟨hblock,hδ⟩ := point_reduction_eq_blocks_offsets f g hm hmprime
    hj hjm hj₀ hj₀m hk hk₀ horder hgap he
  have hjcop : j.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hj₀cop : j₀.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  rw [seedPoint_eq_zpow g hmprime.pos hjcop,seedPoint_eq_zpow g hmprime.pos hj₀cop]
  simp only [pointExponent,hblock,hδ]

/-- Both actual local gaps make every distinct sampled point difference a unit. -/
theorem original_sample_unit_separated {p q m : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hgapP : BlockSetPeriodGap m blocks (orderOf (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g m))))
    (hgapQ : BlockSetPeriodGap m blocks (orderOf (Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom (projectedUnit g m)))) :
    let sample := (Finset.range (m-1)) ×ˢ blocks
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    ∀ u∈sample,∀ v∈sample,point u≠point v → IsUnit (point u-point v) := by
  dsimp only
  intro u hu v hv hne
  have huj : u.1+1<m := by have hh := Finset.mem_range.mp (Finset.mem_product.mp hu).1; omega
  have hvj : v.1+1<m := by have hh := Finset.mem_range.mp (Finset.mem_product.mp hv).1; omega
  have huk := (Finset.mem_product.mp hu).2
  have hvk := (Finset.mem_product.mp hv).2
  apply isUnit_of_prime_reductions hp hq
  · rw [map_sub]
    intro he
    exact hne (point_eq_of_period_gap_reduction _ (projectedUnit g m) hm hmprime
      (by omega) huj (by omega) hvj huk hvk
      (by have hh := hlong.2.2.2.1.1
          change (2*m)^2<orderOf (Units.map
            (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g m)) at hh
          nlinarith only [hh]) hgapP (sub_eq_zero.mp he))
  · rw [map_sub]
    intro he
    exact hne (point_eq_of_period_gap_reduction _ (projectedUnit g m) hm hmprime
      (by omega) huj (by omega) hvj huk hvk
      (by have hh := hlong.2.2.2.1.2
          change (2*m)^2<orderOf (Units.map
            (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom (projectedUnit g m)) at hh
          nlinarith only [hh]) hgapQ (sub_eq_zero.mp he))

/-- Proper-factor credit is impossible for every pair, including global duplicates. -/
theorem original_sample_no_proper_difference {p q m : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hgapP : BlockSetPeriodGap m blocks (orderOf (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g m))))
    (hgapQ : BlockSetPeriodGap m blocks (orderOf (Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom (projectedUnit g m)))) :
    let sample := (Finset.range (m-1)) ×ˢ blocks
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    ∀ u∈sample,∀ v∈sample,
      ¬SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (point u-point v).val) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  dsimp only
  intro u hu v hv hproper
  by_cases he : seedPoint (projectedUnit g m) m (4*m) (u.1+1) u.2=
      seedPoint (projectedUnit g m) m (4*m) (v.1+1) v.2
  · rw [he,sub_self,ZMod.val_zero,Nat.gcd_zero_right] at hproper
    exact (Nat.lt_irrefl (p*q)) hproper.2.1
  · have hunit := original_sample_unit_separated hp hq hm hmprime g hlong hgapP hgapQ u hu v hv he
    have hg := (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hunit
    rw [hg] at hproper
    exact (Nat.lt_irrefl 1) hproper.1

/-- One local gap retains half the raw sample mass throughout the original domain. -/
theorem original_sample_local_card_lower {p q m : ℕ} {blocks : Finset ℕ}
    {R : Type*} [CommRing R] [DecidableEq R]
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hblocks : blocks⊆Finset.range (blockCount m (4*m)))
    (f : ZMod (p*q)→+*R) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (horder : 4*m^2<orderOf (Units.map f.toMonoidHom (projectedUnit g m)))
    (hgap : BlockSetPeriodGap m blocks (orderOf (Units.map f.toMonoidHom (projectedUnit g m)))) :
    let sample := (Finset.range (m-1)) ×ˢ blocks
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    (m-1)*blocks.card≤2*(sample.image (fun jk => f (point jk))).card := by
  classical
  let sample := (Finset.range (m-1)) ×ˢ blocks
  let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
  let S := sample.image point
  have hdomain : sample⊆pointDomain m (4*m) := by
    intro jk hjk
    have hh := Finset.mem_product.mp hjk
    exact Finset.mem_product.mpr ⟨hh.1,hblocks hh.2⟩
  have hfiber : ∀ x∈S,(sample.filter fun jk => point jk=x).card≤2 := by
    intro x _
    have hsub : (sample.filter fun jk => point jk=x)⊆pointFiber (projectedUnit g m) m (4*m) x := by
      intro jk hjk
      exact Finset.mem_filter.mpr ⟨hdomain (Finset.mem_filter.mp hjk).1,(Finset.mem_filter.mp hjk).2⟩
    exact (Finset.card_le_card hsub).trans (pointFiber_card_le_two hp hq hpq hm hmprime
      (original_modulus_coprime hp hq hm g hlong) (by omega) (by nlinarith only [hm]) g hlong x)
  have hraw : (m-1)*blocks.card≤2*S.card := by
    calc
      (m-1)*blocks.card=sample.card := by simp only [sample,Finset.card_product,Finset.card_range]
      _=∑ x∈S,(sample.filter fun jk => point jk=x).card := Finset.card_eq_sum_card_image point sample
      _≤∑ _x∈S,2 := Finset.sum_le_sum hfiber
      _=2*S.card := by simp only [Finset.sum_const,smul_eq_mul,mul_comm]
  have hinj : Set.InjOn (fun x => f x) S := by
    intro x hx y hy he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    have huj : u.1+1<m := by have hh := Finset.mem_range.mp (Finset.mem_product.mp hu).1; omega
    have hvj : v.1+1<m := by have hh := Finset.mem_range.mp (Finset.mem_product.mp hv).1; omega
    exact point_eq_of_period_gap_reduction f (projectedUnit g m) hm hmprime
      (by omega) huj (by omega) hvj (Finset.mem_product.mp hu).2
      (Finset.mem_product.mp hv).2 horder hgap he
  have hcard : (S.image (fun x => f x)).card=S.card := Finset.card_image_of_injOn hinj
  change (m-1)*blocks.card≤2*(sample.image (fun jk => f (point jk))).card
  rw [←hcard] at hraw
  simpa only [S,Finset.image_image,Function.comp_def] using hraw

/-- The full original positive moment carrier must retain this sparse local support. -/
theorem original_period_gap_denominator_degree {p q m : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hblocks : blocks⊆Finset.range (blockCount m (4*m)) ∧
      blocks⊆Finset.range (seedLength m/(4*m)+1))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hgap : BlockSetPeriodGap m blocks (orderOf (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g m))))
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
      (seedLength m/(4*m)+1)=(V : PowerSeries (ZMod (p*q)))) :
    (m-1)*blocks.card≤2*U.natDegree := by
  classical
  let sample := (Finset.range (m-1)) ×ˢ blocks
  let I := (Finset.range (m-1)) ×ˢ (Finset.range (seedLength m/(4*m)+1))
  let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  have hsample : sample⊆I := by
    intro jk hjk
    have hh := Finset.mem_product.mp hjk
    exact Finset.mem_product.mpr ⟨hh.1,hblocks.2 hh.2⟩
  have hlower := original_sample_local_card_lower hp hq hpq hm hmprime hblocks.1 f g hlong
    (by have hh := hlong.2.2.2.1.1
        change (2*m)^2<orderOf (Units.map f.toMonoidHom (projectedUnit g m)) at hh
        nlinarith only [hh]) hgap
  have hupper := (original_denominator_local_degrees hp hq hm g hlong U V hU hUV).1
  have hsub : sample.image (fun jk => f (point jk))⊆I.image (fun jk => f (point jk)) :=
    Finset.image_subset_image hsample
  exact hlower.trans (Nat.mul_le_mul_left 2 ((Finset.card_le_card hsub).trans hupper))

/-- Matching a genuine finite prefix cannot bypass the same whole-family degree floor. -/
theorem original_period_gap_prefix_degree {p q m d : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hd : d≤m^2) (hblocks : blocks⊆Finset.range (blockCount m (4*m)) ∧
      blocks⊆Finset.range (seedLength m/(4*m)+1))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hgap : BlockSetPeriodGap m blocks (orderOf (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g m))))
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) : (m-1)*blocks.card≤2*d := by
  have hUV := original_polynomial_prefix_certificate hp hq hm hd g hlong U V hU hUd hVd hprefix
  exact (original_period_gap_denominator_degree hp hq hpq hm hmprime hblocks
    g hlong hgap U V hU hUV).trans (Nat.mul_le_mul_left 2 hUd)

end RiemannGaussian.SemiprimeSparseBlockPeriodObstruction
