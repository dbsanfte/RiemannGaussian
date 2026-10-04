/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedMomentPrefixRigidity

/-!
# Positive original moment weights cannot cancel local poles

A rational denominator of a finite weighted moment series must vanish at
every inverse point with nonzero weight. On the original long branch the
full grid label count is smaller than both hidden primes, so EVERY positive
local multiplicity survives. A short prefix certificate therefore retains
all original grid points in both prime reductions.

This is an arithmetic necessity and information-retention result. It does
not assume or prove cheap acquisition, small-denominator existence, or a
complete factorizer bit-time and peak-memory bound. All finite products
and moment series are proof-side witnesses, never executable input advice.
-/

namespace RiemannGaussian.SemiprimeSeedMomentPoleRetention

open scoped BigOperators
open Polynomial SemiprimeSeedMomentPrefixRigidity
open SemiprimeSeedMomentCancellationObstruction SemiprimeSeedPointRigidity
open SemiprimeSeedSumAcquisition SemiprimeLocalOrderRouting
open SemiprimeDenseRowCarries SemiprimeCentreFreeCover SemiprimeIntervalJet

/-- Proof-side centered geometric moments of one point. -/
noncomputable def positiveMoments {R : Type*} [CommRing R] (x : R) : PowerSeries R :=
  PowerSeries.mk fun r => if r=0 then 0 else x^r

/-- The exact linear clearing relation for one centered point series. -/
theorem positiveMoments_linear {R : Type*} [CommRing R] (x : R) :
    ((1-C x*X : R[X]) : PowerSeries R)*positiveMoments x=
      ((C x*X : R[X]) : PowerSeries R) := by
  have hs : positiveMoments x=PowerSeries.rescale x (PowerSeries.mk (1 : ℕ→R))-1 := by
    ext r
    by_cases hr : r=0
    · subst r
      rw [positiveMoments,PowerSeries.coeff_mk,map_sub,PowerSeries.coeff_rescale,PowerSeries.coeff_mk]
      simp
    · simp [positiveMoments,hr,PowerSeries.coeff_rescale]
  rw [hs]
  have he := congrArg (PowerSeries.rescale x) (PowerSeries.mk_one_mul_one_sub_eq_one R)
  simp only [map_mul,map_sub,map_one,PowerSeries.rescale_X] at he
  simp only [Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_mul,
    Polynomial.coe_C,Polynomial.coe_X]
  linear_combination he

/-- Each nonzero weighted point is an unavoidable denominator root.
The clearing product is a proof witness, not a required algorithm output. -/
theorem weighted_denominator_roots {K : Type*} [Field K]
    (S : Finset K) (weight : K→K) (hx : ∀ x∈S,x≠0) (hw : ∀ x∈S,weight x≠0)
    (U V : K[X])
    (hUV : (U : PowerSeries K)*
      (∑ x∈S,PowerSeries.C (weight x)*positiveMoments x)=(V : PowerSeries K)) :
    ∀ x∈S,U.eval x⁻¹=0 := by
  classical
  let L := fun x : K => (1-C x*X : K[X])
  let P : K[X] := ∏ x∈S,L x
  let T : K[X] := ∑ x∈S,C (weight x)*(C x*X)*(∏ y∈S.erase x,L y)
  have hclear : (P : PowerSeries K)*(∑ x∈S,PowerSeries.C (weight x)*positiveMoments x)=
      (T : PowerSeries K) := by
    rw [Finset.mul_sum]
    change (∑ x∈S,(P : PowerSeries K)*(PowerSeries.C (weight x)*positiveMoments x))=
      Polynomial.coeToPowerSeries.ringHom
        (∑ x∈S,C (weight x)*(C x*X)*(∏ y∈S.erase x,L y) : K[X])
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hxs
    have hprod : P=(∏ y∈S.erase x,L y)*L x := (Finset.prod_erase_mul S L hxs).symm
    rw [hprod]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_mul,Polynomial.coe_C]
    change ((∏ y∈S.erase x,L y : K[X]) : PowerSeries K)*
      ((1-C x*X : K[X]) : PowerSeries K)*(PowerSeries.C (weight x)*positiveMoments x)=_
    calc
      _=PowerSeries.C (weight x)*
          (((1-C x*X : K[X]) : PowerSeries K)*positiveMoments x)*
            ((∏ y∈S.erase x,L y : K[X]) : PowerSeries K) := by ring
      _=_ := by rw [positiveMoments_linear,Polynomial.coe_mul,Polynomial.coe_C]
  have hpoly : U*T=V*P := by
    apply Polynomial.coe_injective K
    simp only [Polynomial.coe_mul]
    calc
      (U : PowerSeries K)*T=(U : PowerSeries K)*
          ((P : PowerSeries K)*(∑ x∈S,PowerSeries.C (weight x)*positiveMoments x)) := by rw [hclear]
      _=((U : PowerSeries K)*(∑ x∈S,PowerSeries.C (weight x)*positiveMoments x))*P := by ring
      _=(V : PowerSeries K)*P := by rw [hUV]
  intro x hxs
  have hL : (L x).eval x⁻¹=0 := by simp [L,hx x hxs]
  have hP : P.eval x⁻¹=0 := by
    dsimp only [P]
    rw [(Finset.mul_prod_erase S L hxs).symm]
    rw [eval_mul,hL,zero_mul]
  have hT : T.eval x⁻¹=weight x*∏ y∈S.erase x,(L y).eval x⁻¹ := by
    dsimp only [T]
    rw [eval_finsetSum,Finset.sum_eq_single x]
    · simp only [eval_mul,eval_C,eval_X,eval_prod,mul_inv_cancel₀ (hx x hxs),mul_one]
    · intro y hys hyx
      have hmem : x∈S.erase y := Finset.mem_erase.mpr ⟨hyx.symm,hxs⟩
      have hz : (∏ t∈S.erase y,L t).eval x⁻¹=0 := by
        rw [eval_prod]
        exact Finset.prod_eq_zero hmem hL
      simp only [eval_mul,hz,mul_zero]
    · exact (not_not.mpr hxs).elim
  have hTne : T.eval x⁻¹≠0 := by
    rw [hT]
    apply mul_ne_zero (hw x hxs)
    apply Finset.prod_ne_zero_iff.mpr
    intro y hys
    have hyx := (Finset.mem_erase.mp hys).1
    simp only [L,eval_sub,eval_one,eval_mul,eval_C,eval_X]
    intro he
    have hsame : y=x := by
      have hm := congrArg (fun t : K => t*x) (sub_eq_zero.mp he)
      simpa [hx x hxs] using hm.symm
    exact hyx hsame
  have he := congrArg (fun A : K[X] => A.eval x⁻¹) hpoly
  rw [eval_mul,eval_mul,hP,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_right hTne

/-- The degree cannot be reduced by cancellation of surviving point weights. -/
theorem weighted_denominator_degree {K : Type*} [Field K]
    (S : Finset K) (weight : K→K) (hx : ∀ x∈S,x≠0) (hw : ∀ x∈S,weight x≠0)
    (U V : K[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries K)*
      (∑ x∈S,PowerSeries.C (weight x)*positiveMoments x)=(V : PowerSeries K)) :
    S.card≤U.natDegree := by
  classical
  have hUne : U≠0 := by intro he; simp [he] at hU
  let roots := S.image fun x => x⁻¹
  have hinj : Set.InjOn (fun x : K => x⁻¹) S := fun _ _ _ _ he => inv_injective he
  have hcard : roots.card=S.card := Finset.card_image_of_injOn hinj
  have hsub : roots.val⊆U.roots := by
    intro y hy
    obtain ⟨x,hxs,rfl⟩ := Finset.mem_image.mp hy
    exact (Polynomial.mem_roots hUne).mpr (weighted_denominator_roots S weight hx hw U V hUV x hxs)
  rw [←hcard]
  exact Polynomial.card_le_degree_of_subset_roots hsub

/-- Deduplicating labels preserves their full positive multiplicity.
Repeated original contributions add; none is silently removed. -/
theorem labelled_moments_group {R ι : Type*} [CommRing R] [DecidableEq R]
    (I : Finset ι) (x : ι→R) :
    (∑ i∈I,positiveMoments (x i))=
      ∑ y∈I.image x,PowerSeries.C (((I.filter fun i => x i=y).card : ℕ) : R)*positiveMoments y := by
  classical
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem x hi) (fun i => positiveMoments (x i))]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_congr rfl (fun i hi => congrArg positiveMoments (Finset.mem_filter.mp hi).2)]
  rw [Finset.sum_const,nsmul_eq_mul]
  congr 1

/-- Below the characteristic, every original positive fiber weight
is nonzero, including all duplicate-point multiplicities. -/
theorem labelled_prime_denominator_roots {p : ℕ} {ι : Type*} (hp : p.Prime)
    (I : Finset ι) (x : ι→ZMod p) (hsize : I.card<p) (hx : ∀ i∈I,x i≠0)
    (U V : (ZMod p)[X])
    (hUV : (U : PowerSeries (ZMod p))*(∑ i∈I,positiveMoments (x i))=
      (V : PowerSeries (ZMod p))) : ∀ i∈I,U.eval (x i)⁻¹=0 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rw [labelled_moments_group I x] at hUV
  have hpoints : ∀ y∈I.image x,y≠0 := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact hx i hi
  have hweights : ∀ y∈I.image x,(((I.filter fun i => x i=y).card : ℕ) : ZMod p)≠0 := by
    intro y hy
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hy
    have hpos : 0<(I.filter fun j => x j=y).card :=
      Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,he⟩⟩
    have hlt := (Finset.card_le_card (Finset.filter_subset (fun i => x i=y) I)).trans_lt hsize
    exact fun hz => Nat.not_dvd_of_pos_of_lt hpos hlt
      ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  intro i hi
  exact weighted_denominator_roots (I.image x)
    (fun y => (((I.filter fun i => x i=y).card : ℕ) : ZMod p))
    hpoints hweights U V hUV (x i) (Finset.mem_image_of_mem x hi)

/-- Every surviving local point contributes to the denominator degree. -/
theorem labelled_prime_denominator_degree {p : ℕ} {ι : Type*} (hp : p.Prime)
    (I : Finset ι) (x : ι→ZMod p) (hsize : I.card<p) (hx : ∀ i∈I,x i≠0)
    (U V : (ZMod p)[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries (ZMod p))*(∑ i∈I,positiveMoments (x i))=
      (V : PowerSeries (ZMod p))) : (I.image x).card≤U.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hUne : U≠0 := by intro he; simp [he] at hU
  let roots := (I.image x).image fun y => y⁻¹
  have hinj : Set.InjOn (fun y : ZMod p => y⁻¹) (I.image x) :=
    fun _ _ _ _ he => inv_injective he
  have hcard : roots.card=(I.image x).card := Finset.card_image_of_injOn hinj
  have hsub : roots.val⊆U.roots := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact (Polynomial.mem_roots hUne).mpr (labelled_prime_denominator_roots hp I x hsize hx U V hUV i hi)
  rw [←hcard]
  exact Polynomial.card_le_degree_of_subset_roots hsub

/-- Coefficient reduction preserves the exact centered point series. -/
theorem positiveMoments_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (x : R) : PowerSeries.map f (positiveMoments x)=positiveMoments (f x) := by
  ext r
  by_cases hr : r=0
  · subst r
    rw [PowerSeries.coeff_map]
    simp [positiveMoments]
  · simp only [PowerSeries.coeff_map,positiveMoments,PowerSeries.coeff_mk,if_neg hr,map_pow]

/-- The centered grid sum contains EVERY original normalized label. -/
theorem original_grid_labelled {N : ℕ} (g : (ZMod N)ˣ) (m w J : ℕ) :
    centredGridSeries g m w J=
      ∑ jk∈(Finset.range (m-1)) ×ˢ (Finset.range J),positiveMoments (seedPoint g m w (jk.1+1) jk.2) := by
  ext r
  simp only [centredGridSeries,PowerSeries.coeff_mk,map_sum,positiveMoments]
  by_cases hr : r=0
  · simp [hr]
  · simp only [if_neg hr,gridMoment,Finset.sum_product]

/-- Original normalized grid points are units before ANY reduction. -/
theorem original_point_unit {N : ℕ} (g : (ZMod N)ˣ) (m w j k : ℕ) :
    IsUnit (seedPoint g m w j k) := by
  rw [seedPoint_geometric]
  exact (((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ).isUnit).pow k).mul
    (progressionSeed g N m j).step.isUnit

/-- Both hidden characteristics exceed the retained long-period cap. -/
theorem original_characteristics_above_cap {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (_hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    4*m^2<p ∧ 4*m^2<q := by
  have hP : 4*m^2<p := by
    let : Fact p.Prime := ⟨hp⟩
    have hd := ZMod.orderOf_units_dvd_card_sub_one (leftUnit (projectedUnit g m))
    have hle := Nat.le_of_dvd (by have hh := hp.one_lt; omega : 0<p-1) hd
    nlinarith only [hle,hlong.2.2.2.1.1,Nat.sub_le p 1]
  have hQ : 4*m^2<q := by
    let : Fact q.Prime := ⟨hq⟩
    have hd := ZMod.orderOf_units_dvd_card_sub_one (rightUnit (projectedUnit g m))
    have hle := Nat.le_of_dvd (by have hh := hq.one_lt; omega : 0<q-1) hd
    nlinarith only [hle,hlong.2.2.2.1.2,Nat.sub_le q 1]
  exact ⟨hP,hQ⟩

/-- The long branch forces both hidden characteristics above the
ENTIRE raw grid mass. This uses no new trial-prefix premise. -/
theorem original_grid_mass_below_primes {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    (m-1)*(seedLength m/(4*m)+1)<p ∧ (m-1)*(seedLength m/(4*m)+1)<q := by
  have hcount := (linear_moment_grid_count hm).2.2
  have hcap := original_characteristics_above_cap hp hq hm g hlong
  constructor <;> omega

/-- The actual long orders already exclude a public modulus dividing
either hidden prime; no additional trial-prefix assumption is needed. -/
theorem original_modulus_coprime {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) : m.Coprime (p*q) := by
  have hcap := original_characteristics_above_cap hp hq hm g hlong
  have hsmall : m≤4*m^2 := by nlinarith only [hm]
  exact (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (hsmall.trans_lt hcap.1))).symm.mul_right
      (hq.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) (hsmall.trans_lt hcap.2))).symm

/-- A complete original grid presentation reduces to the exact
labeled local moments; no hidden polynomial or order is algorithm advice. -/
theorem original_grid_map_relation {N : ℕ} {S : Type*} [CommRing S]
    (f : ZMod N→+*S) (g : (ZMod N)ˣ) (m w J : ℕ) (U V : (ZMod N)[X])
    (hUV : (U : PowerSeries (ZMod N))*centredGridSeries g m w J=(V : PowerSeries (ZMod N))) :
    ((U.map f) : PowerSeries S)*
      (∑ jk∈(Finset.range (m-1)) ×ˢ (Finset.range J),
        positiveMoments (f (seedPoint g m w (jk.1+1) jk.2)))=(V.map f : PowerSeries S) := by
  have he := congrArg (PowerSeries.map f) hUV
  rw [map_mul,original_grid_labelled,map_sum] at he
  simp only [←Polynomial.polynomial_map_coe,positiveMoments_map] at he
  exact he

/-- No individual original local point can disappear from the
denominator by moment cancellation when the raw mass is below the prime. -/
theorem prime_grid_denominator_roots {N r : ℕ} (hr : r.Prime)
    (f : ZMod N→+*ZMod r) (g : (ZMod N)ˣ) (m w J : ℕ)
    (hsize : (m-1)*J<r) (U V : (ZMod N)[X])
    (hUV : (U : PowerSeries (ZMod N))*centredGridSeries g m w J=(V : PowerSeries (ZMod N))) :
    ∀ j<m-1,∀ k<J,(U.map f).eval (f (seedPoint g m w (j+1) k))⁻¹=0 := by
  let : Fact r.Prime := ⟨hr⟩
  let I := (Finset.range (m-1)) ×ˢ (Finset.range J)
  have hcount : I.card=(m-1)*J := by simp only [I,Finset.card_product,Finset.card_range]
  have hx : ∀ jk∈I,f (seedPoint g m w (jk.1+1) jk.2)≠0 := by
    intro jk _
    exact ((original_point_unit g m w (jk.1+1) jk.2).map f).ne_zero
  intro j hj k hk
  exact labelled_prime_denominator_roots hr I
    (fun jk => f (seedPoint g m w (jk.1+1) jk.2)) (by simpa only [hcount] using hsize)
    hx (U.map f) (V.map f) (original_grid_map_relation f g m w J U V hUV)
    (j,k) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,Finset.mem_range.mpr hk⟩)

/-- A denominator must pay for EVERY distinct local point. No
root-count principle over the composite ring is used. -/
theorem prime_grid_denominator_degree {N r : ℕ} (hr : r.Prime)
    (f : ZMod N→+*ZMod r) (g : (ZMod N)ˣ) (m w J : ℕ)
    (hsize : (m-1)*J<r) (U V : (ZMod N)[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries (ZMod N))*centredGridSeries g m w J=(V : PowerSeries (ZMod N))) :
    (((Finset.range (m-1)) ×ˢ (Finset.range J)).image
      (fun jk => f (seedPoint g m w (jk.1+1) jk.2))).card≤U.natDegree := by
  let : Fact r.Prime := ⟨hr⟩
  let I := (Finset.range (m-1)) ×ˢ (Finset.range J)
  have hcount : I.card=(m-1)*J := by simp only [I,Finset.card_product,Finset.card_range]
  have hx : ∀ jk∈I,f (seedPoint g m w (jk.1+1) jk.2)≠0 := by
    intro jk _
    exact ((original_point_unit g m w (jk.1+1) jk.2).map f).ne_zero
  have hlocal := labelled_prime_denominator_degree hr I
    (fun jk => f (seedPoint g m w (jk.1+1) jk.2)) (by simpa only [hcount] using hsize)
    hx (U.map f) (V.map f) (by simp only [coeff_map,hU,map_one])
    (original_grid_map_relation f g m w J U V hUV)
  exact hlocal.trans natDegree_map_le

/-- EVERY actual local pole survives in the whole ORIGINAL linear-width
grid. Its denominator degree is at least the larger local point count. -/
theorem original_denominator_local_degrees {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
      (seedLength m/(4*m)+1)=(V : PowerSeries (ZMod (p*q)))) :
    let I := (Finset.range (m-1)) ×ˢ (Finset.range (seedLength m/(4*m)+1))
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    (I.image (fun jk => ZMod.castHom (dvd_mul_right p q) (ZMod p) (point jk))).card≤U.natDegree ∧
      (I.image (fun jk => ZMod.castHom (dvd_mul_left q p) (ZMod q) (point jk))).card≤U.natDegree := by
  have hmass := original_grid_mass_below_primes hp hq hm g hlong
  exact ⟨prime_grid_denominator_degree hp _ _ _ _ _ hmass.1 U V hU hUV,
    prime_grid_denominator_degree hq _ _ _ _ _ hmass.2 U V hU hUV⟩

/-- A short finite prefix certificate can have degree d only if the
ENTIRE original grid actually coalesces to at most d points in EACH
hidden field. Formal coefficient cancellations cannot substitute for
those arithmetic collisions. No universal degree bound is inferred. -/
theorem original_prefix_requires_local_collisions {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hd : d≤m^2)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) :
    let I := (Finset.range (m-1)) ×ˢ (Finset.range (seedLength m/(4*m)+1))
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    (I.image (fun jk => ZMod.castHom (dvd_mul_right p q) (ZMod p) (point jk))).card≤d ∧
      (I.image (fun jk => ZMod.castHom (dvd_mul_left q p) (ZMod q) (point jk))).card≤d := by
  have hUV := original_polynomial_prefix_certificate hp hq hm hd g hlong U V hU hUd hVd hprefix
  have hlocal := original_denominator_local_degrees hp hq hm g hlong U V hU hUV
  exact ⟨hlocal.1.trans hUd,hlocal.2.trans hUd⟩

/-- Too many distinct global points for their local image force a
proper public gcd. Equal global points are explicitly excluded. -/
theorem small_local_image_proper_difference {p q d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (S : Finset (ZMod (p*q)))
    (hlocal : (S.image (ZMod.castHom (dvd_mul_right p q) (ZMod p))).card≤d)
    (hlarge : d<S.card) :
    ∃ x∈S,∃ y∈S,x≠y ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (x-y).val) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  have hn : ¬(∀ x∈S,∀ y∈S,x≠y → IsUnit (x-y)) := by
    intro hs
    have hinj : Set.InjOn f S := by
      intro x hx y hy he
      by_contra hxy
      have hne := ((hs x hx y hy hxy).map f).ne_zero
      exact hne (by rw [map_sub,he,sub_self])
    have hcard := Finset.card_image_of_injOn hinj
    exact (hcard ▸ hlocal).not_gt hlarge
  push Not at hn
  obtain ⟨x,hx,y,hy,hxy,hunit⟩ := hn
  exact ⟨x,hx,y,hy,hxy,
    SemiprimeTraceRows.proper_gcd_of_nonzero_nonunit (sub_ne_zero.mpr hxy) hunit⟩

/-- The first three blocks are retained both in the full new padding
and in the frozen original point domain used for the exact fiber bound. -/
theorem original_three_blocks_retained {m : ℕ} (hm : 4≤m) :
    3≤SemiprimeSharedIntervalJet.blockCount m (4*m) ∧
      3≤seedLength m/(4*m)+1 := by
  have hw : 0<4*m := by omega
  have hb : 2*(4*m)≤3*m^2 := by nlinarith only [hm]
  have hL : 2*(4*m)≤seedLength m := by
    have hh := (seedLength_bounds hm).1
    nlinarith only [hh,hm]
  have hbdiv := (Nat.le_div_iff_mul_le hw).mpr hb
  have hLdiv := (Nat.le_div_iff_mul_le hw).mpr hL
  simp only [SemiprimeSharedIntervalJet.blockCount]
  constructor <;> omega

/-- A validated candidate forces a proper-factor collision in ANY
short original sample exceeding twice its degree. The sample must be
retained in both the full padding and the frozen exact-fiber domain. -/
theorem original_prefix_sample_proper_difference {p q m d T : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime) (hd : d≤m^2)
    (hblocks : T≤SemiprimeSharedIntervalJet.blockCount m (4*m) ∧
      T≤seedLength m/(4*m)+1) (hsource : 2*d<T*(m-1))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) :
    let sample := (Finset.range (m-1)) ×ˢ (Finset.range T)
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    ∃ u∈sample,∃ v∈sample,point u≠point v ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (point u-point v).val) := by
  classical
  let sample := (Finset.range (m-1)) ×ˢ (Finset.range T)
  let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
  let S := sample.image point
  let I := (Finset.range (m-1)) ×ˢ (Finset.range (seedLength m/(4*m)+1))
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  have hdomain : sample⊆pointDomain m (4*m) := by
    intro jk hjk
    have hh := Finset.mem_product.mp hjk
    exact Finset.mem_product.mpr ⟨hh.1,Finset.mem_range.mpr
      ((Finset.mem_range.mp hh.2).trans_le hblocks.1)⟩
  have hsample : sample⊆I := by
    intro jk hjk
    have hh := Finset.mem_product.mp hjk
    exact Finset.mem_product.mpr ⟨hh.1,Finset.mem_range.mpr
      ((Finset.mem_range.mp hh.2).trans_le hblocks.2)⟩
  have hcount : sample.card=T*(m-1) := by
    simp only [sample,Finset.card_product,Finset.card_range,mul_comm]
  have hfiber : ∀ x∈S,(sample.filter fun jk => point jk=x).card≤2 := by
    intro x _
    have hsub : (sample.filter fun jk => point jk=x)⊆pointFiber (projectedUnit g m) m (4*m) x := by
      intro jk hjk
      exact Finset.mem_filter.mpr ⟨hdomain (Finset.mem_filter.mp hjk).1,(Finset.mem_filter.mp hjk).2⟩
    exact (Finset.card_le_card hsub).trans (pointFiber_card_le_two hp hq hpq hm hmprime
      (original_modulus_coprime hp hq hm g hlong) (by omega) (by nlinarith only [hm]) g hlong x)
  have hraw : sample.card≤2*S.card := by
    calc
      sample.card=∑ x∈S,(sample.filter fun jk => point jk=x).card :=
        Finset.card_eq_sum_card_image point sample
      _ ≤ ∑ _x∈S,2 := Finset.sum_le_sum hfiber
      _=2*S.card := by simp only [Finset.sum_const,smul_eq_mul,mul_comm]
  have hbig : d<S.card := by rw [hcount] at hraw; omega
  have hsmall := (original_prefix_requires_local_collisions hp hq hm
    hd g hlong U V hU hUd hVd hprefix).1
  have himage : S.image f⊆I.image (fun jk => f (point jk)) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨jk,hjk,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (hsample hjk)
  have hlocal : (S.image f).card≤d := (Finset.card_le_card himage).trans hsmall
  obtain ⟨x,hx,y,hy,hxy,hproper⟩ := small_local_image_proper_difference hp hq S hlocal hbig
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨u,hu,v,hv,hxy,hproper⟩

/-- A degree-at-most-m prefix certificate forces a proper collision
among only 3(m-1) original public labels, with no prefix-none premise. -/
theorem original_small_prefix_proper_difference {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime) (hd : d≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) :
    let sample := (Finset.range (m-1)) ×ˢ (Finset.range 3)
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    ∃ u∈sample,∃ v∈sample,point u≠point v ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (point u-point v).val) := by
  exact original_prefix_sample_proper_difference hp hq hpq hm hmprime
    (hd.trans (by nlinarith only [hm] : m≤m^2)) (original_three_blocks_retained hm)
    (by omega) g hlong U V hU hUd hVd hprefix

/-- A public sample of at most 2d+m-1 labels already exceeds twice
degree d. Its first T blocks are retained whenever d<=m^2/8; in
particular this permits soft-linear degrees inside that public window. -/
theorem public_short_sample_bounds {m d : ℕ} (hm : 4≤m) (hd : d≤m^2/8) :
    let T := 2*d/(m-1)+1
    T≤SemiprimeSharedIntervalJet.blockCount m (4*m) ∧
      T≤seedLength m/(4*m)+1 ∧ 2*d<T*(m-1) ∧ T*(m-1)≤2*d+(m-1) := by
  let M := m-1
  have hM : 0<M := by dsimp only [M]; omega
  have hMeq : M+1=m := by dsimp only [M]; omega
  have h8 : 8*d≤m^2 := by
    have hh := (Nat.le_div_iff_mul_le (by decide : 0<8)).mp hd
    nlinarith only [hh]
  have hMsq : m^2≤2*M^2 := by nlinarith only [hm,hMeq]
  have hhalf : M≤2*(m/2) := by omega
  have hmul := Nat.mul_le_mul_left M hhalf
  have hbudget : 2*d≤(m/2)*M := by nlinarith only [h8,hMsq,hmul]
  have ht : 2*d/M≤m/2 := by
    have hh := Nat.div_le_div_right (c:=M) hbudget
    simpa only [Nat.mul_div_cancel _ hM] using hh
  have hhalfle : 2*(m/2)≤m := by omega
  have hhalfprod := Nat.mul_le_mul_left (2*m) hhalfle
  have hb : (m/2)*(4*m)≤3*m^2 := by nlinarith only [hhalfprod]
  have hL : (m/2)*(4*m)≤seedLength m := by
    have hh := (seedLength_bounds hm).1
    nlinarith only [hhalfprod,hh]
  have hw : 0<4*m := by omega
  have hbdiv := (Nat.le_div_iff_mul_le hw).mpr hb
  have hLdiv := (Nat.le_div_iff_mul_le hw).mpr hL
  have hmod := Nat.mod_lt (2*d) hM
  have hdiv := Nat.mod_add_div (2*d) M
  change 2*d/M+1≤SemiprimeSharedIntervalJet.blockCount m (4*m) ∧
    2*d/M+1≤seedLength m/(4*m)+1 ∧
      2*d<(2*d/M+1)*M ∧ (2*d/M+1)*M≤2*d+M
  refine ⟨?_,by omega,?_,?_⟩
  · simp only [SemiprimeSharedIntervalJet.blockCount]
    omega
  · nlinarith only [hmod,hdiv]
  · nlinarith only [hdiv,Nat.zero_le ((2*d)%M)]

/-- For the actual finite candidate, a public sample of size at most
2d+m-1 forces a proper-factor pair. Prefix acquisition, candidate
existence and the cost of finding that pair remain separate obligations. -/
theorem original_public_sample_proper_difference {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime) (hd : d≤m^2/8)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) :
    let sample := (Finset.range (m-1)) ×ˢ (Finset.range (2*d/(m-1)+1))
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    sample.card≤2*d+(m-1) ∧
      ∃ u∈sample,∃ v∈sample,point u≠point v ∧
        SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (point u-point v).val) := by
  have hbounds := public_short_sample_bounds hm hd
  refine ⟨?_,?_⟩
  · simpa only [Finset.card_product,Finset.card_range,mul_comm] using hbounds.2.2.2
  · exact original_prefix_sample_proper_difference hp hq hpq hm hmprime
      (hd.trans (Nat.div_le_self _ _)) ⟨hbounds.1,hbounds.2.1⟩ hbounds.2.2.1
      g hlong U V hU hUd hVd hprefix

/-- The moment certificate's short public proper-factor witness attaches
to the ACTUAL N-only saved long base. Small-candidate existence and
bit-priced acquisition/search are deliberately not supplied as premises. -/
theorem actual_public_route_prefix_proper_difference {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : SemiprimeWrapIndexRecovery.routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      let B := centredGridSeries h m (4*m) (seedLength m/(4*m)+1)
      ∀ (d : ℕ) (U V : (ZMod (p*q))[X]), d≤m^2/8 → U.coeff 0=1 →
        U.natDegree≤d → V.natDegree≤d →
        (∀ r≤2*(d+(m-1)), PowerSeries.coeff r ((U : PowerSeries (ZMod (p*q)))*B)=V.coeff r) →
        let sample := (Finset.range (m-1)) ×ˢ (Finset.range (2*d/(m-1)+1))
        let point := fun jk : ℕ×ℕ => seedPoint h m (4*m) (jk.1+1) jk.2
        sample.card≤2*d+(m-1) ∧
          ∃ u∈sample,∃ v∈sample,point u≠point v ∧
            SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (point u-point v).val) := by
  have hd := SemiprimeWrapIndexRecovery.routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := hB.trans hmBounds.1
  refine ⟨hc,?_⟩
  dsimp only
  intro d U V hdegree hU hUd hVd hprefix
  exact original_public_sample_proper_difference hp hq hpq.ne hm
    (SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)) hdegree
    (ZMod.unitOfCoprime a hc) hlong U V hU hUd hVd hprefix

/-- A large local support rigorously excludes EVERY small polynomial
prefix candidate, regardless of its acquisition or representation.
This is a support criterion, not an assertion that all inputs meet it. -/
theorem large_local_support_excludes_prefix {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hd : d≤m^2)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let I := (Finset.range (m-1)) ×ˢ (Finset.range (seedLength m/(4*m)+1))
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    (d<(I.image (fun jk => ZMod.castHom (dvd_mul_right p q) (ZMod p) (point jk))).card ∨
      d<(I.image (fun jk => ZMod.castHom (dvd_mul_left q p) (ZMod q) (point jk))).card) →
      ¬∃ U V : (ZMod (p*q))[X], U.coeff 0=1 ∧ U.natDegree≤d ∧ V.natDegree≤d ∧
        ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
          ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
            (seedLength m/(4*m)+1))=V.coeff r := by
  dsimp only
  intro hlarge
  rintro ⟨U,V,hU,hUd,hVd,hprefix⟩
  have hcounts := original_prefix_requires_local_collisions hp hq hm hd g hlong U V hU hUd hVd hprefix
  rcases hlarge with hleft|hright
  · exact hcounts.1.not_gt hleft
  · exact hcounts.2.not_gt hright

/-- If the public short sample has no proper-factor pair, the proposed
small moment reconstruction cannot produce ANY valid prefix candidate.
This is an exact route-failure criterion, not a universal no-hit claim
or a bit-cost bound for checking all sample pairs. -/
theorem no_public_sample_hit_excludes_prefix {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime) (hd : d≤m^2/8)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let sample := (Finset.range (m-1)) ×ˢ (Finset.range (2*d/(m-1)+1))
    let point := fun jk : ℕ×ℕ => seedPoint (projectedUnit g m) m (4*m) (jk.1+1) jk.2
    (∀ u∈sample,∀ v∈sample,
      ¬SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (point u-point v).val)) →
      ¬∃ U V : (ZMod (p*q))[X], U.coeff 0=1 ∧ U.natDegree≤d ∧ V.natDegree≤d ∧
        ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
          ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
            (seedLength m/(4*m)+1))=V.coeff r := by
  dsimp only
  intro hclear
  rintro ⟨U,V,hU,hUd,hVd,hprefix⟩
  obtain ⟨u,hu,v,hv,_,hproper⟩ :=
    (original_public_sample_proper_difference hp hq hpq hm hmprime hd g hlong U V hU hUd hVd hprefix).2
  exact hclear u hu v hv hproper

end RiemannGaussian.SemiprimeSeedMomentPoleRetention
