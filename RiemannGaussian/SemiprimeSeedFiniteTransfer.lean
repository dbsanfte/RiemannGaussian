/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedGeometricRecurrence

/-!
# Arithmetic of the finite original seed targets

The short integer offsets and the retained local orders imply that distinct
unshifted seed values have unit differences. Duplicate values are exact offset
duplicates, rather than collisions confined to one hidden prime field. After
removing those duplicates the target polynomial has unit derivatives at its
roots. These facts justify interpolation denominators; they do not acquire
the original geometric interval remainders or price their construction.

An explicit factor residual forces a prime-field collision at an original
seed. Splitting the retained simple-root interval makes exactly one half
vanish there. Thus no unit-valued multiplicative ratio can transfer between
the two halves at every original target, even for this finite actual family.
Additional derivative state or a different acquisition algorithm is not ruled out.
-/

namespace RiemannGaussian.SemiprimeSeedFiniteTransfer

open scoped BigOperators
open Polynomial SemiprimeGeometricRows SemiprimeIntervalJet
open SemiprimeGlobalPhaseCancellation SemiprimeSeedSumAcquisition
open SemiprimeSeedHermiteQuotient SemiprimeSeedGeometricRecurrence
open SemiprimeLocalOrderRouting SemiprimeCentreFreeCover SemiprimeLongPowerRouting
open SemiprimeDenseRowCarries SemiprimeQuotientRows SemiprimeDenseRowCoverage
open SemiprimeWrapIndexRecovery SemiprimeSharedIntervalJet SemiprimeWideWrapCoverage

/-- Original unshifted offsets differ by at most four quadratic widths. -/
theorem seed_offset_difference_bound {N m j j₀ : ℕ} (hm : 1<m)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m) :
    |seedOffset N m j-seedOffset N m j₀|≤4*(m : ℤ)^2 := by
  have hδ := seedOffset_bounds (N:=N) hm hj hjm
  have hδ₀ := seedOffset_bounds (N:=N) hm hj₀ hj₀m
  apply abs_le.mpr
  constructor <;> linarith only [hδ.1,hδ.2,hδ₀.1,hδ₀.2]

/-- Equality in any retained reduction with long enough order forces
exact equality of the integer offsets. The common N term cancels. -/
theorem seed_reduction_eq_iff_offset {N m j j₀ : ℕ}
    {R : Type*} [CommRing R] (f : ZMod N→+*R) (g : (ZMod N)ˣ)
    (hm : 1<m) (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hjcop : j.Coprime m) (hj₀cop : j₀.Coprime m)
    (horder : 4*m^2<orderOf (Units.map f.toMonoidHom g)) :
    f ((progressionSeed g N m j).step : ZMod N)=
      f ((progressionSeed g N m j₀).step : ZMod N) ↔
      seedOffset N m j=seedOffset N m j₀ := by
  constructor
  · intro he
    have hu : Units.map f.toMonoidHom (progressionSeed g N m j).step=
        Units.map f.toMonoidHom (progressionSeed g N m j₀).step := Units.ext he
    rw [seed_step_offset g (by omega) hjcop,seed_step_offset g (by omega) hj₀cop,
      map_zpow,map_zpow] at hu
    have hd : (orderOf (Units.map f.toMonoidHom g) : ℤ)∣
        seedOffset N m j-seedOffset N m j₀ := by
      simpa only [add_sub_add_left_eq_sub] using
        (orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hu)
    have ho : 4*(m : ℤ)^2<(orderOf (Units.map f.toMonoidHom g) : ℤ) := by
      exact_mod_cast horder
    have hab := (seed_offset_difference_bound (N:=N) hm hj hjm hj₀ hj₀m).trans_lt ho
    rw [←Int.natCast_natAbs] at hab
    have habN : (seedOffset N m j-seedOffset N m j₀).natAbs<
        (orderOf (Units.map f.toMonoidHom g) : ℤ).natAbs := by
      simpa only [Int.natAbs_natCast] using (show _<orderOf (Units.map f.toMonoidHom g)
        by exact_mod_cast hab)
    exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habN)
  · intro he
    rw [seed_step_offset g (by omega) hjcop,seed_step_offset g (by omega) hj₀cop,he]

/-- A local equality among original seed values is already a global
equality, whenever that local order exceeds the short offset range. -/
theorem seed_eq_of_reduction_eq {N m j j₀ : ℕ}
    {R : Type*} [CommRing R] (f : ZMod N→+*R) (g : (ZMod N)ˣ)
    (hm : 1<m) (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hjcop : j.Coprime m) (hj₀cop : j₀.Coprime m)
    (horder : 4*m^2<orderOf (Units.map f.toMonoidHom g))
    (he : f ((progressionSeed g N m j).step : ZMod N)=
      f ((progressionSeed g N m j₀).step : ZMod N)) :
    ((progressionSeed g N m j).step : ZMod N)=
      ((progressionSeed g N m j₀).step : ZMod N) := by
  have hδ := (seed_reduction_eq_iff_offset f g hm hj hjm hj₀ hj₀m hjcop hj₀cop horder).mp he
  rw [seed_step_offset g (by omega) hjcop,seed_step_offset g (by omega) hj₀cop,hδ]

/-- Both actual prime-field projections separate every pair of
globally distinct unshifted original seed values. Their difference is a unit. -/
theorem long_seed_difference_unit {p q m j j₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hne : ((progressionSeed (projectedUnit g m) (p*q) m j).step : ZMod (p*q))≠
      ((progressionSeed (projectedUnit g m) (p*q) m j₀).step : ZMod (p*q))) :
    IsUnit (((progressionSeed (projectedUnit g m) (p*q) m j).step : ZMod (p*q))-
      ((progressionSeed (projectedUnit g m) (p*q) m j₀).step : ZMod (p*q))) := by
  have hjcop : j.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hj₀cop : j₀.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  apply isUnit_of_prime_reductions hp hq
  · rw [map_sub]
    apply sub_ne_zero.mpr
    intro he
    apply hne
    apply seed_eq_of_reduction_eq _ _ (by omega) hj hjm hj₀ hj₀m hjcop hj₀cop _ he
    change 4*m^2<orderOf (leftUnit (projectedUnit g m))
    nlinarith only [hlong.2.2.2.1.1]
  · rw [map_sub]
    apply sub_ne_zero.mpr
    intro he
    apply hne
    apply seed_eq_of_reduction_eq _ _ (by omega) hj hjm hj₀ hj₀m hjcop hj₀cop _ he
    change 4*m^2<orderOf (rightUnit (projectedUnit g m))
    nlinarith only [hlong.2.2.2.1.2]

/-- The unit separation theorem applies to the actual original seed
list, not to the larger family of normalized block points. -/
theorem long_seedTargets_difference_unit {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    {x y : ZMod (p*q)} (hx : x∈seedTargets (projectedUnit g m) m)
    (hy : y∈seedTargets (projectedUnit g m) m) (hne : x≠y) : IsUnit (x-y) := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hy
  obtain ⟨hsmin,hsm,he⟩ := cached_seed_source hs
  obtain ⟨htmin,htm,he₀⟩ := cached_seed_source ht
  rw [he,he₀] at hne ⊢
  exact long_seed_difference_unit hp hq hm hmprime g hlong hsmin hsm htmin htm hne

/-- One finite value set, while the original labelled seed list remains available. -/
def distinctSeedTargets {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : Finset (ZMod N) :=
  (seedTargets g m).toFinset

/-- Removing exact duplicate values keeps at most the original linear seed count. -/
theorem distinctSeedTargets_card_le {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    (distinctSeedTargets g m).card≤m-1 := by
  exact (List.toFinset_card_le (l:=seedTargets g m)).trans_eq (seedTargets_length g m)

/-- A target polynomial retaining each distinct supplied value once. -/
noncomputable def finiteTargetPolynomial {R : Type*} [CommRing R] (s : Finset R) : R[X] :=
  ∏ x ∈ s, (X-C x : R[X])

/-- Its derivative at a retained root is the product of distinct value differences. -/
theorem finiteTargetPolynomial_derivative_eval {R : Type*} [CommRing R] [DecidableEq R]
    {s : Finset R} {x : R} (hx : x∈s) :
    (finiteTargetPolynomial s).derivative.eval x = ∏ y ∈ (s.erase x), (x-y : R) := by
  classical
  have he : finiteTargetPolynomial s=(X-C x)*finiteTargetPolynomial (s.erase x) :=
    (Finset.mul_prod_erase s (fun y => (X-C y : R[X])) hx).symm
  rw [he,derivative_mul,derivative_X_sub_C,eval_add,eval_mul,eval_mul,
    eval_one,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero,one_mul]
  simp only [finiteTargetPolynomial,eval_prod,eval_sub,eval_X,eval_C]

/-- Pairwise unit differences certify every finite interpolation derivative,
over a composite coefficient ring as well as over a field. -/
theorem finiteTargetPolynomial_derivative_unit {R : Type*} [CommRing R]
    {s : Finset R} {x : R} (hx : x∈s)
    (hunit : ∀ y∈s, x≠y→IsUnit (x-y)) :
    IsUnit ((finiteTargetPolynomial s).derivative.eval x) := by
  classical
  rw [finiteTargetPolynomial_derivative_eval hx]
  apply IsUnit.prod_iff.mpr
  intro y hy
  exact hunit y (Finset.mem_erase.mp hy).2 (Ne.symm (Finset.mem_erase.mp hy).1)

/-- The actual deduplicated original seed modulus has unit interpolation
denominators. Evaluated geometric interval products are not inverted here. -/
theorem long_distinctSeedTargets_derivative_unit {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    {x : ZMod (p*q)} (hx : x∈distinctSeedTargets (projectedUnit g m) m) :
    IsUnit ((finiteTargetPolynomial (distinctSeedTargets (projectedUnit g m) m)).derivative.eval x) := by
  apply finiteTargetPolynomial_derivative_unit hx
  intro y hy hne
  exact long_seedTargets_difference_unit hp hq hm hmprime g hlong
    (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hne

/-- The exact arithmetic residual forcing the original seed collision.
The index and offset are bounded integer lifts, not unknown discrete logs. -/
theorem forced_seed_arithmetic {p q m : ℕ} (hp : 0<p) (hpq : p≤q) (hm : 4≤m)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6) :
    ∃ r : ℕ, r≤2*m^2+1 ∧ r<seedLength m ∧
      ((p*q : ℕ) : ℤ)+seedOffset (p*q) m (p%m)-(m : ℤ)^2*r=
        ((p : ℤ)-1)*((q : ℤ)-(representative (p*q) m (p%m) 1 : ℤ)) := by
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  obtain ⟨I,hI,_⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (j:=p%m) (t:=1) (by omega) hj false)
  have hden : (denseRow (p*q) m (p%m) 1 false).t=(1 : ℤ) := rfl
  rw [hden,one_mul] at hI
  change (m : ℤ)^2*I=(seedRow (p*q) m (p%m)).a*p+
    (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q at hI
  have hbounds := seed_index_bounds (by omega) hpq hprefix hsize hI
  let r := I.toNat
  have hrI : (r : ℤ)=I := Int.toNat_of_nonneg hbounds.1
  have hupper := hbounds.2
  change I≤(2*m^2+1 : ℕ) at hupper
  have hr : r≤2*m^2+1 := by omega
  refine ⟨r,hr,?_,?_⟩
  · have hl := (seedLength_bounds hm).1
    omega
  · unfold seedOffset
    rw [Nat.cast_mul,hrI]
    change (m : ℤ)^2*I=(representative (p*q) m (p%m) 1 : ℤ)*p+
      (seedRow (p*q) m (p%m)).b*m-
      2*(representative (p*q) m (p%m) 1 : ℤ)*(p%m : ℕ)+q at hI
    linear_combination -hI

/-- Fermat turns the explicit residual into a collision in the p-field
for every public unit. The true residue belongs to the original seed list. -/
theorem forced_seed_prime_hit {p q m : ℕ}
    (hp : p.Prime) (hpq : p≤q) (hm : 4≤m)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) :
    ∃ r : ℕ, r≤2*m^2+1 ∧ r<seedLength m ∧
      (progressionSeed g (p*q) m (p%m))∈progressionSeeds g (p*q) m ∧
      ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((progressionSeed g (p*q) m (p%m)).step : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q)))^r := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,hrbound,hr,hres⟩ := forced_seed_arithmetic hp.pos hpq hm hprefix hN hsize
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hjpos : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    omega
  have hperiod : (leftUnit g)^((p : ℤ)-1)=1 := by
    simpa only [←zpow_natCast,Nat.cast_sub hp.one_le,Nat.cast_one] using
      ZMod.units_pow_card_sub_one_eq_one p (leftUnit g)
  have hsum : ((p*q : ℕ) : ℤ)+seedOffset (p*q) m (p%m)=
      (m : ℤ)^2*r+((p : ℤ)-1)*((q : ℤ)-(representative (p*q) m (p%m) 1 : ℤ)) := by
    linarith only [hres]
  have hu : leftUnit (progressionSeed g (p*q) m (p%m)).step=(leftUnit (seedBase g m))^r := by
    rw [seed_step_offset g (by omega) hj]
    simp only [leftUnit,map_zpow,seedBase,map_pow]
    change (leftUnit g)^(((p*q : ℕ) : ℤ)+seedOffset (p*q) m (p%m))=
      ((leftUnit g)^(m^2))^r
    rw [hsum,zpow_add]
    simp only [zpow_mul,hperiod,one_zpow,mul_one,←zpow_natCast,Nat.cast_pow]
  refine ⟨r,hrbound,hr,progressionSeed_mem g hjpos (Nat.mod_lt p (by omega)),?_⟩
  simpa [leftUnit,RingHom.toMonoidHom] using
    congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hu

/-- Literal second-block products commute with retained coefficient reductions. -/
theorem blockProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (alpha x : R) (o L : ℕ) :
    f (blockProduct alpha x o L)=blockProduct (f alpha) (f x) o L := by
  simp only [blockProduct,blockFactor,map_prod,map_sub,map_pow]

/-- A root in a simple-root interval lies in exactly one of its two
disjoint halves. The other half is nonzero in the same prime field. -/
theorem split_interval_root_separates {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L K r : ℕ} (hK : K≤L) (hr : r<L) (hperiod : L≤orderOf alpha) :
    (intervalProduct alpha (alpha^r) K=0 ∧
      blockProduct alpha (alpha^r) K (L-K)≠0) ∨
    (intervalProduct alpha (alpha^r) K≠0 ∧
      blockProduct alpha (alpha^r) K (L-K)=0) := by
  by_cases hrK : r<K
  · left
    refine ⟨(intervalProduct_zero_iff _ _ _).mpr ⟨r,hrK,rfl⟩,?_⟩
    intro hz
    obtain ⟨v,hv,he⟩ := Finset.prod_eq_zero_iff.mp hz
    have hvbound := Finset.mem_range.mp hv
    change alpha^r-alpha^(K+v)=0 at he
    have heq := pow_injOn_Iio_orderOf (hr.trans_le hperiod)
      (show K+v<orderOf alpha by omega) (sub_eq_zero.mp he)
    omega
  · right
    constructor
    · intro hz
      obtain ⟨v,hv,he⟩ := (intervalProduct_zero_iff _ _ _).mp hz
      have heq := pow_injOn_Iio_orderOf (hr.trans_le hperiod)
        (show v<orderOf alpha by omega) he
      omega
    · apply Finset.prod_eq_zero (i:=r-K)
      · apply Finset.mem_range.mpr
        omega
      · change alpha^r-alpha^(K+(r-K))=0
        rw [Nat.add_sub_of_le (by omega),sub_self]

/-- A pair of cleared multiplicative transfers at a separated root must
use a nonunit denominator in at least one direction. This applies to
arbitrary target-dependent scalars, not just polynomial multipliers. -/
theorem separated_root_forces_nonunit {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (f : R→+*S) {F G a d b e : R}
    (hseparate : (f F=0 ∧ f G≠0) ∨ (f F≠0 ∧ f G=0))
    (hforward : a*F=d*G) (hbackward : b*G=e*F) : ¬IsUnit d ∨ ¬IsUnit e := by
  rcases hseparate with hleft|hright
  · left
    intro hd
    have heq := congrArg f hforward
    rw [map_mul,map_mul,hleft.1,mul_zero] at heq
    have hz : f d=0 := (mul_eq_zero.mp heq.symm).resolve_right hleft.2
    exact (hd.map f).ne_zero hz
  · right
    intro he
    have heq := congrArg f hbackward
    rw [map_mul,map_mul,hright.2,mul_zero] at heq
    have hz : f e=0 := (mul_eq_zero.mp heq.symm).resolve_right hright.1
    exact (he.map f).ne_zero hz

/-- The actual arithmetic witness makes multiplicative two-way reuse
of the two half-interval values singular at an original seed target. -/
theorem long_seed_finite_transfer_singular {p q m : ℕ}
    (hp : p.Prime) (hpq : p≤q) (hm : 4≤m)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ x∈seedTargets (projectedUnit g m) m,
      let alpha := ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))
      let F := intervalProduct alpha x (seedHalfLength m)
      let G := blockProduct alpha x (seedHalfLength m) (seedLength m-seedHalfLength m)
      ∀ a d b e : ZMod (p*q), a*F=d*G→b*G=e*F→¬IsUnit d ∨ ¬IsUnit e := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,_,hr,hs,hhit⟩ := forced_seed_prime_hit hp hpq hm hprefix hN hsize
    (projectedUnit g m)
  let x : ZMod (p*q) := ((progressionSeed (projectedUnit g m) (p*q) m (p%m)).step : ZMod (p*q))
  refine ⟨x,List.mem_map.mpr ⟨_,hs,rfl⟩,?_⟩
  dsimp only
  intro a d b e hf hb
  apply separated_root_forces_nonunit (ZMod.castHom (dvd_mul_right p q) (ZMod p)) _ hf hb
  rw [intervalProduct_map,blockProduct_map,hhit]
  exact split_interval_root_separates _
    (by have hh := seedHalfLength_bounds hm; omega) hr
    (long_seed_interval_periods hm g hlong).1

/-- Even a target-dependent unit ratio cannot turn one actual half product
into the other on every original seed. The obstruction uses the forced
prime-field zero, not a universal operator on arbitrary polynomials. -/
theorem long_no_unit_half_transfer {p q m : ℕ}
    (hp : p.Prime) (hpq : p≤q) (hm : 4≤m)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ¬∃ u : ZMod (p*q)→(ZMod (p*q))ˣ, ∀ x∈seedTargets (projectedUnit g m) m,
      let alpha := ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))
      (u x : ZMod (p*q))*intervalProduct alpha x (seedHalfLength m)=
        blockProduct alpha x (seedHalfLength m) (seedLength m-seedHalfLength m) := by
  obtain ⟨x,hx,hsingular⟩ :=
    long_seed_finite_transfer_singular hp hpq hm hprefix hN hsize g hlong
  dsimp only at hsingular
  rintro ⟨u,hu⟩
  have hf := hu x hx
  have hb := congrArg (fun z : ZMod (p*q) => (((u x)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q))*z) hf
  rw [←mul_assoc,(u x).inv_mul,one_mul] at hb
  have hbad := hsingular (u x) 1 ((((u x)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q))) 1
    (by simpa only [one_mul] using hf) (by simpa only [one_mul] using hb.symm)
  rcases hbad with hbad|hbad
  · exact hbad isUnit_one
  · exact hbad isUnit_one

/-- These finite-target arithmetic properties apply to the actual public
long route after its public factor prefix has returned none. The route
and prefix supply arithmetic hypotheses, not their bit-operation prices. -/
theorem actual_public_route_finite_checkpoint {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      (∀ x∈seedTargets h m, ∀ y∈seedTargets h m, x≠y→IsUnit (x-y)) ∧
      (∀ x∈distinctSeedTargets h m,
        IsUnit ((finiteTargetPolynomial (distinctSeedTargets h m)).derivative.eval x)) ∧
      (∃ x∈seedTargets h m,
        let alpha := ((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q))
        let F := intervalProduct alpha x (seedHalfLength m)
        let G := blockProduct alpha x (seedHalfLength m) (seedLength m-seedHalfLength m)
        ∀ a d b e : ZMod (p*q), a*F=d*G→b*G=e*F→¬IsUnit d ∨ ¬IsUnit e) ∧
      ¬∃ u : ZMod (p*q)→(ZMod (p*q))ˣ, ∀ x∈seedTargets h m,
        let alpha := ((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q))
        (u x : ZMod (p*q))*intervalProduct alpha x (seedHalfLength m)=
          blockProduct alpha x (seedHalfLength m) (seedLength m-seedHalfLength m) := by
  have hdata := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hbounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hbounds.1
  have hbudget : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hbounds.1 6)
  have hcover : m^2<p*q := public_modulus_prefix_below_input hN hB
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hmprime : m.Prime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hmprime.pos
    (by have hh := hmprime.two_le; nlinarith only [hh] : m≤m^2)
  refine ⟨hc,?_⟩
  dsimp only
  refine ⟨?_,?_,long_seed_finite_transfer_singular hp hpq.le hm hprefix.le hcop.symm
    hbudget g hlong,long_no_unit_half_transfer hp hpq.le hm hprefix.le hcop.symm hbudget g hlong⟩
  · intro x hx y hy hne
    exact long_seedTargets_difference_unit hp hq hm hmprime g hlong hx hy hne
  · intro x hx
    exact long_distinctSeedTargets_derivative_unit hp hq hm hmprime g hlong hx

end RiemannGaussian.SemiprimeSeedFiniteTransfer
