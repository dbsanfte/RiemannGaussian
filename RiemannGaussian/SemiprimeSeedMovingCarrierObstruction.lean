/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedLinearStateObstruction

/-!
# Whole-family moving root carriers: acquisition floor or a proper factor

Allow unrelated monic carriers at every acquisition stage, with arbitrary
overlap and no fixed transition or recurrence. Each actual normalized leaf
point must be a root of at least one retained carrier. Unit-separated roots
inject into a hidden prime field, so their number is at most the total
carrier degree. The original adaptive coverage and unit factory coefficients
then force a superlinear factory/carrier source.

The work consequence explicitly charges the acquired quotient bases. It
does not infer that charge for a shared implicit encoding, an inexpensive
update of reused storage, or an algorithm emitting no such bases.

Over the composite ring a monic carrier can have more global roots than its
degree. We retain that alternative: two distinct points have a nonunit
difference, whose public gcd is a proper factor. Only 2*d+1 original leaf
labels are needed to force this witness if a degree-at-most-d carrier has
already been obtained. These are necessity and existence theorems, not an
executable near-linear construction or witness-search cost certificate.
-/

namespace RiemannGaussian.SemiprimeSeedMovingCarrierObstruction

open scoped BigOperators
open SemiprimeAdaptiveSeedAcquisitionObstruction SemiprimeSeedPointRigidity
open SemiprimeLocalOrderRouting SemiprimeSeedSumAcquisition SemiprimeGeometricRows
open SemiprimeWrapIndexRecovery SemiprimeWideWrapCoverage
open SemiprimeCentreFreeCover

/-- Unit differences make reduction to one hidden prime injective on
the retained points. Monicity prevents the carrier from becoming zero.
No root bound over the composite ring itself is assumed. -/
theorem unit_separated_carrier_root_count {p q : ℕ} (hp : p.Prime)
    (S : Finset (ZMod (p*q))) (U : Polynomial (ZMod (p*q))) (hU : U.Monic)
    (hroots : ∀ x∈S,U.eval x=0)
    (hseparated : ∀ x∈S,∀ y∈S,x≠y → IsUnit (x-y)) :
    S.card≤U.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  have hmonic : (U.map f).Monic := hU.map f
  have hmapping : Set.MapsTo f S (U.map f).roots.toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hmonic.ne_zero).mpr
    change (U.map f).eval (f x)=0
    rw [Polynomial.eval_map_apply,hroots x hx,map_zero]
  have hinj : (S : Set (ZMod (p*q))).InjOn f := by
    intro x hx y hy he
    by_contra hxy
    have hn := ((hseparated x hx y hy hxy).map f).ne_zero
    exact hn (by rw [map_sub,he,sub_self])
  have hc := Finset.card_le_card_of_injOn _ hmapping hinj
  have hr := Multiset.toFinset_card_le (U.map f).roots
  have hd := Polynomial.card_roots' (U.map f)
  rw [hU.natDegree_map f] at hd
  omega

/-- An arbitrary forest of monic root carriers has total degree at
least the number of distinct points it covers when points in each
carrier are unit-separated. Cross-carrier separation is not required.
Carriers may change between stages and share roots. -/
theorem unit_separated_carrier_forest_root_count {p q : ℕ} {ι : Type*}
    (hp : p.Prime) (S : Finset (ZMod (p*q))) (I : Finset ι)
    (U : ι→Polynomial (ZMod (p*q))) (hU : ∀ i∈I,(U i).Monic)
    (hcover : ∀ x∈S,∃ i∈I,(U i).eval x=0)
    (hseparated : ∀ i∈I,∀ x∈S,∀ y∈S,
      (U i).eval x=0 → (U i).eval y=0 → x≠y → IsUnit (x-y)) :
    S.card≤∑ i∈I,(U i).natDegree := by
  classical
  let rootsAt := fun i => S.filter fun x => (U i).eval x=0
  have hsubset : S⊆I.biUnion rootsAt := by
    intro x hx
    obtain ⟨i,hi,he⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hx,he⟩⟩
  calc
    S.card≤(I.biUnion rootsAt).card := Finset.card_le_card hsubset
    _ ≤ ∑ i∈I,(rootsAt i).card := Finset.card_biUnion_le
    _ ≤ ∑ i∈I,(U i).natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      exact unit_separated_carrier_root_count hp (rootsAt i) (U i) (hU i hi)
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (fun x hx y hy hxy => hseparated i hi x (Finset.mem_filter.mp hx).1
          y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hx).2
          (Finset.mem_filter.mp hy).2 hxy)

/-- Exceeding total monic carrier degree forces a NONZERO nonunit
point difference within one carrier and a proper public gcd. Equal global points cannot
be used as this witness, so complete-modulus saturation is excluded. -/
theorem small_carrier_forest_proper_difference {p q : ℕ} {ι : Type*}
    (hp : p.Prime) (hq : q.Prime) (S : Finset (ZMod (p*q))) (I : Finset ι)
    (U : ι→Polynomial (ZMod (p*q))) (hU : ∀ i∈I,(U i).Monic)
    (hcover : ∀ x∈S,∃ i∈I,(U i).eval x=0)
    (hsmall : ∑ i∈I,(U i).natDegree<S.card) :
    ∃ i∈I,∃ x∈S,∃ y∈S,(U i).eval x=0 ∧ (U i).eval y=0 ∧ x≠y ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (x-y).val) := by
  classical
  let : NeZero (p*q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hq.pos)⟩
  have hn : ¬(∀ i∈I,∀ x∈S,∀ y∈S,
      (U i).eval x=0 → (U i).eval y=0 → x≠y → IsUnit (x-y)) := by
    intro hs
    exact (unit_separated_carrier_forest_root_count hp S I U hU hcover hs).not_gt hsmall
  push Not at hn
  obtain ⟨i,hi,x,hx,y,hy,hrootx,hrooty,hxy,hunit⟩ := hn
  exact ⟨i,hi,x,hx,y,hy,hrootx,hrooty,hxy,
    SemiprimeTraceRows.proper_gcd_of_nonzero_nonunit (sub_ne_zero.mpr hxy) hunit⟩

/-- More than twice the carrier degree in ORIGINAL raw leaf labels
already forces a proper-factor pair. The frozen whole-family quadratic
fiber bound handles exact duplicate points before the prime-field step. -/
theorem adaptive_carrier_overflow_factor {p q m : ℕ} {ι : Type*}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (I : Finset ι) (U : ι→Polynomial (ZMod (p*q))) (hU : ∀ i∈I,(U i).Monic)
    (hroots : ∀ x∈adaptivePoints (projectedUnit g m) m leaves,
      ∃ i∈I,(U i).eval x=0)
    (hoverflow : 2*(∑ i∈I,(U i).natDegree)<leaves.card) :
    ∃ u∈leaves,∃ v∈leaves,
      seedPoint (projectedUnit g m) m 1 (u.1+1) u.2≠
        seedPoint (projectedUnit g m) m 1 (v.1+1) v.2 ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd
        (seedPoint (projectedUnit g m) m 1 (u.1+1) u.2-
          seedPoint (projectedUnit g m) m 1 (v.1+1) v.2).val) := by
  have hf := adaptive_distinct_point_count hp hq hpq hm hmprime hN g hlong leaves hcore
  have hsmall : (∑ i∈I,(U i).natDegree)<
      (adaptivePoints (projectedUnit g m) m leaves).card := by omega
  obtain ⟨i,hi,x,hx,y,hy,hrootx,hrooty,hxy,hfactor⟩ := small_carrier_forest_proper_difference
    hp hq (adaptivePoints (projectedUnit g m) m leaves) I U hU hroots hsmall
  obtain ⟨u,hu,hux⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,hvy⟩ := Finset.mem_image.mp hy
  exact ⟨u,hu,v,hv,by simpa only [hux,hvy] using hxy,
    by simpa only [hux,hvy] using hfactor⟩

/-- A degree-at-most-d monic carrier already acquired on just 2*d+1
original labels forces a proper point-difference factor witness. This
does not require constructing the entire superlinear point stream;
obtaining the carrier and finding the witness are still unpriced. -/
theorem short_carrier_leaf_factor_witness {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (hcount : leaves.card=2*d+1) (U : Polynomial (ZMod (p*q))) (hU : U.Monic)
    (hdegree : U.natDegree≤d)
    (hroots : ∀ x∈adaptivePoints (projectedUnit g m) m leaves,U.eval x=0) :
    ∃ u∈leaves,∃ v∈leaves,
      seedPoint (projectedUnit g m) m 1 (u.1+1) u.2≠
        seedPoint (projectedUnit g m) m 1 (v.1+1) v.2 ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd
        (seedPoint (projectedUnit g m) m 1 (u.1+1) u.2-
          seedPoint (projectedUnit g m) m 1 (v.1+1) v.2).val) := by
  apply adaptive_carrier_overflow_factor hp hq hpq hm hmprime hN g hlong leaves hcore
    ({()} : Finset Unit) (fun _ => U)
  · intro i hi
    exact hU
  · intro x hx
    exact ⟨(),Finset.mem_singleton_self (),hroots x hx⟩
  · simpa only [Finset.sum_singleton] using
      (show 2*U.natDegree<leaves.card by omega)

/-- Root-retaining moving carriers cannot reduce a factor-free,
unit-interpolable WHOLE-FAMILY materialized source to near-linear size.
Only factory coefficient slots and total quotient basis degrees are
charged; no explicit normalized-point or leaf-label stream is assumed. -/
theorem adaptive_unit_carrier_factory_source_floor {p q m : ℕ} {ι : Type*}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (width : (ℕ×ℕ)→ℕ) (hwidth : ∀ u∈leaves,width u≤seedLength m)
    (coefficientSlots : Finset ℕ)
    (hcoefficients : ∀ u∈leaves,∀ k,(rowPolynomial
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) (width u)).coeff k≠0 →
        k∈coefficientSlots)
    (hcover : ∀ v∈coreLabels m,∃ u∈leaves,
      u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u)
    (I : Finset ι) (U : ι→Polynomial (ZMod (p*q))) (hU : ∀ i∈I,(U i).Monic)
    (hroots : ∀ x∈adaptivePoints (projectedUnit g m) m leaves,
      ∃ i∈I,(U i).eval x=0)
    (hseparated : ∀ i∈I,∀ x∈adaptivePoints (projectedUnit g m) m leaves,
      ∀ y∈adaptivePoints (projectedUnit g m) m leaves,
      (U i).eval x=0 → (U i).eval y=0 → x≠y → IsUnit (x-y)) :
    2*m^3<(coefficientSlots.card+∑ i∈I,(U i).natDegree)^2 := by
  have hcapacity : ∀ u∈leaves,width u≤coefficientSlots.card := by
    intro u hu
    have hc := original_leaf_coefficient_source_floor hp hq hm g hlong (hwidth u hu)
      coefficientSlots (hcoefficients u hu)
    omega
  have hf := adaptive_source_floor hp hq hpq hm hmprime hN g hlong leaves hcore
    (variable_leaf_coverage leaves width hcapacity hcover)
  have hd := unit_separated_carrier_forest_root_count hp
    (adaptivePoints (projectedUnit g m) m leaves) I U hU hroots hseparated
  exact hf.trans_le (Nat.pow_le_pow_left (Nat.add_le_add_left hd coefficientSlots.card) 2)

/-- Unconditional arithmetic dichotomy for the moving-carrier route:
superlinear charged factory/carrier acquisition, or an actual normalized-point
pair with a proper public gcd. The latter is an existence conclusion,
not an oracle for acquiring or searching a small carrier. -/
theorem adaptive_carrier_factory_acquisition_dichotomy {p q m work : ℕ} {ι : Type*}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (width : (ℕ×ℕ)→ℕ) (hwidth : ∀ u∈leaves,width u≤seedLength m)
    (coefficientSlots : Finset ℕ)
    (hcoefficients : ∀ u∈leaves,∀ k,(rowPolynomial
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) (width u)).coeff k≠0 →
        k∈coefficientSlots)
    (hcover : ∀ v∈coreLabels m,∃ u∈leaves,
      u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u)
    (I : Finset ι) (U : ι→Polynomial (ZMod (p*q))) (hU : ∀ i∈I,(U i).Monic)
    (hroots : ∀ x∈adaptivePoints (projectedUnit g m) m leaves,
      ∃ i∈I,(U i).eval x=0)
    (hcharged : coefficientSlots.card+(∑ i∈I,(U i).natDegree)≤work) :
    (2*m^3<(coefficientSlots.card+∑ i∈I,(U i).natDegree)^2 ∧ 2*m^3<work^2) ∨
      ∃ i∈I,∃ x∈adaptivePoints (projectedUnit g m) m leaves,
        ∃ y∈adaptivePoints (projectedUnit g m) m leaves,
          (U i).eval x=0 ∧ (U i).eval y=0 ∧ x≠y ∧
          SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (x-y).val) := by
  classical
  let : NeZero (p*q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hq.pos)⟩
  by_cases hs : ∀ i∈I,∀ x∈adaptivePoints (projectedUnit g m) m leaves,
      ∀ y∈adaptivePoints (projectedUnit g m) m leaves,
      (U i).eval x=0 → (U i).eval y=0 → x≠y → IsUnit (x-y)
  · have hf := adaptive_unit_carrier_factory_source_floor hp hq hpq hm hmprime hN
      g hlong leaves hcore width hwidth coefficientSlots hcoefficients hcover I U hU hroots hs
    exact Or.inl ⟨hf,hf.trans_le (Nat.pow_le_pow_left hcharged 2)⟩
  · push Not at hs
    obtain ⟨i,hi,x,hx,y,hy,hrootx,hrooty,hxy,hunit⟩ := hs
    exact Or.inr ⟨i,hi,x,hx,y,hy,hrootx,hrooty,hxy,
      SemiprimeTraceRows.proper_gcd_of_nonzero_nonunit (sub_ne_zero.mpr hxy) hunit⟩

/-- Attachment to the actual original N-only long route and its prefix.
Hidden factors enter the proof only. No explicit point enumeration,
fixed remainder, fixed linear transition or recurrence is required. -/
theorem actual_public_route_carrier_acquisition_dichotomy {p q a : ℕ} {ι : Type*}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∀ (leaves : Finset (ℕ×ℕ)) (width : (ℕ×ℕ)→ℕ) (coefficientSlots : Finset ℕ)
        (I : Finset ι) (U : ι→Polynomial (ZMod (p*q))) (work : ℕ),
        leaves⊆coreLabels m →
        (∀ u∈leaves,width u≤seedLength m) →
        (∀ u∈leaves,∀ k,(rowPolynomial
          ((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q)) (width u)).coeff k≠0 →
            k∈coefficientSlots) →
        (∀ v∈coreLabels m,∃ u∈leaves,
          u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u) →
        (∀ i∈I,(U i).Monic) →
        (∀ x∈adaptivePoints h m leaves,∃ i∈I,(U i).eval x=0) →
        coefficientSlots.card+(∑ i∈I,(U i).natDegree)≤work →
        (2*m^3<(coefficientSlots.card+∑ i∈I,(U i).natDegree)^2 ∧
          2*m^3<work^2 ∧ 4*(p*q)<work^4) ∨
          ∃ i∈I,∃ x∈adaptivePoints h m leaves,∃ y∈adaptivePoints h m leaves,
            (U i).eval x=0 ∧ (U i).eval y=0 ∧ x≠y ∧
            SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd (x-y).val) := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hmBounds.1
  have hprefix := public_modulus_prefix_below_input hN hB
  have hmprime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hprefix hnone hmprime.pos
    (by have hh := hmprime.two_le; nlinarith only [hh] : m≤m^2)
  have hsize : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  refine ⟨hc,?_⟩
  dsimp only
  intro leaves width coefficientSlots I U work hcore hwidth hcoefficients hcoverage hU hroots hcharged
  obtain hf|hfactor := adaptive_carrier_factory_acquisition_dichotomy hp hq hpq.ne
    hm hmprime hcop.symm g hlong leaves hcore width hwidth coefficientSlots hcoefficients
    hcoverage I U hU hroots hcharged
  · exact Or.inl ⟨hf.1,hf.2,adaptive_input_fourth_power_floor hsize hf.2⟩
  · exact Or.inr hfactor

end RiemannGaussian.SemiprimeSeedMovingCarrierObstruction
