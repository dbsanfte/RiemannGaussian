/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedShiftClosureObstruction
import RiemannGaussian.SemiprimeSeedFiniteTransfer

/-!
# Adaptive whole-family block acquisition still has a superlinear source

The original forced collisions already fit the shorter core of length
2*m^2+2. Allow each seed to choose unrelated block starts and widths,
overlaps and an unbalanced recursion frontier. Even perfect reuse of all
identical actual normalized points leaves at most two labels per point.
Coverage bounds the number of leaf labels in terms of the widest charged
factory source. The resulting source has an m^(3/2) lower bound without
assuming a common width or common seed partition. This is an obstruction
to explicit block-factory/point acquisition, not to compressed circuits,
specialized recurrence state or all implicit acquisition algorithms.
-/

namespace RiemannGaussian.SemiprimeAdaptiveSeedAcquisitionObstruction

open scoped BigOperators
open SemiprimeSeedPointRigidity SemiprimeSeedSumAcquisition
open SemiprimeSharedIntervalJet SemiprimeGlobalPhaseCancellation
open SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeSeedGeometricRecurrence SemiprimeSeedShiftClosureObstruction
open SemiprimeGeometricRows SemiprimeIntervalJet SemiprimeDensePeriodForcing
open SemiprimeWrapIndexRecovery
open SemiprimeSeedFiniteTransfer SemiprimeDenseRowCarries
open SemiprimeWideWrapCoverage

/-- Proof-side labels in the shorter original arithmetic collision core.
The first coordinate is the original nonzero seed residue minus one. -/
noncomputable def coreLabels (m : ℕ) : Finset (ℕ×ℕ) :=
  (Finset.range (m-1))×ˢ(Finset.range (2*m^2+2))

/-- The core retains every original seed and every possible forced index. -/
theorem coreLabels_card (m : ℕ) : (coreLabels m).card=(m-1)*(2*m^2+2) := by
  simp only [coreLabels,Finset.card_product,Finset.card_range]

/-- Arbitrary starts in the shorter core are covered by the frozen
whole-family phase rigidity theorem's one-cell domain. -/
theorem coreLabels_subset_pointDomain {m : ℕ} (hm : 4≤m) :
    coreLabels m⊆pointDomain m 1 := by
  intro u hu
  simp only [coreLabels,Finset.mem_product,Finset.mem_range] at hu
  simp only [pointDomain,blockCount,Nat.div_one,Finset.mem_product,Finset.mem_range]
  have hm2 : 1≤m^2 := by nlinarith only [hm]
  exact ⟨hu.1,by omega⟩

/-- Optimistic positions covered by one leaf at its charged maximum
width. Exact leaf lengths may be smaller and are handled below. This
finite set is proof-side coverage, not an executable enumeration oracle. -/
noncomputable def coveredPositions (leaves : Finset (ℕ×ℕ)) (W : ℕ) : Finset (ℕ×ℕ) :=
  (leaves×ˢFinset.range W).image fun u => (u.1.1,u.1.2+u.2)

/-- Any adaptive frontier covering every original core factor needs
at least coreSlots/W leaf labels. Disjointness, common starts and common
widths are not assumed; overlaps can only increase the optimistic count. -/
theorem adaptive_cover_count {m W : ℕ} (leaves : Finset (ℕ×ℕ))
    (hcover : coreLabels m⊆coveredPositions leaves W) :
    (m-1)*(2*m^2+2)≤leaves.card*W := by
  calc
    _ = (coreLabels m).card := (coreLabels_card m).symm
    _ ≤ (coveredPositions leaves W).card := Finset.card_le_card hcover
    _ ≤ (leaves×ˢFinset.range W).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product,Finset.card_range]

/-- Every actual per-seed, per-leaf extent bounded by W supplies the
optimistic coverage premise. Leaves may overlap, have unrelated widths
and occur at arbitrary positions of an unbalanced recursion tree. -/
theorem variable_leaf_coverage {m W : ℕ} (leaves : Finset (ℕ×ℕ))
    (width : (ℕ×ℕ)→ℕ) (hwidth : ∀ u∈leaves,width u≤W)
    (hcover : ∀ v∈coreLabels m,∃ u∈leaves,
      u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u) :
    coreLabels m⊆coveredPositions leaves W := by
  intro v hv
  obtain ⟨u,hu,hseed,hstart,hend⟩ := hcover v hv
  have hW := hwidth u hu
  apply Finset.mem_image.mpr
  refine ⟨(u,v.2-u.2),Finset.mem_product.mpr ⟨hu,Finset.mem_range.mpr (by omega)⟩,?_⟩
  refine Prod.ext hseed ?_
  dsimp only
  omega

/-- All distinct ACTUAL normalized leaf points. Removing exact repeats
is optimistic: source channels, block sizes and labels may still differ. -/
noncomputable def adaptivePoints {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (leaves : Finset (ℕ×ℕ)) : Finset (ZMod N) :=
  leaves.image fun u => seedPoint g m 1 (u.1+1) u.2

/-- Every actual point in ANY adaptive subset has at most two original
leaf labels, including reuse between different seeds and unequal blocks.
The arithmetic reason is the frozen public quadratic offset class. -/
theorem adaptive_fiber_card_le_two {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m) (x : ZMod (p*q)) :
    (leaves.filter fun u => seedPoint (projectedUnit g m) m 1 (u.1+1) u.2=x).card≤2 := by
  classical
  have hsubset : (leaves.filter fun u =>
      seedPoint (projectedUnit g m) m 1 (u.1+1) u.2=x)⊆
        pointFiber (projectedUnit g m) m 1 x := by
    intro u hu
    apply Finset.mem_filter.mpr
    exact ⟨coreLabels_subset_pointDomain hm (hcore (Finset.mem_filter.mp hu).1),
      (Finset.mem_filter.mp hu).2⟩
  exact (Finset.card_le_card hsubset).trans
    (pointFiber_card_le_two hp hq hpq hm hmprime hN (by omega) (by nlinarith only [hm]) g hlong x)

/-- Perfect exact-value reuse among ALL adaptive normalized leaf points
removes at most a factor of two from the full original leaf count. -/
theorem adaptive_distinct_point_count {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m) :
    leaves.card≤2*(adaptivePoints (projectedUnit g m) m leaves).card := by
  classical
  calc
    leaves.card=∑ x∈adaptivePoints (projectedUnit g m) m leaves,
        (leaves.filter fun u => seedPoint (projectedUnit g m) m 1 (u.1+1) u.2=x).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _x∈adaptivePoints (projectedUnit g m) m leaves,2 :=
      Finset.sum_le_sum fun x _ => adaptive_fiber_card_le_two
        hp hq hpq hm hmprime hN g hlong leaves hcore x
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul,mul_comm]

/-- Every adaptive explicit source retains the m^(3/2) floor even with
perfect value deduplication and only the shorter forced-collision core.
W is the charged factory capacity bounding every actual leaf width. -/
theorem adaptive_source_floor {p q m W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (hcover : coreLabels m⊆coveredPositions leaves W) :
    2*m^3<(W+(adaptivePoints (projectedUnit g m) m leaves).card)^2 := by
  have hc := adaptive_cover_count leaves hcover
  have hd := adaptive_distinct_point_count hp hq hpq hm hmprime hN g hlong leaves hcore
  let Q := (adaptivePoints (projectedUnit g m) m leaves).card
  have hpairs : (m-1)*(2*m^2+2)≤2*Q*W :=
    hc.trans (Nat.mul_le_mul_right W hd)
  have hM : m≤2*(m-1) := by omega
  have hR := Nat.mul_le_mul_right (2*m^2) hM
  have hstrict : 2*m^3<2*(m-1)*(2*m^2+2) := by
    nlinarith only [hR,show 0<m-1 by omega]
  have hproduct : 2*m^3<4*W*Q := by nlinarith only [hpairs,hstrict]
  have hsquare : 4*W*Q≤(W+Q)^2 := by
    have hZ : 4*(W : ℤ)*(Q : ℤ)≤((W : ℤ)+(Q : ℤ))^2 := by
      nlinarith only [sq_nonneg ((W : ℤ)-(Q : ℤ))]
    exact_mod_cast hZ
  exact hproduct.trans_le hsquare

/-- Unequal seed-specific leaf widths and arbitrary partitions inherit
the same whole-family floor. No supplied common width or aligned block
grid appears; the actual width capacity is the charged source parameter. -/
theorem adaptive_frontier_work_floor {p q m W work : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (width : (ℕ×ℕ)→ℕ) (hwidth : ∀ u∈leaves,width u≤W)
    (hcover : ∀ v∈coreLabels m,∃ u∈leaves,
      u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u)
    (hcharged : W+(adaptivePoints (projectedUnit g m) m leaves).card≤work) :
    2*m^3<work^2 := by
  exact (adaptive_source_floor hp hq hpq hm hmprime hN g hlong leaves hcore
    (variable_leaf_coverage leaves width hwidth hcover)).trans_le
      (Nat.pow_le_pow_left hcharged 2)

/-- Every original padded-range base-power gap is a unit on the long
branch. The actual rough local orders exceed the FULL padded length,
so unequal leaf factories do not gain zero coefficients at larger widths. -/
theorem original_padded_power_gaps_unit {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∀ i : ℕ, 0 < i → i ≤ seedLength m →
      IsUnit ((((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^i)-1) := by
  have hporder : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))=
        orderOf (leftUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      ((projectedUnit g m)^(m^2)) : (ZMod p)ˣ) : ZMod p)=_
    rw [orderOf_units,map_pow]
    exact ((rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1).pow_right 2).orderOf_pow
  have hqorder : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))=
        orderOf (rightUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom)
      ((projectedUnit g m)^(m^2)) : (ZMod q)ˣ) : ZMod q)=_
    rw [orderOf_units,map_pow]
    exact ((rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.2).pow_right 2).orderOf_pow
  have hlength := (seedLength_bounds hm).2
  intro i hi hiL
  apply isUnit_of_prime_reductions hp hq
  · rw [map_sub,map_pow,map_one]
    apply sub_ne_zero.mpr
    intro hpower
    have hfirst : i<orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) := by
      rw [hporder]
      nlinarith only [hiL,hlength,hlong.2.2.2.1.1]
    have he := pow_injOn_Iio_orderOf hfirst
      (show 0<orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) by omega)
      (by simpa only [pow_zero] using hpower)
    omega
  · rw [map_sub,map_pow,map_one]
    apply sub_ne_zero.mpr
    intro hpower
    have hfirst : i<orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) := by
      rw [hqorder]
      nlinarith only [hiL,hlength,hlong.2.2.2.1.2]
    have he := pow_injOn_Iio_orderOf hfirst
      (show 0<orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) by omega)
      (by simpa only [pow_zero] using hpower)
    omega

/-- Every coefficient of EVERY actual leaf-width geometric factory is
a unit, up to the entire original padded interval. Thus allowing sparse
coefficient sources cannot evade the factory width charge by cancellation. -/
theorem original_leaf_coefficients_unit {p q m w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (hw : w≤seedLength m) :
    ∀ k≤w, IsUnit ((rowPolynomial
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) w).coeff k) := by
  exact geometric_coefficients_unit (seedBase (projectedUnit g m) m) w
    (fun i hi hiw => original_padded_power_gaps_unit hp hq hm g hlong i hi (hiw.trans hw))

/-- An explicit source covering all nonzero coefficients of even one
actual adaptive leaf factory has at least width+1 slots. Original unit
coefficients make the statement apply to sparse as well as dense sources. -/
theorem original_leaf_coefficient_source_floor {p q m w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (hw : w≤seedLength m)
    (slots : Finset ℕ)
    (hcover : ∀ k, (rowPolynomial
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) w).coeff k≠0→k∈slots) :
    w+1≤slots.card := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  have hsubset : Finset.range (w+1)⊆slots := by
    intro k hk
    exact hcover k ((original_leaf_coefficients_unit hp hq hm g hlong hw k
      (by have hh := Finset.mem_range.mp hk; omega)).ne_zero)
  simpa only [Finset.card_range] using Finset.card_le_card hsubset

/-- Even granting perfect coefficient-index reuse between all unequal
leaf factories, actual original unit coefficients force each leaf's
width below the charged factory source size. Combined with perfect point
deduplication, every adaptive whole-family source is still superlinear. -/
theorem adaptive_factory_point_source_floor {p q m work : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (width : (ℕ×ℕ)→ℕ) (hwidth : ∀ u∈leaves,width u≤seedLength m)
    (coefficientSlots : Finset ℕ)
    (hcoefficients : ∀ u∈leaves,∀ k,(rowPolynomial
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) (width u)).coeff k≠0→
        k∈coefficientSlots)
    (hcover : ∀ v∈coreLabels m,∃ u∈leaves,
      u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u)
    (hcharged : coefficientSlots.card+
      (adaptivePoints (projectedUnit g m) m leaves).card≤work) :
    2*m^3<(coefficientSlots.card+
      (adaptivePoints (projectedUnit g m) m leaves).card)^2 ∧ 2*m^3<work^2 := by
  have hcapacity : ∀ u∈leaves,width u≤coefficientSlots.card := by
    intro u hu
    have hc := original_leaf_coefficient_source_floor hp hq hm g hlong (hwidth u hu)
      coefficientSlots (hcoefficients u hu)
    omega
  have hfloor := adaptive_source_floor hp hq hpq hm hmprime hN g hlong leaves hcore
    (variable_leaf_coverage leaves width hcapacity hcover)
  exact ⟨hfloor,hfloor.trans_le (Nat.pow_le_pow_left hcharged 2)⟩

/-- Exact numerical exclusion of a linear source budget. Any source
with the proved floor needs work/m greater than sqrt(2m); this statement
uses only integer comparisons, with no asymptotic or root approximation. -/
theorem adaptive_no_small_linear_budget {m work A : ℕ}
    (hfloor : 2*m^3<work^2) (hA : A^2≤2*m) : ¬work≤A*m := by
  intro hbound
  have hsq := Nat.mul_self_le_mul_self hbound
  have hmul := Nat.mul_le_mul_right (m^2) hA
  nlinarith only [hfloor,hsq,hmul]

/-- At the original sixth-root parameter scale, the explicit adaptive
source's fourth power exceeds four times the semiprime. This is a route
source lower bound, never a general factoring or memory lower bound. -/
theorem adaptive_input_fourth_power_floor {N m work : ℕ}
    (hsize : N≤m^6) (hfloor : 2*m^3<work^2) : 4*N<work^4 := by
  have hsq := Nat.mul_self_lt_mul_self hfloor
  have hN := Nat.mul_le_mul_left 4 hsize
  nlinarith only [hsq,hN]

/-- The shorter core really contains the ORIGINAL arithmetic collision
for every unit and every surviving factor ratio. This preserves the
frozen forcing theorem while removing unneeded padding from the floor. -/
theorem original_forced_collision_in_core {p q m : ℕ}
    (hp : p.Prime) (hpq : p≤q) (hm : 4≤m)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) :
    ∃ r : ℕ, (p%m-1,r)∈coreLabels m ∧
      ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((progressionSeed g (p*q) m (p%m)).step : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q)))^r := by
  obtain ⟨r,hrbound,_,_,hhit⟩ := forced_seed_prime_hit hp hpq hm hprefix hN hsize g
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hjpos : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    omega
  have hjlt := Nat.mod_lt p (show 0<m by omega)
  refine ⟨r,?_,hhit⟩
  simp only [coreLabels,Finset.mem_product,Finset.mem_range]
  exact ⟨by omega,by omega⟩

/-- The complete adaptive factory/point obstruction applies to the
ACTUAL N-only public long route after its original prefix. It covers
arbitrary unequal frontiers and optimistic sparse coefficient/point
reuse, and translates the count floor to the semiprime input itself. -/
theorem actual_public_route_adaptive_source_obstruction {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∀ (leaves : Finset (ℕ×ℕ)) (width : (ℕ×ℕ)→ℕ) (coefficientSlots : Finset ℕ)
        (work : ℕ), leaves⊆coreLabels m→
        (∀ u∈leaves,width u≤seedLength m)→
        (∀ u∈leaves,∀ k,(rowPolynomial
          ((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q)) (width u)).coeff k≠0→
            k∈coefficientSlots)→
        (∀ v∈coreLabels m,∃ u∈leaves,
          u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u)→
        coefficientSlots.card+(adaptivePoints h m leaves).card≤work→
        2*m^3<(coefficientSlots.card+(adaptivePoints h m leaves).card)^2 ∧
          2*m^3<work^2 ∧ 4*(p*q)<work^4 := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hmBounds.1
  have hcover := public_modulus_prefix_below_input hN hB
  have hmprime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hmprime.pos
    (by have hh := hmprime.two_le; nlinarith only [hh] : m≤m^2)
  have hsize : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  refine ⟨hc,?_⟩
  dsimp only
  intro leaves width coefficientSlots work hcore hwidth hcoefficients hcoverage hcharged
  have hf := adaptive_factory_point_source_floor hp hq hpq.ne hm hmprime hcop.symm
    g hlong leaves hcore width hwidth coefficientSlots hcoefficients hcoverage hcharged
  exact ⟨hf.1,hf.2,adaptive_input_fourth_power_floor hsize hf.2⟩

/-- Implicit generation of geometric points does not evade the floor
if the backend still emits individual labelled leaf evaluations. Any
physical output list covering all leaf labels has at least the distinct
normalized-point count many slots, even when equal values share words. -/
theorem adaptive_explicit_leaf_output_work_floor {p q m work : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (leaves : Finset (ℕ×ℕ)) (hcore : leaves⊆coreLabels m)
    (width : (ℕ×ℕ)→ℕ) (hwidth : ∀ u∈leaves,width u≤seedLength m)
    (coefficientSlots : Finset ℕ)
    (hcoefficients : ∀ u∈leaves,∀ k,(rowPolynomial
      ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) (width u)).coeff k≠0→
        k∈coefficientSlots)
    (hcover : ∀ v∈coreLabels m,∃ u∈leaves,
      u.1=v.1 ∧ u.2≤v.2 ∧ v.2<u.2+width u)
    (outputs : List (ℕ×ℕ)) (houtputs : ∀ u∈leaves,u∈outputs)
    (hcharged : coefficientSlots.card+outputs.length≤work) :
    2*m^3<work^2 := by
  classical
  have hsubset : leaves⊆outputs.toFinset := by
    intro u hu
    exact List.mem_toFinset.mpr (houtputs u hu)
  have hpoints : (adaptivePoints (projectedUnit g m) m leaves).card≤outputs.length :=
    (Finset.card_image_le).trans
      ((Finset.card_le_card hsubset).trans (List.toFinset_card_le (l:=outputs)))
  exact (adaptive_factory_point_source_floor hp hq hpq hm hmprime hN g hlong
    leaves hcore width hwidth coefficientSlots hcoefficients hcover
    ((Nat.add_le_add_left hpoints _).trans hcharged)).2

end RiemannGaussian.SemiprimeAdaptiveSeedAcquisitionObstruction
