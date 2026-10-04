/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedHermiteQuotient
import RiemannGaussian.SemiprimeSeedGeometricRecurrence

/-!
# Enlarging a fixed seed quotient cannot repair near-linear acquisition

A faithful fixed-remainder scale operator requires divisibility by the
scaled modulus. Enlarging the original Hermite modulus to obtain that
closure forces a complete multiplicative root orbit. On the original
long branch, dyadic shifts preserve the large rough orders: even an
enlargement with nonunit constant term has quadratic degree, and a unit
constant term forces quartic degree. These are obstructions to this
fixed-quotient acquisition route, not to all implicit acquisition methods
or to factoring in general. Moving moduli and specialized extra state
are separate possibilities; no backend implementation is added here.
-/

namespace RiemannGaussian.SemiprimeSeedShiftClosureObstruction

open Polynomial
open SemiprimeSeedHermiteQuotient SemiprimeSeedSumAcquisition
open SemiprimeGlobalPhaseCancellation SemiprimeLocalOrderRouting
open SemiprimeWrapIndexRecovery
open SemiprimeGroupSelection SemiprimeCentreFreeCover
open SemiprimeSeedGeometricRecurrence

/-- Any function implementing scale substitution from a fixed monic
remainder for every polynomial requires actual quotient closure. The
function may be nonlinear; the indistinguishable inputs are U and zero. -/
theorem fixed_remainder_operator_requires_closure {R : Type*} [CommRing R]
    {U : R[X]} (hU : U.Monic) (c : R)
    (hoperator : ∃ T : R[X]→R[X], ∀ P : R[X],
      T (P %ₘ U)=(P.comp (C c*X)) %ₘ U) :
    U∣U.comp (C c*X) := by
  obtain ⟨T,hT⟩ := hoperator
  have hs := hT U
  have hz := hT 0
  rw [modByMonic_self hU] at hs
  simp only [zero_modByMonic,zero_comp] at hz
  exact (modByMonic_eq_zero_iff_dvd hU).mp (hs.symm.trans hz)

/-- Actual quotient closure propagates any retained root along every
power of the original scale. This is arithmetic information lost by a
small nonclosed remainder, rather than a Fourier cost obligation. -/
theorem closure_forces_root_orbit {R : Type*} [CommRing R]
    {U : R[X]} {c x : R} (hroot : U.eval x=0)
    (hclosed : U∣U.comp (C c*X)) :
    ∀ k : ℕ, U.eval (c^k*x)=0 := by
  obtain ⟨Q,hQ⟩ := hclosed
  intro k
  induction k with
  | zero => simpa only [pow_zero,one_mul] using hroot
  | succ k ih =>
    have he := congrArg (fun P : R[X] => P.eval (c^k*x)) hQ
    simp only [eval_comp,eval_mul,eval_C,eval_X,ih,zero_mul] at he
    simpa only [pow_succ,mul_assoc,mul_comm c] using he

/-- In a domain, a closed polynomial retaining one unit root has at
least the scale order many coefficients in its degree. No constant-term
unit assumption or simple-root hypothesis is needed. -/
theorem closed_unit_root_degree {R : Type*} [CommRing R] [IsDomain R]
    {U : R[X]} (hU : U≠0) (c x : Rˣ)
    (hroot : U.eval (x : R)=0)
    (hclosed : U∣U.comp (C (c : R)*X)) :
    orderOf c≤U.natDegree := by
  classical
  let orbit := (Finset.range (orderOf c)).image fun k => ((c^k*x : Rˣ) : R)
  have hinj : Set.InjOn (fun k => ((c^k*x : Rˣ) : R)) (Finset.range (orderOf c)) := by
    intro i hi j hj he
    have hu : c^i*x=c^j*x := Units.ext he
    have hp : c^i=c^j := mul_right_cancel hu
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hp
  have hcard : orbit.card=orderOf c := by
    rw [Finset.card_image_of_injOn hinj,Finset.card_range]
  have hsubset : orbit.val⊆U.roots := by
    intro y hy
    change y∈orbit at hy
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hy
    apply (Polynomial.mem_roots hU).mpr
    change U.eval ((c^k*x : Rˣ) : R)=0
    simpa only [Units.val_mul,Units.val_pow_eq_pow_val] using
      closure_forces_root_orbit hroot hclosed k
  rw [←hcard]
  exact Polynomial.card_le_degree_of_subset_roots hsubset

/-- Every original dyadic scale preserves the ENTIRE global order on
the long branch. Roughness makes both local orders coprime to m^2*2^t;
their coprime product is the original global order. -/
theorem long_dyadic_scale_order {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ) :
    orderOf ((seedBase (projectedUnit g m) m)^(2^t))=
      orderOf (projectedUnit g m) := by
  have hpm := rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1
  have hqm := rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.2
  have hp2 := rough_coprime_small (by omega : 0<2) (by omega : 2≤m) hlong.2.2.2.2.2.1
  have hq2 := rough_coprime_small (by omega : 0<2) (by omega : 2≤m) hlong.2.2.2.2.2.2
  have hcop : (orderOf (projectedUnit g m)).Coprime (m^2*2^t) := by
    rw [global_order_eq_lcm hp hq hpq,(hlong.2.2.2.2.1).lcm_eq_mul]
    exact ((hpm.pow_right 2).mul_right (hp2.pow_right t)).mul_left
      ((hqm.pow_right 2).mul_right (hq2.pow_right t))
  simpa only [seedBase,←pow_mul] using hcop.orderOf_pow

/-- Every dyadic scale also preserves the original long p-field order.
This will obstruct enlarged carriers even with nonunit constant terms. -/
theorem long_dyadic_left_scale_order {p q m : ℕ} (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ) :
    orderOf (leftUnit ((seedBase (projectedUnit g m) m)^(2^t)))=
      orderOf (leftUnit (projectedUnit g m)) := by
  have hpm := rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1
  have hp2 := rough_coprime_small (by omega : 0<2) (by omega : 2≤m) hlong.2.2.2.2.2.1
  have hcop := (hpm.pow_right 2).mul_right (hp2.pow_right t)
  simpa only [leftUnit,seedBase,map_pow,←pow_mul] using hcop.orderOf_pow

/-- Any nonconstant enlarged monic fixed carrier with unit constant
term and an ORIGINAL dyadic shift has degree greater than 16*m^4.
Adding more nonzero target roots cannot repair a linear-size carrier. -/
theorem long_closed_unit_constant_degree {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    {U : (ZMod (p*q))[X]} (hU : U.Monic) (hconstant : IsUnit (U.coeff 0))
    (hpositive : 0<U.natDegree)
    (hclosed : U∣U.comp (C (((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))*X)) :
    16*m^4<U.natDegree := by
  have hpowers := shift_dvd_forces_power hU hconstant _ hclosed
  have hunitpower : ((seedBase (projectedUnit g m) m)^(2^t))^U.natDegree=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using hpowers
  have hle := orderOf_le_of_pow_eq_one hpositive hunitpower
  rw [long_dyadic_scale_order hp hq hpq hm g hlong t] at hle
  exact (long_global_order_bound hp hq hpq g hlong).trans_le hle

/-- Even permitting a nonunit constant term, any enlarged monic
carrier retaining ONE original unit root and closed under an original
dyadic scale must have degree greater than 4*m^2. Its p-field image
contains the complete rough local orbit. -/
theorem long_closed_unit_root_degree {p q m : ℕ}
    (hp : p.Prime) (hm : 4≤m) (g : (ZMod (p*q))ˣ)
    (hlong : LongData g m) (t : ℕ)
    {U : (ZMod (p*q))[X]} (hU : U.Monic) (x : (ZMod (p*q))ˣ)
    (hroot : U.eval (x : ZMod (p*q))=0)
    (hclosed : U∣U.comp (C (((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))*X)) :
    4*m^2<U.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  have hmaproot : (U.map f).eval (leftUnit x : ZMod p)=0 := by
    change (U.map f).eval (f (x : ZMod (p*q)))=0
    rw [eval_map_apply,hroot,map_zero]
  have hmapclosed : U.map f∣(U.map f).comp
      (C (leftUnit ((seedBase (projectedUnit g m) m)^(2^t)) : ZMod p)*X) := by
    dsimp only [leftUnit]
    rw [Units.coe_map]
    simp only [RingHom.toMonoidHom_eq_coe,MonoidHom.coe_coe]
    change U.map f∣(U.map f).comp
      (C (f (((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)
    simpa only [map_comp,Polynomial.map_mul,map_C,map_X] using Polynomial.map_dvd f hclosed
  have hle := closed_unit_root_degree (Polynomial.map_monic_ne_zero hU)
    (leftUnit ((seedBase (projectedUnit g m) m)^(2^t))) (leftUnit x) hmaproot hmapclosed
  rw [long_dyadic_left_scale_order hm g hlong t] at hle
  have hlarge : 4*m^2<orderOf (leftUnit (projectedUnit g m)) := by
    nlinarith only [hlong.2.2.2.1.1]
  exact hlarge.trans_le (hle.trans natDegree_map_le)

/-- Whole-family faithful fixed-remainder acquisition has no linear-
degree repair by modulus enlargement. Retaining all original targets
already retains a unit root; permitting extra zero roots does not help.
Unit constant term strengthens the quadratic floor to a quartic floor. -/
theorem original_family_enlarged_carrier_obstruction {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    {U : (ZMod (p*q))[X]} (hU : U.Monic)
    (htargets : ∀ x∈seedTargets (projectedUnit g m) m,U.eval x=0)
    (hoperator : ∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P,
      T (P %ₘ U)=(P.comp
        (C (((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))*X)) %ₘ U) :
    4*m^2<U.natDegree ∧ (IsUnit (U.coeff 0)→16*m^4<U.natDegree) := by
  have hclosed := fixed_remainder_operator_requires_closure hU _ hoperator
  have hlen : 0<(seedTargets (projectedUnit g m) m).length := by
    rw [seedTargets_length]
    omega
  have hmem := List.getElem_mem hlen
  obtain ⟨x,hx⟩ := seedTargets_units (projectedUnit g m) m _ hmem
  have hroot : U.eval (x : ZMod (p*q))=0 := by rw [hx]; exact htargets _ hmem
  have hdegree := long_closed_unit_root_degree hp hm g hlong t hU x hroot hclosed
  exact ⟨hdegree,fun hconstant =>
    long_closed_unit_constant_degree hp hq hpq hm g hlong t hU hconstant (by omega) hclosed⟩

/-- A shift-closed repair leaves the ACTUAL original geometric half
unchanged as its canonical remainder. Its m^2+2 nonzero coefficients
survive even if the enlarged modulus itself has a sparse encoding.
Thus coefficient cancellation cannot make this remainder route linear. -/
theorem original_family_closed_half_remains_dense {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    {U : (ZMod (p*q))[X]} (hU : U.Monic)
    (htargets : ∀ x∈seedTargets (projectedUnit g m) m,U.eval x=0)
    (hoperator : ∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P,
      T (P %ₘ U)=(P.comp
        (C (((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))*X)) %ₘ U) :
    (seedHalfPolynomial (projectedUnit g m) m) %ₘ U=
        seedHalfPolynomial (projectedUnit g m) m ∧
      m^2+2≤((seedHalfPolynomial (projectedUnit g m) m) %ₘ U).support.card := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  have hdegree := (original_family_enlarged_carrier_obstruction hp hq hpq hm g hlong t
    hU htargets hoperator).1
  have hhalf := (seedHalfLength_bounds hm).2.1
  have hneq : seedHalfPolynomial (projectedUnit g m) m≠0 := by
    intro hz
    have hc := long_seedHalf_coeff_ne_zero hp hq hm g hlong (Nat.zero_le (seedHalfLength m))
    apply hc
    rw [hz,coeff_zero]
  have hrem : (seedHalfPolynomial (projectedUnit g m) m) %ₘ U=
      seedHalfPolynomial (projectedUnit g m) m := by
    apply (modByMonic_eq_self_iff hU).mpr
    rw [degree_eq_natDegree hU.ne_zero]
    apply (natDegree_lt_iff_degree_lt hneq).mp
    rw [seedHalfPolynomial_natDegree]
    omega
  exact ⟨hrem,by rw [hrem]; exact (long_seedHalf_dense_support hp hq hm g hlong).1⟩

/-- The obstruction applies to the ACTUAL N-only public long outcome
and its ORIGINAL seed family. No supplied private order, alternative
target family or factor-dependent carrier is needed in this statement. -/
theorem actual_public_route_shift_closed_carrier_obstruction {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let g := ZMod.unitOfCoprime a hc
      let h := projectedUnit g m
      ∀ (t : ℕ) (U : (ZMod (p*q))[X]), U.Monic→
        (∀ x∈seedTargets h m,U.eval x=0)→
        (∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P,
          T (P %ₘ U)=(P.comp
            (C (((seedBase h m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))*X)) %ₘ U)→
        4*m^2<U.natDegree ∧
          (IsUnit (U.coeff 0)→16*m^4<U.natDegree) ∧
          (seedHalfPolynomial h m) %ₘ U=seedHalfPolynomial h m ∧
          m^2+2≤((seedHalfPolynomial h m) %ₘ U).support.card := by
  have hdata := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  have hm : 4≤m := hB.trans
    (SemiprimeEuclidRowBudget.publicRowModulus_bounds (Nat.mul_pos hp.pos hq.pos)).1
  refine ⟨hc,?_⟩
  dsimp only
  intro t U hU htargets hoperator
  have hdegree := original_family_enlarged_carrier_obstruction hp hq hpq.ne hm
    (ZMod.unitOfCoprime a hc) hlong t hU htargets hoperator
  have hdense := original_family_closed_half_remains_dense hp hq hpq.ne hm
    (ZMod.unitOfCoprime a hc) hlong t hU htargets hoperator
  exact ⟨hdegree.1,hdegree.2,hdense.1,hdense.2⟩

/-- Every explicit coefficient source for the repaired whole-family
half remainder has at least m^2+2 slots, even if it omits all zero
coefficients. A clock charging at least one primitive per emitted slot
inherits this quadratic lower bound. The premise defines that explicit
source route; compressed circuits and specialized recurrence states are
not asserted to satisfy it. -/
theorem original_family_closed_remainder_source_floor {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    {U : (ZMod (p*q))[X]} (hU : U.Monic)
    (htargets : ∀ x∈seedTargets (projectedUnit g m) m,U.eval x=0)
    (hoperator : ∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P,
      T (P %ₘ U)=(P.comp
        (C (((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))*X)) %ₘ U)
    (slots : Finset ℕ)
    (hcover : ∀ k, ((seedHalfPolynomial (projectedUnit g m) m) %ₘ U).coeff k≠0→k∈slots)
    (work : ℕ) (hcharged : slots.card≤work) :
    m^2+2≤slots.card ∧ m^2+2≤work := by
  have hdense := (original_family_closed_half_remains_dense hp hq hpq hm g hlong t
    hU htargets hoperator).2
  have hsubset : ((seedHalfPolynomial (projectedUnit g m) m) %ₘ U).support⊆slots := by
    intro k hk
    exact hcover k (mem_support_iff.mp hk)
  have hslots := hdense.trans (Finset.card_le_card hsubset)
  exact ⟨hslots,hslots.trans hcharged⟩

end RiemannGaussian.SemiprimeSeedShiftClosureObstruction
