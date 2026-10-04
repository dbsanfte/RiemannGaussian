/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedMomentCancellationObstruction
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Finite-prefix certification of the original whole-family moment series

The original geometric block sum satisfies a difference equation with an
original seed series of degree at most m-1. A candidate rational series
of degree d can be certified using 2d+2(m-1)+1 genuine coefficients,
provided the original scale has no short resonances. The proof works over
the composite ring; it never assumes that ring is a field.

This is a whole-family VALIDATION theorem. It does not assert existence
of a linear-degree candidate, an algorithm to find one, a bound for
acquiring the genuine prefix, or a full bit-time or memory bound.
All polynomial presentations and infinite series here are proof-side.
-/

namespace RiemannGaussian.SemiprimeSeedMomentPrefixRigidity

open scoped BigOperators
open Polynomial
open SemiprimeSeedMomentCancellationObstruction SemiprimeSeedPointRigidity
open SemiprimeDenseRowCarries SemiprimeSeedSumAcquisition
open SemiprimeCentreFreeCover SemiprimeLocalOrderRouting
open SemiprimeWrapIndexRecovery SemiprimeIntervalJet

/-- A proof-side rational presentation with denominator constant one.
Neither the presentation nor its degree is executable input advice. -/
abbrev RationalBound {R : Type*} [CommRing R] (F : PowerSeries R) (d : ℕ) : Prop :=
  ∃ U V : R[X], U.coeff 0=1 ∧ U.natDegree≤d ∧ V.natDegree≤d ∧
    (U : PowerSeries R)*F=(V : PowerSeries R)

/-- A zero prefix remains zero after multiplication by ANY series. -/
theorem zero_prefix_mul {R : Type*} [CommRing R] {H : PowerSeries R} {K : ℕ}
    (hH : ∀ r≤K, PowerSeries.coeff r H=0) (P : PowerSeries R) :
    ∀ r≤K, PowerSeries.coeff r (P*H)=0 := by
  intro r hr
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [hH ij.2 (by omega),mul_zero]

/-- Degree plus a genuine zero prefix annihilates a rational series.
Cancellation uses a unit constant, not a domain assumption. -/
theorem rational_zero_of_prefix {R : Type*} [CommRing R] {H : PowerSeries R} {K : ℕ}
    (hH : RationalBound H K) (hzero : ∀ r≤K, PowerSeries.coeff r H=0) : H=0 := by
  obtain ⟨U,V,hU,_,hV,hUV⟩ := hH
  have hVzero : V=0 := by
    ext r
    by_cases hr : r≤K
    · have he := zero_prefix_mul hzero (U : PowerSeries R) r hr
      rw [hUV,Polynomial.coeff_coe] at he
      exact he
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hunit : IsUnit (U : PowerSeries R) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,Polynomial.coeff_coe,hU]
    exact isUnit_one
  apply hunit.mul_left_cancel
  simpa only [hVzero,Polynomial.coe_zero,mul_zero] using hUV

/-- Addition of rational presentations charges the SUM of their degrees. -/
theorem rational_add {R : Type*} [CommRing R] {F G : PowerSeries R} {a b : ℕ}
    (hF : RationalBound F a) (hG : RationalBound G b) : RationalBound (F+G) (a+b) := by
  obtain ⟨U,V,hU,hUd,hVd,hUV⟩ := hF
  obtain ⟨S,T,hS,hSd,hTd,hST⟩ := hG
  refine ⟨U*S,V*S+T*U,?_,?_,?_,?_⟩
  · simp [hU,hS]
  · exact natDegree_mul_le.trans (Nat.add_le_add hUd hSd)
  · apply natDegree_add_le_of_degree_le
    · exact natDegree_mul_le.trans (Nat.add_le_add hVd hSd)
    · exact natDegree_mul_le.trans (by omega)
  · simp only [Polynomial.coe_mul,Polynomial.coe_add]
    calc
      (U : PowerSeries R)*S*(F+G)=((U : PowerSeries R)*F)*S+
          ((S : PowerSeries R)*G)*U := by ring
      _=(V : PowerSeries R)*S+(T : PowerSeries R)*U := by rw [hUV,hST]

/-- Subtraction has the same composite-ring-safe degree bound. -/
theorem rational_sub {R : Type*} [CommRing R] {F G : PowerSeries R} {a b : ℕ}
    (hF : RationalBound F a) (hG : RationalBound G b) : RationalBound (F-G) (a+b) := by
  obtain ⟨U,V,hU,hUd,hVd,hUV⟩ := hF
  obtain ⟨S,T,hS,hSd,hTd,hST⟩ := hG
  refine ⟨U*S,V*S-T*U,?_,?_,?_,?_⟩
  · simp [hU,hS]
  · exact natDegree_mul_le.trans (Nat.add_le_add hUd hSd)
  · exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le.trans (Nat.add_le_add hVd hSd))
      (natDegree_mul_le.trans (by omega)))
  · simp only [Polynomial.coe_mul,Polynomial.coe_sub]
    calc
      (U : PowerSeries R)*S*(F-G)=((U : PowerSeries R)*F)*S-
          ((S : PowerSeries R)*G)*U := by ring
      _=(V : PowerSeries R)*S-(T : PowerSeries R)*U := by rw [hUV,hST]

/-- Polynomial scaling and series rescaling agree coefficient by coefficient. -/
theorem polynomial_rescale {R : Type*} [CommRing R] (U : R[X]) (c : R) :
    ((U.comp (C c*X) : R[X]) : PowerSeries R)=PowerSeries.rescale c (U : PowerSeries R) := by
  ext r
  rw [Polynomial.coeff_coe,comp_C_mul_X_coeff,PowerSeries.coeff_rescale,
    Polynomial.coeff_coe,mul_comm]

/-- Rescaling preserves a rational degree bound and denominator constant one. -/
theorem rational_rescale {R : Type*} [CommRing R] {F : PowerSeries R} {d : ℕ}
    (hF : RationalBound F d) (c : R) : RationalBound (PowerSeries.rescale c F) d := by
  obtain ⟨U,V,hU,hUd,hVd,hUV⟩ := hF
  have hlinear : (C c*X : R[X]).natDegree≤1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le c 1
  refine ⟨U.comp (C c*X),V.comp (C c*X),?_,?_,?_,?_⟩
  · simp only [comp_C_mul_X_coeff,pow_zero,mul_one,hU]
  · exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlinear).trans (by simpa using hUd))
  · exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlinear).trans (by simpa using hVd))
  · rw [polynomial_rescale,polynomial_rescale,←map_mul,hUV]

/-- A rational series with zero constant and no short scale resonances
cannot hide as a nonzero invariant remainder. -/
theorem rational_invariant_zero {R : Type*} [CommRing R] {H : PowerSeries R} {c : R} {d : ℕ}
    (hH : RationalBound H d) (h0 : PowerSeries.coeff 0 H=0)
    (hinv : PowerSeries.rescale c H=H)
    (hgaps : ∀ r, 0<r → r≤d → IsUnit (c^r-1)) : H=0 := by
  apply rational_zero_of_prefix hH
  intro r hr
  by_cases hzero : r=0
  · simpa only [hzero] using h0
  · have he := congrArg (PowerSeries.coeff r) hinv
    rw [PowerSeries.coeff_rescale] at he
    apply (hgaps r (by omega) hr).mul_left_cancel
    rw [mul_zero]
    calc
      (c^r-1)*PowerSeries.coeff r H=c^r*PowerSeries.coeff r H-PowerSeries.coeff r H := by ring
      _=0 := sub_eq_zero.mpr he

/-- A low-degree candidate matching a short genuine prefix agrees with
the ENTIRE structured family. No hidden-field computation is a premise. -/
theorem structured_prefix_rigidity {R : Type*} [CommRing R]
    {A B F : PowerSeries R} {c : R} {J M Q d : ℕ}
    (hA : RationalBound A M) (hB : RationalBound B Q) (hF : RationalBound F d)
    (heq : PowerSeries.rescale c B-B=PowerSeries.rescale (c^J) A-A)
    (hprefix : ∀ r≤2*(d+M), PowerSeries.coeff r F=PowerSeries.coeff r B)
    (hgaps : ∀ r, 0<r → r≤d+Q → IsUnit (c^r-1)) : F=B := by
  have hdiff : RationalBound (F-B) (d+Q) := rational_sub hF hB
  have hresidual : RationalBound
      ((PowerSeries.rescale c F-F)-(PowerSeries.rescale (c^J) A-A)) (2*(d+M)) := by
    have hh := rational_sub (rational_sub (rational_rescale hF c) hF)
      (rational_sub (rational_rescale hA (c^J)) hA)
    convert hh using 1
    omega
  have hreszero : (PowerSeries.rescale c F-F)-(PowerSeries.rescale (c^J) A-A)=0 := by
    apply rational_zero_of_prefix hresidual
    intro r hr
    rw [←heq,map_sub,map_sub,map_sub,PowerSeries.coeff_rescale,
      PowerSeries.coeff_rescale,hprefix r hr]
    ring
  have hinv : PowerSeries.rescale c (F-B)=F-B := by
    rw [map_sub]
    rw [←heq] at hreszero
    linear_combination hreszero
  have h0 : PowerSeries.coeff 0 (F-B)=0 := by
    rw [map_sub,hprefix 0 (Nat.zero_le _),sub_self]
  exact sub_eq_zero.mp (rational_invariant_zero hdiff h0 hinv hgaps)

/-- One centered geometric moment series has a linear presentation. -/
theorem single_moments_rational {R : Type*} [CommRing R] (x : R) :
    RationalBound (PowerSeries.mk fun r => if r=0 then 0 else x^r) 1 := by
  have hx : (C x*X : R[X]).natDegree≤1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le x 1
  have hs : (PowerSeries.mk fun r => if r=0 then 0 else x^r)=
      PowerSeries.rescale x (PowerSeries.mk (1 : ℕ→R))-1 := by
    ext r
    by_cases hr : r=0
    · subst r
      rw [PowerSeries.coeff_mk,map_sub,PowerSeries.coeff_rescale,PowerSeries.coeff_mk]
      simp
    · simp [hr,PowerSeries.coeff_rescale]
  refine ⟨1-C x*X,C x*X,by simp,?_,hx,?_⟩
  · exact (natDegree_sub_le _ _).trans (max_le (by simp) hx)
  · rw [hs]
    have he := congrArg (PowerSeries.rescale x)
      (PowerSeries.mk_one_mul_one_sub_eq_one R)
    simp only [map_mul,map_sub,map_one,PowerSeries.rescale_X] at he
    simp only [Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_mul,
      Polynomial.coe_C,Polynomial.coe_X]
    calc
      (1-PowerSeries.C x*PowerSeries.X)*
          (PowerSeries.rescale x (PowerSeries.mk (1 : ℕ→R))-1)=
        PowerSeries.rescale x (PowerSeries.mk (1 : ℕ→R))*
          (1-PowerSeries.C x*PowerSeries.X)-1+PowerSeries.C x*PowerSeries.X := by ring
      _=PowerSeries.C x*PowerSeries.X := by rw [he]; ring

/-- The full finite labeled moment family has a rational presentation
of degree at most its raw label count. This presentation is ghost data. -/
theorem finite_moments_rational {R ι : Type*} [CommRing R]
    (S : Finset ι) (x : ι→R) :
    RationalBound (∑ i∈S,PowerSeries.mk fun r => if r=0 then 0 else (x i)^r) S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,0,by simp,by simp,by simp,by simp⟩
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi]
    simpa only [Nat.add_comm 1] using rational_add (single_moments_rational (x i)) ih

/-- The ORIGINAL centered seed series has degree at most m-1. -/
theorem original_seed_rational {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    RationalBound (centredSeedSeries g m) (m-1) := by
  have he : centredSeedSeries g m=
      ∑ j∈Finset.range (m-1),PowerSeries.mk fun r => if r=0 then 0 else
        (((progressionSeed g N m (j+1)).step : ZMod N)^r) := by
    ext r
    simp only [centredSeedSeries,PowerSeries.coeff_mk,map_sum]
    by_cases hr : r=0
    · simp [hr]
    · simp only [if_neg hr,seedMoment]
  rw [he]
  simpa only [Finset.card_range] using finite_moments_rational (Finset.range (m-1))
    (fun j => ((progressionSeed g N m (j+1)).step : ZMod N))

/-- The complete ORIGINAL normalized grid has degree at most (m-1)J.
The large product is used only in the proof, never by a constructor. -/
theorem original_grid_rational {N : ℕ} (g : (ZMod N)ˣ) (m w J : ℕ) :
    RationalBound (centredGridSeries g m w J) ((m-1)*J) := by
  have he : centredGridSeries g m w J=
      ∑ jk∈(Finset.range (m-1)) ×ˢ (Finset.range J),
        PowerSeries.mk fun r => if r=0 then 0 else (seedPoint g m w (jk.1+1) jk.2)^r := by
    ext r
    simp only [centredGridSeries,PowerSeries.coeff_mk,map_sum]
    by_cases hr : r=0
    · simp [hr]
    · simp only [if_neg hr,gridMoment,Finset.sum_product]
  rw [he]
  simpa only [Finset.card_product,Finset.card_range] using
    finite_moments_rational ((Finset.range (m-1)) ×ˢ (Finset.range J))
      (fun jk => seedPoint g m w (jk.1+1) jk.2)

/-- The exact difference equation of the ORIGINAL family, including
coefficients where division by a geometric denominator is impossible. -/
theorem original_moment_equation {N : ℕ} (g : (ZMod N)ˣ) (m w J : ℕ) :
    let c := (((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N))
    PowerSeries.rescale c (centredGridSeries g m w J)-centredGridSeries g m w J=
      PowerSeries.rescale (c^J) (centredSeedSeries g m)-centredSeedSeries g m := by
  dsimp only
  ext r
  by_cases hr : r=0
  · subst r
    rw [map_sub,map_sub,PowerSeries.coeff_rescale,PowerSeries.coeff_rescale]
    simp [centredGridSeries,centredSeedSeries]
  · rw [map_sub,map_sub,PowerSeries.coeff_rescale,PowerSeries.coeff_rescale,
      centredGridSeries_coeff g m w J r (by omega),centredSeedSeries_coeff g m r (by omega)]
    have he := gridMoment_geometric_difference g m w J r
    rw [pow_right_comm] at he
    linear_combination he

/-- Roughness preserves both hidden local periods at the public width
4m. Orders remain proof-side; the constructor receives only public data. -/
theorem original_linear_scale_orders {p q m : ℕ} (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let h := projectedUnit g m
    let c := ((seedBase h m)^(4*m))⁻¹
    orderOf (leftUnit c)=orderOf (leftUnit h) ∧
      orderOf (rightUnit c)=orderOf (rightUnit h) := by
  have he : m^2*(4*m)=4*m^3 := by ring
  have hp := (rough_coprime_small (by omega : 0<4) hm hlong.2.2.2.2.2.1).mul_right
    ((rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1).pow_right 3)
  have hq := (rough_coprime_small (by omega : 0<4) hm hlong.2.2.2.2.2.2).mul_right
    ((rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.2).pow_right 3)
  constructor
  · simpa only [leftUnit,seedBase,map_inv,orderOf_inv,map_pow,←pow_mul,he] using hp.orderOf_pow
  · simpa only [rightUnit,seedBase,map_inv,orderOf_inv,map_pow,←pow_mul,he] using hq.orderOf_pow

/-- No original linear-width scale resonance survives in this entire
quadratic coefficient window, in EITHER prime reduction. -/
theorem original_linear_scale_gaps {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let c := (((((seedBase (projectedUnit g m) m)^(4*m))⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))
    ∀ r, 0<r → r≤2*m^2 → IsUnit (c^r-1) := by
  dsimp only
  let c := ((seedBase (projectedUnit g m) m)^(4*m))⁻¹
  have hord := original_linear_scale_orders hm g hlong
  have hleft : 4*m^2<orderOf (leftUnit c) := by
    rw [hord.1]
    nlinarith only [hlong.2.2.2.1.1]
  have hright : 4*m^2<orderOf (rightUnit c) := by
    rw [hord.2]
    nlinarith only [hlong.2.2.2.1.2]
  intro r hr hrbound
  apply isUnit_of_prime_reductions hp hq
  · rw [map_sub,map_pow,map_one]
    apply sub_ne_zero.mpr
    intro he
    have hu : (leftUnit c)^r=(leftUnit c)^0 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val,pow_zero,Units.val_one]
      change (ZMod.castHom (dvd_mul_right p q) (ZMod p) (c : ZMod (p*q)))^r=1
      exact he
    have heq := pow_injOn_Iio_orderOf (by omega : r<orderOf (leftUnit c))
      (by omega : 0<orderOf (leftUnit c)) hu
    omega
  · rw [map_sub,map_pow,map_one]
    apply sub_ne_zero.mpr
    intro he
    have hu : (rightUnit c)^r=(rightUnit c)^0 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val,pow_zero,Units.val_one]
      change (ZMod.castHom (dvd_mul_left q p) (ZMod q) (c : ZMod (p*q)))^r=1
      exact he
    have heq := pow_injOn_Iio_orderOf (by omega : r<orderOf (rightUnit c))
      (by omega : 0<orderOf (rightUnit c)) hu
    omega

/-- Linear-many genuine coefficients certify a degree-at-most-m
candidate for the FULL padded original family. Existence is NOT asserted. -/
theorem original_linear_prefix_rigidity {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hd : d≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (F : PowerSeries (ZMod (p*q))) (hF : RationalBound F d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r F=
      PowerSeries.coeff r (centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))) :
    F=centredGridSeries (projectedUnit g m) m (4*m)
      (seedLength m/(4*m)+1) := by
  have hcount := (linear_moment_grid_count hm).2.2
  apply structured_prefix_rigidity (original_seed_rational _ m)
    (original_grid_rational _ m (4*m) _) hF (original_moment_equation _ m (4*m) _) hprefix
  intro r hr hrbound
  apply original_linear_scale_gaps hp hq hm g hlong r hr
  have hm2 : m≤m^2 := by nlinarith only [hm]
  omega

/-- A concrete finite polynomial certificate replaces the unknown
infinite candidate by U,V and genuine prefix equations. -/
theorem structured_polynomial_prefix_certificate {R : Type*} [CommRing R]
    {A B : PowerSeries R} {c : R} {J M Q d : ℕ}
    (hA : RationalBound A M) (hB : RationalBound B Q)
    (heq : PowerSeries.rescale c B-B=PowerSeries.rescale (c^J) A-A)
    (hgaps : ∀ r, 0<r → r≤d+Q → IsUnit (c^r-1))
    (U V : R[X]) (hU : U.coeff 0=1) (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+M), PowerSeries.coeff r ((U : PowerSeries R)*B)=V.coeff r) :
    (U : PowerSeries R)*B=(V : PowerSeries R) := by
  have hconstant : PowerSeries.constantCoeff (U : PowerSeries R)=(1 : Rˣ) := by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,Polynomial.coeff_coe,hU,Units.val_one]
  let I := PowerSeries.invOfUnit (U : PowerSeries R) 1
  have hUI : (U : PowerSeries R)*I=1 := PowerSeries.mul_invOfUnit _ _ hconstant
  have hIU : I*(U : PowerSeries R)=1 := PowerSeries.invOfUnit_mul _ _ hconstant
  let F := I*(V : PowerSeries R)
  have hUV : (U : PowerSeries R)*F=(V : PowerSeries R) := by
    dsimp only [F]
    rw [←mul_assoc,hUI,one_mul]
  have hzero : ∀ r≤2*(d+M), PowerSeries.coeff r ((U : PowerSeries R)*(F-B))=0 := by
    intro r hr
    rw [mul_sub,hUV,map_sub,Polynomial.coeff_coe,hprefix r hr,sub_self]
  have hplain : ∀ r≤2*(d+M), PowerSeries.coeff r (F-B)=0 := by
    have hh := zero_prefix_mul hzero I
    simpa only [←mul_assoc,hIU,one_mul] using hh
  have hF : F=B := structured_prefix_rigidity hA hB ⟨U,V,hU,hUd,hVd,hUV⟩ heq
    (fun r hr => sub_eq_zero.mp (by simpa only [map_sub] using hplain r hr)) hgaps
  rw [←hF]
  exact hUV

/-- The public-width ORIGINAL family needs at most 4m-1 coefficients,
including its already-known zero constant, to validate this finite
degree-at-most-m certificate. No certificate existence is inferred. -/
theorem original_linear_polynomial_certificate {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hd : d≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) :
    2*(d+(m-1))+1≤4*m-1 ∧
      (U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1)=(V : PowerSeries (ZMod (p*q))) := by
  refine ⟨by omega,?_⟩
  apply structured_polynomial_prefix_certificate (original_seed_rational _ m)
    (original_grid_rational _ m (4*m) _) (original_moment_equation _ m (4*m) _)
    _ U V hU hUd hVd hprefix
  intro r hr hrbound
  apply original_linear_scale_gaps hp hq hm g hlong r hr
  have hcount := (linear_moment_grid_count hm).2.2
  have hm2 : m≤m^2 := by nlinarith only [hm]
  omega

/-- The same certificate applies throughout the quadratic degree
window. In particular, degrees of the form m times a polylogarithmic
factor are allowed whenever they remain at most m^2. -/
theorem original_polynomial_prefix_certificate {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hd : d≤m^2)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (U V : (ZMod (p*q))[X]) (hU : U.coeff 0=1)
    (hUd : U.natDegree≤d) (hVd : V.natDegree≤d)
    (hprefix : ∀ r≤2*(d+(m-1)), PowerSeries.coeff r
      ((U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
        (seedLength m/(4*m)+1))=V.coeff r) :
    (U : PowerSeries (ZMod (p*q)))*centredGridSeries (projectedUnit g m) m (4*m)
      (seedLength m/(4*m)+1)=(V : PowerSeries (ZMod (p*q))) := by
  apply structured_polynomial_prefix_certificate (original_seed_rational _ m)
    (original_grid_rational _ m (4*m) _) (original_moment_equation _ m (4*m) _)
    _ U V hU hUd hVd hprefix
  intro r hr hrbound
  apply original_linear_scale_gaps hp hq hm g hlong r hr
  have hcount := (linear_moment_grid_count hm).2.2
  omega

/-- Finite-prefix whole-family validation attaches to the ACTUAL
N-only public long route. It supplies no private factor, order, candidate
existence, or acquisition-cost premise to an executable algorithm. -/
theorem actual_public_route_prefix_certificate {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      let B := centredGridSeries h m (4*m) (seedLength m/(4*m)+1)
      ∀ (d : ℕ) (U V : (ZMod (p*q))[X]), d≤m^2 → U.coeff 0=1 →
        U.natDegree≤d → V.natDegree≤d →
        (∀ r≤2*(d+(m-1)), PowerSeries.coeff r ((U : PowerSeries (ZMod (p*q)))*B)=V.coeff r) →
        (U : PowerSeries (ZMod (p*q)))*B=(V : PowerSeries (ZMod (p*q))) := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := hB.trans hmBounds.1
  refine ⟨hc,?_⟩
  dsimp only
  intro d U V hdegree hU hUd hVd hprefix
  exact original_polynomial_prefix_certificate hp hq hm hdegree
    (ZMod.unitOfCoprime a hc) hlong U V hU hUd hVd hprefix

end RiemannGaussian.SemiprimeSeedMomentPrefixRigidity
