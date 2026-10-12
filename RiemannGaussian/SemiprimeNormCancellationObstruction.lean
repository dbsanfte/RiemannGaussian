/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCauchyAcquisitionObstruction
import RiemannGaussian.SemiprimeSeedShiftClosureObstruction
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Actual geometric doubling and complement norms resist the proposed cancellation

Naive reduce-then-shift doubling loses a nonzero correction at the first
degree boundary of the actual geometric product. The premise that short
prefix cross differences are units is supplied classically by the existing
arithmetic counterfamily, rather than by successful examples.

Deleting only unit cross differences cannot desaturate the whole original
norm. Full rectangular Cauchy clearings with such selected columns retain
the same zero scalar. Partial-row norms and corrected recurrences remain open.
-/

namespace RiemannGaussian.SemiprimeNormCancellationObstruction

open scoped BigOperators
open Polynomial Matrix SemiprimeSeedHermiteQuotient SemiprimeSeedGeometricRecurrence
open SemiprimeSeedShiftClosureObstruction SemiprimeSeedSumAcquisition
open SemiprimeIntervalJet SemiprimeSharedIntervalJet SemiprimeLocalOrderRouting
open SemiprimeCentreFreeCover SemiprimeGlobalPhaseCancellation
open SemiprimeDenseRowCarries SemiprimeBalancedAcquisitionObstruction
open SemiprimeGeometricRows

/-- Equal-degree monic division discards exactly one copy of the carrier. -/
theorem monic_equal_degree_remainder {R : Type*} [CommRing R] [Nontrivial R]
    {P U : R[X]} (hP : P.Monic) (hU : U.Monic) (hd : P.natDegree=U.natDegree) :
    P %ₘ U=P-U := by
  have hq : (P /ₘ U).natDegree=0 := by rw [natDegree_divByMonic P hU,hd,Nat.sub_self]
  have hc : (P /ₘ U).leadingCoeff=1 := by
    apply (leadingCoeff_divByMonic_of_monic hU _).trans hP.leadingCoeff
    rw [degree_eq_natDegree hU.ne_zero,degree_eq_natDegree hP.ne_zero,hd]
  have he : P /ₘ U=1 := by
    rw [eq_C_of_natDegree_eq_zero hq]
    have hzero : (P /ₘ U).coeff 0=1 := by simpa only [leadingCoeff,hq] using hc
    rw [hzero,C_1]
  rw [modByMonic_eq_sub_mul_div,he,mul_one]

/-- Equality of canonical remainders makes the polynomial difference divisible. -/
theorem dvd_sub_of_equal_remainders {R : Type*} [CommRing R]
    {P Q U : R[X]} (hU : U.Monic) (he : P %ₘ U=Q %ₘ U) : U∣P-Q := by
  apply (modByMonic_eq_zero_iff_dvd hU).mp
  rw [sub_modByMonic,he,sub_self]

/-- The omitted correction cannot vanish when the actual half product is coprime to U. -/
theorem actual_product_reduce_then_shift_fails {R : Type*} [CommRing R] [Nontrivial R]
    {P U : R[X]} (hP : P.Monic) (hU : U.Monic) (hd : P.natDegree=U.natDegree)
    (hconstant : IsUnit (U.coeff 0)) (hcop : IsCoprime U P)
    (c : R) (v : Rˣ) (hpower : c^U.natDegree≠1) :
    (P*C (v : R)*P.comp (C c*X)) %ₘ U≠
      ((P %ₘ U)*C (v : R)*(P %ₘ U).comp (C c*X)) %ₘ U := by
  intro he
  let A := C c*X
  let Q := P-U
  have hrem := monic_equal_degree_remainder hP hU hd
  rw [hrem] at he
  have hdifference := dvd_sub_of_equal_remainders hU he
  have herror : P*C (v : R)*P.comp A-Q*C (v : R)*Q.comp A=
      P*C (v : R)*U.comp A+U*(C (v : R)*Q.comp A) := by
    dsimp only [Q]
    rw [sub_comp]
    ring
  change U∣P*C (v : R)*P.comp A-Q*C (v : R)*Q.comp A at hdifference
  rw [herror] at hdifference
  have herr : U∣P*C (v : R)*U.comp A := by
    have h := hdifference.sub (dvd_mul_right U (C (v : R)*Q.comp A))
    simpa only [add_sub_cancel_right] using h
  have hunit : IsUnit (C (v : R) : R[X]) := v.isUnit.map C
  have hcop' : IsCoprime U (P*C (v : R)) := by
    rw [mul_comm P,isCoprime_mul_unit_left_right hunit]
    exact hcop
  exact hpower (shift_dvd_forces_power hU hconstant c
    (hcop'.dvd_of_dvd_mul_left herr))

/-- A prefix avoiding all selected cross hits is coprime to the literal target carrier. -/
theorem prefix_coprime_target {R : Type*} [CommRing R] (alpha : R)
    (xs : List R) (d : ℕ) (hcross : ∀ x∈xs, ∀ r<d, IsUnit (x-alpha^r)) :
    IsCoprime (targetPolynomial xs) (rowPolynomial alpha d) := by
  induction xs with
  | nil => exact isCoprime_one_left
  | cons x xs ih =>
    change IsCoprime ((X-C x)*targetPolynomial xs) (rowPolynomial alpha d)
    apply IsCoprime.mul_left _ (ih (fun y hy => hcross y (List.mem_cons_of_mem x hy)))
    unfold rowPolynomial SemiprimeCartesianCompletion.rootPolynomial
    apply IsCoprime.prod_right
    intro r hr
    exact isCoprime_X_sub_C_of_isUnit_sub (hcross x List.mem_cons_self r
      (Finset.mem_range.mp hr))

/-- The failure applies to the ACTUAL original product, including a Hermite carrier power. -/
theorem long_original_doubling_fails {p q m e : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (xs : List (ZMod (p*q))) (hunit : ∀ x∈xs, IsUnit x)
    (hdpos : 0<e*xs.length) (hdsmall : e*xs.length≤2*m)
    (hcross : ∀ x∈xs, ∀ r<e*xs.length,
      IsUnit (x-((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^r)) :
    let alpha := seedBase (projectedUnit g m) m
    let d := e*xs.length
    let U := (targetPolynomial xs)^e
    let P := rowPolynomial (alpha : ZMod (p*q)) d
    rowPolynomial (alpha : ZMod (p*q)) (d+d) %ₘ U≠
      ((P %ₘ U)*C (((alpha : ZMod (p*q))^d)^d)*
        (P %ₘ U).comp (C ((((alpha^d)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)) %ₘ U := by
  let : Fact (1<p*q) := ⟨by nlinarith [hp.one_lt,hq.one_lt]⟩
  dsimp only
  let alpha := seedBase (projectedUnit g m) m
  let d := e*xs.length
  let U := (targetPolynomial xs)^e
  have hU : U.Monic := (targetPolynomial_monic xs).pow e
  have hdegree : U.natDegree=d := by
    dsimp only [U,d]
    rw [(targetPolynomial_monic xs).natDegree_pow,targetPolynomial_natDegree,mul_comm]
  have hconstant : IsUnit (U.coeff 0) := by
    dsimp only [U]
    change IsUnit (Polynomial.constantCoeff (targetPolynomial xs^e))
    rw [map_pow]
    exact (targetPolynomial_constant_unit xs hunit).pow e
  have hcop : IsCoprime U (rowPolynomial (alpha : ZMod (p*q)) d) :=
    (prefix_coprime_target (alpha : ZMod (p*q)) xs d hcross).pow_left
  have hpowers : ((((alpha^d)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))^U.natDegree≠1 := by
    intro he
    have hu : (alpha^(d*d))⁻¹=1 := by
      apply Units.ext
      simpa only [hdegree,←Units.val_pow_eq_pow_val,←inv_pow,←pow_mul,Units.val_one] using he
    have hz : alpha^(d*d)=1 := inv_eq_one.mp hu
    have hle := orderOf_le_of_pow_eq_one (Nat.mul_pos hdpos hdpos) hz
    have hord : orderOf alpha=orderOf (projectedUnit g m) := by
      simpa only [pow_zero,pow_one] using long_dyadic_scale_order hp hq hpq hm g hlong 0
    rw [hord] at hle
    have hlarge := long_global_order_bound hp hq hpq g hlong
    have hds : d≤2*m := hdsmall
    have hbound : d*d≤4*m^2 := by nlinarith only [hds]
    have hm2 : 1≤m^2 := by nlinarith only [hm]
    have h24 : m^2≤m^4 := by
      calc
        m^2=m^2*1 := by ring
        _≤m^2*m^2 := Nat.mul_le_mul_left _ hm2
        _=m^4 := by ring
    change orderOf (projectedUnit g m)≤d*d at hle
    have hlast : 4*m^2≤16*m^4 := by nlinarith only [h24]
    exact (not_lt_of_ge (hle.trans (hbound.trans hlast))) hlarge
  rw [rowPolynomial_doubling]
  exact actual_product_reduce_then_shift_fails
    (by unfold rowPolynomial SemiprimeCartesianCompletion.rootPolynomial
        exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
    hU (by
      change (SemiprimeCartesianCompletion.rootPolynomial (Finset.range d)
        (fun r => (alpha : ZMod (p*q))^r)).natDegree=U.natDegree
      unfold SemiprimeCartesianCompletion.rootPolynomial
      rw [natDegree_finsetProd_X_sub_C_eq_card,Finset.card_range,hdegree])
    hconstant hcop _ ((alpha^d)^d) hpowers

/-- Original whole-family value and squared Hermite carriers both lose this actual correction. -/
theorem original_family_doubling_fails {p q m e : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (he : 0<e) (he2 : e≤2)
    (hcross : ∀ x∈seedTargets (projectedUnit g m) m, ∀ r<e*(m-1),
      IsUnit (x-((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^r)) :
    let alpha := seedBase (projectedUnit g m) m
    let d := e*(m-1)
    let U := (targetPolynomial (seedTargets (projectedUnit g m) m))^e
    let P := rowPolynomial (alpha : ZMod (p*q)) d
    rowPolynomial (alpha : ZMod (p*q)) (d+d) %ₘ U≠
      ((P %ₘ U)*C (((alpha : ZMod (p*q))^d)^d)*
        (P %ₘ U).comp (C ((((alpha^d)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)) %ₘ U := by
  have hunits : ∀ x∈seedTargets (projectedUnit g m) m, IsUnit x := by
    intro x hx
    obtain ⟨u,hu⟩ := seedTargets_units (projectedUnit g m) m x hx
    rw [←hu]
    exact u.isUnit
  have hdpos : 0<e*(seedTargets (projectedUnit g m) m).length := by
    rw [seedTargets_length]
    exact Nat.mul_pos he (by omega)
  have hdsmall : e*(seedTargets (projectedUnit g m) m).length≤2*m := by
    rw [seedTargets_length]
    exact (Nat.mul_le_mul_right _ he2).trans (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))
  have hcross' : ∀ x∈seedTargets (projectedUnit g m) m,
      ∀ r<e*(seedTargets (projectedUnit g m) m).length,
      IsUnit (x-((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^r) := by
    simpa only [seedTargets_length] using hcross
  simpa only [seedTargets_length] using
    long_original_doubling_fails hp hq hpq hm g hlong
      (seedTargets (projectedUnit g m) m) hunits hdpos hdsmall hcross'

/-- Removing only unit factors leaves a zero norm zero, with per-row deletion sets. -/
theorem complement_norm_zero {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n→R) (y : ℕ→R) (I : Finset ℕ) (D : Fin n→Finset ℕ)
    (hD : ∀ i, D i⊆I) (hunit : ∀ i, ∀ r∈D i, IsUnit (x i-y r))
    (hfull : (∏ i, ∏ r∈I, (x i-y r))=0) :
    (∏ i, ∏ r∈I\D i, (x i-y r))=0 := by
  classical
  have hremoved : IsUnit (∏ i, ∏ r∈D i, (x i-y r)) := by
    apply IsUnit.prod_iff.mpr
    intro i _
    exact IsUnit.prod_iff.mpr (hunit i)
  have hsplit : (∏ i, ∏ r∈D i, (x i-y r))*(∏ i, ∏ r∈I\D i, (x i-y r))=0 := by
    rw [←Finset.prod_mul_distrib]
    convert hfull using 1
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_comm]
    exact Finset.prod_sdiff (hD i)
  exact hremoved.mul_left_cancel (by simpa only [mul_zero] using hsplit)

/-- The literal balanced original whole-family norm stays saturated after every unit-only deletion. -/
theorem balanced_original_complement_zero {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (D : Fin (m-1)→Finset ℕ)
    (hD : ∀ i, D i⊆Finset.range (seedLength m))
    (hunit : ∀ i, ∀ r∈D i, IsUnit
      (((progressionSeed g (p*q) m (i.val+1)).step : ZMod (p*q))-
        ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q))^r)) :
    (∏ i : Fin (m-1), ∏ r∈Finset.range (seedLength m)\D i,
      (((progressionSeed g (p*q) m (i.val+1)).step : ZMod (p*q))-
        ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q))^r))=0 := by
  apply complement_norm_zero _ _ _ D hD hunit
  change (∏ i : Fin (m-1), (fun j : ℕ => ∏ r∈Finset.range (seedLength m),
    (((progressionSeed g (p*q) m (j+1)).step : ZMod (p*q))-
      ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q))^r)) i.val)=0
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => ∏ r∈Finset.range (seedLength m),
    (((progressionSeed g (p*q) m (j+1)).step : ZMod (p*q))-
      ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q))^r)) (m-1)]
  have h := balanced_seedAggregate_zero hp hq hpq hm hprefixp hprefixq
    hpupper hqupper hN g
  simpa only [SemiprimeSeedLinearStateObstruction.seedAggregate,
    SemiprimeQAggregate.rowAggregate,one_mul,intervalProduct] using h

/-- A whole-family rectangular clearing retains this saturated outside-column norm. -/
theorem whole_family_clearing_det_zero {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n→R) (y : ℕ→R) (I J : Finset ℕ) (hJ : J⊆I)
    (hunit : ∀ i, ∀ r∈J, IsUnit (x i-y r))
    (hfull : (∏ i, ∏ r∈I, (x i-y r))=0)
    (B : Matrix (Fin n) (Fin n) R) :
    (diagonal (fun i => ∏ r∈I\J, (x i-y r))*B).det=0 := by
  rw [det_mul,det_diagonal,complement_norm_zero x y I (fun _ => J)
    (fun _ => hJ) hunit hfull,zero_mul]

end RiemannGaussian.SemiprimeNormCancellationObstruction
