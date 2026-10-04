/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedPointRigidity
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Original seed jets in a Hermite remainder carrier

A squared monic target modulus retains each original detector and target
derivative; a second remainder retains the marked base derivative. This
compresses the output carrier, not the cost of constructing its remainders.
Geometric substitution must respect the modulus before a reduced polynomial
can safely be reused by a proposed fixed-modulus doubling algorithm.
-/

namespace RiemannGaussian.SemiprimeSeedHermiteQuotient

open scoped BigOperators
open Polynomial
open SemiprimeDenseRowCarries SemiprimeGlobalPhaseCancellation SemiprimeSeedSumAcquisition
open SemiprimeIntervalJet SemiprimeSharedIntervalJet SemiprimeWrapIndexRecovery
open SemiprimeLocalOrderRouting SemiprimeCentreFreeCover SemiprimeLongPowerRouting

/-- A monic target polynomial preserves every supplied value with multiplicity. -/
noncomputable def targetPolynomial {R : Type*} [CommRing R] (xs : List R) : R[X] :=
  (xs.map fun x => X-C x).prod

/-- The target product is monic over every commutative coefficient ring. -/
theorem targetPolynomial_monic {R : Type*} [CommRing R] (xs : List R) :
    (targetPolynomial xs).Monic := by
  induction xs with
  | nil => exact monic_one
  | cons x xs ih => exact (monic_X_sub_C x).mul ih

/-- Over a nontrivial ring its exact degree is the number of original values. -/
theorem targetPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R] (xs : List R) :
    (targetPolynomial xs).natDegree=xs.length := by
  induction xs with
  | nil => exact natDegree_one
  | cons x xs ih =>
    change ((X-C x)*targetPolynomial xs).natDegree=xs.length+1
    rw [(monic_X_sub_C x).natDegree_mul (targetPolynomial_monic xs),natDegree_X_sub_C,ih]
    omega

/-- Every original supplied target remains a literal root, including duplicates. -/
theorem targetPolynomial_root {R : Type*} [CommRing R] {xs : List R} {x : R}
    (hx : x∈xs) : (targetPolynomial xs).eval x=0 := by
  induction xs with
  | nil => cases hx
  | cons y xs ih =>
    change ((X-C y)*targetPolynomial xs).eval x=0
    rw [eval_mul,eval_sub,eval_X,eval_C]
    rcases List.mem_cons.mp hx with hsame|htail
    · rw [hsame,sub_self,zero_mul]
    · rw [ih htail,mul_zero]

/-- A squared target modulus preserves both value and first target
derivative at every root, without dividing an evaluated factor. -/
theorem hermite_remainder_exact {R : Type*} [CommRing R] (P U : R[X]) {x : R}
    (hx : U.eval x=0) :
    (P %ₘ U^2).eval x=P.eval x ∧ (P %ₘ U^2).derivative.eval x=P.derivative.eval x := by
  constructor
  · simpa only [eval₂_id] using
      eval₂_modByMonic_eq_self_of_root (f:=RingHom.id R) (p:=P) (q:=U^2)
        (x:=x) (by simp only [eval₂_id,eval_pow,hx,zero_pow (by decide : (2 : ℕ)≠0)])
  · have he := congrArg (fun Q : R[X] => Q.derivative.eval x) (modByMonic_add_div P (U^2))
    simpa only [derivative_add,derivative_mul,derivative_pow,eval_add,eval_mul,
      eval_pow,eval_C,hx,show (2 : ℕ)-1=1 by decide,pow_one,
      zero_pow (by decide : (2 : ℕ)≠0),mul_zero,
      zero_mul,add_zero] using he

/-- Two small remainders retain all three original interval channels. -/
noncomputable def intervalRemainders {R : Type*} [CommRing R] (alpha : R)
    (xs : List R) (L : ℕ) : R[X]×R[X] :=
  let U := targetPolynomial xs
  let P := SemiprimeCartesianCompletion.rootPolynomial (Finset.range L) (fun u => alpha^u)
  (P %ₘ U^2,babyBasePolynomial alpha L %ₘ U)

/-- Read one original target's detector and both marked derivatives
from the Hermite carrier, with its original label kept separately. -/
noncomputable def remainderJet {R : Type*} [CommRing R] (A : R[X]×R[X]) (x : R) : R×R×R :=
  (A.1.eval x,A.1.derivative.eval x,A.2.eval x)

/-- The carrier preserves exact interval jets at every original target,
including saturated products and repeated supplied targets. -/
theorem remainderJet_exact {R : Type*} [CommRing R] (alpha : R) {xs : List R} {x : R}
    (hx : x∈xs) (L : ℕ) :
    remainderJet (intervalRemainders alpha xs L) x=
      (intervalProduct alpha x L,targetDerivative alpha x L,baseDerivative alpha x L) := by
  have hroot := targetPolynomial_root hx
  have hh := hermite_remainder_exact
    (SemiprimeCartesianCompletion.rootPolynomial (Finset.range L) (fun u => alpha^u))
    (targetPolynomial xs) hroot
  have hbase := eval₂_modByMonic_eq_self_of_root (f:=RingHom.id R)
    (p:=babyBasePolynomial alpha L) (q:=targetPolynomial xs) (x:=x)
    (by simpa only [eval₂_id] using hroot)
  unfold remainderJet intervalRemainders
  rw [hh.1,hh.2]
  simp only [eval₂_id] at hbase
  rw [hbase,babyBasePolynomial_eval]
  exact Prod.ext (by simp only [SemiprimeCartesianCompletion.rootPolynomial,intervalProduct,
    eval_prod,eval_sub,eval_X,eval_C])
    (Prod.ext (targetDerivative_eq_derivative alpha x L).symm rfl)

/-- A scale shift can preserve a monic modulus with unit constant term
only when the scale raised to its degree is one. -/
theorem shift_dvd_forces_power {R : Type*} [CommRing R] {U : R[X]}
    (hU : U.Monic) (hconstant : IsUnit (U.coeff 0)) (c : R)
    (hdvd : U∣U.comp (C c*X)) : c^U.natDegree=1 := by
  have hlinear : (C c*X : R[X]).natDegree≤1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le c 1
  have hmul := Nat.mul_le_mul_left U.natDegree hlinear
  have hdegree : (U.comp (C c*X)).natDegree≤U.natDegree :=
    natDegree_comp_le.trans (by simpa only [mul_one] using hmul)
  have he := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hU hdvd hdegree
  have hc := congrArg (fun P : R[X] => P.coeff 0) he
  simp only [comp_C_mul_X_coeff,pow_zero,mul_one,mul_coeff_zero,coeff_C_zero] at hc
  have hs : (U.comp (C c*X)).leadingCoeff=1 := hconstant.mul_left_cancel
    (by simpa only [mul_one] using hc.symm)
  rw [hs,C_1,mul_one] at he
  have htop := congrArg (fun P : R[X] => P.coeff U.natDegree) he
  simpa only [comp_C_mul_X_coeff,coeff_natDegree,hU.leadingCoeff,one_mul] using htop

/-- A forbidden scale supplies a uniform exact counterexample to
shifting a reduced representative: U and zero have identical remainders. -/
theorem remainder_shift_counterexample {R : Type*} [CommRing R] {U : R[X]}
    (hU : U.Monic) (hconstant : IsUnit (U.coeff 0)) {c : R}
    (hpower : c^U.natDegree≠1) :
    U %ₘ U=(0 : R[X]) %ₘ U ∧
      (U.comp (C c*X)) %ₘ U≠((0 : R[X]).comp (C c*X)) %ₘ U := by
  constructor
  · rw [modByMonic_self hU,zero_modByMonic]
  · simp only [zero_comp,zero_modByMonic]
    intro hz
    exact hpower (shift_dvd_forces_power hU hconstant c
      ((modByMonic_eq_zero_iff_dvd hU).mp hz))

/-- No function of the fixed-modulus remainder alone can implement the
scale shift for every original polynomial when its degree condition fails. -/
theorem no_fixed_remainder_shift {R : Type*} [CommRing R] {U : R[X]}
    (hU : U.Monic) (hconstant : IsUnit (U.coeff 0)) {c : R}
    (hpower : c^U.natDegree≠1) :
    ¬∃ T : R[X]→R[X], ∀ P : R[X], T (P %ₘ U)=(P.comp (C c*X)) %ₘ U := by
  rintro ⟨T,hT⟩
  have hUeq := hT U
  have hzero := hT 0
  obtain ⟨hsame,hneq⟩ := remainder_shift_counterexample hU hconstant hpower
  rw [hsame] at hUeq
  exact hneq (hUeq.symm.trans hzero)

/-- Unit target values make the target polynomial's constant term a unit. -/
theorem targetPolynomial_constant_unit {R : Type*} [CommRing R] (xs : List R) :
    (∀ x∈xs,IsUnit x)→IsUnit ((targetPolynomial xs).coeff 0) := by
  induction xs with
  | nil =>
    intro _
    simpa only [targetPolynomial,List.map_nil,List.prod_nil,coeff_one_zero] using
      (isUnit_one : IsUnit (1 : R))
  | cons x xs ih =>
    intro hxs
    change IsUnit (((X-C x)*targetPolynomial xs).coeff 0)
    rw [mul_coeff_zero,coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub]
    exact (hxs x List.mem_cons_self).neg.mul
      (ih (fun y hy => hxs y (List.mem_cons_of_mem x hy)))

/-- The full remainder pair has strictly linear degree in the number of
original targets; constructing it is a separate algorithmic obligation. -/
theorem intervalRemainders_degree {R : Type*} [CommRing R] [Nontrivial R]
    (alpha : R) (xs : List R) (hxs : 0<xs.length) (L : ℕ) :
    (intervalRemainders alpha xs L).1.natDegree<2*xs.length ∧
      (intervalRemainders alpha xs L).2.natDegree<xs.length := by
  let U := targetPolynomial xs
  have hU : U.Monic := targetPolynomial_monic xs
  have hdegree : U.natDegree=xs.length := targetPolynomial_natDegree xs
  have hneq : U≠1 := by
    intro he
    rw [he,natDegree_one] at hdegree
    omega
  have hdegree₂ : (U^2).natDegree=2*xs.length := by rw [hU.natDegree_pow,hdegree]
  have hneq₂ : U^2≠1 := by
    intro he
    rw [he,natDegree_one] at hdegree₂
    omega
  constructor
  · simpa only [intervalRemainders,hdegree₂] using
      natDegree_modByMonic_lt
        (SemiprimeCartesianCompletion.rootPolynomial (Finset.range L) (fun u => alpha^u))
        (hU.pow 2) hneq₂
  · simpa only [intervalRemainders,hdegree] using
      natDegree_modByMonic_lt (babyBasePolynomial alpha L) hU hneq

/-- Original labelled seed targets, with no denominator or block-value axis. -/
def seedTargets {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : List (ZMod N) :=
  (progressionSeeds g N m).map fun s => (s.step : ZMod N)

/-- The exact target-polynomial degree comes from m-1 original labels. -/
theorem seedTargets_length {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    (seedTargets g m).length=m-1 := by simp only [seedTargets,List.length_map,progressionSeeds_length]

/-- Every original target is a unit independently of collision behavior. -/
theorem seedTargets_units {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    ∀ x∈seedTargets g m,IsUnit x := by
  intro x hx
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
  exact Units.isUnit s.step

/-- One common Hermite carrier for the full original seed interval. -/
noncomputable def seedRemainders {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : (ZMod N)[X]×(ZMod N)[X] :=
  intervalRemainders ((seedBase g m : (ZMod N)ˣ) : ZMod N) (seedTargets g m) (seedLength m)

/-- The compressed output carrier has only linear coefficient capacity. -/
theorem seedRemainders_degree {N m : ℕ} [Nontrivial (ZMod N)] (g : (ZMod N)ˣ) (hm : 4≤m) :
    (seedRemainders g m).1.natDegree<2*(m-1) ∧
      (seedRemainders g m).2.natDegree<m-1 := by
  have hh := intervalRemainders_degree ((seedBase g m : (ZMod N)ˣ) : ZMod N) (seedTargets g m)
    (by rw [seedTargets_length]; omega) (seedLength m)
  simpa only [seedRemainders,seedTargets_length] using hh

/-- A coefficient-capacity counter for the output pair, not a construction
or bit-operation clock. It includes one slot even for a zero polynomial. -/
noncomputable def seedRemainderSlots {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : ℕ :=
  (seedRemainders g m).1.natDegree+1+(seedRemainders g m).2.natDegree+1

/-- At most three times the original seed count coefficient slots suffice. -/
theorem seedRemainderSlots_le {N m : ℕ} [Nontrivial (ZMod N)] (g : (ZMod N)ˣ) (hm : 4≤m) :
    seedRemainderSlots g m≤3*(m-1) := by
  have hh := seedRemainders_degree g hm
  unfold seedRemainderSlots
  omega

/-- Restore original labelled triples from the common remainder carrier. -/
noncomputable def seedRemainderBatch {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ)×(ZMod N×ZMod N×ZMod N)) :=
  let A := seedRemainders g m
  (progressionSeeds g N m).map fun s => (s,remainderJet A (s.step : ZMod N))

/-- The entire Hermite batch equals the original shared acquisition,
including both marked derivatives and all mixed-saturation cases. -/
theorem seedRemainderBatch_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    seedRemainderBatch g m=seedBatchJets g m := by
  dsimp only [seedRemainderBatch,seedRemainders,seedBatchJets]
  apply List.map_congr_left
  intro s hs
  apply Prod.ext
  · rfl
  · have htarget : (s.step : ZMod N)∈seedTargets g m := List.mem_map.mpr ⟨s,hs,rfl⟩
    rw [remainderJet_exact ((seedBase g m : (ZMod N)ˣ) : ZMod N) htarget,
      sharedSeedJet_exact (seedBase g m) (s.step : ZMod N) (seedBlockWidth_pos m)]
    rfl

/-- The same complete seed controller can consume the compressed carrier. -/
theorem seedRemainderBatch_scan_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    scanSeedJetBatch g m (seedRemainderBatch g m)=scanSeedSums g m (progressionSeeds g N m) := by
  rw [seedRemainderBatch_exact,seedBatch_scan_exact]

/-- The actual public long output succeeds with the whole Hermite batch;
this supplies correctness, not fast remainder acquisition or bit costs. -/
theorem actual_public_route_remainder_batch_succeeds {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ d, scanSeedJetBatch h m (seedRemainderBatch h m)=some d ∧
        SemiprimeGroupSelection.ProperDivisor (p*q) d := by
  simpa only [seedRemainderBatch_exact] using
    long_public_route_seed_batch_succeeds hp hq hpq hB hnone hroute

/-- A positive power of the original target polynomial, including the
ordinary and squared Hermite moduli. -/
noncomputable def seedModulus {N : ℕ} (g : (ZMod N)ˣ) (m e : ℕ) : (ZMod N)[X] :=
  (targetPolynomial (seedTargets g m))^e

/-- Every original seed modulus power is monic. -/
theorem seedModulus_monic {N : ℕ} (g : (ZMod N)ˣ) (m e : ℕ) :
    (seedModulus g m e).Monic := (targetPolynomial_monic _).pow e

/-- Every original seed modulus power has unit constant term. -/
theorem seedModulus_constant_unit {N : ℕ} (g : (ZMod N)ˣ) (m e : ℕ) :
    IsUnit ((seedModulus g m e).coeff 0) := by
  change IsUnit (Polynomial.constantCoeff ((targetPolynomial (seedTargets g m))^e))
  rw [map_pow]
  exact (targetPolynomial_constant_unit _ (seedTargets_units g m)).pow e

/-- Exact degree of any original seed modulus power. -/
theorem seedModulus_natDegree {N : ℕ} [Nontrivial (ZMod N)] (g : (ZMod N)ˣ) (m e : ℕ) :
    (seedModulus g m e).natDegree=e*(m-1) := by
  rw [seedModulus,(targetPolynomial_monic _).natDegree_pow,targetPolynomial_natDegree,
    seedTargets_length]

/-- Roughness excludes the degree condition needed for a fixed-modulus
shift, for every positive d<=4*m^2 and every positive multiplicity e<=m. -/
theorem long_shift_degree_power_ne_one {p q m d e : ℕ}
    (hm : 4≤m) (hd : 0<d) (hdm : d≤4*m^2) (he : 0<e) (hem : e≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ((((leftUnit (seedBase (projectedUnit g m) m))^d : (ZMod p)ˣ) : ZMod p))^(e*(m-1))≠1 := by
  intro hpower
  have hu : (leftUnit (seedBase (projectedUnit g m) m)^d)^(e*(m-1))=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using hpower
  have hpow : (leftUnit (projectedUnit g m))^(m^2*(d*(e*(m-1))))=1 := by
    simpa only [leftUnit,seedBase,map_pow,←pow_mul,mul_assoc] using hu
  have hdiv := orderOf_dvd_of_pow_eq_one hpow
  have hcm := rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1
  have hce := rough_coprime_small he hem hlong.2.2.2.2.2.1
  have hcR := rough_coprime_small (by omega : 0<m-1) (by omega : m-1≤m) hlong.2.2.2.2.2.1
  have hcop := (hcm.pow_right 2).mul_right (hce.mul_right hcR)
  have hdiv' : orderOf (leftUnit (projectedUnit g m))∣(m^2*(e*(m-1)))*d := by
    convert hdiv using 1
    ring
  have hdivd := hcop.dvd_mul_left.mp hdiv'
  have hle := Nat.le_of_dvd hd hdivd
  have horder := hlong.2.2.2.1.1
  nlinarith only [hle,hdm,horder]

/-- The actual original seed modulus fails the necessary scale-power
condition on the long branch, for ordinary and Hermite multiplicities. -/
theorem long_seedModulus_power_ne_one {p q m d e : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hm : 4≤m) (hd : 0<d) (hdm : d≤4*m^2) (he : 0<e) (hem : e≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ((((seedBase (projectedUnit g m) m)^d : (ZMod (p*q))ˣ) : ZMod (p*q)))^
      (seedModulus (projectedUnit g m) m e).natDegree≠1 := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  rw [seedModulus_natDegree]
  intro hpower
  have hfield := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hpower
  apply long_shift_degree_power_ne_one hm hd hdm he hem g hlong
  simpa only [leftUnit,Units.coe_map,map_pow,map_one,Units.val_pow_eq_pow_val,
    RingHom.toMonoidHom_eq_coe,MonoidHom.coe_coe] using hfield

/-- Even the actual arithmetic seed moduli are not invariant under any
positive geometric shift within the whole padded-interval scale. -/
theorem long_seedModulus_shift_not_dvd {p q m d e : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hm : 4≤m) (hd : 0<d) (hdm : d≤4*m^2) (he : 0<e) (hem : e≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ¬seedModulus (projectedUnit g m) m e∣
      (seedModulus (projectedUnit g m) m e).comp
        (C ((((seedBase (projectedUnit g m) m)^d : (ZMod (p*q))ˣ) : ZMod (p*q)))*X) := by
  intro hdiv
  exact long_seedModulus_power_ne_one hp hq hm hd hdm he hem g hlong
    (shift_dvd_forces_power (seedModulus_monic _ _ _)
      (seedModulus_constant_unit _ _ _) _ hdiv)

/-- A fixed original seed remainder has no universal shift operator on
the actual long branch. This does not exclude algorithms that exploit
additional structure of the particular geometric interval polynomials. -/
theorem long_seedModulus_no_fixed_shift {p q m d e : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hm : 4≤m) (hd : 0<d) (hdm : d≤4*m^2) (he : 0<e) (hem : e≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ¬∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P : (ZMod (p*q))[X],
      T (P %ₘ seedModulus (projectedUnit g m) m e)=
        (P.comp (C ((((seedBase (projectedUnit g m) m)^d : (ZMod (p*q))ˣ) : ZMod (p*q)))*X))
          %ₘ seedModulus (projectedUnit g m) m e := by
  exact no_fixed_remainder_shift (seedModulus_monic _ _ _)
    (seedModulus_constant_unit _ _ _)
    (long_seedModulus_power_ne_one hp hq hm hd hdm he hem g hlong)

/-- Inverse shifts used in geometric product doubling fail the same
necessary power identity, since inversion cannot turn a nonidentity
unit power into the identity. -/
theorem long_seedModulus_inverse_power_ne_one {p q m d e : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hm : 4≤m) (hd : 0<d) (hdm : d≤4*m^2) (he : 0<e) (hem : e≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    (((((seedBase (projectedUnit g m) m)^d)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))^
      (seedModulus (projectedUnit g m) m e).natDegree≠1 := by
  intro hpower
  have hu : (((seedBase (projectedUnit g m) m)^d)⁻¹)^
      (seedModulus (projectedUnit g m) m e).natDegree=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using hpower
  have hu' : ((seedBase (projectedUnit g m) m)^d)^
      (seedModulus (projectedUnit g m) m e).natDegree=1 := by
    simpa only [inv_pow,inv_eq_one] using hu
  apply long_seedModulus_power_ne_one hp hq hm hd hdm he hem g hlong
  simpa only [Units.val_pow_eq_pow_val,Units.val_one] using
    congrArg (fun u : (ZMod (p*q))ˣ => (u : ZMod (p*q))) hu'

/-- The inverse geometric substitution also has no universal operator
on the fixed original seed remainder alone. -/
theorem long_seedModulus_no_fixed_inverse_shift {p q m d e : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hm : 4≤m) (hd : 0<d) (hdm : d≤4*m^2) (he : 0<e) (hem : e≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ¬∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P : (ZMod (p*q))[X],
      T (P %ₘ seedModulus (projectedUnit g m) m e)=
        (P.comp (C (((((seedBase (projectedUnit g m) m)^d)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X))
          %ₘ seedModulus (projectedUnit g m) m e := by
  exact no_fixed_remainder_shift (seedModulus_monic _ _ _)
    (seedModulus_constant_unit _ _ _)
    (long_seedModulus_inverse_power_ne_one hp hq hm hd hdm he hem g hlong)

/-- Both fixed-remainder shift failures apply to the actual public long
output, at its matched row modulus, for all supported multiplicities. -/
theorem actual_public_route_no_fixed_shift {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∀ d, 0<d→d≤4*m^2→∀ e, 0<e→e≤m→
        (¬∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P : (ZMod (p*q))[X],
          T (P %ₘ seedModulus h m e)=
            (P.comp (C ((((seedBase h m)^d : (ZMod (p*q))ˣ) : ZMod (p*q)))*X))
              %ₘ seedModulus h m e) ∧
        (¬∃ T : (ZMod (p*q))[X]→(ZMod (p*q))[X], ∀ P : (ZMod (p*q))[X],
          T (P %ₘ seedModulus h m e)=
            (P.comp (C (((((seedBase h m)^d)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X))
              %ₘ seedModulus h m e) := by
  have hdata := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  have hN := Nat.mul_pos hp.pos hq.pos
  have hbounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hbounds.1
  refine ⟨hc,?_⟩
  dsimp only
  intro d hd hdm e he hem
  exact ⟨long_seedModulus_no_fixed_shift hp hq hm hd hdm he hem _ hlong,
    long_seedModulus_no_fixed_inverse_shift hp hq hm hd hdm he hem _ hlong⟩

end RiemannGaussian.SemiprimeSeedHermiteQuotient
