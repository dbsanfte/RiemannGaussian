/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.GramJointFixed
import OAI.NumberTheory.DirichletL.Detector.CalibrationFourier
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual native bad-place sixth-power invariance

The literal numeratorBadTwist is invariant under multiplication by the
sixth power of every supported element, at ALL inputs including nonunits.
The canonical calibrated arithmetic monoid retains its actual coprimality
mask. This is finite native arithmetic, not a sextic-residue/cusp bridge.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.NativeRaySixth
open OAI ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalUnitEuler CompletedGauss ConcreteTraceCRT
open SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

/-- Every good numerator has a primary sixth power, with its actual unit retained. -/
theorem supported_sixth_primary (x : O) (hx : Supported (Ideal.span {x})) :
    lambda^2∣x^6-1 := by
  obtain ⟨u,hu⟩ := exists_supported_primary_unit x hx
  have h := CubicEisenstein.primary_pow_congruence (u.val*x) hu 6
  simpa only [mul_pow, CanonicalUnitEuler.unit_pow_six, one_mul] using h

/-- Supportedness is preserved by taking the actual sixth power. -/
theorem supported_sixth (x : O) (hx : Supported (Ideal.span {x})) :
    Supported (Ideal.span {x^6}) := by
  rw [←Ideal.span_singleton_pow]
  exact supported_pow hx 6

/-- Actual sixth character values in the denominator, including repeated primes. -/
theorem ideal_row_sixth_denominator (m x : O) (hx : Supported (Ideal.span {x}))
    (hc : IsCoprime m x) : idealRowHom m (Ideal.span {x^6})=1 := by
  rw [←Ideal.span_singleton_pow,map_pow,←idealRowHom_argument_pow m 6 _ hx,
    idealRowHom_sixth_mask m _ hx,
    ite_eq_left ((Ideal.isCoprime_span_singleton_iff x m).mpr hc.symm)]

/-- The actual unit supplement is one on every supported sixth power. -/
theorem unit_supplement_sixth (u : Oˣ) (x : O) (hx : Supported (Ideal.span {x})) :
    unitSupplement u (x^6)=1 := by
  change (if Supported (Ideal.span {x^6}) then idealRowHom u.val (Ideal.span {x^6}) else 0)=1
  rw [ite_eq_left (supported_sixth x hx)]
  exact ideal_row_sixth_denominator u.val x hx ⟨(u⁻¹).val,0,by simp⟩

/-- The actual ramified supplement is one on every supported sixth power. -/
theorem lambda_supplement_sixth (x : O) (hx : Supported (Ideal.span {x})) :
    supportedIdealRow lambda (x^6)=1 := by
  change (if Supported (Ideal.span {x^6}) then idealRowHom lambda (Ideal.span {x^6}) else 0)=1
  rw [ite_eq_left (supported_sixth x hx)]
  exact ideal_row_sixth_denominator lambda x hx
    (PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
      ((supported_span_iff x).mp hx).1)

/-- The native cubic-times-norm-quadratic two-supplement is also sixth-invariant. -/
theorem two_supplement_sixth (x : O) (hx : Supported (Ideal.span {x})) :
    twoSupplement (x^6)=1 := by
  rw [←idealRowHom_two_formula (x^6) (supported_sixth_primary x hx) (supported_sixth x hx)]
  have hn : IsCoprime (-2 : O) x := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff x).mp hx).2)
  exact ideal_row_sixth_denominator 2 x hx
    (hn.of_isCoprime_of_dvd_left ⟨-1,by ring⟩)

/-- The actual bad-place reciprocity sign is one on every supported sixth power. -/
theorem reciprocity_sixth (r x : O) (hr : Supported (Ideal.span {r}))
    (hx : Supported (Ideal.span {x})) : sexticReciprocityPhase r (x^6)=1 := by
  have hs : sexticReciprocityPhase r x^2=1 := by
    unfold sexticReciprocityPhase
    exact_mod_cast QuadraticAllOddCRT.quadraticRaySign_sq
      (ActualEisensteinCoordinates.residue r) (ActualEisensteinCoordinates.residue x)
      (supported_residue_odd r hr) (supported_residue_odd x hx)
  change reciprocityPhaseMonoid r hr (x^6)=1
  rw [map_pow,show (6 : ℕ)=2*3 from rfl,pow_mul]
  change (sexticReciprocityPhase r x^2)^3=1
  rw [hs,one_pow]

/-- The literal assembled bad-place profile, not an arbitrary period72 function. -/
theorem numerator_bad_sixth (u : Oˣ) (a b : ℕ) (r x : O)
    (hr : Supported (Ideal.span {r})) (hx : Supported (Ideal.span {x})) :
    numeratorBadTwist u a b r hr (x^6)=1 := by
  change ((unitSupplement u (x^6)*(supportedIdealRow lambda (x^6))^a)*
    twoSupplement (x^6)^b)*sexticReciprocityPhase r (x^6)=1
  rw [unit_supplement_sixth u x hx,lambda_supplement_sixth x hx,
    two_supplement_sixth x hx,reciprocity_sixth r x hr hx]
  simp

/-- All inputs, including zero and bad-prime nonunits, are preserved exactly. -/
theorem numerator_bad_mul_sixth (u : Oˣ) (a b : ℕ) (r n x : O)
    (hr : Supported (Ideal.span {r})) (hx : Supported (Ideal.span {x})) :
    numeratorBadTwist u a b r hr (n*x^6)=numeratorBadTwist u a b r hr n := by
  rw [map_mul,numerator_bad_sixth u a b r x hr hx,mul_one]

/-- The choose-based canonical calibration preserves every input on its actual unit support. -/
theorem canonical_residue_mul_sixth (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (n x : O)
    (hc : IsCoprime (calibrationForSet S hS).generator x) :
    (calibrationForSet S hS).residueMonoid (n*x^6)=
      (calibrationForSet S hS).residueMonoid n := by
  rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS x hc,mul_one]

/-- The good factor in the actual low-row data divides the calibration generator. -/
theorem calibration_good_factor_dvd (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator) : D.numeratorGood∣C.generator := by
  refine ⟨D.numeratorUnit.val*lambda^D.numeratorLambda*(2:O)^D.numeratorTwo,?_⟩
  have he : C.generator=D.numeratorUnit.val*lambda^D.numeratorLambda*
      (2:O)^D.numeratorTwo*D.numeratorGood := by simpa using D.numeratorFactor
  exact he.trans (by ring)

/-- The literal complete canonical arithmetic monoid is one on coprime sixth powers. -/
theorem canonical_gram_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (x : O)
    (hc : IsCoprime (calibrationForSet S hS).generator x) :
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
      (calibrationLowData S hS) (x^6)=1 := by
  let C := calibrationForSet S hS
  let D := calibrationLowData S hS
  have hb := calibration_generator_bad S hS hbad
  have hx : Supported (Ideal.span {x}) := supported_of_coprime_bad C.generator x hb.1 hb.2 hc
  have hrx : IsCoprime D.numeratorGood x :=
    hc.of_isCoprime_of_dvd_left (calibration_good_factor_dvd C D)
  have hres : C.residueMonoid (x^6)=1 := by
    rw [map_pow]
    exact calibrationForSet_residue_sixth S hS x hc
  have hmask : coprimalityMask C.generator (x^6)=(1:ℂ) := by
    change (if IsCoprime C.generator (x^6) then (1:ℂ) else 0)=1
    exact ite_eq_left hc.pow_right
  have hmov : movingNumeratorRow D.numeratorGood D.numeratorSupported (x^6)=1 := by
    change idealRowHom (x^6) (Ideal.span {D.numeratorGood})=1
    rw [idealRowHom_sixth_mask x _ D.numeratorSupported,
      ite_eq_left ((Ideal.isCoprime_span_singleton_iff D.numeratorGood x).mpr hrx)]
  change star (C.residueMonoid (x^6))*
    ((((1:O→*ℂ) (x^6)*coprimalityMask C.generator (x^6))*
      numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo
        D.numeratorGood D.numeratorSupported (x^6))*
      movingNumeratorRow D.numeratorGood D.numeratorSupported (x^6))=1
  rw [hres,hmask,hmov,numerator_bad_sixth _ _ _ _ x _ hx]
  simp

/-- Complete native arithmetic invariance includes all original zero/nonunit inputs. -/
theorem canonical_gram_mul_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (n x : O)
    (hc : IsCoprime (calibrationForSet S hS).generator x) :
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
      (calibrationLowData S hS) (n*x^6)=
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
      (calibrationLowData S hS) n := by
  rw [map_mul,canonical_gram_sixth S hS hbad x hc,mul_one]

/-- Exact original masked lowArithmeticCoefficient, with every supported physical power. -/
theorem low_arithmetic_sixth_product (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (s t : {I : Ideal O // Supported I})
    (hc : IsCoprime (calibrationForSet S hS).generator (primaryGenerator t.val)) :
    lowArithmeticCoefficient (calibrationForSet S hS)
      ⟨s.val*t.val^6,(supported_mul_iff _ _).mpr ⟨s.property,supported_pow t.property 6⟩⟩=
    lowArithmeticCoefficient (calibrationForSet S hS) s := by
  rw [lowArithmeticCoefficient_periodic S hS hbad,
    lowArithmeticCoefficient_periodic S hS hbad,
    primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow,
    canonical_gram_mul_sixth S hS hbad _ _ hc]

/-- The actual modulus-four physical ray is unchanged by good sixth powers. -/
theorem physical_ray_sixth (x : O) (hx : Supported (Ideal.span {x})) :
    physicalRay (x^6)=1 := by
  have hfinite : ∀r : EisensteinEPrimaryPhase.Coord,EisensteinEPrimaryPhase.odd r →
      EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul (EisensteinEPrimaryPhase.mul r r)
          (EisensteinEPrimaryPhase.mul r r))
        (EisensteinEPrimaryPhase.mul r r)=((1:ZMod 4),0) := by decide
  have hres : ActualEisensteinCoordinates.residue (x^6)=
      ActualEisensteinCoordinates.residue (1:O) := by
    rw [show x^6=(x*x*(x*x))*(x*x) by ring]
    simp only [ActualEisensteinCoordinates.residue_mul]
    rw [hfinite _ (supported_residue_odd x hx)]
    symm
    have he : (1:O)=ActualEisensteinCoordinates.eval 1 0 := by simp [ActualEisensteinCoordinates.eval]
    rw [he,ActualEisensteinCoordinates.residue_eval]
    norm_num
  apply Ideal.Quotient.eq.mpr
  obtain ⟨k,hk⟩ := ActualEisensteinCoordinates.congr_mod_four_of_residue_eq hres
  exact Ideal.mem_span_singleton.mpr ⟨k,hk⟩

/-- Physical ray labels are preserved at all numerator inputs, not just units. -/
theorem physical_ray_mul_sixth (n x : O) (hx : Supported (Ideal.span {x})) :
    physicalRay (n*x^6)=physicalRay n := by
  change Ideal.Quotient.mk (Ideal.span {(4:O)}) (n*x^6)=_
  rw [map_mul]
  change physicalRay n*physicalRay (x^6)=_
  rw [physical_ray_sixth x hx,mul_one]

/-- The actual fixed-ray calibrated extension retains all zero inputs and exclusions. -/
theorem canonical_gram_extension_mul_sixth (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayFourExpansion.RayRing) (n x : O)
    (hc : IsCoprime (calibrationForSet S hS).generator x) :
    gramCoefficientExtension S hS σ (n*x^6)=gramCoefficientExtension S hS σ n := by
  have hb := calibration_generator_bad S hS hbad
  have hx := supported_of_coprime_bad (calibrationForSet S hS).generator x hb.1 hb.2 hc
  unfold gramCoefficientExtension
  rw [physical_ray_mul_sixth n x hx,canonical_gram_mul_sixth S hS hbad n x hc]

/-- For every good x the original calibration exclusions remain as their exact mask. -/
theorem canonical_gram_mul_sixth_mask (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (n x : O) :
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
      (calibrationLowData S hS) (n*x^6)=
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
      (calibrationLowData S hS) n * coprimalityMask (calibrationForSet S hS).generator x := by
  by_cases hc : IsCoprime (calibrationForSet S hS).generator x
  · rw [canonical_gram_mul_sixth S hS hbad n x hc]
    change _=_*(if IsCoprime (calibrationForSet S hS).generator x then (1:ℂ) else 0)
    rw [ite_eq_left hc,mul_one]
  · have hc6 : ¬IsCoprime (calibrationForSet S hS).generator (x^6) := by
      intro h
      exact hc (h.of_isCoprime_of_dvd_right (dvd_pow_self x (by decide : (6:ℕ)≠0)))
    have hz := gramPeriodicMonoid_zero (calibrationForSet S hS)
      (calibrationForSet S hS).generator (calibrationLowData S hS) (x^6) hc6
    rw [map_mul,hz,mul_zero]
    change (0:ℂ)=_*(if IsCoprime (calibrationForSet S hS).generator x then (1:ℂ) else 0)
    rw [ite_eq_right hc,mul_zero]

/-- The whole fixed-ray arithmetic profile has the SAME exact excluded-prime mask. -/
theorem canonical_extension_mul_sixth_mask (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayFourExpansion.RayRing) (n x : O) (hx : Supported (Ideal.span {x})) :
    gramCoefficientExtension S hS σ (n*x^6)=
      gramCoefficientExtension S hS σ n * coprimalityMask (calibrationForSet S hS).generator x := by
  unfold gramCoefficientExtension
  rw [physical_ray_mul_sixth n x hx,canonical_gram_mul_sixth_mask S hS hbad n x]
  split_ifs <;> ring

/-- The literal primary numerator mask is invariant even at nonprimary inputs. -/
theorem primary_condition_mul_sixth (n x : O) (hx : Supported (Ideal.span {x})) :
    (lambda^2∣n*x^6-1) ↔ (lambda^2∣n-1) := by
  have hd : lambda^2∣n*x^6-n := by
    convert (supported_sixth_primary x hx).mul_left n using 1; ring
  constructor
  · intro h
    convert dvd_sub h hd using 1; ring
  · intro h
    convert dvd_add hd h using 1; ring

/-- The actual primary fixed-ray coefficient keeps exactly its original exclusions. -/
theorem native_primary_coefficient_mul_sixth_mask (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayFourExpansion.RayRing) (n x : O) (hx : Supported (Ideal.span {x})) :
    SevenEighths.ProbeGramCommon.primaryCoefficient S hS σ (n*x^6)=
      SevenEighths.ProbeGramCommon.primaryCoefficient S hS σ n *
        coprimalityMask (calibrationForSet S hS).generator x := by
  unfold SevenEighths.ProbeGramCommon.primaryCoefficient
  rw [show (ConcretePrimeRowBridge.goodLambda:O)=lambda from rfl,
    primary_condition_mul_sixth n x hx,canonical_extension_mul_sixth_mask S hS hbad σ n x hx]
  split_ifs <;> ring

/-- The actual finite bad-place character has order dividing six on units and zero elsewhere. -/
theorem numerator_bad_value_sixth_mask (u : Oˣ) (a b : ℕ) (r n : O)
    (hr : Supported (Ideal.span {r})) :
    numeratorBadTwist u a b r hr n ^ 6=
      if Supported (Ideal.span {n}) then 1 else 0 := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [ite_eq_left hn,←map_pow]
    exact numerator_bad_sixth u a b r n hr hn
  · rw [ite_eq_right hn,numeratorBadTwist_zero_of_not_supported u a b r hr n hn]
    norm_num

end OpenAIReview.NativeRaySixth

#lint+ in OpenAIReview.NativeRaySixth

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty native ray sixth audit."
  logInfo m!"Native ray sixth audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-ray-sixth-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-native-ray-sixth-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual numeratorBadTwist sixth-power/order-six mask; actual canonical calibration, fixed physical ray, primaryCoefficient and original exclusion mask; all inputs including zero/nonunits. No sextic-rho/cusp or analytic Gaussian/source bridge"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
