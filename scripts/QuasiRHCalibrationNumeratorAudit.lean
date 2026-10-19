/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.LowRowMellin
import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Canonical calibration characters and fixed numerator transfer

The actual choose-based localCalibration is not assumed equal to the cubic
witness used to prove existence. At a good prime it is a nonzero power of the
actual canonical sextic character. This is finite algebra, not a mean estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.CalibrationNumerator
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.CanonicalRowCompletion
  OAI.SevenEighths.ProbePhysical OAI.ConcreteTraceCRT OAI.ConcretePrimeRowBridge
  OAI.CanonicalQuadraticSieve
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Actual good-prime sextic order, transported through the injective complex embedding. -/
theorem actualSextic_order (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (hc : ringChar (O ⧸ P)≠2) : orderOf (actualSextic P hg)=6 := by
  let f : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hf : Function.Injective f := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun χ : MulChar (O ⧸ P) ℂ => χ t) h
  change orderOf (f (sexticChar P hg))=6
  rw [orderOf_injective f hf,sexticChar_order P hg hc]

/-- Every actual choose-based good-prime calibration is a canonical sextic power.
The exponent is fixed by the calibration prime and lies between one and five. -/
theorem localCalibration_eq_power (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (hc : ringChar (O ⧸ P)≠2) :
    ∃ j : ℕ, 0<j ∧ j<6 ∧ localCalibration P=(actualSextic P hg)^j := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨g,hggen⟩ := IsCyclic.exists_generator (α := (O ⧸ P)ˣ)
  let ev : MulChar (O ⧸ P) ℂ →* ℂ := {
    toFun := fun χ => χ (g : O ⧸ P)
    map_one' := by simp
    map_mul' := by intro χ ψ; simp }
  have hev : Function.Injective ev := by
    intro χ ψ h
    exact (MulChar.eq_iff hggen χ ψ).mpr h
  have hp : IsPrimitiveRoot (actualSextic P hg (g : O ⧸ P)) 6 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    change orderOf (ev (actualSextic P hg))=6
    rw [orderOf_injective ev hev,actualSextic_order P hg hc]
  obtain ⟨j,hj,hval⟩ := MulChar.exists_apply_eq_pow (localCalibration_pow_six P) hp g.ne_zero
  have heq : localCalibration P=(actualSextic P hg)^j := by
    apply (MulChar.eq_iff hggen _ _).mpr
    simpa only [MulChar.pow_apply_coe] using hval
  refine ⟨j,?_,hj,heq⟩
  by_contra h
  have hj0 : j=0 := by omega
  exact localCalibration_nonprincipal P (by simpa [hj0] using heq)

/-- Literal evaluation of native CRT calibration, including every nonunit zero. -/
theorem calibrationFromPrimes_residue_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (a : O) :
    (calibrationFromPrimes P hcop).residueMonoid a =
      ∏ i, localCalibration (P i) (Ideal.Quotient.mk (P i) a) := by
  change (∏ i, localCalibration (P i)
    ((IdealGaussCRT.quotientProdEquivPi P hcop)
      ((Ideal.quotEquivOfEq (span_finitePrimeModulus P))
        (Ideal.Quotient.mk _ a)) i)) = _
  simp only [Ideal.quotEquivOfEq_mk,IdealGaussCRT.quotientProdEquivPi_mk]

/-- Actual calibrationForSet uses the literal product of its local characters. -/
theorem calibrationForSet_residue_product (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (a : O) :
    (calibrationForSet S hS).residueMonoid a =
      ∏ P : S, @localCalibration P.val (hS P.val P.property) (Ideal.Quotient.mk P.val a) := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  exact calibrationFromPrimes_residue_product (fun P : S=>P.val) _ a

/-- A native local calibration factor becomes an actual fixed numerator power.
The physical modulus is supported and primary, but need not be squarefree.
The coprimality condition is exactly the retained calibration exclusion. -/
theorem localCalibration_gauss_transfer (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hp : lambda^2∣p-1)
    (hsp : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {p})) :
    ∃ j : ℕ, 0<j ∧ j<6 ∧
      ∀ (s : O) (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s})),
        lambda^2∣s-1 → IsCoprime p s → ∀ m : O,
          idealRowHom p (Ideal.span {s}) /
            localCalibration (Ideal.span {p}) (Ideal.Quotient.mk _ s) *
              sexticGauss s (supportedElement_ne_zero s hs) (-m) =
          (sexticReciprocityPhase p s ^ j)⁻¹ *
            sexticGauss s (supportedElement_ne_zero s hs) (-(p^(j-1)*m)) := by
  obtain ⟨j,hj,hj6,hcal⟩ := localCalibration_eq_power (Ideal.span {p}) hg hc
  refine ⟨j,hj,hj6,?_⟩
  intro s hs hps hcop m
  have hvalue := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ s)) hcal
  rw [MulChar.pow_apply' _ (by omega : j≠0)] at hvalue
  rw [← idealRowHom_prime s (Ideal.span {p}) hg,
    idealRowHom_primary_reciprocity p s hp hps hsp hs] at hvalue
  have hχ6 : idealRowHom p (Ideal.span {s})^6=1 := by
    have he := idealRowHom_sixth_mask p (Ideal.span {s}) hs
    rw [idealRowHom_argument_pow _ _ _ hs,
      ite_eq_left ((Ideal.isCoprime_span_singleton_iff s p).mpr hcop.symm)] at he
    exact he
  have hχ : idealRowHom p (Ideal.span {s})≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (6:ℕ)≠0)] at hχ6
    exact zero_ne_one hχ6
  have hR2 : sexticReciprocityPhase p s ^ 2=1 := by
    unfold sexticReciprocityPhase
    exact_mod_cast OAI.QuadraticAllOddCRT.quadraticRaySign_sq _ _
      (supported_residue_odd p hsp) (supported_residue_odd s hs)
  have hR : sexticReciprocityPhase p s≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hR2
    exact zero_ne_one hR2
  rw [hvalue,show -(p^(j-1)*m)=p^(j-1)*(-m) by ring,
    sexticGauss_unit_scale s hs (p^(j-1)) (-m) hcop.pow_left,
    idealRowHom_argument_pow _ _ _ hs]
  have hjdec : j-1+1=j := Nat.sub_add_cancel hj
  rw [← hjdec,mul_pow,pow_succ]
  field_simp
  rw [Nat.add_sub_cancel,pow_succ]
  ring

/-- Exact first numerator transfer for literal lowArithmeticCoefficient and
canonical calibrationForSet. Its ORIGINAL exclusion mask is retained, and
the remaining calibration denominator is not silently replaced by a bad-6 ray. -/
theorem lowArithmeticCoefficient_generator_transfer
    (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (s : {I : Ideal O // OAI.CanonicalQuadraticSieve.Supported I}) (m : O) :
    let C := calibrationForSet S hS
    let a := primaryGenerator s.val
    let ha := supported_primaryGenerator_ne_zero s.val s.property
    lowArithmeticCoefficient C s * sexticGauss a ha (-m) =
      if ∀ P∈S, ¬P∣s.val then
        (C.tau*C.residueMonoid a)⁻¹ * sexticGauss a ha (-(C.generator^5*m))
      else 0 := by
  dsimp only
  let C := calibrationForSet S hS
  let a := primaryGenerator s.val
  have ha := supported_primaryGenerator_ne_zero s.val s.property
  have has := (supported_span_primaryGenerator_iff s.val).mpr s.property
  have hspan : Ideal.span {a}=s.val := (primaryGenerator_spec s.val ha).1
  change lowArithmeticCoefficient C s * sexticGauss a ha (-m) = _
  unfold lowArithmeticCoefficient
  rw [calibrationForSet_excluded]
  by_cases hm : ∀ P∈S, ¬P∣s.val
  · rw [ite_eq_left hm,ite_eq_left hm]
    have hcop : IsCoprime C.generator a := by
      apply calibrationForSet_coprime_of_excluded S hS a
      simpa only [hspan] using hm
    have h6 : idealRowHom C.generator (Ideal.span {a})^6=1 := by
      have he := idealRowHom_sixth_mask C.generator (Ideal.span {a}) has
      rw [idealRowHom_argument_pow _ _ _ has,
        ite_eq_left ((Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm)] at he
      exact he
    have hinv : (idealRowHom C.generator (Ideal.span {a})^5)⁻¹ =
        idealRowHom C.generator (Ideal.span {a}) := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [← pow_succ] using h6
    rw [show -(C.generator^5*m)=C.generator^5*(-m) by ring,
      sexticGauss_unit_scale a has (C.generator^5) (-m) hcop.pow_left,
      idealRowHom_argument_pow _ _ _ has,hinv,← hspan]
    ring
  · rw [ite_eq_right hm,ite_eq_right hm,zero_mul]

end OpenAIReview.CalibrationNumerator

#lint+ in OpenAIReview.CalibrationNumerator

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
  unless declarations>0 do throwError "Empty calibration-numerator audit."
  logInfo m!"Calibration-numerator audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-calibration-numerator-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-calibration-numerator-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual choose-based local sextic power; literal canonical CRT residue product; local fixed numerator transfer for all supported physical powers; original masked lowArithmeticCoefficient generator transfer. Global good/bad-six assembly and finite-ray expansion remain paper-level; no mean/source estimate."),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
