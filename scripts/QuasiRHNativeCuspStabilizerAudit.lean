/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.GramJointFixed
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual sextic symbols on integral-cusp translations

Native numerator factorization, including its bad-place period72, makes
the actual symbol of each conjugated unipotent trivial at the actual
fixed native level. This is finite arithmetic, not automorphy, a cusp
residue computation, a source-allocation theorem, or a signed estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
noncomputable section
open scoped Classical MatrixGroups Matrix

namespace OpenAIReview.NativeCuspStabilizer
open OAI ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

/-- Congruence to one modulo72 gives the actual supported denominator. -/
theorem supported_of_one_mod_seventy_two (D : O) (h72 : (72:O)∣D-1) :
    Supported (Ideal.span {D}) := by
  have h36 : D-1∈(Ideal.span {(36:O)}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((show (36:O)∣72 from ⟨2,by norm_num⟩).trans h72)
  apply (CanonicalUnitEuler.supported_span_congruent_mod_thirty_six D 1 h36).mpr
  rw [Ideal.span_singleton_one,←Ideal.one_eq_top]
  refine ⟨one_ne_zero,?_⟩
  intro P hP
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP

/-- Arbitrary bad/nonunit numerators dividing D-1 have literal native symbol one. -/
theorem native_symbol_of_dvd_sub_one (D k : O) (h72 : (72:O)∣D-1)
    (hk : k∣D-1) : idealRowHom k (Ideal.span {D})=1 := by
  have hD := supported_of_one_mod_seventy_two D h72
  have hp : lambda^2∣D-1 := lambda_sq_dvd_three.trans
    ((show (3:O)∣72 from ⟨24,by norm_num⟩).trans h72)
  by_cases hk0 : k=0
  · have hD1 : D=1 := by simpa [hk0,sub_eq_zero] using hk
    simp [hD1,Ideal.span_singleton_one,←Ideal.one_eq_top]
  obtain ⟨u,a,b,r,hr,hpr,hkform⟩ := exists_supported_numerator_factorization k hk0
  have hrk : r∣k := ⟨u.val*lambda^a*(2:O)^b,by rw [hkform];ring⟩
  have hmov : movingNumeratorRow r hr D=1 := by
    change idealRowHom D (Ideal.span {r})=1
    rw [idealRowHom_congr_mod _ D 1 (Ideal.mem_span_singleton.mpr (hrk.trans hk)),
      idealRowHom_one_supported _ hr]
  have hbad : numeratorBadTwist u a b r hr D=1 := by
    rw [numeratorBadTwist_periodic u a b r hr D 1 (Ideal.mem_span_singleton.mpr h72),map_one]
  rw [hkform,idealRowHom_factor_numerator u a b r D hr hpr hD hp,hbad,hmov,one_mul]

/-- Exact native multiplier on a conjugated integral-cusp translation. -/
theorem native_conjugate_unipotent_symbol (a c t : O) (ht : (72:O)∣t) :
    idealRowHom (-c^2*t) (Ideal.span {1+a*c*t})=1 := by
  have h72 : (72:O)∣(1+a*c*t)-1 := by
    convert dvd_mul_of_dvd_right ht (a*c) using 1
    ring
  have hc : c∣(1+a*c*t)-1 := ⟨a*t,by ring⟩
  have htD : t∣(1+a*c*t)-1 := ⟨a*c,by ring⟩
  have hm : (-1:O)∣(1+a*c*t)-1 := isUnit_neg_one.dvd
  have hD := supported_of_one_mod_seventy_two (1+a*c*t) h72
  rw [show -c^2*t=(-1:O)*c^2*t by ring,
    idealRowHom_argument_mul,idealRowHom_argument_mul,
    idealRowHom_argument_pow c 2 _ hD,
    native_symbol_of_dvd_sub_one _ _ h72 hm,
    native_symbol_of_dvd_sub_one _ _ h72 hc,
    native_symbol_of_dvd_sub_one _ _ h72 htD]
  norm_num

/-- The actual fixed native coefficient modulus enforces the required period72. -/
theorem native_level_conjugate_unipotent_symbol (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (a c t : O)
    (ht : t∈SevenEighths.ProbeGramCommon.jointFixedModulus S hS) :
    idealRowHom (-c^2*t) (Ideal.span {1+a*c*t})=1 := by
  exact native_conjugate_unipotent_symbol a c t
    (Ideal.mem_span_singleton.mp (Ideal.mul_le_right ht))

/-- The actual determinant-one matrix of an integral-cusp translation. -/
def cuspTranslationMatrix (a c t : O) : SL(2,O) :=
  ⟨!![1-a*c*t,a^2*t;-c^2*t,1+a*c*t],by
    rw [Matrix.det_fin_two]
    change (1-a*c*t)*(1+a*c*t)-(a^2*t)*(-c^2*t)=1
    ring⟩

/-- Literal bottom entries of the actual cusp translation matrix have native symbol one. -/
theorem actual_matrix_native_symbol (a c : O) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (t : O)
    (ht : t∈SevenEighths.ProbeGramCommon.jointFixedModulus S hS) :
    idealRowHom (cuspTranslationMatrix a c t 1 0)
      (Ideal.span {cuspTranslationMatrix a c t 1 1})=1 := by
  simp only [cuspTranslationMatrix,
    Matrix.SpecialLinearGroup.coe_mk,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact native_level_conjugate_unipotent_symbol S hS a c t ht

end OpenAIReview.NativeCuspStabilizer

#lint+ in OpenAIReview.NativeCuspStabilizer

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
  unless declarations>0 do throwError "Empty native cusp stabilizer audit."
  logInfo m!"Native cusp stabilizer audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-cusp-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-native-cusp-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual native sextic symbol one on literal determinant-one cusp translation matrices at jointFixedModulus; conjugation interpretation and automorphy/residue/source are paper-level"),
      ("namespaceLinters",toJson (15:Nat)),("allLocalDeclarationsByModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
