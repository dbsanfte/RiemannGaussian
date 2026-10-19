/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCalibratedMatchingAudit
import OAI.NumberTheory.DirichletL.Detector.CubicGaussCRT
import OAI.NumberTheory.DirichletL.Detector.SpectralCoefficient
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual marked-prime incidence after physical matching

For the actual Eisenstein ideal row and `A=P^(6t+1)*B`, removing the matching
prime leaves `chi_A(m)*conj(chi_P(m))`, with the nonunit puncture included.
The varying prime character survives product reindexing. Same-product cross
terms cancel the common cofactor phase, retain its support mask, and retain
both actual Gauss constants and the calibration factor. The remaining prime
factor is nonconstant at every permitted odd-characteristic prime.

These are exact finite identities. They give no cancellation of a moving
annulus, mixed-moment estimate, zero-source theorem, or RH progress.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
set_option warningAsError true
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.MarkedIncidence
open OAI OAI.CanonicalRowCompletion OAI.ConcretePrimeRowBridge
open OAI.CompletedGauss OAI.ConcreteTraceCRT
open OAI.SevenEighths.ProbePhysical
open OpenAIReview.CoupledResidue OpenAIReview.CalibratedMatching
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The actual prime character times its conjugate is precisely its
nonunit support mask, not an everywhere-one phase. -/
theorem actual_prime_mul_star (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (m : O) :
    idealRowHom m (Ideal.span {p}) * star (idealRowHom m (Ideal.span {p})) =
      if m ∈ (Ideal.span {p} : Ideal O) then 0 else 1 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [idealRowHom_prime _ _ hg, MulChar.star_apply', MulChar.inv_apply_eq_inv']
  by_cases hm : m ∈ (Ideal.span {p} : Ideal O)
  · have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [hz, (actualSextic (Ideal.span {p}) hg).map_zero]
    simp [hm]
  · have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) m) := by
      apply isUnit_iff_ne_zero.mpr
      intro hz
      exact hm (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hn := (MulChar.apply_ne_zero_iff (χ := actualSextic (Ideal.span {p}) hg)).mpr hu
    simp [hm, hn]

/-- Exact actual row after matching, including every nonunit. The extra
prime character depends on the numerator even when the product `A` is fixed. -/
theorem actual_punctured_cofactor_eq (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (A B : Ideal O)
    (hA : A = (Ideal.span {p})^(6*t+1)*B) (m : O) :
    (if m ∈ (Ideal.span {p} : Ideal O) then 0 else idealRowHom m B) =
      idealRowHom m A * star (idealRowHom m (Ideal.span {p})) := by
  rw [hA, map_mul, actual_matching_valuation p hg t]
  have hm := actual_prime_mul_star p hg m
  calc
    _ = (if m ∈ (Ideal.span {p} : Ideal O) then (0 : ℂ) else 1) *
        idealRowHom m B := by split_ifs <;> simp
    _ = (idealRowHom m (Ideal.span {p}) *
        star (idealRowHom m (Ideal.span {p}))) * idealRowHom m B := by rw [hm]
    _ = _ := by ring

/-- Same-product mixed rows retain both prime factors and the complete
common support mask `chi_A*conj(chi_A)`. No period average is taken. -/
theorem actual_same_product_cross (p q : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [(Ideal.span {q} : Ideal O).IsMaximal]
    (hgp : goodLambda ∉ Ideal.span {p}) (hgq : goodLambda ∉ Ideal.span {q})
    (t u : ℕ) (A B D : Ideal O)
    (hA : A = (Ideal.span {p})^(6*t+1)*B)
    (hA' : A = (Ideal.span {q})^(6*u+1)*D) (m : O) :
    (if m ∈ (Ideal.span {p} : Ideal O) then 0 else idealRowHom m B) *
      star (if m ∈ (Ideal.span {q} : Ideal O) then 0 else idealRowHom m D) =
      (idealRowHom m A * star (idealRowHom m A)) *
        (star (idealRowHom m (Ideal.span {p})) * idealRowHom m (Ideal.span {q})) := by
  rw [actual_punctured_cofactor_eq p hgp t A B hA m,
    actual_punctured_cofactor_eq q hgq u A D hA' m, star_mul, star_star]
  ring

/-- The actual Gauss constant, with its literal sign convention. -/
def matchingGaussConstant (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) : ℂ :=
  actualSextic (Ideal.span {p}) hg (-1) *
    gaussSum (actualSextic (Ideal.span {p}) hg) (OAI.CubicEisenstein.quotientTrace p hp)

/-- Physical matching with the calibration and genuine Gauss phase retained. -/
theorem calibrated_matching_reindexed (C : CalibrationData) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (B : Ideal O) (a m : O)
    (ha : (Ideal.span {a} : Ideal O) = (Ideal.span {p})^(6*t+1)*B) :
    calibratedNumerator C a m * sexticGauss p hp (-m) =
      matchingGaussConstant p hp hg * C.residueMonoid m *
        idealRowHom m (Ideal.span {a}) * star (idealRowHom m (Ideal.span {p})) := by
  rw [calibrated_matching_atom C p hp hg t B a m ha]
  have he := actual_punctured_cofactor_eq p hg t (Ideal.span {a}) B ha m
  change matchingGaussConstant p hp hg *
    (if m ∈ (Ideal.span {p} : Ideal O) then 0 else cofactorCharacter C B m) = _
  have hc : (if m ∈ (Ideal.span {p} : Ideal O) then (0 : ℂ) else cofactorCharacter C B m) =
      C.residueMonoid m * (if m ∈ (Ideal.span {p} : Ideal O) then 0 else idealRowHom m B) := by
    split_ifs <;> simp [cofactorCharacter]
  rw [hc, he]
  ring

/-- Same-product physical cross term before norms: both actual Gauss
constants, calibration, common support and varying prime factors survive. -/
theorem calibrated_same_product_cross (C : CalibrationData)
    (p q : O) (hp : p ≠ 0) (hq : q ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [(Ideal.span {q} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})] [Fintype (O ⧸ Ideal.span {q})]
    (hgp : goodLambda ∉ Ideal.span {p}) (hgq : goodLambda ∉ Ideal.span {q})
    (t u : ℕ) (B D : Ideal O) (a m : O)
    (ha : (Ideal.span {a} : Ideal O) = (Ideal.span {p})^(6*t+1)*B)
    (ha' : (Ideal.span {a} : Ideal O) = (Ideal.span {q})^(6*u+1)*D) :
    (calibratedNumerator C a m * sexticGauss p hp (-m)) *
      star (calibratedNumerator C a m * sexticGauss q hq (-m)) =
      (matchingGaussConstant p hp hgp * star (matchingGaussConstant q hq hgq)) *
        (C.residueMonoid m * star (C.residueMonoid m)) *
        (idealRowHom m (Ideal.span {a}) * star (idealRowHom m (Ideal.span {a}))) *
        (star (idealRowHom m (Ideal.span {p})) * idealRowHom m (Ideal.span {q})) := by
  rw [calibrated_matching_reindexed C p hp hgp t B a m ha,
    calibrated_matching_reindexed C q hq hgq u D a m ha']
  simp only [star_mul, star_star]
  ring

/-- A good odd-characteristic actual prime has a numerator unit where the
surviving conjugate prime factor differs from one. This is not a window claim. -/
theorem actual_prime_factor_varies (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ∃ m : O, m ∉ (Ideal.span {p} : Ideal O) ∧
      star (idealRowHom m (Ideal.span {p})) ≠ 1 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  have hchi := actual_character_nonprincipal p hg hc
  have hex : ∃ x : O ⧸ Ideal.span {p}, x ≠ 0 ∧
      actualSextic (Ideal.span {p}) hg x ≠ 1 := by
    by_contra h
    push Not at h
    apply hchi
    apply MulChar.ext'
    intro x
    by_cases hx : x = 0
    · rw [hx, (actualSextic (Ideal.span {p}) hg).map_zero,
        (1 : MulChar (O ⧸ Ideal.span {p}) ℂ).map_zero]
    · rw [h x hx]
      exact (MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)).symm
  obtain ⟨x, hx, hval⟩ := hex
  obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨m, ?_, ?_⟩
  · intro hmem
    exact hx (hm ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  · have hval' : idealRowHom m (Ideal.span {p}) ≠ 1 := by
      rwa [idealRowHom_prime _ _ hg, hm]
    intro he
    apply hval'
    have hstar := congrArg star he
    simpa only [star_star, star_one] using hstar

/-- The actual cubic CRT pair leaves a fourth-power sextic label after
primary reciprocity; the finite quadratic reciprocity sign squares away. -/
theorem actual_pair_square_eq_fourth (a b : O)
    (hpa : goodLambda^2 ∣ a-1) (hpb : goodLambda^2 ∣ b-1)
    (ha : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {a}))
    (hb : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {b})) :
    OAI.SevenEighths.ProbePhase.sexticPair a b ^ 2 =
      idealRowHom a (Ideal.span {b}) ^ 4 := by
  have hr := idealRowHom_primary_reciprocity a b hpa hpb ha hb
  change idealRowHom b (Ideal.span {a}) =
    OAI.SevenEighths.ProbePhase.reciprocitySign a b * idealRowHom a (Ideal.span {b}) at hr
  have hs := OAI.SevenEighths.ProbePhase.reciprocitySign_sq a b
    (OAI.CanonicalRowCompletion.supported_residue_odd a ha)
    (OAI.CanonicalRowCompletion.supported_residue_odd b hb)
  unfold OAI.SevenEighths.ProbePhase.sexticPair
  rw [hr]
  calc
    _ = OAI.SevenEighths.ProbePhase.reciprocitySign a b ^ 2 *
        idealRowHom a (Ideal.span {b}) ^ 4 := by ring
    _ = _ := by rw [hs, one_mul]

/-- Native squarefree Gauss coefficients retain the growing fourth-power
cofactor label, including its actual CRT factor and angular normalization. -/
theorem actual_squarefree_coefficient_product (I B : Ideal O)
    (hI : OAI.SevenEighths.CubicSieve.Admissible I)
    (hB : OAI.SevenEighths.CubicSieve.Admissible B)
    (hIB : OAI.SevenEighths.CubicSieve.Admissible (I*B))
    (hcop : IsCoprime I B)
    (hsI : OAI.CanonicalQuadraticSieve.Supported I)
    (hsB : OAI.CanonicalQuadraticSieve.Supported B) :
    squarefreeGaussCoefficient (I*B) =
      squarefreeGaussCoefficient I * squarefreeGaussCoefficient B *
        idealRowHom (OAI.CompletedGauss.primaryGenerator I) B ^ 4 := by
  have hp := actual_pair_square_eq_fourth
    (OAI.CompletedGauss.primaryGenerator I) (OAI.CompletedGauss.primaryGenerator B)
    (OAI.CompletedGauss.primaryGenerator_spec I hI.2).2
    (OAI.CompletedGauss.primaryGenerator_spec B hB.2).2
    ((OAI.CanonicalQuadraticSieve.supported_span_primaryGenerator_iff I).mpr hsI)
    ((OAI.CanonicalQuadraticSieve.supported_span_primaryGenerator_iff B).mpr hsB)
  rw [(OAI.CompletedGauss.primaryGenerator_spec B hB.2).1] at hp
  rw [squarefreeGaussCoefficient_eq (I*B) hIB.1 hIB.2,
    squarefreeGaussCoefficient_eq I hI.1 hI.2,
    squarefreeGaussCoefficient_eq B hB.1 hB.2,
    gaussTwo_coprime_product_sextic I B hI hB hIB hcop, hp,
    OAI.CompletedGauss.primaryGenerator_mul, angularFactor_mul, star_mul]
  ring

/-- The actual completed correction and physical reciprocity normalization
cancel only the finite cross sign. The fourth-power label survives.
Multiplying by the matching Gauss constant changes only the first bracket. -/
theorem physical_fourth_label_survives (I B : Ideal O)
    (hI : OAI.SevenEighths.CubicSieve.Admissible I)
    (hB : OAI.SevenEighths.CubicSieve.Admissible B)
    (hIB : OAI.SevenEighths.CubicSieve.Admissible (I*B))
    (hcop : IsCoprime I B)
    (hsI : OAI.CanonicalQuadraticSieve.Supported I)
    (hsB : OAI.CanonicalQuadraticSieve.Supported B) :
    squarefreeGaussCoefficient (I*B) *
      star (OAI.SevenEighths.ProbePhase.G (OAI.CompletedGauss.primaryGenerator (I*B))) *
      OAI.SevenEighths.ProbePhase.reciprocitySign
        (OAI.CompletedGauss.primaryGenerator (I*B)) (OAI.CompletedGauss.primaryGenerator I) =
      (squarefreeGaussCoefficient I *
        star (OAI.SevenEighths.ProbePhase.G (OAI.CompletedGauss.primaryGenerator I)) *
        OAI.SevenEighths.ProbePhase.reciprocitySign
          (OAI.CompletedGauss.primaryGenerator I) (OAI.CompletedGauss.primaryGenerator I)) *
      (squarefreeGaussCoefficient B *
        star (OAI.SevenEighths.ProbePhase.G (OAI.CompletedGauss.primaryGenerator B))) *
      idealRowHom (OAI.CompletedGauss.primaryGenerator I) B ^ 4 := by
  let a := OAI.CompletedGauss.primaryGenerator I
  let b := OAI.CompletedGauss.primaryGenerator B
  have ha := OAI.CanonicalRowCompletion.supported_residue_odd a
    ((OAI.CanonicalQuadraticSieve.supported_span_primaryGenerator_iff I).mpr hsI)
  have hb := OAI.CanonicalRowCompletion.supported_residue_odd b
    ((OAI.CanonicalQuadraticSieve.supported_span_primaryGenerator_iff B).mpr hsB)
  have hsign := OAI.SevenEighths.ProbePhase.reciprocitySign_sq a b ha hb
  rw [actual_squarefree_coefficient_product I B hI hB hIB hcop hsI hsB,
    OAI.CompletedGauss.primaryGenerator_mul]
  change (_ * _ * _) * star (OAI.SevenEighths.ProbePhase.G (a*b)) *
    OAI.SevenEighths.ProbePhase.reciprocitySign (a*b) a = _
  rw [OAI.SevenEighths.ProbePhase.G_mul a b ha hb,
    OAI.SevenEighths.ProbePhase.reciprocitySign_mul_left,
    OAI.SevenEighths.ProbePhase.reciprocitySign_symm b a]
  simp only [star_mul, OAI.SevenEighths.ProbePhase.reciprocitySign_star]
  calc
    _ = (squarefreeGaussCoefficient I * star (OAI.SevenEighths.ProbePhase.G a) *
        OAI.SevenEighths.ProbePhase.reciprocitySign a a) *
        (squarefreeGaussCoefficient B * star (OAI.SevenEighths.ProbePhase.G b)) *
        idealRowHom a B ^ 4 * OAI.SevenEighths.ProbePhase.reciprocitySign a b ^ 2 := by ring
    _ = _ := by rw [hsign, mul_one]

end OpenAIReview.MarkedIncidence

#lint+ in OpenAIReview.MarkedIncidence

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
  unless declarations>0 do throwError "Empty actual marked-incidence audit."
  logInfo m!"Actual marked-incidence audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-marked-correlation"
  IO.FS.writeFile ".lake/arithmetic-operator-marked-correlation/axioms.json"
    (Json.mkObj [("scope",toJson "actual zero-extended matched cofactor row, calibrated Gauss cross relation and nonconstant prime factor; no annular estimate or zero source"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
