/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler
import OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual principal-source local coefficients for the Patterson cubic model

All local blocks below are literal sums of `bareIdealHighSummand` at a genuine
Eisenstein prime. Density normalization leaves the exact zero, squarefree,
and positive even-cube coefficients. The Patterson ratio retains the native
ramified ray and has its actual ideal-norm decay. No global continuation,
complete model/source subtraction, or new zero exclusion is claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.PattersonModelLocal
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcreteTraceCRT
  OAI.ConcretePrimeRowBridge OAI.CubicEisenstein OAI.CubicJacobiGlobal
  OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeEuler
  OAI.SevenEighths.ProbeRow OAI.SevenEighths.CubicSieve
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The same ramified ray multiplying the paper-oriented cubic Gauss sum. -/
def nativeRay (I : Ideal O) : ℂ :=
  eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I))

/-- The model-to-native coefficient ratio, with the global Patterson constant omitted. -/
def pattersonRatio (I : Ideal O) (hI : Admissible I) : ℂ :=
  nativeRay I * (Real.rpow (Ideal.absNorm I : ℝ) (-(1/6 : ℝ)) : ℂ) / gaussTwo I hI.2

/-- The literal ratio has precisely the ideal-norm sixth-root decay. -/
theorem pattersonRatio_norm (I : Ideal O) (hI : Admissible I) :
    ‖pattersonRatio I hI‖ = (Ideal.absNorm I : ℝ) ^ (-(1/6 : ℝ)) := by
  rw [pattersonRatio, norm_div, norm_mul, gaussTwo_norm_one I hI, div_one]
  have hr : ‖nativeRay I‖ = 1 :=
    paperLambda_symbol_norm _ (primaryGenerator_spec I hI.2).2
  rw [hr, one_mul, Complex.norm_real, Real.norm_eq_abs]
  change |Real.rpow (Ideal.absNorm I : ℝ) (-(1/6 : ℝ))| =
    Real.rpow (Ideal.absNorm I : ℝ) (-(1/6 : ℝ))
  exact abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) _)

/-- Multiplication by the ratio replaces the actual cubic Gauss coefficient by its ray model. -/
theorem pattersonRatio_mul_gaussTwo (I : Ideal O) (hI : Admissible I) :
    pattersonRatio I hI * gaussTwo I hI.2 =
      nativeRay I * (Real.rpow (Ideal.absNorm I : ℝ) (-(1/6 : ℝ)) : ℂ) := by
  have hn : gaussTwo I hI.2 ≠ 0 := by
    intro hz
    have h := gaussTwo_norm_one I hI
    rw [hz, norm_zero] at h
    exact zero_ne_one h
  exact div_mul_cancel₀ _ hn

/-- The literal same-weight source coefficient after replacing only the cubic Gauss factor. -/
def modelSourceCoefficient (η : OAI.SevenEighths.HeckeFamily.Character)
    (I : Ideal O) (A s : O) (hA : A ≠ 0) (H : O) : ℂ :=
  targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
    (nativeRay I * (Real.rpow (Ideal.absNorm I : ℝ) (-(1/6 : ℝ)) : ℂ) *
      star (OAI.SevenEighths.ProbePhase.G A) * reciprocityCoefficient A s hA H)

/-- No calibration, congruence, character or completed-index factor is changed by this exact ratio. -/
theorem modelSourceCoefficient_eq_ratio (η : OAI.SevenEighths.HeckeFamily.Character)
    (I : Ideal O) (hI : Admissible I) (A s : O) (hA : A ≠ 0) (H : O) :
    modelSourceCoefficient η I A s hA H =
      pattersonRatio I hI * bareSourceCoefficient η I hI.2 A s hA H := by
  unfold modelSourceCoefficient bareSourceCoefficient correctedFiniteCoefficient
  rw [show pattersonRatio I hI *
      (targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
        (gaussTwo I hI.2 * star (OAI.SevenEighths.ProbePhase.G A) *
          reciprocityCoefficient A s hA H)) =
      targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
        ((pattersonRatio I hI * gaussTwo I hI.2) *
          star (OAI.SevenEighths.ProbePhase.G A) * reciprocityCoefficient A s hA H) by ring,
    pattersonRatio_mul_gaussTwo I hI]

/-- Literal local principal-frequency block, retaining both physical and sixth-frequency indices. -/
def actualBlock (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (x w z : ℂ) (e l : ℕ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ,
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m)

/-- The two density factors at one actual prime. -/
def density (p : O) (w z : ℂ) : ℂ :=
  (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w)) *
    (1 - coordV (Ideal.absNorm (Ideal.span {p})) z)

/-- The exact normalized zero-index coefficient at one actual prime. -/
def zeroCoefficient (p : O) (w z : ℂ) : ℂ :=
  1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w) *
    coordV (Ideal.absNorm (Ideal.span {p})) z

/-- The exact normalized squarefree coefficient, with the target character retained. -/
def squarefreeCoefficient (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (x w z : ℂ) : ℂ :=
  -targetMonoid η p * (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x) *
    (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w)) *
    (1 - coordV (Ideal.absNorm (Ideal.span {p})) z +
      ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1) *
        (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w) *
          coordV (Ideal.absNorm (Ideal.span {p})) z)

/-- The exact normalized positive even-cube coefficient. -/
def cubeCoefficient (p : O) (w z : ℂ) : ℂ :=
  (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w)) *
    (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ +
      (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w) *
        (1 - coordV (Ideal.absNorm (Ideal.span {p})) z))

/-- The actual geometric ratio for pairs of native cube orders. -/
def nativeCubeRatio (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (x z : ℂ) : ℂ :=
  coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z

section Prime
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : goodLambda^2 ∣ p-1) (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {p}))

include hp hg hc hprimary hs

private theorem block_source (η : OAI.SevenEighths.HeckeFamily.Character)
    (x w z : ℂ) (e l : ℕ) (he : e ≤ 1) :
    actualBlock η p x w z e l =
      ∑' k : ℕ, ∑' m : ℕ,
        sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold actualBlock
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hc hprimary hs e l k m he x w z

private theorem block_positive (η : OAI.SevenEighths.HeckeFamily.Character)
    (x w z : ℂ) (e l : ℕ) (he : e ≤ 1) (ht : e+3*l ≠ 0) :
    actualBlock η p x w z e l =
      principalInner p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) e l := by
  rw [block_source p hp hg hc hprimary hs η x w z e l he]
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact sourcePrincipalTerm_pos p hp hg _ _ x w z e l k m ht

/-- The actual zero-index block has precisely the two known density denominators. -/
theorem actualBlock_zero (η : OAI.SevenEighths.HeckeFamily.Character) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖ < 1)
    (hW : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w)‖ < 1) :
    density p w z * actualBlock η p x w z 0 0 = zeroCoefficient p w z := by
  rw [block_source p hp hg hc hprimary hs η x w z 0 0 (by decide)]
  simp_rw [sourcePrincipalTerm_zero]
  change density p w z * zeroIndexSeries p (actualSextic (Ideal.span {p}) hg)
    ((Ideal.absNorm (Ideal.span {p}) : ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) = _
  rw [zeroIndexSeries_eq p hp _ _ _ hW hV]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  unfold density zeroCoefficient
  field_simp [hv, hw]
  ring

/-- Exact actual squarefree coefficients after multiplying out the density factors. -/
theorem actualBlock_squarefree (η : OAI.SevenEighths.HeckeFamily.Character)
    (x w z : ℂ) (r : ℕ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖ < 1) :
    density p w z * actualBlock η p x w z 1 (2*r) =
      squarefreeCoefficient η p x w z * nativeCubeRatio η p x z ^ r := by
  rw [block_positive p hp hg hc hprimary hs η x w z 1 (2*r) (by decide) (by omega),
    principalInner_squarefree p hp hg hc _ _ _ _ _ hV r]
  have hq : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr : evenRatio (Ideal.absNorm (Ideal.span {p}) : ℂ) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) = nativeCubeRatio η p x z := by
    simpa only [nativeCubeRatio, Complex.ofReal_natCast] using
      evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}) : ℝ) hq (actualACube η p) x z
  rw [hr]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  unfold density squarefreeCoefficient nativeCubeRatio
  field_simp [hv]
  ring

/-- Exact actual coefficients of every positive even cube order. -/
theorem actualBlock_cube (η : OAI.SevenEighths.HeckeFamily.Character)
    (x w z : ℂ) (r : ℕ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖ < 1) :
    density p w z * actualBlock η p x w z 0 (2*r+2) =
      cubeCoefficient p w z * nativeCubeRatio η p x z ^ (r+1) := by
  rw [block_positive p hp hg hc hprimary hs η x w z 0 (2*r+2) (by decide) (by omega),
    principalInner_even p hp hg hc _ _ _ _ _ hV r]
  have hq : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr : evenRatio (Ideal.absNorm (Ideal.span {p}) : ℂ) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) = nativeCubeRatio η p x z := by
    simpa only [nativeCubeRatio, Complex.ofReal_natCast] using
      evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}) : ℝ) hq (actualACube η p) x z
  rw [hr]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  unfold density cubeCoefficient nativeCubeRatio
  field_simp [hv]
  ring

/-- All odd cube orders vanish in the actual principal-frequency block. -/
theorem actualBlock_odd (η : OAI.SevenEighths.HeckeFamily.Character)
    (x w z : ℂ) (e r : ℕ) (he : e ≤ 1) :
    actualBlock η p x w z e (2*r+1) = 0 := by
  rw [block_positive p hp hg hc hprimary hs η x w z e (2*r+1) he (by omega)]
  exact principalInner_odd p hp hg hc _ _ _ _ _ e r he

end Prime
/-- At the actual source residue the sixth-frequency local coordinate is the inverse norm. -/
theorem source_coordV (p : O) :
    coordV (Ideal.absNorm (Ideal.span {p})) (1/6) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  unfold coordV
  rw [show -(6 : ℂ)*(1/6 : ℂ) = -1 by ring, Complex.cpow_neg_one,
    Complex.ofReal_natCast]

/-- The known two density residues leave the exact positive zero-index factor. -/
theorem zeroCoefficient_at_source (p : O) :
    zeroCoefficient p 1 (1/6) = 1 - ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹)^2 := by
  unfold zeroCoefficient
  rw [source_coordV]
  simp only [Complex.cpow_neg_one]
  ring

/-- The actual squarefree source residue retains its target character and exact Euler-totient factor. -/
theorem squarefreeCoefficient_at_source
    (η : OAI.SevenEighths.HeckeFamily.Character) (p : O) (hp : p ≠ 0) (x : ℂ) :
    squarefreeCoefficient η p x 1 (1/6) =
      (-targetMonoid η p * (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x) *
        (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹)) * zeroCoefficient p 1 (1/6) := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp)
  unfold squarefreeCoefficient
  rw [source_coordV, zeroCoefficient_at_source]
  simp only [Complex.cpow_neg_one]
  field_simp
  ring

/-- The actual even-cube residue has the same exact totient factor. -/
theorem cubeCoefficient_at_source (p : O) (hp : p ≠ 0) :
    cubeCoefficient p 1 (1/6) =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * zeroCoefficient p 1 (1/6) := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp)
  unfold cubeCoefficient
  rw [source_coordV, zeroCoefficient_at_source]
  simp only [Complex.cpow_neg_one]
  field_simp
  ring

/-- Every retained pair of cube orders has its exact norm exponent at the source residue. -/
theorem nativeCubeRatio_at_source (η : OAI.SevenEighths.HeckeFamily.Character)
    (p : O) (x : ℂ) :
    nativeCubeRatio η p x (1/6) = actualAPhase η p *
      (Ideal.absNorm (Ideal.span {p}) : ℂ)^(3-6*x) := by
  unfold nativeCubeRatio coordR
  rw [actualACube_sq]
  simp only [Complex.ofReal_natCast]
  congr 1
  ring

/-- The Euler-totient factor at every nonzero actual ideal has norm at most one. -/
theorem source_totient_norm (I : Ideal O) (hI : I ≠ 0) :
    ‖1 - (Ideal.absNorm I : ℂ)⁻¹‖ ≤ 1 := by
  have hq : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hi : 0 ≤ (Ideal.absNorm I : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hi1 : (Ideal.absNorm I : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- The actual modeled squarefree residue gains exactly one sixth in its summable norm exponent. -/
theorem modeled_squarefree_residue_norm
    (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (hI : Admissible (Ideal.span {p})) (x : ℂ) :
    ‖pattersonRatio (Ideal.span {p}) hI *
      (-targetMonoid η p * (Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x) *
        (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹))‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)^(-(x.re+1/6)) := by
  have hI0 : (Ideal.span {p} : Ideal O) ≠ 0 := primaryGenerator_ne_zero_ideal _ hI.2
  have hq : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [norm_mul, norm_mul, norm_mul, norm_neg, pattersonRatio_norm,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp only [Complex.neg_re]
  calc
    _ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)^(-(1/6 : ℝ)) *
        (1 * (Ideal.absNorm (Ideal.span {p}) : ℝ)^(-x.re) * 1) := by
      gcongr
      · exact targetMonoid_norm_le_one η p
      · exact source_totient_norm _ hI0
    _ = _ := by
      simp only [one_mul, mul_one]
      rw [← Real.rpow_add hq]
      congr 1
      ring

/-- Every actual retained cube pair has its summable source-residue norm exponent. -/
theorem nativeCubeRatio_source_norm
    (η : OAI.SevenEighths.HeckeFamily.Character) (p : O) (hp : p ≠ 0) (x : ℂ) :
    ‖nativeCubeRatio η p x (1/6)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)^(3-6*x.re) := by
  have hq : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  rw [nativeCubeRatio_at_source, norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have hr : (3-6*x : ℂ).re = 3-6*x.re := by simp
  rw [hr]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (le_of_lt hq) _)
    (actualAPhase_norm_le_one η p)

end OpenAIReview.PattersonModelLocal

#lint+ in OpenAIReview.PattersonModelLocal

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty Patterson model local audit."
  logInfo m!"Patterson model local audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-joint-gauss-correlation"
  IO.FS.writeFile ".lake/arithmetic-operator-joint-gauss-correlation/axioms.json"
    (Json.mkObj [("scope",toJson "actual Patterson ratio and native principal-source local coefficients; no global continuation or new zero exclusion"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
