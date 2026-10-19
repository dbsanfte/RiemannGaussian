/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.PrincipalProduct
import OAI.NumberTheory.DirichletL.Hecke.Reciprocal
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Coprime source correction and conditional pole gate

The local correction uses actual ideal-character and actual angular/character cube
phases at genuine prime ideals. Its defect is absolutely summable and its product
is nonzero. The source-identification and local normal-convergence bridges remain
explicit hypotheses in the final reciprocal-Hecke pole transfer. No literal detector
holomorphy theorem or independent arithmetic saving is claimed.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical Topology
namespace OpenAIReview.CoprimePoleGate
open OAI OAI.ActualEisensteinCubic OAI.ConcretePrimeRowBridge
  OAI.CompletedGauss OAI.SmoothMobiusCorrection
  OAI.SevenEighths OAI.SevenEighths.ProbeEuler
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Actual primes in the supported native family, with the small excluded norms removed. -/
abbrev GoodPrime := {P : PrimeIdeal // CanonicalQuadraticSieve.Supported P.val ∧ 7 ≤ Ideal.absNorm P.val}

/-- Actual reciprocal-target prime coordinate. -/
def nativeDelta (η : HeckeFamily.Character) (P : PrimeIdeal) (x : ℂ) : ℂ :=
  HeckeFamily.idealCoeff η P.val * (Ideal.absNorm P.val : ℂ)^(-x)

/-- Actual even-cube geometric coordinate at the two source density residues. -/
def nativeCube (η : HeckeFamily.Character) (P : PrimeIdeal) (x : ℂ) : ℂ :=
  coordR (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val)) x (1/6)

/-- The exact disjoint/full principal-source Euler ratio, specialized to the density residues. -/
def localCorrection (η : HeckeFamily.Character) (P : PrimeIdeal) (x : ℂ) : ℂ :=
  let s : ℂ := (Ideal.absNorm P.val : ℂ)⁻¹
  1+s*(nativeDelta η P x-nativeCube η P x)*(1-s)^2 /
    ((1-s^2)*(1-(1-s)*nativeDelta η P x-s*nativeCube η P x))

private theorem ratio_bound (s : ℝ) (δ R : ℂ) (hs0 : 0 ≤ s) (hs : s ≤ 1/7)
    (hd : ‖δ‖ ≤ 1/4) (hr : ‖R‖ ≤ 1/49) :
    ‖(s:ℂ)*(δ-R)*(1-(s:ℂ))^2 /
      ((1-(s:ℂ)^2)*(1-(1-(s:ℂ))*δ-(s:ℂ)*R))‖ ≤
      (3/2:ℝ)*s*(‖δ‖+‖R‖) := by
  have ht0 : 0 ≤ 1-s := by linarith
  have ht1 : 1-s ≤ 1 := by linarith
  have hs2 : s^2 ≤ 1/49 := by nlinarith
  have hb0 : 0 ≤ 1-s^2 := by linarith
  have hsn : ‖(s:ℂ)‖ = s := by simp [abs_of_nonneg hs0]
  have htn : ‖1-(s:ℂ)‖ = 1-s := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0]
  have hbn : ‖1-(s:ℂ)^2‖ = 1-s^2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
  have hsum : ‖(1-(s:ℂ))*δ+(s:ℂ)*R‖ ≤ 1/4+1/343 := by
    calc
      _ ≤ (1-s)*‖δ‖+s*‖R‖ := by simpa only [norm_mul, hsn, htn] using norm_add_le ((1-(s:ℂ))*δ) ((s:ℂ)*R)
      _ ≤ 1/4+1/343 := by
        have h1 : (1-s)*‖δ‖ ≤ 1/4 := by nlinarith [norm_nonneg δ]
        have h2 : s*‖R‖ ≤ 1/343 := by nlinarith [norm_nonneg R]
        linarith
  have hT : 3/4-1/343 ≤ ‖1-(1-(s:ℂ))*δ-(s:ℂ)*R‖ := by
    have h := norm_sub_norm_le (1:ℂ) ((1-(s:ℂ))*δ+(s:ℂ)*R)
    rw [norm_one] at h
    have he : 1-((1-(s:ℂ))*δ+(s:ℂ)*R) = 1-(1-(s:ℂ))*δ-(s:ℂ)*R := by ring
    rw [he] at h
    linarith
  have hden : (2/3:ℝ) ≤ ‖(1-(s:ℂ)^2)*(1-(1-(s:ℂ))*δ-(s:ℂ)*R)‖ := by
    rw [norm_mul, hbn]
    have h1 : (48/49:ℝ) ≤ 1-s^2 := by linarith
    have h2 : (48/49:ℝ)*(3/4-1/343) ≤ (1-s^2)*‖1-(1-(s:ℂ))*δ-(s:ℂ)*R‖ := by
      exact mul_le_mul h1 hT (by norm_num) hb0
    norm_num at h2 ⊢
    linarith
  have hnum : ‖(s:ℂ)*(δ-R)*(1-(s:ℂ))^2‖ ≤ s*(‖δ‖+‖R‖) := by
    rw [norm_mul, norm_mul, norm_pow, hsn, htn]
    have hn : ‖δ-R‖ ≤ ‖δ‖+‖R‖ := norm_sub_le δ R
    have ht : (1-s)^2 ≤ 1 := by nlinarith
    calc
      _ ≤ s*(‖δ‖+‖R‖)*1 := by gcongr
      _ = _ := by ring
  rw [norm_div]
  calc
    _ ≤ (s*(‖δ‖+‖R‖))/(2/3:ℝ) := div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ = _ := by ring

/-- The actual target prime coordinate is bounded by its native norm power. -/
theorem nativeDelta_norm (η : HeckeFamily.Character) (P : PrimeIdeal) (x : ℂ) :
    ‖nativeDelta η P x‖ ≤ (Ideal.absNorm P.val : ℝ)^(-x.re) := by
  have hq := SmoothMobiusCorrection.prime_norm_pos P
  unfold nativeDelta
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp only [Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hq.le _) (HeckeFamily.idealCoeff_norm_le_one η _)

/-- The actual cube coordinate has its exact source norm exponent bound. -/
theorem nativeCube_norm (η : HeckeFamily.Character) (P : PrimeIdeal) (x : ℂ) :
    ‖nativeCube η P x‖ ≤ (Ideal.absNorm P.val : ℝ)^(3-6*x.re) := by
  have hq := SmoothMobiusCorrection.prime_norm_pos P
  unfold nativeCube coordR
  rw [show (4-6*x-6*(1/6) : ℂ) = 3-6*x by ring, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have he : (3-6*x : ℂ).re = 3-6*x.re := by simp
  rw [he]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hq.le _) (actualAPhase_norm_le_one η _)

private theorem power_caps (q σ : ℝ) (hq : 7 ≤ q) (hσ : 5/6 ≤ σ) :
    q^(-σ) ≤ 1/4 ∧ q^(3-6*σ) ≤ q^(-2:ℝ) ∧ q^(-2:ℝ) ≤ 1/49 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have h6 : q^(-(5/6:ℝ)) ≤ 1/4 := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hq0.le _) (by norm_num : (0:ℝ)≤1/4) (by norm_num : (0:ℝ)<6)).mp
    rw [← Real.rpow_mul hq0.le]
    have he : (-(5/6:ℝ))*6 = -5 := by ring
    rw [he, Real.rpow_neg hq0.le, show (5:ℝ)=(5:ℕ) by norm_num, Real.rpow_natCast]
    norm_num only [Real.rpow_natCast, one_div, inv_pow]
    have hq5 : (4096:ℝ) ≤ q^5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7) hq 5
      norm_num at h
      linarith
    have h := (inv_le_inv₀ (by positivity : (0:ℝ)<q^5) (by norm_num : (0:ℝ)<4096)).mpr hq5
    norm_num at h ⊢
    exact h
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)).trans h6,
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith), ?_⟩
  rw [Real.rpow_neg hq0.le, show (2:ℝ)=(2:ℕ) by norm_num, Real.rpow_natCast]
  have hq2 : (49:ℝ) ≤ q^2 := by nlinarith
  have h := (inv_le_inv₀ (by positivity : (0:ℝ)<q^2) (by norm_num : (0:ℝ)<49)).mpr hq2
  norm_num at h ⊢
  exact h

/-- The exact native coprime correction has an absolutely summable defect bound. -/
theorem localCorrection_bound (η : HeckeFamily.Character) (P : GoodPrime) (x : ℂ)
    (hx : 5/6 ≤ x.re) :
    ‖localCorrection η P.val x-1‖ ≤ (3/2:ℝ)*
      ((Ideal.absNorm P.val.val : ℝ)^(-(1+x.re))+(Ideal.absNorm P.val.val : ℝ)^(-3:ℝ)) := by
  let q : ℝ := Ideal.absNorm P.val.val
  have hq : 7 ≤ q := by
    change (7:ℝ) ≤ (Ideal.absNorm P.val.val : ℝ)
    exact_mod_cast P.property.2
  have hq0 : 0 < q := by linarith
  have caps := power_caps q x.re hq hx
  have hd := nativeDelta_norm η P.val x
  have hr := nativeCube_norm η P.val x
  have hs : q⁻¹ ≤ 1/7 := by
    simpa only [one_div] using (inv_le_inv₀ hq0 (by norm_num : (0:ℝ)<7)).mpr hq
  have h := ratio_bound q⁻¹ (nativeDelta η P.val x) (nativeCube η P.val x)
    (inv_nonneg.mpr hq0.le) hs (hd.trans caps.1) (hr.trans (caps.2.1.trans caps.2.2))
  have he : localCorrection η P.val x-1 = ((q⁻¹:ℝ):ℂ)*(nativeDelta η P.val x-nativeCube η P.val x)*
      (1-((q⁻¹:ℝ):ℂ))^2 / ((1-((q⁻¹:ℝ):ℂ)^2)*(1-(1-((q⁻¹:ℝ):ℂ))*nativeDelta η P.val x-((q⁻¹:ℝ):ℂ)*nativeCube η P.val x)) := by
    simp only [localCorrection, q, Complex.ofReal_inv, Complex.ofReal_natCast, add_sub_cancel_left]
  rw [he]
  calc
    _ ≤ (3/2:ℝ)*q⁻¹*(‖nativeDelta η P.val x‖+‖nativeCube η P.val x‖) := h
    _ ≤ (3/2:ℝ)*q⁻¹*(q^(-x.re)+q^(-2:ℝ)) := by gcongr; exact hr.trans caps.2.1
    _ = (3/2:ℝ)*(q⁻¹*q^(-x.re)+q⁻¹*q^(-2:ℝ)) := by ring
    _ = _ := by
      have he1 : q⁻¹*q^(-x.re) = q^(-(1+x.re)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
        congr 1
        ring
      have he3 : q⁻¹*q^(-2:ℝ) = q^(-3:ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
        norm_num
      rw [he1, he3]

/-- Every actual supported good-prime correction is nonzero throughout the stated source half-plane. -/
theorem localCorrection_ne_zero (η : HeckeFamily.Character) (P : GoodPrime) (x : ℂ)
    (hx : 5/6 ≤ x.re) : localCorrection η P.val x ≠ 0 := by
  have hb := localCorrection_bound η P x hx
  have hq : (7:ℝ) ≤ Ideal.absNorm P.val.val := by exact_mod_cast P.property.2
  have hq0 : (0:ℝ) < Ideal.absNorm P.val.val := by linarith
  have hc := power_caps (Ideal.absNorm P.val.val : ℝ) x.re hq hx
  have hi : (Ideal.absNorm P.val.val : ℝ)⁻¹ ≤ 1/7 := by
    simpa only [one_div] using (inv_le_inv₀ hq0 (by norm_num : (0:ℝ)<7)).mpr hq
  have hb' : ‖localCorrection η P.val x-1‖ < 1 := by
    have he1 : (Ideal.absNorm P.val.val : ℝ)^(-(1+x.re)) =
        (Ideal.absNorm P.val.val : ℝ)⁻¹*(Ideal.absNorm P.val.val : ℝ)^(-x.re) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
      congr 1
      ring
    have he3 : (Ideal.absNorm P.val.val : ℝ)^(-3:ℝ) =
        (Ideal.absNorm P.val.val : ℝ)⁻¹*(Ideal.absNorm P.val.val : ℝ)^(-2:ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
      congr 1
      ring
    rw [he1, he3] at hb
    have ha : (Ideal.absNorm P.val.val : ℝ)⁻¹*(Ideal.absNorm P.val.val : ℝ)^(-x.re) ≤ (1/7:ℝ)*(1/4) := by gcongr; exact hc.1
    have hc3 : (Ideal.absNorm P.val.val : ℝ)⁻¹*(Ideal.absNorm P.val.val : ℝ)^(-2:ℝ) ≤ (1/7:ℝ)*(1/49) := by gcongr; exact hc.2.2
    linarith
  intro hz
  simp [hz] at hb'

/-- Existing prime-norm summability makes the actual correction defects summable. -/
theorem correction_defects_summable (η : HeckeFamily.Character) (x : ℂ) (hx : 5/6 ≤ x.re) :
    Summable (fun P : GoodPrime => ‖localCorrection η P.val x-1‖) := by
  have hs := (SmoothMobiusCorrection.prime_norm_series_summable x.re (by linarith)).subtype
    (fun P : PrimeIdeal => CanonicalQuadraticSieve.Supported P.val ∧ 7 ≤ Ideal.absNorm P.val)
  have h3 := (SmoothMobiusCorrection.prime_norm_series_summable 2 (by norm_num)).subtype
    (fun P : PrimeIdeal => CanonicalQuadraticSieve.Supported P.val ∧ 7 ≤ Ideal.absNorm P.val)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun P => localCorrection_bound η P x hx)
  convert (hs.add h3).mul_left (3/2:ℝ) using 1
  norm_num

/-- Every finite actual good-prime correction product is nonzero. -/
theorem finite_correction_ne_zero (η : HeckeFamily.Character) (x : ℂ) (hx : 5/6 ≤ x.re)
    (T : Finset GoodPrime) : ∏ P ∈ T, localCorrection η P.val x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun P _ => localCorrection_ne_zero η P x hx)

/-- The actual correction product is nonzero, independently of any source/Euler identification. -/
theorem correction_product_ne_zero (η : HeckeFamily.Character) (x : ℂ) (hx : 5/6 ≤ x.re) :
    ∏' P : GoodPrime, localCorrection η P.val x ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f:=fun P : GoodPrime => localCorrection η P.val x-1)
    (fun P => by simpa using localCorrection_ne_zero η P x hx)
    (correction_defects_summable η x hx)
  simpa using h

/-- Conditional native reciprocal-source holomorphy transfer: a nonzero analytic correction cannot help. -/
theorem native_reciprocal_analytic_iff (η : HeckeFamily.Character) (ρ : ℂ)
    (M : ℂ → ℂ) (hM : AnalyticAt ℂ M ρ) (hne : M ρ ≠ 0) :
    AnalyticAt ℂ (fun x => M x*HeckeReciprocal.reciprocal η x) ρ ↔
      AnalyticAt ℂ (HeckeReciprocal.reciprocal η) ρ := by
  exact (analyticAt_iff_analytic_fun_mul hM hne).symm

/-- The actual target reciprocal's meromorphic order is unchanged by any proved analytic nonzero correction. -/
theorem native_reciprocal_order_preserved (η : HeckeFamily.Character) (ρ : ℂ)
    (M : ℂ → ℂ) (hM : AnalyticAt ℂ M ρ) (hne : M ρ ≠ 0) :
    meromorphicOrderAt (fun x => M x*HeckeReciprocal.reciprocal η x) ρ =
      meromorphicOrderAt (HeckeReciprocal.reciprocal η) ρ := by
  exact meromorphicOrderAt_mul_of_ne_zero hM hne

/-- Once the native source equals an analytic nonzero multiple, a reciprocal pole is not regularized. -/
theorem native_pole_not_regularized (η : HeckeFamily.Character) (ρ : ℂ)
    (M : ℂ → ℂ) (hM : AnalyticAt ℂ M ρ) (hne : M ρ ≠ 0)
    (hpole : meromorphicOrderAt (HeckeReciprocal.reciprocal η) ρ < 0) :
    ¬AnalyticAt ℂ (fun x => M x*HeckeReciprocal.reciprocal η x) ρ := by
  intro h
  have hnonneg := h.meromorphicOrderAt_nonneg
  rw [native_reciprocal_order_preserved η ρ M hM hne] at hnonneg
  exact not_lt_of_ge hnonneg hpole


/-- For the actual correction product, source analyticity still requires an explicit analytic-product bridge. -/
theorem actual_product_analytic_iff (η : HeckeFamily.Character) (ρ : ℂ)
    (hρ : 5/6 ≤ ρ.re)
    (hM : AnalyticAt ℂ (fun x => ∏' P : GoodPrime, localCorrection η P.val x) ρ) :
    AnalyticAt ℂ (fun x => (∏' P : GoodPrime, localCorrection η P.val x)*
      HeckeReciprocal.reciprocal η x) ρ ↔
      AnalyticAt ℂ (HeckeReciprocal.reciprocal η) ρ := by
  exact native_reciprocal_analytic_iff η ρ _ hM (correction_product_ne_zero η ρ hρ)

/-- A literal restricted source inherits a reciprocal pole only after the source identity is proved. -/
theorem restricted_source_not_regularized (η : HeckeFamily.Character) (ρ : ℂ)
    (hρ : 5/6 ≤ ρ.re) (F : ℂ → ℂ)
    (hM : AnalyticAt ℂ (fun x => ∏' P : GoodPrime, localCorrection η P.val x) ρ)
    (hsource : F =ᶠ[𝓝 ρ] fun x => (∏' P : GoodPrime, localCorrection η P.val x)*
      HeckeReciprocal.reciprocal η x)
    (hpole : meromorphicOrderAt (HeckeReciprocal.reciprocal η) ρ < 0) :
    ¬AnalyticAt ℂ F ρ := by
  intro hF
  exact native_pole_not_regularized η ρ _ hM (correction_product_ne_zero η ρ hρ)
    hpole (hF.congr hsource)

end OpenAIReview.CoprimePoleGate

#lint+ in OpenAIReview.CoprimePoleGate

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
  unless declarations > 0 do throwError "Empty coprime-pole audit."
  logInfo m!"Coprime-pole audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-coprime-pole-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-coprime-pole-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual prime correction bounds/nonvanishing and conditional reciprocal-source pole transfer; native global source bridge absent"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
