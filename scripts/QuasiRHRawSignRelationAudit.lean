/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual raw Gauss / prescribed Mobius relation

The raw sum and its mixed denominator use the imported native CRT Gauss APIs.
Eliminating the actual rational sign gives a sixth-degree relation. Clearing
an entire matrix column pays exactly the denominator's actual norm. The final
floor statement concerns only the explicit finite exponent box; no spanning,
interpolation, integral-field Frobenius, native source or saving is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.RawSignRelation
open OAI ActualEisensteinCubic CompletedGauss FiniteGaussPhase ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

section Native
variable {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [hmax : ∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hgood : ∀ i, lambda ∉ Ideal.span {p i})
  (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)

/-- Actual prescribed rational sign of the squarefree supported spectral ideal. -/
def sign : ℂ := (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)

/-- Actual ideal norm, before any analytic profile. -/
def q : ℕ := Ideal.absNorm (Ideal.span {∏ i, p i})

/-- Raw native trace Gauss sum, undoing its literal norm normalization. -/
def raw (j : ℕ) : ℂ :=
  (‖eisEmbedding (∏ i, p i)‖ : ℂ) * canonicalProductGauss p hp hcop hgood (fun _ => j)

/-- Actual mixed denominator pi times the raw quadratic Gauss/ray factor. -/
def denominator : ℂ :=
  (‖eisEmbedding (∏ i, p i)‖ : ℂ) * eisEmbedding (∏ i, p i) *
    canonicalProductG p hp hcop hgood

omit hmax in
/-- The square of the literal normalization is the actual ideal norm. -/
theorem radius_sq : (‖eisEmbedding (∏ i, p i)‖ : ℂ)^2 = (q p : ℂ) := by
  exact_mod_cast eisEmbedding_norm_sq_eq_absNorm_span (∏ i, p i)

include hp in
omit hmax in
/-- No zero normalization is introduced on the actual supported product. -/
theorem radius_ne_zero : (‖eisEmbedding (∏ i, p i)‖ : ℂ) ≠ 0 := by
  exact_mod_cast norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr
    (fun i _ => hp i)))

include hcop in
/-- The prescribed Mobius sign square is exactly one. -/
theorem sign_sq : sign p ^ 2 = 1 := by
  unfold sign
  rw [product_moebius_eq_sign p hcop, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

include hchar hprimary in
/-- Actual native mixed raw identity; no independent sign variable is substituted. -/
theorem raw_mixed : raw p hp hcop hgood 1 * raw p hp hcop hgood 2 =
    sign p * denominator p hp hcop hgood := by
  have hm := canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary
  have hr := radius_ne_zero p hp
  unfold raw denominator sign
  rw [show ((‖eisEmbedding (∏ i, p i)‖ : ℂ) *
      canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
      ((‖eisEmbedding (∏ i, p i)‖ : ℂ) *
      canonicalProductGauss p hp hcop hgood (fun _ => 2)) =
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)^2 *
      (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
        canonicalProductGauss p hp hcop hgood (fun _ => 2)) by ring, hm]
  unfold angularFactor
  field_simp

include hprimary in
/-- The actual raw cubic Gauss cube retains the prescribed sign. -/
theorem raw_two_cube : raw p hp hcop hgood 2 ^ 3 =
    sign p * eisEmbedding (∏ i, p i) * (q p : ℂ) := by
  have hc := canonicalProductGauss_two_cube p hp hcop hgood hprimary
  have hr := radius_ne_zero p hp
  unfold raw sign
  rw [mul_pow, hc, ← radius_sq p]
  unfold angularFactor
  field_simp

include hprimary in
/-- Faithful elimination of the sign gives degree six, not an unsigned cubic relation. -/
theorem raw_two_sixth : raw p hp hcop hgood 2 ^ 6 =
    (eisEmbedding (∏ i, p i) * (q p : ℂ))^2 := by
  calc
    _ = (raw p hp hcop hgood 2 ^ 3)^2 := by ring
    _ = (sign p * eisEmbedding (∏ i, p i) * (q p : ℂ))^2 := by
      rw [raw_two_cube p hp hcop hgood hprimary]
    _ = sign p ^ 2 * (eisEmbedding (∏ i, p i) * (q p : ℂ))^2 := by ring
    _ = _ := by rw [sign_sq p hcop, one_mul]

include hchar hprimary in
/-- The actual mixed denominator has exactly the ideal norm as its complex modulus. -/
theorem denominator_norm : ‖denominator p hp hcop hgood‖ = (q p : ℝ) := by
  unfold denominator
  rw [norm_mul, norm_mul, norm_canonicalProductG p hp hcop hgood hchar hprimary]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_one]
  simpa [q, pow_two] using eisEmbedding_norm_sq_eq_absNorm_span (∏ i, p i)

include hchar hprimary in
/-- In particular the literal raw quotient is defined on the actual supported family. -/
theorem denominator_ne_zero : denominator p hp hcop hgood ≠ 0 := by
  intro hz
  have hn := denominator_norm p hp hcop hgood hchar hprimary
  have hq : q p ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  rw [hz, norm_zero] at hn
  exact hq (Nat.cast_eq_zero.mp hn.symm)

include hchar hprimary in
/-- The native raw quotient recovers exactly the rational Mobius sign. -/
theorem raw_quotient :
    (raw p hp hcop hgood 1 * raw p hp hcop hgood 2) /
      denominator p hp hcop hgood = sign p := by
  rw [raw_mixed p hp hcop hgood hchar hprimary]
  exact mul_div_cancel_right₀ _ (denominator_ne_zero p hp hcop hgood hchar hprimary)

include hcop in
/-- An odd power fixes the actual rational sign exactly. -/
theorem sign_pow_odd (k : ℕ) (hk : Odd k) : sign p ^ k = sign p := by
  unfold sign
  rw [product_moebius_eq_sign p hcop, ← pow_mul, Nat.mul_comm, pow_mul, hk.neg_one_pow]

omit hmax in
/-- Any common ring map preserves this rational sign; no native Frobenius map is constructed. -/
theorem map_sign (σ : ℂ →+* ℂ) : σ (sign p) = sign p := by
  simp [sign]

include hchar hprimary in
/-- The mixed identity transfers a common Frobenius-type defect by the same unit sign. -/
theorem odd_map_defect (k : ℕ) (hk : Odd k) (σ : ℂ →+* ℂ) :
    (raw p hp hcop hgood 1 * raw p hp hcop hgood 2)^k -
      σ (raw p hp hcop hgood 1 * raw p hp hcop hgood 2) =
      sign p * (denominator p hp hcop hgood ^ k - σ (denominator p hp hcop hgood)) := by
  rw [raw_mixed p hp hcop hgood hchar hprimary, mul_pow, map_mul,
    sign_pow_odd p hcop k hk, map_sign p σ]
  ring

/-- Clearing the WHOLE column scales its determinant by the actual denominator. -/
theorem clear_whole_column {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (A.updateCol j (denominator p hp hcop hgood • fun i => A i j)).det =
      denominator p hp hcop hgood * A.det := by
  rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]

include hchar hprimary in
/-- The corresponding Archimedean cost is exactly q, not an uncharged source gain. -/
theorem clear_whole_column_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    ‖(A.updateCol j (denominator p hp hcop hgood • fun i => A i j)).det‖ =
      (q p : ℝ) * ‖A.det‖ := by
  rw [clear_whole_column p hp hcop hgood A j, norm_mul,
    denominator_norm p hp hcop hgood hchar hprimary]

end Native

/-- Explicit localized degree-six/quadratic exponent box only; no spanning claim. -/
theorem explicit_normal_form_floor (a : Fin 6) (b : Fin 2) (ℓ : ℕ) (hℓ : 7 ≤ ℓ) :
    a.val / ℓ + b.val / ℓ = 0 := by
  rw [Nat.div_eq_of_lt (by omega : a.val < ℓ),
    Nat.div_eq_of_lt (by omega : b.val < ℓ)]

end OpenAIReview.RawSignRelation

#lint+ in OpenAIReview.RawSignRelation

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
  unless declarations > 0 do throwError "Empty raw-sign audit."
  logInfo m!"Raw-sign audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-integral-border-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-integral-border-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual native raw mixed sign/sixth-degree identities, exact whole-column norm cost and explicit finite floor gate; no interpolation/source/Frobenius-field construction"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
