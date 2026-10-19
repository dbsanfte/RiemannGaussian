/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual unselected tuple mass with an additional norm power

The literal unselected weight has norm L^(-3/2) times its slot profiles.
Multiplying it by L^theta is summable uniformly over the actual supported
prime-slot tuples for every fixed theta<1/2. In particular theta=1/6
uses the genuine supported-ideal exponent -4/3. This pays only the tuple
factor, without a theta-residue recurrence or physical transfer claim.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.UnselectedWeightedMass
open OAI
open OAI.SevenEighths
open ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

/-- The actual canonical prime-slot support inherits the ordinary supported-ideal
summability bound, at any fixed exponent strictly below minus one. -/
theorem canonical_slot_rpow_bound (r : ℝ) (hr : r < -1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Finset PrimeIdeal) (_hT : ∀ P ∈ T, Supported P.val),
        (∑ a : canonicalSlotSupport T, elementNorm a.val ^ r) ≤ C := by
  obtain ⟨C, hC, hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound r hr
  refine ⟨C, hC, ?_⟩
  intro T hT
  let f : T → SupportedIdeal := fun P => ⟨P.val.val, hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal => I.val) h
  have he : (∑ a : canonicalSlotSupport T, elementNorm a.val ^ r) =
      ∑ I ∈ Finset.univ.image f, ProbeGramCommon.gramIdealNorm I ^ r := by
    rw [Finset.sum_image (fun P _ Q _ h => hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a => elementNorm a.val ^ r)
    rw [← hh]
    apply Finset.sum_congr rfl
    intro P _
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

/-- Exact extra-power identity for the native unselected weight and its actual
selected-index complement; no mask or slot profile is replaced. -/
theorem lowUnselectedWeight_norm_power_identity {K : ℕ} (slots : Fin K → Finset O)
    (hslots : ∀ i x, x ∈ slots i → x ≠ 0) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ) (theta : ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖ * elementNorm (∏ i : J, (a i).val) ^ theta =
      ∏ i : J, elementNorm (a i).val ^ (-(3/2 : ℝ) + theta) *
        ‖W i.val (elementNorm (a i).val / P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL.le _), norm_prod]
  calc
    _ = (elementNorm (∏ i : J, (a i).val) ^ (-(3/2 : ℝ)) *
          elementNorm (∏ i : J, (a i).val) ^ theta) *
        ∏ i : J, ‖W i.val (elementNorm (a i).val / P i.val)‖ := by ring
    _ = elementNorm (∏ i : J, (a i).val) ^ (-(3/2 : ℝ) + theta) *
        ∏ i : J, ‖W i.val (elementNorm (a i).val / P i.val)‖ := by
      rw [← Real.rpow_add hL]
    _ = _ := by
      rw [elementNorm_finset_prod, Finset.prod_mul_distrib,
        Real.finsetProd_rpow Finset.univ (fun i : J => elementNorm (a i).val)
          (fun i _ => by unfold elementNorm; positivity)]

/-- Fixed-size mass bound for the SAME actual canonical prime-slot tuples, with
bounded literal profiles and any fixed power theta<1/2. -/
theorem lowUnselectedWeightedMass_bound (K : ℕ) (M theta : ℝ)
    (hM : 0 ≤ M) (htheta : theta < 1/2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Fin K → Finset PrimeIdeal) (_hT : ∀ i P, P ∈ T i → Supported P.val)
        (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ),
        (∀ i x, ‖W i x‖ ≤ M) →
        (∑ a : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J,
          ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P a‖ *
            elementNorm (∏ i : J, (a i).val) ^ theta) ≤ C := by
  obtain ⟨C, hC, hb⟩ := canonical_slot_rpow_bound (-(3/2 : ℝ) + theta) (by linarith)
  refine ⟨(max 1 (C * M)) ^ K, by positivity, ?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_power_identity _
    (fun i => canonicalSlotSupport_nonzero _ (hT i))]
  rw [← Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val)) =>
    elementNorm a.val ^ (-(3/2 : ℝ) + theta) *
      ‖W i.val (elementNorm a.val / P i.val)‖)]
  calc
    _ ≤ ∏ i : J, C * M := by
      apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun a _ =>
        mul_nonneg (Real.rpow_nonneg (by unfold elementNorm; positivity) _) (norm_nonneg _)))
      intro i _
      calc
        _ ≤ ∑ a : canonicalSlotSupport (T i.val),
            elementNorm a.val ^ (-(3/2 : ℝ) + theta) * M := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (hW i.val _)
            (Real.rpow_nonneg (by unfold elementNorm; positivity) _)
        _ = (∑ a : canonicalSlotSupport (T i.val),
            elementNorm a.val ^ (-(3/2 : ℝ) + theta)) * M := (Finset.sum_mul ..).symm
        _ ≤ C * M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _ ≤ ∏ _i : J, max 1 (C * M) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun _ _ => le_max_right _ _)
    _ ≤ _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _)
        (by simpa using Finset.card_le_card (Finset.subset_univ J))

/-- The literal sixth-power tuple factor is paid by exponent minus four-thirds. -/
theorem lowUnselected_sixth_mass_bound (K : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Fin K → Finset PrimeIdeal) (_hT : ∀ i P, P ∈ T i → Supported P.val)
        (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ),
        (∀ i x, ‖W i x‖ ≤ M) →
        (∑ a : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J,
          ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P a‖ *
            elementNorm (∏ i : J, (a i).val) ^ (1/6 : ℝ)) ≤ C :=
  lowUnselectedWeightedMass_bound K M (1/6) hM (by norm_num)

/-- Literal tuple restrictions may be retained in a finite subset of the native
tuple type, with the same constant and without replacing any selected incidence. -/
theorem lowUnselected_sixth_retained_mass_bound (K : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Fin K → Finset PrimeIdeal) (_hT : ∀ i P, P ∈ T i → Supported P.val)
        (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
        (R : Finset (LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J)),
        (∀ i x, ‖W i x‖ ≤ M) →
        (∑ a ∈ R,
          ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P a‖ *
            elementNorm (∏ i : J, (a i).val) ^ (1/6 : ℝ)) ≤ C := by
  obtain ⟨C, hC, hb⟩ := lowUnselected_sixth_mass_bound K M hM
  refine ⟨C, hC, ?_⟩
  intro T hT J W P R hW
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) ?_).trans
    (hb T hT J W P hW)
  intro a _ _
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by unfold elementNorm; positivity) _)

end OpenAIReview.UnselectedWeightedMass
#lint+ in OpenAIReview.UnselectedWeightedMass

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty actual weighted tuple audit."
  logInfo m!"Weighted tuple audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-unselected-weighted-mass-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-unselected-weighted-mass-gate/axioms.json"
    (Json.mkObj [("scope", toJson "actual unselected prime-slot tuple mass with extra norm power; tuple factor only, no rho recurrence or physical transfer"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
