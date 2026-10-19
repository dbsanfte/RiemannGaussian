/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHSquareSectorTransfer
import scripts.QuasiRHAllSquareAmplitudeBridgeAudit
import OAI.NumberTheory.DirichletL.Detector.LowGramIntegrated
import OAI.NumberTheory.DirichletL.Detector.LowTupleGram
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
The original Mellin integral splits exactly into square and complementary
numerators. A uniform all-root square energy pays the square integral with
the original companion mass; it assigns no zero source to this sector.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical ContDiff BigOperators
open MeasureTheory
namespace OpenAIReview.SquareSectorIntegral
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.CubicSieve
open RayFourExpansion SquareSectorTransfer
local notation "O" => ActualEisensteinCubic.O
/-- The actual finite group of Eisenstein units used by the root energy. -/
local instance unitFintype : Fintype Oˣ :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

/-- A numerator restriction is placed in the original companion, keeping
every calibration, phase and physical modulus in the original amplitude. -/
theorem sector_eq_separated (P : O → Prop) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ → ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing → O → ℂ) (v : ℝ) :
    physicalSector
      ((lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY)).filter P) C W0 W1 a b X Y B v =
      lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y
        (fun σ m => if P m then B σ m else 0) v := by
  let R := lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
    (lowPhysicalScale_pos C X Y hX hY)
  have hz (m : O) (hm : m ∉ R) :
      lowNumeratorWeight C (lowOuterCutoff a b) X Y m v = 0 := by
    have hc : lowOuterCutoff a b (elementNorm m / lowPhysicalScale C X Y) = 0 := by
      simpa only [R, lowNumeratorRows_mem, not_not] using hm
    simp [lowNumeratorWeight, hc]
  unfold lowSeparatedIntegrand
  change _ = mellin W0 ((v:ℂ)*Complex.I) *
    (∑' m : O, lowNumeratorWeight C (lowOuterCutoff a b) X Y m v *
      ∑ σ : RayRing, lowRayAmplitude C W1 Y σ m v * (if P m then B σ m else 0))
  rw [tsum_eq_sum (s:=R) (fun m hm => by rw [hz m hm, zero_mul])]
  unfold physicalSector
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hp : P m <;> simp [hp, mul_assoc]

/-- Every finite numerator restriction is genuinely integrable, including
the square sector and its exact complement. -/
theorem sector_integrable (P : O → Prop) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0)
    (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing → O → ℂ) :
    Integrable (physicalSector
      ((lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY)).filter P) C W0 W1 a b X Y B) := by
  have he : physicalSector
      ((lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY)).filter P) C W0 W1 a b X Y B =
      lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y
        (fun σ m => if P m then B σ m else 0) := by
    funext v
    exact sector_eq_separated P a b ha hb C W0 W1 X Y hX hY B v
  rw [he]
  exact lowSeparatedIntegrand_integrable C W0 W1 _ a0 b0 ha0 hW0 hW0s hW1
    (lowOuterCutoff_compact a b ha hb) (lowOuterCutoff_small a b ha 0 (by positivity))
    X Y hX hY _

/-- The exact original integral ledger. Neither sector is assigned the
source of the complete carrier. -/
theorem integral_sector_ledger (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0)
    (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing → O → ℂ) :
    let Q := lowPhysicalScale C X Y
    let hQ := lowPhysicalScale_pos C X Y hX hY
    let R := lowNumeratorRows a b ha hb Q hQ
    (∫ v : ℝ, lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v) =
      (∫ v : ℝ, physicalSector (squareRows a b ha hb Q hQ) C W0 W1 a b X Y B v) +
      (∫ v : ℝ, physicalSector (R.filter (fun m => ¬SquareNumerator m))
        C W0 W1 a b X Y B v) := by
  dsimp only
  simp_rw [physical_sector_ledger a b ha hb C W0 W1 X Y hX hY B]
  apply integral_add
  · simpa only [squareRows] using
      sector_integrable SquareNumerator a b ha hb C W0 W1 a0 b0 ha0 hW0 hW0s hW1 X Y hX hY B
  · convert sector_integrable (fun m => ¬SquareNumerator m) a b ha hb C W0 W1
      a0 b0 ha0 hW0 hW0s hW1 X Y hX hY B using 1
    congr 2

/-- Integrating a uniform actual square-root energy loses only a fixed
Mellin-profile constant. The original full companion energy remains literal. -/
theorem square_integral_bound
    (W0 : ℝ → ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0) :
    ∃ CM : ℝ, 0<CM ∧
      ∀ (a b : ℝ) (ha : 0<a) (hb : 0<b)
        (C : CalibrationData) (W1 : ℝ → ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
        (B : RayRing → O → ℂ) (E : ℝ),
      (∀ (σ : RayRing) (ζ : Oˣ) (v : ℝ),
        (∑ x ∈ elementRange (Real.sqrt (2*b*lowPhysicalScale C X Y)),
          ‖lowRayAmplitude C W1 Y σ (ζ.val*x^2) v‖^2) ≤ E) →
      ‖∫ v : ℝ, physicalSector
        (squareRows a b ha hb (lowPhysicalScale C X Y)
          (lowPhysicalScale_pos C X Y hX hY)) C W0 W1 a b X Y B v‖ ≤
        CM * Real.sqrt (6*E) * lowInverseMass C a b ha hb X Y hX hY B := by
  obtain ⟨CM, hCM, hm⟩ := low_mellin_sqrt_weight_bound W0 a0 b0 ha0 hW0 hW0s 0
  simp only [pow_zero, Real.sqrt_one, mul_one] at hm
  refine ⟨CM*Real.pi, by positivity, ?_⟩
  intro a b ha hb C W1 X Y hX hY B E hE
  let M := lowInverseMass C a b ha hb X Y hX hY B
  have hM : 0≤M := lowInverseMass_nonneg C a b ha hb X Y hX hY B
  have hh (v : ℝ) :
      ‖physicalSector (squareRows a b ha hb (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY)) C W0 W1 a b X Y B v‖ ≤
      (CM*Real.sqrt (6*E)*M)*(1+v^2)⁻¹ := by
    have hs := physical_square_bound a b ha hb C W0 W1 X Y hX hY B v
      (fun _ => E) (fun σ ζ => hE σ ζ v)
    dsimp only at hs
    rw [← Finset.mul_sum] at hs
    change _ ≤ ‖mellin W0 ((v:ℂ)*Complex.I)‖ * (Real.sqrt (6*E)*M) at hs
    calc
      _ ≤ ‖mellin W0 ((v:ℂ)*Complex.I)‖ * (Real.sqrt (6*E)*M) := hs
      _ ≤ (CM/(1+v^2))*(Real.sqrt (6*E)*M) :=
        mul_le_mul_of_nonneg_right (hm v) (mul_nonneg (Real.sqrt_nonneg _) hM)
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hi := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (CM*Real.sqrt (6*E)*M))
    (Filter.Eventually.of_forall hh)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hi
  convert hi using 1
  ring

/-- Unconditional bound for the square sector of the ORIGINAL physical
Mellin integral. The root energy is proved, not a premise. All physical
prime-power columns and the unchanged original companion are retained. -/
theorem actual_square_integral_bound (ε η : ℝ) (hε : 0<ε) (hη : 0<η)
    (W0 : ℝ → ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0) :
    ∃ D : ℝ, 0<D ∧
      ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
        (W1 : ℝ → ℂ) (_hW1c : HasCompactSupport W1) (a1 b1 B1 : ℝ),
      0<a1 → 0≤B1 → Function.support W1 ⊆ Set.Icc a1 b1 →
      (∀ t, ‖W1 t‖ ≤ B1) →
      ∀ (a b : ℝ) (ha : 0<a) (hb : 0<b)
        (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y),
      1≤Z → b1*Y≤Z → 1≤Real.sqrt (2*b*lowPhysicalScale (calibrationForSet S hS) X Y) →
      ∀ B : RayRing → O → ℂ,
      let C := calibrationForSet S hS
      let Q := lowPhysicalScale C X Y
      let A := Real.sqrt (2*b*Q)
      ‖∫ v : ℝ, physicalSector (squareRows a b ha hb Q (lowPhysicalScale_pos C X Y hX hY))
        C W0 W1 a b X Y B v‖ ≤
        D * Real.sqrt ((B1*a1^(-(1/2 : ℝ)))^2 * A^η * (A*Z)^ε * (Z/Y)^2 *
          (A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z)) * lowInverseMass C a b ha hb X Y hX hY B := by
  obtain ⟨K, hK, he⟩ := AllSquareAmplitudeBridge.lowRayAmplitude_all_square_energy ε η hε hη
  obtain ⟨CM, hCM, hi⟩ := square_integral_bound W0 a0 b0 ha0 hW0 hW0s
  refine ⟨CM*Real.sqrt (6*K), by positivity, ?_⟩
  intro S hS W1 hW1c a1 b1 B1 ha1 hB1 hW1 hWB1 a b ha hb X Y Z hX hY hZ hcut hA B
  dsimp only
  let C := calibrationForSet S hS
  let A := Real.sqrt (2*b*lowPhysicalScale C X Y)
  let F := (B1*a1^(-(1/2 : ℝ)))^2 * A^η * (A*Z)^ε * (Z/Y)^2 *
    (A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z)
  have hE (σ : RayRing) (ζ : Oˣ) (v : ℝ) :
      (∑ x ∈ elementRange A, ‖lowRayAmplitude C W1 Y σ (ζ.val*x^2) v‖^2) ≤ K*F := by
    convert he S hS W1 hW1c a1 b1 B1 ha1 hB1 hW1 hWB1 A Z Y hA hZ hY hcut
      σ v ζ.val ζ.isUnit using 1
    dsimp [F]
    ring
  have hh := hi a b ha hb C W1 X Y hX hY B (K*F) hE
  have hsplit : 6*(K*F)=(6*K)*F := by ring
  rw [hsplit, Real.sqrt_mul (by positivity)] at hh
  convert hh using 1
  ring

end OpenAIReview.SquareSectorIntegral
#lint+ in OpenAIReview.SquareSectorIntegral

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
  unless declarations > 0 do throwError "Empty square-sector integral audit."
  logInfo m!"Square-sector integral: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-sector-integral"
  IO.FS.writeFile ".lake/arithmetic-operator-square-sector-integral/axioms.json"
    (Json.mkObj [("scope", toJson "exact original integral square/complement ledger and energy-to-integral transfer; no source on square sector"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
