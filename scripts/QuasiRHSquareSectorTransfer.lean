/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.LowElementRows
import OAI.NumberTheory.DirichletL.CubicSieve.FullNorm
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
Transfer from all-root square energy to the literal finite physical sector.
The original calibration, numerator phase and companion remain unchanged.
This is an energy interface, not a claim that the zero source belongs to
the square sector. The exact complementary sector is retained.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.SquareSectorTransfer
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.CubicSieve
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
/-- The actual finite group of six Eisenstein units. -/
local instance unitFintype : Fintype Oˣ :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

/-- The literal numerator is a unit times an arbitrary square; roots need not
be squarefree or coprime to the physical Gauss modulus. -/
def SquareNumerator (m : O) : Prop := ∃ (ζ : Oˣ) (x : O), m = ζ.val * x^2

/-- Original physical rows, restricted only to the stated square sector. -/
def squareRows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) : Finset O :=
  (lowNumeratorRows a b ha hb Q hQ).filter SquareNumerator

/-- The physical window forces each square root into the precise native
element range. No physical cutoff is replaced in the summand. -/
theorem square_root_in_range (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (Q : ℝ) (hQ : 0<Q) (m : O)
    (hm : m ∈ lowNumeratorRows a b ha hb Q hQ) (ζ : Oˣ) (x : O)
    (he : m = ζ.val*x^2) : x ∈ elementRange (Real.sqrt (2*b*Q)) := by
  apply (mem_elementRange _ _).mpr
  have hx : x ≠ 0 := by
    intro hx
    exact lowNumeratorRows_nonzero a b ha hb Q hQ m hm (by simp [he, hx])
  refine ⟨hx, ?_⟩
  have hnorm : elementNorm (ζ.val*x^2) = elementNorm x ^ 2 := by
    unfold elementNorm
    rw [Ideal.span_singleton_mul_left_unit ζ.isUnit,
      ← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  have hbound := lowNumeratorRows_norm_bound a b ha hb Q hQ m hm
  rw [he, hnorm] at hbound
  exact Real.le_sqrt_of_sq_le hbound

/-- All physical square rows are covered by six unit choices and actual
nonzero roots. Duplicates are harmless only in this nonnegative energy. -/
theorem square_energy_le_root_energy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (Q : ℝ) (hQ : 0<Q) (F : O → ℂ) :
    (∑ m ∈ squareRows a b ha hb Q hQ, ‖F m‖^2) ≤
      ∑ ζ : Oˣ, ∑ x ∈ elementRange (Real.sqrt (2*b*Q)), ‖F (ζ.val*x^2)‖^2 := by
  let P : Finset (Oˣ × O) := Finset.univ ×ˢ elementRange (Real.sqrt (2*b*Q))
  let f : Oˣ × O → O := fun p => p.1.val*p.2^2
  have hs : squareRows a b ha hb Q hQ ⊆ P.image f := by
    intro m hm
    obtain ⟨hm, ζ, x, he⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_image.mpr ⟨(ζ,x),
      Finset.mem_product.mpr ⟨Finset.mem_univ _,
        square_root_in_range a b ha hb Q hQ m hm ζ x he⟩, he.symm⟩
  calc
    _ ≤ ∑ m ∈ P.image f, ‖F m‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ p ∈ P, ‖F (f p)‖^2 :=
      Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
    _ = _ := by simp only [P, f, Finset.sum_product]

/-- Uniform per-unit root energy costs exactly the known six units. -/
theorem square_energy_le_six (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (Q : ℝ) (hQ : 0<Q) (F : O → ℂ) (E : ℝ)
    (hE : ∀ ζ : Oˣ, (∑ x ∈ elementRange (Real.sqrt (2*b*Q)),
      ‖F (ζ.val*x^2)‖^2) ≤ E) :
    (∑ m ∈ squareRows a b ha hb Q hQ, ‖F m‖^2) ≤ 6*E := by
  apply (square_energy_le_root_energy a b ha hb Q hQ F).trans
  calc
    _ ≤ ∑ _ζ : Oˣ, E := Finset.sum_le_sum (fun ζ _ => hE ζ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, low_unit_card, nsmul_eq_mul, Nat.cast_ofNat]

/-- Finite physical integral summand with one explicit numerator selection.
Both sectors together are the original integrand, not a new carrier. -/
def physicalSector (R : Finset O) (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a b X Y : ℝ) (B : RayRing → O → ℂ) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I) * ∑ σ : RayRing, ∑ m ∈ R,
    lowNumeratorWeight C (lowOuterCutoff a b) X Y m v *
      lowRayAmplitude C W1 Y σ m v * B σ m

/-- Exact square/complement ledger. In particular the complete source is
not assigned to the square sector. -/
theorem physical_sector_ledger (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ → ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing → O → ℂ) (v : ℝ) :
    let Q := lowPhysicalScale C X Y
    let hQ := lowPhysicalScale_pos C X Y hX hY
    let R := lowNumeratorRows a b ha hb Q hQ
    lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v =
      physicalSector (squareRows a b ha hb Q hQ) C W0 W1 a b X Y B v +
      physicalSector (R.filter (fun m => ¬SquareNumerator m)) C W0 W1 a b X Y B v := by
  dsimp only
  let R := lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
    (lowPhysicalScale_pos C X Y hX hY)
  have hz (m : O) (hm : m ∉ R) :
      lowNumeratorWeight C (lowOuterCutoff a b) X Y m v = 0 := by
    have hc : lowOuterCutoff a b (elementNorm m / lowPhysicalScale C X Y) = 0 := by
      simpa only [R, lowNumeratorRows_mem, not_not] using hm
    simp [lowNumeratorWeight, hc]
  unfold lowSeparatedIntegrand
  change mellin W0 ((v:ℂ)*Complex.I) *
    (∑' m : O, lowNumeratorWeight C (lowOuterCutoff a b) X Y m v *
      ∑ σ : RayRing, lowRayAmplitude C W1 Y σ m v * B σ m) = _
  rw [tsum_eq_sum (s:=R) (fun m hm => by rw [hz m hm, zero_mul])]
  have hs : (∑ m ∈ R, lowNumeratorWeight C (lowOuterCutoff a b) X Y m v *
      ∑ σ : RayRing, lowRayAmplitude C W1 Y σ m v * B σ m) =
      ∑ σ : RayRing, ∑ m ∈ R,
        lowNumeratorWeight C (lowOuterCutoff a b) X Y m v *
          lowRayAmplitude C W1 Y σ m v * B σ m := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [hs]
  simp only [physicalSector, squareRows, mul_assoc, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact (Finset.sum_filter_add_sum_filter_not R SquareNumerator _).symm

/-- The literal square-sector Cauchy bound consumes an all-root estimate.
Every original numerator weight and the original companion B are retained;
the complementary rows remain in the preceding exact ledger. -/
theorem physical_square_bound (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ → ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing → O → ℂ) (v : ℝ) (E : RayRing → ℝ)
    (hE : ∀ (σ : RayRing) (ζ : Oˣ),
      (∑ x ∈ elementRange (Real.sqrt (2*b*lowPhysicalScale C X Y)),
        ‖lowRayAmplitude C W1 Y σ (ζ.val*x^2) v‖^2) ≤ E σ) :
    let Q := lowPhysicalScale C X Y
    let hQ := lowPhysicalScale_pos C X Y hX hY
    ‖physicalSector (squareRows a b ha hb Q hQ) C W0 W1 a b X Y B v‖ ≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖ * ∑ σ : RayRing,
        Real.sqrt (6*E σ) *
          Real.sqrt (∑ m ∈ lowNumeratorRows a b ha hb Q hQ, ‖B σ m‖^2) := by
  dsimp only
  unfold physicalSector
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro σ _
  apply (CenteredMomentCauchy.bounded_row_cauchy _
    (fun m => lowNumeratorWeight C (lowOuterCutoff a b) X Y m v)
    (fun m => lowRayAmplitude C W1 Y σ m v) (B σ)
    (fun m _ => lowNumeratorWeight_norm C _ (lowOuterCutoff_norm a b)
      (lowOuterCutoff_small a b ha 0 (by positivity)) X Y hX hY m v)).trans
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (square_energy_le_six a b ha hb _
      (lowPhysicalScale_pos C X Y hX hY) _ (E σ) (hE σ))
  · apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

end OpenAIReview.SquareSectorTransfer
#lint+ in OpenAIReview.SquareSectorTransfer

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
  unless declarations > 0 do throwError "Empty square-sector transfer audit."
  logInfo m!"Square-sector transfer: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-sector-transfer"
  IO.FS.writeFile ".lake/arithmetic-operator-square-sector-transfer/axioms.json"
    (Json.mkObj [("scope", toJson "literal physical square-sector energy transfer and exact unpaid complement; no sector source or zero-free claim"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
