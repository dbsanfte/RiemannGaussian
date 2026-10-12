/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCoupledSummandAudit
import OAI.NumberTheory.DirichletL.Detector.RadialIdentity
import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
import OAI.NumberTheory.DirichletL.Detector.LowRowMellin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Lean.Util.CollectAxioms

/-!
# Actual calibrated matching numerator

Matching-prime removal preserves the calibration character and the entire
cofactor row.  Its native annular puncture is a difference of two complete
calibrated cofactor sums, at scales `Q` and `Q / Norm(p)`.  The actual
complete-period mean is zero on a nonempty calibration, including cofactor
one.  No estimate of the growing-cofactor sum or whole probe is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.CalibratedMatching
open OAI OAI.CanonicalRowCompletion OAI.ConcretePrimeRowBridge
open OAI.CompletedGauss OAI.ConcreteTraceCRT
open OAI.GaussianShiftedPartition
open Filter Topology
open OAI.CubicEisenstein hiding O
open OAI.SevenEighths.ProbePhysical
open OpenAIReview.CoupledSummand
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The literal calibration and cofactor phase, not an arbitrary row weight. -/
def cofactorCharacter (C : CalibrationData) (B : Ideal O) (m : O) : ℂ :=
  C.residueMonoid m * idealRowHom m B

/-- The complete native annular cofactor sum, including its height phase in `W`. -/
def cofactorAnnulus (C : CalibrationData) (B : Ideal O) (W : ℝ → ℂ) (Q : ℝ) : ℂ :=
  ∑' m : O, cofactorCharacter C B m * W (elementNorm m / Q)

/-- The actual matched row has the nonunit puncture, without removing cofactor one. -/
def puncturedAnnulus (C : CalibrationData) (B : Ideal O) (p : O)
    (W : ℝ → ℂ) (Q : ℝ) : ℂ :=
  ∑' m : O, if m ∈ (Ideal.span {p} : Ideal O) then 0 else
    cofactorCharacter C B m * W (elementNorm m / Q)

theorem cofactorCharacter_mul (C : CalibrationData) (B : Ideal O) (a b : O) :
    cofactorCharacter C B (a*b) = cofactorCharacter C B a * cofactorCharacter C B b := by
  rw [cofactorCharacter, map_mul, idealRowHom_argument_mul]
  simp only [cofactorCharacter]
  ring

theorem cofactor_annular_summable (C : CalibrationData) (B : Ideal O)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (Q : ℝ) (hQ : 0<Q) :
    Summable (fun m : O => cofactorCharacter C B m * W (elementNorm m / Q)) := by
  apply summable_of_hasFiniteSupport
  exact (elementWindow_finite_support W hW Q hQ).subset
    (Function.support_mul_subset_right _ _)

/-- Pulling the excluded principal ideal back by `m=p*a` retains all characters. -/
theorem divisible_annulus_eq (C : CalibrationData) (B : Ideal O)
    (p : O) (hp : p≠0) (W : ℝ → ℂ) (Q : ℝ) :
    (∑' m : O, if m ∈ (Ideal.span {p} : Ideal O) then
      cofactorCharacter C B m * W (elementNorm m / Q) else 0) =
      cofactorCharacter C B p * cofactorAnnulus C B W (Q / elementNorm p) := by
  let f (m : O) : ℂ := if m ∈ (Ideal.span {p} : Ideal O) then
    cofactorCharacter C B m * W (elementNorm m / Q) else 0
  have hf : Function.support f ⊆ Set.range (fun a : O => p*a) := by
    intro m hm
    by_cases hmem : m ∈ (Ideal.span {p} : Ideal O)
    · obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hmem
      exact ⟨a,ha.symm⟩
    · exact (hm (by simp [f,hmem])).elim
  have he := (mul_right_injective₀ hp).tsum_eq hf
  have hpm (a : O) : p*a ∈ (Ideal.span {p} : Ideal O) :=
    Ideal.mem_span_singleton.mpr (dvd_mul_right p a)
  calc
    _ = ∑' a : O, f (p*a) := he.symm
    _ = ∑' a : O, cofactorCharacter C B p *
        (cofactorCharacter C B a * W (elementNorm a / (Q / elementNorm p))) := by
      apply tsum_congr
      intro a
      simp only [f,hpm a,ite_true,cofactorCharacter_mul,elementNorm_mul]
      have hv : elementNorm p * elementNorm a / Q =
          elementNorm a / (Q / elementNorm p) := by rw [div_div_eq_mul_div]; ring
      rw [hv]
      ring
    _ = _ := by rw [tsum_mul_left]; rfl

/-- Exact native puncture: fixed cofactor Poisson and growing cofactor Poisson
have different conductors, and neither sum is discarded here. -/
theorem puncturedAnnulus_eq (C : CalibrationData) (B : Ideal O)
    (p : O) (hp : p≠0) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Q : ℝ) (hQ : 0<Q) :
    puncturedAnnulus C B p W Q = cofactorAnnulus C B W Q -
      cofactorCharacter C B p * cofactorAnnulus C B W (Q / elementNorm p) := by
  let f (m : O) : ℂ := cofactorCharacter C B m * W (elementNorm m / Q)
  let g (m : O) : ℂ := if m ∈ (Ideal.span {p} : Ideal O) then f m else 0
  have hf : Summable f := cofactor_annular_summable C B W hW Q hQ
  have hg : Summable g := by
    exact hf.indicator {m : O | m ∈ (Ideal.span {p} : Ideal O)}
  calc
    _ = (∑' m : O, (f m - g m)) := by
      apply tsum_congr
      intro m
      by_cases hm : m ∈ (Ideal.span {p} : Ideal O) <;> simp [f,g,hm]
    _ = _ := by
      rw [hf.tsum_sub hg]
      change cofactorAnnulus C B W Q -
        (∑' m : O, if m ∈ (Ideal.span {p} : Ideal O) then
          cofactorCharacter C B m * W (elementNorm m / Q) else 0) = _
      rw [divisible_annulus_eq C B p hp W Q]

/-- The joined matching atom retains the literal calibration and all cofactor phases. -/
theorem calibrated_matching_atom (C : CalibrationData) (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal] [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (B : Ideal O) (A m : O)
    (hA : (Ideal.span {A} : Ideal O) = (Ideal.span {p})^(6*t+1)*B) :
    calibratedNumerator C A m * sexticGauss p hp (-m) =
      (actualSextic (Ideal.span {p}) hg (-1) *
        gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
      (if m ∈ (Ideal.span {p} : Ideal O) then 0 else cofactorCharacter C B m) := by
  unfold calibratedNumerator
  rw [hA,mul_assoc,matching_cofactor_atom p hp hg t B m]
  split_ifs <;> simp [cofactorCharacter,mul_comm,mul_left_comm,mul_assoc]

/-- Native physical matching joins before norms into two complete calibrated
cofactor annuli; the unit cofactor and the full height/window weight survive. -/
theorem calibrated_matching_annulus_eq (C : CalibrationData) (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal] [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (B : Ideal O) (A : O)
    (hA : (Ideal.span {A} : Ideal O) = (Ideal.span {p})^(6*t+1)*B)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (Q : ℝ) (hQ : 0<Q) :
    (∑' m : O, calibratedNumerator C A m * sexticGauss p hp (-m) *
      W (elementNorm m / Q)) =
      (actualSextic (Ideal.span {p}) hg (-1) *
        gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
      (cofactorAnnulus C B W Q - cofactorCharacter C B p *
        cofactorAnnulus C B W (Q / elementNorm p)) := by
  rw [←puncturedAnnulus_eq C B p hp W hW Q hQ]
  unfold puncturedAnnulus
  rw [←tsum_mul_left]
  apply tsum_congr
  intro m
  rw [calibrated_matching_atom C p hp hg t B A m hA]
  by_cases hm : m ∈ (Ideal.span {p} : Ideal O) <;> simp [hm,mul_assoc]

/-- Nonempty actual calibration kills the complete-period mean even on a
matching column. This is not an annular or growing-conductor bound. -/
theorem calibrated_matching_period_zero (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (hSne : S.Nonempty)
    (p : O) (hp : p≠0) [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})] (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (t : ℕ) (B : Ideal O)
    (A : O) (hA : A≠0)
    (hmatch : (Ideal.span {A} : Ideal O) = (Ideal.span {p})^(6*t+1)*B)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*p)) :
    (∑' m : O ⧸ Ideal.span {((calibrationForSet S hS).generator*A)*p},
      if representative (((calibrationForSet S hS).generator*A)*p) m ∈
          (Ideal.span {p} : Ideal O) then 0 else
        cofactorCharacter (calibrationForSet S hS) B
          (representative (((calibrationForSet S hS).generator*A)*p) m)) = 0 := by
  let C := calibrationForSet S hS
  let c := actualSextic (Ideal.span {p}) hg (-1) *
    gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)
  have hc0 : c≠0 := actual_matching_constant_ne_zero p hp hg hc
  have hz : actualPhysicalFourier C A p hA hp 0=0 := by
    rw [actualPhysicalFourier_eq,actualCongruenceCoefficient_zero_frequency S hS hSne A p hA hp hcop,mul_zero]
  have he : actualPhysicalFourier C A p hA hp 0 = c *
      (∑' m : O ⧸ Ideal.span {(C.generator*A)*p},
        if representative ((C.generator*A)*p) m ∈ (Ideal.span {p} : Ideal O) then 0 else
          cofactorCharacter C B (representative ((C.generator*A)*p) m)) := by
    unfold actualPhysicalFourier
    simp only [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one]
    simp_rw [calibrated_matching_atom C p hp hg t B A _ hmatch]
    rw [tsum_mul_left]
  rw [he] at hz
  exact (mul_eq_zero.mp hz).resolve_left hc0

/-- After exact prime removal, `C.generator*b*p` is an honest period of the
literal calibrated cofactor character and nonunit puncture. -/
theorem punctured_cofactor_congr (C : CalibrationData) (b p m n : O)
    (hd : m-n ∈ (Ideal.span {(C.generator*b)*p} : Ideal O)) :
    (if m ∈ (Ideal.span {p} : Ideal O) then 0 else
      cofactorCharacter C (Ideal.span {b}) m) =
    (if n ∈ (Ideal.span {p} : Ideal O) then 0 else
      cofactorCharacter C (Ideal.span {b}) n) := by
  have hdiv := Ideal.mem_span_singleton.mp hd
  have hCb : m-n ∈ (Ideal.span {C.generator*b} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right (C.generator*b) p).trans hdiv)
  have hP : m-n ∈ (Ideal.span {p} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_left p (C.generator*b)).trans hdiv)
  have hquot := Ideal.Quotient.eq.mpr hP
  have hmem : m ∈ (Ideal.span {p} : Ideal O) ↔ n ∈ (Ideal.span {p} : Ideal O) := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,←Ideal.Quotient.eq_zero_iff_mem,hquot]
  have hchar : cofactorCharacter C (Ideal.span {b}) m =
      cofactorCharacter C (Ideal.span {b}) n := calibratedNumerator_congr C b m n hCb
  by_cases hm : m ∈ (Ideal.span {p} : Ideal O)
  · simp [hm,hmem.mp hm]
  · simp [hm,mt hmem.mpr hm,hchar]

/-- The native numerator scale is exactly `Nc*X*Y`; a calibrated cofactor
period of norm `Nc*Y*B` therefore has scale ratio `X/B`. -/
theorem native_scale_div_conductor (C : CalibrationData) (X Y B : ℝ)
    (hY : Y≠0) (hB : B≠0) :
    lowPhysicalScale C X Y / (elementNorm C.generator * Y * B) = X/B := by
  have hC : elementNorm C.generator ≠ 0 := (calibration_elementNorm_pos C).ne'
  unfold lowPhysicalScale
  field_simp

/-- The native exact period in the preceding theorem has ratio `X/Norm(b)`;
this uses the literal Eisenstein ideal norm, not a random cofactor model. -/
theorem native_period_scale_ratio (C : CalibrationData) (p b : O)
    (hp : p≠0) (hb : b≠0) (X : ℝ) :
    lowPhysicalScale C X (elementNorm p) / elementNorm ((C.generator*b)*p) =
      X / elementNorm b := by
  simp only [elementNorm_mul]
  have hden : elementNorm C.generator * elementNorm b * elementNorm p =
      elementNorm C.generator * elementNorm p * elementNorm b := by ring
  rw [hden]
  exact native_scale_div_conductor C X _ _ (elementNorm_pos p hp).ne' (elementNorm_pos b hb).ne'

/-- Pinned paper geometry, Eq.12.4 and Eq.15.1: an `A=P*B`, `J=1`
Gaussian-centered cofactor has exponent `11/16`, independently of slot depth. -/
theorem gaussian_cofactor_exponent (d : ℝ) :
    (1+(1:ℝ)/6-d)-((23:ℝ)/48-d) = (11:ℝ)/16 := by ring

/-- After matching-prime removal, the honest cofactor-period exponent exceeds
the native annular numerator exponent by `1/3+d`. -/
theorem native_conductor_gap (d : ℝ) :
    ((5:ℝ)/6-2*d)-((23:ℝ)/48-d)-(11:ℝ)/16 = -(1:ℝ)/3-d := by ring

/-- The exact nominal growing-cofactor ratio, not a bound on the signed row. -/
theorem growing_cofactor_scale_ratio (C : CalibrationData) (Z d : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^((17:ℝ)/48-d)) (Z^((23:ℝ)/48-d)) /
      (elementNorm C.generator * Z^((23:ℝ)/48-d) * Z^((11:ℝ)/16)) =
      Z^(-(1:ℝ)/3-d) := by
  rw [native_scale_div_conductor C _ _ _ (Real.rpow_pos_of_pos hZ _).ne'
    (Real.rpow_pos_of_pos hZ _).ne', ←Real.rpow_sub hZ]
  congr 1
  ring

/-- The complete-period mean-zero Poisson regime is not uniform over native
Gaussian-centered growing cofactors: its nominal scale ratio tends to zero.
This does not assert a lower bound on any signed character sum. -/
theorem growing_cofactor_scale_ratio_tendsto_zero (C : CalibrationData) (d : ℝ)
    (hd : 0≤d) :
    Tendsto (fun Z : ℝ =>
      lowPhysicalScale C (Z^((17:ℝ)/48-d)) (Z^((23:ℝ)/48-d)) /
        (elementNorm C.generator * Z^((23:ℝ)/48-d) * Z^((11:ℝ)/16)))
      atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (y:=(1:ℝ)/3+d) (by linarith)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  rw [growing_cofactor_scale_ratio C Z d hZ]
  congr 1
  ring

/-- Cofactor one has the different native ratio `X`, and has not been removed
from the puncture or the actual matched-prime identity. -/
theorem unit_cofactor_scale_ratio (C : CalibrationData) (Z d : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^((17:ℝ)/48-d)) (Z^((23:ℝ)/48-d)) /
      (elementNorm C.generator * Z^((23:ℝ)/48-d)) = Z^((17:ℝ)/48-d) := by
  simpa using native_scale_div_conductor C (Z^((17:ℝ)/48-d))
    (Z^((23:ℝ)/48-d)) 1 (Real.rpow_pos_of_pos hZ _).ne' one_ne_zero

/-- All native slot depths have a growing fixed-cofactor numerator ratio. -/
theorem unit_cofactor_scale_ratio_tendsto_atTop (C : CalibrationData) (d : ℝ)
    (hd : d≤(1:ℝ)/6) :
    Tendsto (fun Z : ℝ =>
      lowPhysicalScale C (Z^((17:ℝ)/48-d)) (Z^((23:ℝ)/48-d)) /
        (elementNorm C.generator * Z^((23:ℝ)/48-d))) atTop atTop := by
  have h := tendsto_rpow_atTop (y:=(17:ℝ)/48-d) (by linarith)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  exact (unit_cofactor_scale_ratio C Z d hZ).symm

end OpenAIReview.CalibratedMatching

#lint+ in OpenAIReview.CalibratedMatching

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
  unless declarations>0 do throwError "Empty actual calibrated matching audit."
  logInfo m!"Actual calibrated matching audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-joint-cofactor-source"
  IO.FS.writeFile ".lake/arithmetic-operator-joint-cofactor-source/axioms.json"
    (Json.mkObj [("scope",toJson "actual calibrated native annular puncture and complete-period zero; no whole-probe estimate or zero-source asymptotic"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
