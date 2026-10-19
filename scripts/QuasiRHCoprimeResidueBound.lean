/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# An algebraic local bound for the disjoint compensated residue

For the displayed rational local formula, the denominator stays away from
zero and the compensated mark lies strictly in the negative real half-plane.
Every positive real weighted single-slot average is consequently nonzero.
This is an algebraic local estimate only. Native identification, global
Euler continuation/nonvanishing and arbitrary coupled tuple averages are
not consequences of this leaf.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.CoprimeResidueBound

/-- The stated disjoint local residue numerator, with `s` real. -/
def residueNumerator (s : ℝ) (delta R : ℂ) : ℂ :=
  ((1-s^2 : ℝ) : ℂ) - (((1-s)^2 : ℝ) : ℂ)*delta -
    ((2*s*(1-s) : ℝ) : ℂ)*R

/-- The actual proposed compensated local mark as an explicit rational formula. -/
def compensatedMark (s : ℝ) (delta theta R : ℂ) : ℂ :=
  -(s : ℂ) + (((1-s)^2 : ℝ) : ℂ)*(theta-1)/residueNumerator s delta R

/-- Uniform positive denominator margin for the displayed parameter ranges. -/
theorem norm_residueNumerator_ge (s : ℝ) (delta R : ℂ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1/7)
    (hd : ‖delta‖ ≤ 1/4) (hR : ‖R‖ ≤ 1/49) :
    (993/1372 : ℝ) ≤ ‖residueNumerator s delta R‖ := by
  have hs1 : s ≤ 1 := by linarith
  have hsub : 0 ≤ 1-s := by linarith
  have hsq : s^2 ≤ 1/49 := by nlinarith
  have hmain : 0 ≤ 1-s^2 := by nlinarith
  have hcoef : 0 ≤ (1-s)^2 ∧ (1-s)^2 ≤ 1 := by
    constructor
    · positivity
    · nlinarith
  have hcoefR : 0 ≤ 2*s*(1-s) ∧ 2*s*(1-s) ≤ 2/7 := by
    constructor
    · positivity
    · nlinarith [sq_nonneg s]
  have hd' : (1-s)^2*‖delta‖ ≤ 1/4 := by
    calc
      _ ≤ 1*‖delta‖ := mul_le_mul_of_nonneg_right hcoef.2 (norm_nonneg _)
      _ ≤ 1/4 := by simpa using hd
  have hR' : (2*s*(1-s))*‖R‖ ≤ 2/343 := by
    calc
      _ ≤ (2/7)*‖R‖ := mul_le_mul_of_nonneg_right hcoefR.2 (norm_nonneg _)
      _ ≤ (2/7)*(1/49) := mul_le_mul_of_nonneg_left hR (by norm_num)
      _ = _ := by norm_num
  have ht : ‖((1-s^2 : ℝ) : ℂ)‖ ≤ ‖residueNumerator s delta R‖ +
      ‖(((1-s)^2 : ℝ) : ℂ)*delta‖ + ‖((2*s*(1-s) : ℝ) : ℂ)*R‖ := by
    calc
      _ = ‖residueNumerator s delta R + (((1-s)^2 : ℝ) : ℂ)*delta +
          ((2*s*(1-s) : ℝ) : ℂ)*R‖ := by
            congr 1
            unfold residueNumerator
            ring
      _ ≤ ‖residueNumerator s delta R + (((1-s)^2 : ℝ) : ℂ)*delta‖ +
          ‖((2*s*(1-s) : ℝ) : ℂ)*R‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmain, abs_of_nonneg hcoef.1, abs_of_nonneg hs0,
    abs_of_nonneg hsub, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  nlinarith

/-- No denominator-zero guard is left over in this local range. -/
theorem residueNumerator_ne_zero (s : ℝ) (delta R : ℂ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1/7)
    (hd : ‖delta‖ ≤ 1/4) (hR : ‖R‖ ≤ 1/49) :
    residueNumerator s delta R ≠ 0 := by
  intro hz
  have h := norm_residueNumerator_ge s delta R hs0 hs hd hR
  rw [hz, norm_zero] at h
  norm_num at h

/-- Exact algebraic centered-mark identity before any norm is taken. -/
theorem compensatedMark_add_one_eq (s : ℝ) (delta theta R : ℂ)
    (hN : residueNumerator s delta R ≠ 0) :
    compensatedMark s delta theta R + 1 =
      (((1-s)^2 : ℝ) : ℂ) *
        ((s : ℂ)+theta-((1-s : ℝ) : ℂ)*delta-((2*s : ℝ) : ℂ)*R) /
          residueNumerator s delta R := by
  unfold compensatedMark
  field_simp [hN]
  unfold residueNumerator
  push_cast
  ring

/-- The centered numerator has the claimed fully rational absolute budget. -/
theorem norm_centered_numerator_le (s : ℝ) (delta theta R : ℂ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1/7)
    (hd : ‖delta‖ ≤ 1/4) (htheta : ‖theta‖ ≤ 1/4) (hR : ‖R‖ ≤ 1/49) :
    ‖(((1-s)^2 : ℝ) : ℂ) *
      ((s : ℂ)+theta-((1-s : ℝ) : ℂ)*delta-((2*s : ℝ) : ℂ)*R)‖ ≤
        (445/686 : ℝ) := by
  have hs1 : s ≤ 1 := by linarith
  have hsub : 0 ≤ 1-s := by linarith
  have hcoef : 0 ≤ (1-s)^2 ∧ (1-s)^2 ≤ 1 := by
    constructor
    · positivity
    · nlinarith
  have hd' : (1-s)*‖delta‖ ≤ 1/4 := by
    calc
      _ ≤ 1*‖delta‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ 1/4 := by simpa using hd
  have hR' : (2*s)*‖R‖ ≤ 2/343 := by
    calc
      _ ≤ (2/7)*‖R‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ (2/7)*(1/49) := mul_le_mul_of_nonneg_left hR (by norm_num)
      _ = _ := by norm_num
  have ht : ‖(s : ℂ)+theta-((1-s : ℝ) : ℂ)*delta-((2*s : ℝ) : ℂ)*R‖ ≤
      s+‖theta‖+(1-s)*‖delta‖+(2*s)*‖R‖ := by
    calc
      _ ≤ ‖(s : ℂ)+theta-((1-s : ℝ) : ℂ)*delta‖ +
          ‖((2*s : ℝ) : ℂ)*R‖ := norm_sub_le _ _
      _ ≤ (‖(s : ℂ)+theta‖+‖((1-s : ℝ) : ℂ)*delta‖) +
          ‖((2*s : ℝ) : ℂ)*R‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (‖(s : ℂ)‖+‖theta‖+‖((1-s : ℝ) : ℂ)*delta‖) +
          ‖((2*s : ℝ) : ℂ)*R‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs0, abs_of_nonneg hsub, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have ht' : ‖(s : ℂ)+theta-((1-s : ℝ) : ℂ)*delta-((2*s : ℝ) : ℂ)*R‖ ≤
      (445/686 : ℝ) := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef.1]
  exact (mul_le_mul_of_nonneg_right hcoef.2 (norm_nonneg _)).trans (by simpa using ht')

/-- Reusable rational local disk: its radius is strictly below nine tenths. -/
theorem norm_compensatedMark_add_one_le (s : ℝ) (delta theta R : ℂ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1/7)
    (hd : ‖delta‖ ≤ 1/4) (htheta : ‖theta‖ ≤ 1/4) (hR : ‖R‖ ≤ 1/49) :
    ‖compensatedMark s delta theta R + 1‖ ≤ (890/993 : ℝ) := by
  have hN := norm_residueNumerator_ge s delta R hs0 hs hd hR
  have hN0 : 0 < ‖residueNumerator s delta R‖ := by linarith
  rw [compensatedMark_add_one_eq s delta theta R
    (residueNumerator_ne_zero s delta R hs0 hs hd hR), norm_div]
  apply (div_le_iff₀ hN0).mpr
  have hnum := norm_centered_numerator_le s delta theta R hs0 hs hd htheta hR
  nlinarith

/-- The disk has a strict positive margin to the imaginary axis. -/
theorem compensatedMark_re_le (s : ℝ) (delta theta R : ℂ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1/7)
    (hd : ‖delta‖ ≤ 1/4) (htheta : ‖theta‖ ≤ 1/4) (hR : ‖R‖ ≤ 1/49) :
    (compensatedMark s delta theta R).re ≤ -(103/993 : ℝ) := by
  have hn := norm_compensatedMark_add_one_le s delta theta R hs0 hs hd htheta hR
  have hr := Complex.re_le_norm (compensatedMark s delta theta R+1)
  simp only [Complex.add_re, Complex.one_re] at hr
  linarith

/-- Explicit comparison with the simpler radius `9/10`. -/
theorem radius_lt_nine_tenths : (890/993 : ℝ) < 9/10 := by norm_num

/-- A positive real weighted SINGLE-SLOT average of local marks cannot
vanish. This does not apply to arbitrary products or coupled tuple weights. -/
theorem positive_weighted_sum_ne_zero {ι : Type*} (F : Finset ι)
    (w : ι → ℝ) (B : ι → ℂ)
    (hw : ∀ i∈F, 0 ≤ w i) (hmass : 0 < ∑ i∈F, w i)
    (hB : ∀ i∈F, ‖B i+1‖ ≤ (890/993 : ℝ)) :
    (∑ i∈F, (w i : ℂ)*B i) ≠ 0 := by
  have hre (i : ι) (hi : i∈F) : (B i).re ≤ -(103/993 : ℝ) := by
    have ht := Complex.re_le_norm (B i+1)
    simp only [Complex.add_re, Complex.one_re] at ht
    linarith [hB i hi]
  have hs : (∑ i∈F, (w i : ℂ)*B i).re ≤
      -(103/993 : ℝ)*(∑ i∈F, w i) := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hre i hi) (hw i hi)
  intro hz
  rw [hz, Complex.zero_re] at hs
  nlinarith

end OpenAIReview.CoprimeResidueBound

#lint+ in OpenAIReview.CoprimeResidueBound

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
  unless declarations>0 do throwError "Empty coprime residue bound."
  logInfo m!"Coprime residue bound: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-coprime-residue-bound"
  IO.FS.writeFile ".lake/arithmetic-operator-coprime-residue-bound/axioms.json"
    (Json.mkObj [("scope",toJson "algebraic local disk and positive real single-slot weighted nonvanishing only; no global Euler/source bridge"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
