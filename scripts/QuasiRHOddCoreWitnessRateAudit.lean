/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Lean.Util.CollectAxioms

/-!
# The large-odd-core norm witness: a conditional localization audit

This leaf verifies the native exponents and a finite-energy localization
implication. Neither the Xu--Sang annular Gauss asymptotic nor the fixed-odd-core
cubic estimate is imported or asserted here. Those are explicit, separate
paper inputs. The witness is NOT the prescribed marked companion, and no
source is assigned to a numerator sector. Thus this is an obstruction to a
generic norm payment, not to the original signed covariance.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open Filter
open scoped Topology

namespace OpenAIReview.OddCoreWitnessRate

/-- Native numerator norm-length exponent, with the original depth. -/
def numeratorRate (d : ℝ) : ℝ := 5/6-2*d
/-- Native physical-modulus norm-length exponent. -/
def physicalRate (d : ℝ) : ℝ := 23/48-d
/-- Squared Gauss-witness energy exponent, conditional on its asymptotic. -/
def mainRate (d : ℝ) : ℝ := 5/6*numeratorRate d-2/3*physicalRate d
/-- Largest small-core cutoff covered by the stated fixed-core budget. -/
def coreRate (d κ : ℝ) : ℝ := 4/5*(numeratorRate d-physicalRate d)-κ

theorem main_rate_eq (d : ℝ) : mainRate d=3/8-d := by
  unfold mainRate numeratorRate physicalRate
  ring

theorem native_norm_rate (d : ℝ) : mainRate d/2=3/16-d/2 := by
  rw [main_rate_eq]
  ring

theorem square_length_gap (d : ℝ) :
    2*physicalRate d-numeratorRate d=1/8 := by
  unfold physicalRate numeratorRate
  ring

theorem core_rate_eq (d κ : ℝ) : coreRate d κ=17/60-4*d/5-κ := by
  unfold coreRate numeratorRate physicalRate
  ring

theorem core_range_nonempty {d κ : ℝ} (hd : d≤1/6) (hκ : κ<3/20) :
    0<coreRate d κ := by
  rw [core_rate_eq]
  linarith

theorem core_rate_below_numerator {d κ : ℝ}
    (hd : d≤1/6) (hκ : 0≤κ) : coreRate d κ≤numeratorRate d := by
  unfold coreRate numeratorRate physicalRate
  linarith

/-- The first small-core contribution loses exactly `5*kappa/6`.
Its analytic estimate remains a paper input. -/
theorem first_core_ratio (d κ : ℝ) :
    numeratorRate d/6+5*coreRate d κ/6-mainRate d= -5*κ/6 := by
  unfold coreRate mainRate
  ring

/-- The second term gains `1/48` for EVERY depth, provided the core
range is contained in the actual numerator range. -/
theorem second_core_ratio {d h : ℝ} (hh : h≤numeratorRate d) :
    2*numeratorRate d/3+h/3-physicalRate d-mainRate d≤ -(1/48:ℝ) := by
  unfold mainRate numeratorRate physicalRate at *
  linarith

/-- The native lengths lie in the cited lower-bound paper's open
unbalanced range, with the fixed exponent margin `delta=1/10`.
This checks lengths only; it supplies no character estimate. -/
theorem lower_bound_length_window {d : ℝ} (hd0 : 0≤d) (hd1 : d≤1/6) :
    (16/11+1/10)*physicalRate d<numeratorRate d ∧
      numeratorRate d<(2-1/10)*physicalRate d := by
  unfold physicalRate numeratorRate
  constructor <;> linarith

/-- All three relative-error exponents in the annular `D=1` formula.
The finite calibration and radial-profile constants stay fixed. -/
theorem annular_relative_error_rates (d : ℝ) :
    -(2*physicalRate d-numeratorRate d)/6= -(1/48:ℝ) ∧
    -(2*physicalRate d-numeratorRate d)/12= -(1/96:ℝ) ∧
    11/6*(2*physicalRate d-numeratorRate d)-physicalRate d= -1/4+d := by
  unfold physicalRate numeratorRate
  constructor
  · ring
  constructor <;> ring

theorem last_annular_error_uniform {d : ℝ} (hd : d≤1/6) :
    -1/4+d≤ -(1/12:ℝ) := by linarith

/-- A useful explicit diagnostic cutoff, leaving positive loss margin. -/
theorem concrete_gap :
    min (5*(1/100:ℝ)/6) (1/96)=1/120 ∧
      (1/1000:ℝ)<min (5*(1/100:ℝ)/6) (1/96) := by norm_num

/-- The finite squared norm before any numerator sector is removed. -/
def energy {ι : Type*} (F : Finset ι) (a : ι→ℂ) : ℝ :=
  ∑i∈F,‖a i‖^2

/-- Literal finite partition: no term is removed before its squared
energy is joined, and no lower bound is assigned to a chosen row. -/
theorem energy_partition {ι : Type*} (F : Finset ι) (a : ι→ℂ)
    (P : ι→Prop) [DecidablePred P] :
    energy (F.filter P) a+energy (F.filter (fun i=>¬P i)) a=energy F a := by
  exact Finset.sum_filter_add_sum_filter_not F P (fun i=>‖a i‖^2)

/-- A positive norm witness with two vanishing small-core costs has
positive energy outside those cores. All analytic bounds are premises. -/
theorem eventually_outside_energy_lower {ι : Type*}
    (F : ℝ→Finset ι) (a : ℝ→ι→ℂ) (P : ℝ→ι→Prop)
    [∀Z,DecidablePred (P Z)] (scale totalError : ℝ→ℝ)
    (c C₁ C₂ κ loss : ℝ) (hc : 0<c)
    (hloss₁ : loss<5*κ/6) (hloss₂ : loss<1/48)
    (herror : Tendsto totalError atTop (𝓝 0))
    (htotal : ∀ᶠZ in atTop,
      c-totalError Z≤energy (F Z) (a Z)/scale Z)
    (hsmall : ∀ᶠZ in atTop,
      energy ((F Z).filter (P Z)) (a Z)/scale Z≤
        C₁*Z^(loss-5*κ/6)+C₂*Z^(loss-1/48)) :
    ∀ᶠZ in atTop,c/2≤
      energy ((F Z).filter (fun i=>¬P Z i)) (a Z)/scale Z := by
  have ht₁ : Tendsto (fun Z : ℝ=>Z^(loss-5*κ/6)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      tendsto_rpow_neg_atTop (show 0<5*κ/6-loss by linarith)
  have ht₂ : Tendsto (fun Z : ℝ=>Z^(loss-1/48)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      tendsto_rpow_neg_atTop (show 0<(1:ℝ)/48-loss by linarith)
  have ht : Tendsto (fun Z : ℝ=>totalError Z+
      (C₁*Z^(loss-5*κ/6)+C₂*Z^(loss-1/48))) atTop (𝓝 0) := by
    simpa using herror.add ((ht₁.const_mul C₁).add (ht₂.const_mul C₂))
  have he := ht.eventually (gt_mem_nhds (show (0:ℝ)<c/2 by linarith))
  filter_upwards [htotal,hsmall,he] with Z htotalZ hsmallZ heZ
  have hp := energy_partition (F Z) (a Z) (P Z)
  have hp' := congrArg (fun v : ℝ=>v/scale Z) hp
  rw [add_div] at hp'
  linarith

end OpenAIReview.OddCoreWitnessRate
#lint+ in OpenAIReview.OddCoreWitnessRate

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  logInfo m!"Odd-core witness rate: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-odd-core-witness-rate"
  IO.FS.writeFile ".lake/arithmetic-operator-odd-core-witness-rate/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
