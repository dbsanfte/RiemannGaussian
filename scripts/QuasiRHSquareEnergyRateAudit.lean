/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native square-sector energy rate

This isolated leaf checks the exact physical exponent after an independently
supplied raw square-energy bound. It does not import the Broeker--Hoffstein
residue formula, the cubic large sieve, or a new bound on actual theta
coefficients. In particular it does not assign a source to the square sector.
The original moving numerator and physical-prime lengths are both retained.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace OpenAIReview.SquareEnergyRate

/-- Numerator norm volume after the original unselected-length compensation. -/
def numeratorRate (d : ℝ) : ℝ := 5/6-2*d

/-- The actual physical-prime norm volume, not the shorter residual label. -/
def physicalRate (d : ℝ) : ℝ := 23/48-d

/-- Rate of `Q^(e/2) Y^(-1/3)` after Cauchy, conditional on raw energy `Q^e`.
The separate native companion energy and normalization must still be proved. -/
def cost (e d : ℝ) : ℝ := (e/2)*numeratorRate d-physicalRate d/3

theorem cost_eq (e d : ℝ) :
    cost e d = 5*e/12-23/144+d*(1/3-e) := by
  unfold cost numeratorRate physicalRate
  ring

/-- A saving in the raw energy produces this exact native saving. -/
theorem energy_saving_eq (η d : ℝ) :
    cost (5/6-η) d = 3/16-5*η/12-d*(1/2-η) := by
  rw [cost_eq]
  ring

/-- The exponent of the unselected length is nonpositive in this range. -/
theorem no_unselected_length_loss {η : ℝ} (hη : η≤1/2) :
    1/3-(5/6-η)≤0 := by linarith

theorem depth_zero_is_worst {η d : ℝ} (hη : η≤1/2) (hd : 0≤d) :
    cost (5/6-η) d≤3/16-5*η/12 := by
  rw [energy_saving_eq]
  have h := mul_nonneg hd (show 0≤1/2-η by linarith)
  linarith

/-- Exact energy improvement needed at the present lowest beta, before losses. -/
theorem minimum_energy_saving_iff (η : ℝ) :
    7/8-8749/10000+1/250000 < 5*η/12 ↔ 156/625000<η := by
  constructor <;> intro h <;> linarith

/-- A small, nonoptimal conditional target already leaves positive room. -/
theorem tiny_target_margin :
    5*(1/2000:ℝ)/12-(7/8-8749/10000+1/250000)=313/3000000 := by
  norm_num

/-- The candidate contour plus cubic-sieve energy has no adverse depth cost. -/
theorem half_energy_cost (d : ℝ) : cost (1/2) d=7/144-d/6 := by
  rw [cost_eq]
  ring

theorem half_energy_uniform {d : ℝ} (hd : 0≤d) : cost (1/2) d≤7/144 := by
  rw [half_energy_cost]
  linarith

/-- The coefficient-convolution conjecture is stronger than necessary here. -/
theorem third_energy_cost (d : ℝ) : cost (1/3) d= -(1/48:ℝ) := by
  rw [cost_eq]
  ring

/-- Exact spare exponent at the lower endpoint, including the retained margin. -/
theorem half_energy_margin :
    (8749/10000-11/16-1/250000:ℝ)-7/144=156133/1125000 := by
  norm_num

/-- Any independently paid additional losses below this margin still fit.
This is an exponent implication, not the missing theta/source transport. -/
theorem half_energy_below_source {β d loss : ℝ}
    (hβ : 8749/10000≤β) (hd : 0≤d)
    (hloss : loss<156133/1125000) :
    cost (1/2) d+loss<β-11/16-1/250000 := by
  have hc := half_energy_uniform hd
  linarith

end OpenAIReview.SquareEnergyRate
#lint+ in OpenAIReview.SquareEnergyRate

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
  logInfo m!"Square energy rate: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-energy-rate"
  IO.FS.writeFile ".lake/arithmetic-operator-square-energy-rate/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
