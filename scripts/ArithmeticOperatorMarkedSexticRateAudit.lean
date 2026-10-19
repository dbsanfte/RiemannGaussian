/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Rate gate for a prescribed-coefficient mean with the physical mark retained

This leaf checks rational exponents only. It does NOT import the new
structured mean theorem or prove applicability to native profiles/marks.
Even granting its positive fourth-power-label average, the physical prime
is a label of length Y', unless an exact additional cancellation removes it.
It is not just a label of length Z^(1/6-d). The native cubic CRT phase
must be accounted for before using a prescribed-coefficient theorem.

At H=V=1, the candidate squared mean is
min(Q+U*Y', Q+Q*Y'). Cauchy over the coherently summed physical primes
and the actual native normalizers give the rate calculated below.
Failure of this candidate budget is not a lower bound for the actual sum.
-/

set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.ArithmeticOperatorMarkedSexticRateAudit

/-- Physical-prime norm length. -/
def physicalMark (d : ℝ) : ℝ := 23/48-d

/-- Numerator norm volume. -/
def numerator (d : ℝ) : ℝ := 5/6-2*d

/-- Residual cofactor norm length at H=V=1. -/
def cofactor : ℝ := 11/16

/-- Candidate positive label-average exponent with the PHYSICAL label. -/
def averagedMean (d : ℝ) : ℝ :=
  min (max (numerator d) (cofactor+physicalMark d))
    (max (numerator d) (numerator d+physicalMark d))

/-- Cauchy/normalization cost, conditional on the candidate analytic mean. -/
def markedRate (d : ℝ) : ℝ := (averagedMean d-physicalMark d)/2-d/2

/-- Both labelled terms dominate the unlabelled numerator term. -/
theorem averagedMean_eq {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    averagedMean d = min (7/6-d) (21/16-3*d) := by
  unfold averagedMean numerator cofactor physicalMark
  rw [max_eq_right (by linarith),max_eq_right (by linarith)]
  congr 1 <;> ring

/-- Exact normalized rate after the surviving fourth-power prime label. -/
theorem markedRate_eq {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    markedRate d = min (11/32-d/2) (5/12-(3/2)*d) := by
  unfold markedRate
  rw [averagedMean_eq hd hd']
  unfold physicalMark
  by_cases h : d≤7/96
  · rw [min_eq_left (by linarith),min_eq_left (by linarith)]
    ring
  · rw [min_eq_right (by linarith),min_eq_right (by linarith)]
    ring

/-- The structured estimate does not give its unlabelled rate at depth zero. -/
theorem markedRate_zero : markedRate 0=11/32 := by
  rw [markedRate_eq (by norm_num) (by norm_num)]
  norm_num

/-- Exact shortfall of this marked positive-average route at shallow depth. -/
theorem shallow_deficit : markedRate 0-3/16=5/32 := by
  rw [markedRate_zero]
  norm_num

/-- Only the deepest part of this range improves the old normalized target. -/
theorem markedRate_lt_baseline_iff {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    markedRate d<3/16 ↔ 11/72<d := by
  rw [markedRate_eq hd hd',min_lt_iff]
  constructor
  · rintro (h|h) <;> linarith
  · intro h
    right
    linarith

/-- Candidate deep-end rate; its analytic/native hypotheses remain unproved. -/
theorem markedRate_deep : markedRate (1/6)=1/6 := by
  rw [markedRate_eq (by norm_num) (by norm_num)]
  norm_num

/-- The earlier generic sextic norm budget, for comparison only. -/
def genericRate (d : ℝ) : ℝ := max (2/9-(5/6)*d) (107/576-d/3)

/-- In the full tested interval this positive-average marked route is worse
than the earlier generic norm budget by at least 7/192. This is a comparison
of candidate upper-budget exponents, not an impossibility theorem. -/
theorem genericRate_add_le_markedRate {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    genericRate d+7/192≤markedRate d := by
  rw [markedRate_eq hd hd']
  unfold genericRate
  by_cases h : d≤7/96
  · rw [max_eq_left (by linarith),min_eq_left (by linarith)]
    linarith
  · rw [max_eq_right (by linarith),min_eq_right (by linarith)]
    linarith

/-- A complete period for two distinct marked primes is longer than the
native numerator window by Z^(1/8), at every compensation depth. -/
theorem sameProduct_period_deficit (d : ℝ) :
    numerator d-2*physicalMark d = -(1/8 : ℝ) := by
  unfold numerator physicalMark
  ring

/-- Triple mark incidences cannot fit the shallow product exponent. -/
theorem shallow_three_mark_margin :
    3*physicalMark 0-(7/6 : ℝ)=13/48 := by
  norm_num [physicalMark]

/-- Four mark incidences have a uniform positive product-length margin.
Actual incidence cardinality requires the separate norm-product argument. -/
theorem four_mark_margin {d : ℝ} (hd : d≤1/6) :
    1/4≤4*physicalMark d-(7/6-d) := by
  unfold physicalMark
  linarith

end RiemannGaussian.ArithmeticOperatorMarkedSexticRateAudit

#lint+ in RiemannGaussian.ArithmeticOperatorMarkedSexticRateAudit

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
  unless declarations>0 do throwError "Empty marked rate audit."
  logInfo m!"Marked rate audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-marked-correlation"
  IO.FS.writeFile ".lake/arithmetic-operator-marked-correlation/rate-axioms.json"
    (Json.mkObj [("scope",toJson "rational conditional positive-average budget with physical mark; no imported analytic mean, native signed estimate or zero exclusion"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
