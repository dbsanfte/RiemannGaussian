/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Exact budget gate for the native marked sextic large-sieve shortcut

This is rational exponent arithmetic, NOT an import of a large-sieve
theorem or a proof of applicability to the native correlated weights.
At H=V=1 and maximal physical mark, the candidate norm bound is
Q+U+Q^(5/6)U^(1/3)+Q^(1/3)U^(5/6). One must fix the literal marked prime
before the cofactor conductor is U. Even granting separated coefficients,
the normalized rate below does not beat 3/16 on 0<=d<=1/24.

The coefficients, masks, Gaussian source and other strata still require
their own transfer. Failure of this generic norm budget does not rule out
a sharper SIGNED estimate for the actual joined coefficients.
-/

set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.ArithmeticOperatorSexticRateAudit

/-- The actual marked-prime length exponent in this stratum. -/
def markExponent (d : ℝ) : ℝ := 23/48-d

/-- The numerator-row norm length exponent. -/
def rowExponent (d : ℝ) : ℝ := 5/6-2*d

/-- The cofactor conductor excludes the fixed marked prime. -/
def cofactorExponent : ℝ := 11/16

/-- The four terms of the candidate sextic squared-operator-norm estimate. -/
def normExponent (d : ℝ) : ℝ :=
  max (max (rowExponent d) cofactorExponent)
    (max ((5/6)*rowExponent d+(1/3)*cofactorExponent)
      ((1/3)*rowExponent d+(5/6)*cofactorExponent))

/-- After the native normalizer and joined d-compensation. An applicability
proof for the arithmetic statistic is not part of this definition. -/
def sexticRate (d : ℝ) : ℝ := (normExponent d-markExponent d)/2-d/2

/-- The two mixed norm terms dominate the linear ones on this d interval. -/
theorem normExponent_eq {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    normExponent d = max (133/144-(5/3)*d) (245/288-(2/3)*d) := by
  have he₁ : (5/6)*rowExponent d+(1/3)*cofactorExponent = 133/144-(5/3)*d := by
    unfold rowExponent cofactorExponent
    ring
  have he₂ : (1/3)*rowExponent d+(5/6)*cofactorExponent = 245/288-(2/3)*d := by
    unfold rowExponent cofactorExponent
    ring
  unfold normExponent
  rw [he₁,he₂]
  apply max_eq_right
  apply max_le
  · apply le_trans _ (le_max_left _ _)
    unfold rowExponent
    linarith
  · apply le_trans _ (le_max_right _ _)
    unfold cofactorExponent
    linarith

/-- The exact two-branch normalized budget. -/
theorem sexticRate_eq {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    sexticRate d = max (2/9-(5/6)*d) (107/576-d/3) := by
  unfold sexticRate
  rw [normExponent_eq hd hd']
  unfold markExponent
  by_cases h : d≤7/96
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    ring

/-- The critical shallow stratum has a worse budget than 3/16. -/
theorem sexticRate_zero : sexticRate 0 = 2/9 := by
  rw [sexticRate_eq (by norm_num) (by norm_num)]
  norm_num

/-- The residual normalized exponent cost at the shallow endpoint. -/
theorem shallow_deficit : sexticRate 0-3/16 = 5/144 := by
  rw [sexticRate_zero]
  norm_num

/-- This candidate budget improves 3/16 exactly beyond d=1/24.
This does not say that no other arithmetic bound can improve it. -/
theorem sexticRate_lt_baseline_iff {d : ℝ} (hd : 0≤d) (hd' : d≤1/6) :
    sexticRate d<3/16 ↔ 1/24<d := by
  rw [sexticRate_eq hd hd',max_lt_iff]
  constructor
  · intro h
    linarith [h.1]
  · intro h
    constructor <;> linarith

/-- Equality, not a saving, at the transition. -/
theorem sexticRate_transition : sexticRate (1/24) = 3/16 := by
  rw [sexticRate_eq (by norm_num) (by norm_num)]
  norm_num

/-- The mixed terms exchange dominance at equal row/cofactor length. -/
theorem balanced_transition :
    rowExponent (7/96)=cofactorExponent ∧ sexticRate (7/96)=31/192 := by
  rw [sexticRate_eq (by norm_num) (by norm_num)]
  norm_num [rowExponent,cofactorExponent]

/-- Deep-stratum candidate gain, subject to the native coefficient bridge. -/
theorem sexticRate_deep : sexticRate (1/6)=25/192 := by
  rw [sexticRate_eq (by norm_num) (by norm_num)]
  norm_num

/-- A joint saving must exceed this threshold for a strict shallow improvement. -/
theorem extra_saving_required (gain : ℝ) :
    sexticRate 0-gain<3/16 ↔ 5/144<gain := by
  rw [sexticRate_zero]
  constructor <;> intro h <;> linarith

/-- Counterfactual quadratic norm budget; no native sextic character
has been replaced by a quadratic character in the actual arithmetic. -/
def quadraticIdealization (d : ℝ) : ℝ :=
  (max (rowExponent d) cofactorExponent-markExponent d)/2-d/2

/-- The quadratic idealization must still retain the marked-prime cost. -/
theorem quadraticIdealization_eq (d : ℝ) :
    quadraticIdealization d = max (17/96-d) (5/48) := by
  unfold quadraticIdealization rowExponent cofactorExponent markExponent
  by_cases h : d≤7/96
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    ring

/-- The optimistic quadratic ledger has only 1/96 margin at d=0. -/
theorem quadraticIdealization_shallow_margin :
    3/16-quadraticIdealization 0=1/96 := by
  rw [quadraticIdealization_eq]
  norm_num

end RiemannGaussian.ArithmeticOperatorSexticRateAudit

#lint+ in RiemannGaussian.ArithmeticOperatorSexticRateAudit

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
  unless declarations>0 do throwError "Empty sextic rate audit."
  logInfo m!"Sextic rate audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-quadratic-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-native-quadratic-gate/rate-axioms.json"
    (Json.mkObj [("scope",toJson "exact rational budget only, H=V=1; no analytic large-sieve import, native applicability or source estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
