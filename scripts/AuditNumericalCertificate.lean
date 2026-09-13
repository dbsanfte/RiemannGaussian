import NumericalCertificate
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-!
# Axiom and declaration audit for the optional numerical proof closure

Run after `lake build NumericalCertificate --wfail`. The audit checks all
project declarations in that environment, including every generated table.
The expected unconditional literal-count statements are checked explicitly
before a successful audit report is written.
-/

open Lean Elab Command

set_option Elab.async false
set_option maxHeartbeats 0

/-- This type check forbids a remaining complete-cover or arithmetic premise. -/
private theorem auditedDyadic : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ((6731 : ℝ) / 10000) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
      Zeta23.N0simple T (2 * T) :=
  RiemannGaussian.Zeta23InverseSampling.simpleCritical_6731_eventually

/-- The cumulative bound must use the same literal counting functions. -/
private theorem auditedCumulative : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ((6731 : ℝ) / 10000) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T :=
  RiemannGaussian.Zeta23InverseSampling.simpleCritical_6731_cumulative_eventually

/-- Retain the proved exact coefficient before rounding the headline bound. -/
private theorem auditedExactCumulative : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (RiemannGaussian.Zeta23InverseSampling.sevenWindowTargetCoefficient - ε) *
      (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T :=
  RiemannGaussian.Zeta23InverseSampling.simpleCritical_sevenWindow_cumulative

#print axioms RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate.CertificateData.Cover.checked
#print axioms RiemannGaussian.Zeta23InverseSampling.sevenWindow_compact_floor
#print axioms RiemannGaussian.Zeta23InverseSampling.simpleCritical_sevenWindow
#print axioms RiemannGaussian.Zeta23InverseSampling.simpleCritical_6731_eventually
#print axioms RiemannGaussian.Zeta23InverseSampling.simpleCritical_6731_cumulative_eventually

#lint- in RiemannGaussian

run_cmd do
  let env ← getEnv
  let checkAxioms (name : Name) : CommandElabM Unit := do
    for axiomName in (← Lean.collectAxioms name) do
      unless axiomName == ``propext || axiomName == ``Classical.choice ||
          axiomName == ``Quot.sound do
        throwError "unexpected transitive axiom in {name}: {axiomName}"
  -- Earlier command diagnostics need not remain in the current message log.
  -- Inspect the actual proofs of the fixed, unconditional statement checks.
  for name in #[``auditedDyadic, ``auditedCumulative, ``auditedExactCumulative] do
    let some info := env.checked.get.find? name
      | throwError "missing certificate statement check: {name}"
    unless info.isTheorem do throwError "certificate statement check is not a theorem: {name}"
    checkAxioms name
  let mut modules : Nat := 0
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    unless (`RiemannGaussian).isPrefixOf env.header.moduleNames[i] do continue
    modules := modules + 1
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      checkAxioms ci.name
  let report := Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("leanVersion", toJson Lean.versionString),
    ("target", toJson "NumericalCertificate"),
    ("compiledProjectModules", toJson modules),
    ("projectDeclarations", toJson declarations),
    ("projectTheorems", toJson theorems),
    ("axiomAudit", toJson "passed: only propext, Classical.choice, Quot.sound"),
    ("certificateStatus", toJson "proved: 6731/10000 for literal simple critical-line zeros"),
    ("scope", toJson "eventual dyadic and cumulative counts; height threshold not numerically evaluated")]
  IO.FS.createDirAll ".lake/numerical-certificate"
  IO.FS.writeFile ".lake/numerical-certificate/audit.json" (report.pretty ++ "\n")
  logInfo m!"Audited {theorems} theorems in {modules} project modules; unconditional literal-count type checks passed."
