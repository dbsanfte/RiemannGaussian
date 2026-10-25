import RiemannGaussian
import RiemannGaussian.SuzukiLocalCancellationCriterion
import RiemannGaussian.SuzukiLocalCancellationKernel
import RiemannGaussian.SuzukiLocalCancellationPrimePowers
import RiemannGaussian.SuzukiLocalCancellationArithmeticBound
import RiemannGaussian.SuzukiLocalCancellationLogSampling
import RiemannGaussian.SuzukiLocalCancellationSharedPrime
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Ordinary-root publication audit: all declaration linters
and all transitive axiom dependencies, including private generated helpers. -/

open Lean Elab Command
set_option maxHeartbeats 0

run_cmd do
  let targets := #[
    `RiemannGaussian.SuzukiLocalCancellation,
    `RiemannGaussian.SuzukiLocalCancellationBoundary,
    `RiemannGaussian.SuzukiLocalCancellationTransfer,
    `RiemannGaussian.SuzukiLocalCancellationKernel,
    `RiemannGaussian.SuzukiLocalCancellationPrimePowers,
    `RiemannGaussian.SuzukiLocalCancellationCriterion,
    `RiemannGaussian.SuzukiLocalCancellationPhysical,
    `RiemannGaussian.SuzukiLocalCancellationSampling,
    `RiemannGaussian.SuzukiLocalCancellationMoment,
    `RiemannGaussian.SuzukiLocalCancellationLogSampling,
    `RiemannGaussian.SuzukiLocalCancellationSharedPrime,
    `RiemannGaussian.SuzukiLocalCancellationPrimitiveBound,
    `RiemannGaussian.SuzukiLocalCancellationExplicitBound,
    `RiemannGaussian.SuzukiLocalCancellationArithmeticBound]
  let env ← getEnv
  let checks ← liftCoreM <| Batteries.Tactic.Lint.getChecks true none none
  let mut modules : Array Json := #[]
  for target in targets do
    let mut found := false
    let mut decls : Array Name := #[]
    let mut theoremCount : Nat := 0
    let mut reports : Array Json := #[]
    for i in [:env.header.moduleNames.size] do
      unless env.header.moduleNames[i]! == target do continue
      found := true
      for ci in env.header.moduleData[i]!.constants do
        decls := decls.push ci.name
        if ci.isAxiom then throwError "Project-defined axiom: {ci.name}"
        let dependencies ← Lean.collectAxioms ci.name
        for ax in dependencies do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected transitive axiom in {ci.name}: {ax}"
        if ci.isTheorem then theoremCount := theoremCount + 1
        reports := reports.push (Json.mkObj [
          ("declaration", toJson ci.name.toString),
          ("isTheorem", toJson ci.isTheorem),
          ("axioms", toJson (dependencies.map Name.toString))])
    unless found && theoremCount > 0 do throwError "Missing or empty target: {target}"
    let lintResults ← liftCoreM <| Batteries.Tactic.Lint.lintCore decls checks (some target)
    for (linter, results) in lintResults do
      for (decl, message) in results.toArray do
        throwError "{target}: {linter.name}: {decl}: {message}"
    modules := modules.push (Json.mkObj [
      ("module", toJson target.toString),
      ("declarations", toJson decls.size),
      ("theoremsIncludingHelpers", toJson theoremCount),
      ("declarationLinters", toJson checks.size),
      ("onlyStandardAxioms", toJson true),
      ("rootRegistered", toJson true),
      ("details", Json.arr reports)])
    logInfo m!"Checked {target}: {decls.size} declarations, {theoremCount} theorems, {checks.size} linters; only standard axioms."
  IO.FS.createDirAll ".lake/suzuki-local-cancellation"
  IO.FS.writeFile ".lake/suzuki-local-cancellation/audit.json"
    (Json.mkObj [("modules", Json.arr modules)]).pretty

#print axioms RiemannGaussian.riemannHypothesis_of_suzukiLocalArithmeticComparison_subpolynomial_lower_bound
#print axioms RiemannGaussian.suzukiLocalArithmeticComparison_div_sqrt_tendsto_zero
#print axioms RiemannGaussian.suzukiLocalOrdinaryArithmeticComparison_lower_bound_three_eighths
#print axioms RiemannGaussian.suzukiLocalPhysicalKernel_prefix_sum_abs_le
