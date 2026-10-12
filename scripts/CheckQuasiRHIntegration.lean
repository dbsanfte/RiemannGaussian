import RiemannGaussian
import OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Check the unconditional endpoint through the actual root library, lint the
two new project namespaces, and audit all declarations in the imported project
and external proof modules, including private and generated helpers. -/
#lint+ in RiemannGaussian.ZetaRieszQuasiRHDischarge
#lint+ in RiemannGaussian.ZetaQuasiRHOpenAI

example : RiemannGaussian.ZetaPrimeMomentTerminal.NoPersistentError :=
  RiemannGaussian.ZetaQuasiRHOpenAI.noPersistentError

#check RiemannGaussian.ZetaQuasiRHOpenAI.noPersistentError
#print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
#print axioms RiemannGaussian.ZetaQuasiRHOpenAI.noPersistentError
#print axioms RiemannGaussian.ZetaQuasiRHOpenAI.exists_coupled_geometric_bound

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let roots := #[`RiemannGaussian, `OAI, `RellichKondrachov,
    `PrimeNumberTheoremAnd, `MathlibExtensions, `Zeta23, `LeanCert]
  let mut modules : Array Json := #[]
  let mut reports : Array Json := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    unless roots.any (·.isPrefixOf moduleName) do continue
    let mut moduleDeclarations : Nat := 0
    let mut moduleTheorems : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      moduleDeclarations := moduleDeclarations + 1
      if ci.isAxiom then throwError "Custom axiom in {moduleName}: {ci.name}"
      let axioms ← Lean.collectAxioms ci.name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected transitive axiom in {ci.name}: {ax}"
      if ci.isTheorem then moduleTheorems := moduleTheorems + 1
      reports := reports.push (Json.mkObj [
        ("module", toJson moduleName.toString),
        ("declaration", toJson ci.name.toString),
        ("isTheorem", toJson ci.isTheorem),
        ("axioms", toJson (axioms.map Name.toString))])
    declarations := declarations + moduleDeclarations
    theorems := theorems + moduleTheorems
    modules := modules.push (Json.mkObj [
      ("module", toJson moduleName.toString),
      ("declarations", toJson moduleDeclarations),
      ("theoremsIncludingGeneratedHelpers", toJson moduleTheorems)])
  for target in #[`RiemannGaussian,
      `RiemannGaussian.ZetaQuasiRHOpenAI,
      `OAI.NumberTheory.DirichletL.Nonvanishing] do
    unless env.header.moduleNames.contains target do
      throwError "Missing required root-chain module: {target}"
  logInfo m!"Checked root chain: {modules.size} modules, {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/lean434-integration"
  IO.FS.writeFile ".lake/lean434-integration/axioms.json"
    (Json.mkObj [
      ("rootLibrary", toJson "RiemannGaussian"),
      ("endpoint", toJson "RiemannGaussian.ZetaQuasiRHOpenAI.noPersistentError"),
      ("externalStrictLowerBoundary", toJson "7/8"),
      ("onlyStandardAxioms", toJson true),
      ("namespaceLintersPerNewModule", toJson (15 : Nat)),
      ("moduleCount", toJson modules.size),
      ("declarations", toJson declarations),
      ("theoremsIncludingGeneratedHelpers", toJson theorems),
      ("modules", Json.arr modules),
      ("declarationAxioms", Json.arr reports)]).pretty
