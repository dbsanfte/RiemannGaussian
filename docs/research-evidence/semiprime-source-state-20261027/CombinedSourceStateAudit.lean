import RiemannGaussian
import RiemannGaussian.SemiprimeSourceOffsetHeight
import RiemannGaussian.SemiprimeSourceUniversalHeight
import RiemannGaussian.SemiprimeSourceConstraintHeight
import RiemannGaussian.SemiprimeSourceCodeArrayHeight
import RiemannGaussian.SemiprimeSourceInterpolationHeight
import RiemannGaussian.SemiprimeSourceInterpolationBits
import RiemannGaussian.SemiprimeSourcePullbackHeight
import RiemannGaussian.SemiprimeSourceScoreState
import RiemannGaussian.SemiprimeSourceAcquiredArrayState
import RiemannGaussian.SemiprimeSourceConstraintState
import RiemannGaussian.SemiprimeSourceSearchState
import RiemannGaussian.SemiprimeSourceAcquiredArrayBits
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceOffsetHeight
#lint+ in RiemannGaussian.SemiprimeSourceUniversalHeight
#lint+ in RiemannGaussian.SemiprimeSourceConstraintHeight
#lint+ in RiemannGaussian.SemiprimeSourceCodeArrayHeight
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationHeight
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationBits
#lint+ in RiemannGaussian.SemiprimeSourcePullbackHeight
#lint+ in RiemannGaussian.SemiprimeSourceScoreState
#lint+ in RiemannGaussian.SemiprimeSourceAcquiredArrayState
#lint+ in RiemannGaussian.SemiprimeSourceConstraintState
#lint+ in RiemannGaussian.SemiprimeSourceSearchState
#lint+ in RiemannGaussian.SemiprimeSourceAcquiredArrayBits
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceOffsetHeight, `RiemannGaussian.SemiprimeSourceUniversalHeight, `RiemannGaussian.SemiprimeSourceConstraintHeight, `RiemannGaussian.SemiprimeSourceCodeArrayHeight, `RiemannGaussian.SemiprimeSourceInterpolationHeight, `RiemannGaussian.SemiprimeSourceInterpolationBits, `RiemannGaussian.SemiprimeSourcePullbackHeight, `RiemannGaussian.SemiprimeSourceScoreState, `RiemannGaussian.SemiprimeSourceAcquiredArrayState, `RiemannGaussian.SemiprimeSourceConstraintState, `RiemannGaussian.SemiprimeSourceSearchState, `RiemannGaussian.SemiprimeSourceAcquiredArrayBits]
  let mut checked : Nat := 0
  let mut totalDeclarations : Nat := 0
  let mut totalTheorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    unless moduleName ∈ expected do continue
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations+1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems+1
      for ax in (← Lean.collectAxioms ci.name) do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {ax}"
    checked := checked+1
    totalDeclarations := totalDeclarations+declarations
    totalTheorems := totalTheorems+theorems
    logInfo m!"AUDIT {moduleName}: declarations={declarations}, theorems={theorems}, standard_axioms_only=true"
  unless checked == expected.length do throwError "missing module: {checked}/{expected.length}"
  logInfo m!"TOTAL modules={checked}, declarations={totalDeclarations}, theorems={totalTheorems}, standard_axioms_only=true"
  liftIO <| IO.FS.writeFile "/tmp/semiprime-source-state-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
