import RiemannGaussian
import RiemannGaussian.SemiprimeSourceCompactBits
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeSourceCompactWordBank
import RiemannGaussian.SemiprimeSourceHistogramGrouping
import RiemannGaussian.SemiprimeSourceIncidenceHistogram
import RiemannGaussian.SemiprimeSourceHistogramOriginalSums
import RiemannGaussian.SemiprimeSourceHistogramMetadata
import RiemannGaussian.SemiprimeSourceHistogramAcquiredSums
import RiemannGaussian.SemiprimeSourceHistogramCountInput
import RiemannGaussian.SemiprimeSourceHistogramScales
import RiemannGaussian.SemiprimeSourceHistogramTrie
import RiemannGaussian.SemiprimeSourceHistogramSquares
import RiemannGaussian.SemiprimeSourceHistogramArithmetic
import RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds
import RiemannGaussian.SemiprimeSourceHistogramTrieBounds
import RiemannGaussian.SemiprimeSourceHistogramTrieStore
import RiemannGaussian.SemiprimeSourceHistogramPrefix
import RiemannGaussian.SemiprimeSourceHistogramPortKeys
import RiemannGaussian.SemiprimeSourceHistogramKeyBits
import RiemannGaussian.SemiprimeSourceHistogramFeatureBits
import RiemannGaussian.SemiprimeSourceHistogramDictRefinement
import RiemannGaussian.SemiprimeSourceHistogramDifferences
import RiemannGaussian.SemiprimeSourceHistogramSquaresBounds
import RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds
import RiemannGaussian.SemiprimeSourceHistogramHeadAggregate
import RiemannGaussian.SemiprimeSourceHistogramRows
import RiemannGaussian.SemiprimeSourceHistogramRowsBounds
import RiemannGaussian.SemiprimeSourceHistogramRowKeys
import RiemannGaussian.SemiprimeSourceHistogramHeadBits
import RiemannGaussian.SemiprimeSourceHistogramHeadRefinement
import RiemannGaussian.SemiprimeSourceHistogramHeadQueryBounds
import RiemannGaussian.SemiprimeSourceHistogramHeadBounds
import RiemannGaussian.SemiprimeSourceHistogramHeadOriginal
import RiemannGaussian.SemiprimeSourceHistogramSetup
import RiemannGaussian.SemiprimeSourceHistogramQuery
import RiemannGaussian.SemiprimeSourceHistogramScalesBounds
import RiemannGaussian.SemiprimeSourceHistogramSetupBounds
import RiemannGaussian.SemiprimeSourceHistogramQueryBounds
import RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness
import RiemannGaussian.SemiprimeSourceHistogramSearch
import RiemannGaussian.SemiprimeSourceHistogramSearchBudget
import RiemannGaussian.SemiprimeSourceHistogramResources
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceCompactBits
#lint+ in RiemannGaussian.SemiprimeSourceCompactWordIds
#lint+ in RiemannGaussian.SemiprimeSourceCompactWordBank
#lint+ in RiemannGaussian.SemiprimeSourceHistogramGrouping
#lint+ in RiemannGaussian.SemiprimeSourceIncidenceHistogram
#lint+ in RiemannGaussian.SemiprimeSourceHistogramOriginalSums
#lint+ in RiemannGaussian.SemiprimeSourceHistogramMetadata
#lint+ in RiemannGaussian.SemiprimeSourceHistogramAcquiredSums
#lint+ in RiemannGaussian.SemiprimeSourceHistogramCountInput
#lint+ in RiemannGaussian.SemiprimeSourceHistogramScales
#lint+ in RiemannGaussian.SemiprimeSourceHistogramTrie
#lint+ in RiemannGaussian.SemiprimeSourceHistogramSquares
#lint+ in RiemannGaussian.SemiprimeSourceHistogramArithmetic
#lint+ in RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramTrieBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramTrieStore
#lint+ in RiemannGaussian.SemiprimeSourceHistogramPrefix
#lint+ in RiemannGaussian.SemiprimeSourceHistogramPortKeys
#lint+ in RiemannGaussian.SemiprimeSourceHistogramKeyBits
#lint+ in RiemannGaussian.SemiprimeSourceHistogramFeatureBits
#lint+ in RiemannGaussian.SemiprimeSourceHistogramDictRefinement
#lint+ in RiemannGaussian.SemiprimeSourceHistogramDifferences
#lint+ in RiemannGaussian.SemiprimeSourceHistogramSquaresBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramHeadAggregate
#lint+ in RiemannGaussian.SemiprimeSourceHistogramRows
#lint+ in RiemannGaussian.SemiprimeSourceHistogramRowsBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramRowKeys
#lint+ in RiemannGaussian.SemiprimeSourceHistogramHeadBits
#lint+ in RiemannGaussian.SemiprimeSourceHistogramHeadRefinement
#lint+ in RiemannGaussian.SemiprimeSourceHistogramHeadQueryBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramHeadBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramHeadOriginal
#lint+ in RiemannGaussian.SemiprimeSourceHistogramSetup
#lint+ in RiemannGaussian.SemiprimeSourceHistogramQuery
#lint+ in RiemannGaussian.SemiprimeSourceHistogramScalesBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramSetupBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramQueryBounds
#lint+ in RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness
#lint+ in RiemannGaussian.SemiprimeSourceHistogramSearch
#lint+ in RiemannGaussian.SemiprimeSourceHistogramSearchBudget
#lint+ in RiemannGaussian.SemiprimeSourceHistogramResources
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceCompactBits, `RiemannGaussian.SemiprimeSourceCompactWordIds, `RiemannGaussian.SemiprimeSourceCompactWordBank, `RiemannGaussian.SemiprimeSourceHistogramGrouping, `RiemannGaussian.SemiprimeSourceIncidenceHistogram, `RiemannGaussian.SemiprimeSourceHistogramOriginalSums, `RiemannGaussian.SemiprimeSourceHistogramMetadata, `RiemannGaussian.SemiprimeSourceHistogramAcquiredSums, `RiemannGaussian.SemiprimeSourceHistogramCountInput, `RiemannGaussian.SemiprimeSourceHistogramScales, `RiemannGaussian.SemiprimeSourceHistogramTrie, `RiemannGaussian.SemiprimeSourceHistogramSquares, `RiemannGaussian.SemiprimeSourceHistogramArithmetic, `RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds, `RiemannGaussian.SemiprimeSourceHistogramTrieBounds, `RiemannGaussian.SemiprimeSourceHistogramTrieStore, `RiemannGaussian.SemiprimeSourceHistogramPrefix, `RiemannGaussian.SemiprimeSourceHistogramPortKeys, `RiemannGaussian.SemiprimeSourceHistogramKeyBits, `RiemannGaussian.SemiprimeSourceHistogramFeatureBits, `RiemannGaussian.SemiprimeSourceHistogramDictRefinement, `RiemannGaussian.SemiprimeSourceHistogramDifferences, `RiemannGaussian.SemiprimeSourceHistogramSquaresBounds, `RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds, `RiemannGaussian.SemiprimeSourceHistogramHeadAggregate, `RiemannGaussian.SemiprimeSourceHistogramRows, `RiemannGaussian.SemiprimeSourceHistogramRowsBounds, `RiemannGaussian.SemiprimeSourceHistogramRowKeys, `RiemannGaussian.SemiprimeSourceHistogramHeadBits, `RiemannGaussian.SemiprimeSourceHistogramHeadRefinement, `RiemannGaussian.SemiprimeSourceHistogramHeadQueryBounds, `RiemannGaussian.SemiprimeSourceHistogramHeadBounds, `RiemannGaussian.SemiprimeSourceHistogramHeadOriginal, `RiemannGaussian.SemiprimeSourceHistogramSetup, `RiemannGaussian.SemiprimeSourceHistogramQuery, `RiemannGaussian.SemiprimeSourceHistogramScalesBounds, `RiemannGaussian.SemiprimeSourceHistogramSetupBounds, `RiemannGaussian.SemiprimeSourceHistogramQueryBounds, `RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness, `RiemannGaussian.SemiprimeSourceHistogramSearch, `RiemannGaussian.SemiprimeSourceHistogramSearchBudget, `RiemannGaussian.SemiprimeSourceHistogramResources]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-histogram-acquisition-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
