import RiemannGaussian.ArithmeticOperatorCommutatorAudit
import RiemannGaussian.ArithmeticOperatorLcmCutoffAudit
import RiemannGaussian.ArithmeticOperatorMovingFloorCode
import RiemannGaussian.ArithmeticOperatorGcdMinorAudit
import RiemannGaussian.ArithmeticOperatorSmoothGramAudit
import RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit
import RiemannGaussian.ArithmeticOperatorCharacterSourceAudit
import RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
import RiemannGaussian.ArithmeticOperatorTwistSourceAudit
import RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
import RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit
import RiemannGaussian.ArithmeticOperatorIncidenceFreedom
import RiemannGaussian.ArithmeticOperatorFullRamanujanAudit
import RiemannGaussian.ArithmeticOperatorSuccessorPowerAudit
import RiemannGaussian.ArithmeticOperatorSuccessorSourceAudit
import RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit
import RiemannGaussian.ArithmeticOperatorRamanujanFreedom
import RiemannGaussian.ArithmeticOperatorCofactorParityAudit
import RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom
import RiemannGaussian.ArithmeticOperatorGammaInverseAudit
import RiemannGaussian.ArithmeticOperatorFixedLagSourceAudit
import RiemannGaussian.ArithmeticOperatorPrimeTowerControl
import RiemannGaussian.ArithmeticOperatorBinaryPrimeControl
import RiemannGaussian.ArithmeticOperatorBinaryEulerControl
import RiemannGaussian.ArithmeticOperatorNormalizedRamanujanAudit
import RiemannGaussian.ArithmeticOperatorGammaConeStability
import RiemannGaussian.ArithmeticOperatorCriticalRamanujanAudit
import RiemannGaussian.ArithmeticOperatorGrowingLagSourceAudit
import RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit
import RiemannGaussian.ArithmeticOperatorMixedHeightInverseAudit
import RiemannGaussian.ArithmeticOperatorGammaPatternAudit
import RiemannGaussian.ArithmeticOperatorPrimeGcdContrast
import RiemannGaussian.ArithmeticOperatorDilationPowerAudit
import RiemannGaussian.ArithmeticOperatorKummerGcdAudit
import RiemannGaussian.ArithmeticOperatorBinaryDensityAudit
import RiemannGaussian.ArithmeticOperatorGammaDilationAudit
import RiemannGaussian.ArithmeticOperatorKummerThresholdAudit
import RiemannGaussian.ArithmeticOperatorKummerThresholdSource
import RiemannGaussian.ArithmeticOperatorSelbergControlAudit
import RiemannGaussian.ArithmeticOperatorSelbergSourceAudit
import RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit
import RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit
import RiemannGaussian.ArithmeticOperatorCarryOrderAudit
import RiemannGaussian.ArithmeticOperatorKummerCrtAudit
import RiemannGaussian.ArithmeticOperatorCrtLagAudit
import RiemannGaussian.ArithmeticOperatorRamanujanInverseAudit
import RiemannGaussian.ArithmeticOperatorCofactorLagAudit
import RiemannGaussian.ArithmeticOperatorCharacterCofactorAudit
import RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
import RiemannGaussian.ArithmeticOperatorResidueInverseAudit
import RiemannGaussian.ArithmeticOperatorUnitaryInverseAudit
import RiemannGaussian.ArithmeticOperatorUnitarySourceAudit
import RiemannGaussian.ArithmeticOperatorGaussianCoprimeAudit
import RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit
import RiemannGaussian.ArithmeticOperatorNonunitCrtAudit
import RiemannGaussian.ArithmeticOperatorCoprimeRepairAudit
import RiemannGaussian.ArithmeticOperatorPoleProjectionAudit
import RiemannGaussian.ArithmeticOperatorHeatFloorAudit
import RiemannGaussian.ArithmeticOperatorSelbergHierarchyAudit
import RiemannGaussian.ArithmeticOperatorSchurProjectionAudit
import RiemannGaussian.ArithmeticOperatorFareyFourierAudit
import RiemannGaussian.ArithmeticOperatorSchurJetAudit
import RiemannGaussian.ArithmeticOperatorIncompleteArcAudit
import RiemannGaussian.ArithmeticOperatorKloostermanPsdAudit
import RiemannGaussian.ArithmeticOperatorFloorApproximationAudit
import RiemannGaussian.ArithmeticOperatorPrimitiveCountAudit
import RiemannGaussian.ArithmeticOperatorFiniteGammaControl
import RiemannGaussian.ArithmeticOperatorGammaToleranceAudit
import RiemannGaussian.ArithmeticOperatorNonlinearFloorAudit
import RiemannGaussian.ArithmeticOperatorPolynomialFloorInverseAudit
import RiemannGaussian.ArithmeticOperatorOrderedGapGeometry
import RiemannGaussian.ArithmeticOperatorOrderedGapAudit
import RiemannGaussian.ArithmeticOperatorPowerCovariance
import RiemannGaussian.ArithmeticOperatorGrowingRamanujan
import RiemannGaussian.ArithmeticOperatorLcmAudit
import RiemannGaussian.ArithmeticOperatorFloorInverseAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Focused local roadmap audit; no root or publication check is run. -/
#lint+ in RiemannGaussian.ArithmeticOperatorKummerCutoff
#lint+ in RiemannGaussian.ArithmeticOperatorRamanujanAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGramAudit
#lint+ in RiemannGaussian.ArithmeticOperatorDilationAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFloorSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGcdAudit
#lint+ in RiemannGaussian.ArithmeticOperatorRamanujanPayment
#lint+ in RiemannGaussian.ArithmeticOperatorFactorialUniqueness
#lint+ in RiemannGaussian.ArithmeticOperatorFloorBoundaryAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCommutatorAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPowerCovariance
#lint+ in RiemannGaussian.ArithmeticOperatorGrowingRamanujan
#lint+ in RiemannGaussian.ArithmeticOperatorGammaTwistAudit
#lint+ in RiemannGaussian.ArithmeticOperatorLcmAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFloorInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorLcmCutoffAudit
#lint+ in RiemannGaussian.ArithmeticOperatorMovingFloorCode
#lint+ in RiemannGaussian.ArithmeticOperatorGcdMinorAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSmoothGramAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCharacterSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
#lint+ in RiemannGaussian.ArithmeticOperatorTwistSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit
#lint+ in RiemannGaussian.ArithmeticOperatorIncidenceFreedom
#lint+ in RiemannGaussian.ArithmeticOperatorFullRamanujanAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSuccessorPowerAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSuccessorSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorRamanujanFreedom
#lint+ in RiemannGaussian.ArithmeticOperatorCofactorParityAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom
#lint+ in RiemannGaussian.ArithmeticOperatorGammaInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFixedLagSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPrimeTowerControl
#lint+ in RiemannGaussian.ArithmeticOperatorBinaryPrimeControl
#lint+ in RiemannGaussian.ArithmeticOperatorBinaryEulerControl
#lint+ in RiemannGaussian.ArithmeticOperatorNormalizedRamanujanAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGammaConeStability
#lint+ in RiemannGaussian.ArithmeticOperatorCriticalRamanujanAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGrowingLagSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit
#lint+ in RiemannGaussian.ArithmeticOperatorMixedHeightInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGammaPatternAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPrimeGcdContrast
#lint+ in RiemannGaussian.ArithmeticOperatorDilationPowerAudit
#lint+ in RiemannGaussian.ArithmeticOperatorKummerGcdAudit
#lint+ in RiemannGaussian.ArithmeticOperatorBinaryDensityAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGammaDilationAudit
#lint+ in RiemannGaussian.ArithmeticOperatorKummerThresholdAudit
#lint+ in RiemannGaussian.ArithmeticOperatorKummerThresholdSource
#lint+ in RiemannGaussian.ArithmeticOperatorSelbergControlAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSelbergSourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCarryOrderAudit
#lint+ in RiemannGaussian.ArithmeticOperatorKummerCrtAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCrtLagAudit
#lint+ in RiemannGaussian.ArithmeticOperatorRamanujanInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCofactorLagAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCharacterCofactorAudit
#lint+ in RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
#lint+ in RiemannGaussian.ArithmeticOperatorResidueInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorUnitaryInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorUnitarySourceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorGaussianCoprimeAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit
#lint+ in RiemannGaussian.ArithmeticOperatorNonunitCrtAudit
#lint+ in RiemannGaussian.ArithmeticOperatorCoprimeRepairAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPoleProjectionAudit
#lint+ in RiemannGaussian.ArithmeticOperatorHeatFloorAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSelbergHierarchyAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSchurProjectionAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFareyFourierAudit
#lint+ in RiemannGaussian.ArithmeticOperatorSchurJetAudit
#lint+ in RiemannGaussian.ArithmeticOperatorIncompleteArcAudit
#lint+ in RiemannGaussian.ArithmeticOperatorKloostermanPsdAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFloorApproximationAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPrimitiveCountAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFiniteGammaControl
#lint+ in RiemannGaussian.ArithmeticOperatorGammaToleranceAudit
#lint+ in RiemannGaussian.ArithmeticOperatorNonlinearFloorAudit
#lint+ in RiemannGaussian.ArithmeticOperatorPolynomialFloorInverseAudit
#lint+ in RiemannGaussian.ArithmeticOperatorOrderedGapGeometry
#lint+ in RiemannGaussian.ArithmeticOperatorOrderedGapAudit

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let targets := #[`RiemannGaussian.ArithmeticOperatorKummerCutoff,
    `RiemannGaussian.ArithmeticOperatorRamanujanAudit,
    `RiemannGaussian.ArithmeticOperatorGramAudit,
    `RiemannGaussian.ArithmeticOperatorDilationAudit,
    `RiemannGaussian.ArithmeticOperatorFloorSourceAudit,
    `RiemannGaussian.ArithmeticOperatorGcdAudit,
    `RiemannGaussian.ArithmeticOperatorRamanujanPayment,
    `RiemannGaussian.ArithmeticOperatorFactorialUniqueness,
    `RiemannGaussian.ArithmeticOperatorFloorBoundaryAudit,
    `RiemannGaussian.ArithmeticOperatorCommutatorAudit,
    `RiemannGaussian.ArithmeticOperatorPowerCovariance,
    `RiemannGaussian.ArithmeticOperatorGrowingRamanujan,
    `RiemannGaussian.ArithmeticOperatorGammaTwistAudit,
    `RiemannGaussian.ArithmeticOperatorLcmAudit,
    `RiemannGaussian.ArithmeticOperatorFloorInverseAudit,
    `RiemannGaussian.ArithmeticOperatorLcmCutoffAudit,
    `RiemannGaussian.ArithmeticOperatorMovingFloorCode,
    `RiemannGaussian.ArithmeticOperatorGcdMinorAudit,
    `RiemannGaussian.ArithmeticOperatorSmoothGramAudit,
    `RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit,
    `RiemannGaussian.ArithmeticOperatorCharacterSourceAudit,
    `RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit,
    `RiemannGaussian.ArithmeticOperatorTwistSourceAudit,
    `RiemannGaussian.ArithmeticOperatorTwistedBulkAudit,
    `RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit,
    `RiemannGaussian.ArithmeticOperatorIncidenceFreedom,
    `RiemannGaussian.ArithmeticOperatorFullRamanujanAudit,
    `RiemannGaussian.ArithmeticOperatorSuccessorPowerAudit,
    `RiemannGaussian.ArithmeticOperatorSuccessorSourceAudit,
    `RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit,
    `RiemannGaussian.ArithmeticOperatorRamanujanFreedom,
    `RiemannGaussian.ArithmeticOperatorCofactorParityAudit,
    `RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom,
    `RiemannGaussian.ArithmeticOperatorGammaInverseAudit,
    `RiemannGaussian.ArithmeticOperatorFixedLagSourceAudit,
    `RiemannGaussian.ArithmeticOperatorPrimeTowerControl,
    `RiemannGaussian.ArithmeticOperatorBinaryPrimeControl,
    `RiemannGaussian.ArithmeticOperatorBinaryEulerControl,
    `RiemannGaussian.ArithmeticOperatorNormalizedRamanujanAudit,
    `RiemannGaussian.ArithmeticOperatorGammaConeStability,
    `RiemannGaussian.ArithmeticOperatorCriticalRamanujanAudit,
    `RiemannGaussian.ArithmeticOperatorGrowingLagSourceAudit,
    `RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit,
    `RiemannGaussian.ArithmeticOperatorMixedHeightInverseAudit,
    `RiemannGaussian.ArithmeticOperatorGammaPatternAudit,
    `RiemannGaussian.ArithmeticOperatorPrimeGcdContrast,
    `RiemannGaussian.ArithmeticOperatorDilationPowerAudit,
    `RiemannGaussian.ArithmeticOperatorKummerGcdAudit,
    `RiemannGaussian.ArithmeticOperatorBinaryDensityAudit,
    `RiemannGaussian.ArithmeticOperatorGammaDilationAudit,
    `RiemannGaussian.ArithmeticOperatorKummerThresholdAudit,
    `RiemannGaussian.ArithmeticOperatorKummerThresholdSource,
    `RiemannGaussian.ArithmeticOperatorSelbergControlAudit,
    `RiemannGaussian.ArithmeticOperatorSelbergSourceAudit,
    `RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit,
    `RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit,
    `RiemannGaussian.ArithmeticOperatorCarryOrderAudit,
    `RiemannGaussian.ArithmeticOperatorKummerCrtAudit,
    `RiemannGaussian.ArithmeticOperatorCrtLagAudit,
    `RiemannGaussian.ArithmeticOperatorRamanujanInverseAudit,
    `RiemannGaussian.ArithmeticOperatorCofactorLagAudit,
    `RiemannGaussian.ArithmeticOperatorCharacterCofactorAudit,
    `RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit,
    `RiemannGaussian.ArithmeticOperatorResidueInverseAudit,
    `RiemannGaussian.ArithmeticOperatorUnitaryInverseAudit,
    `RiemannGaussian.ArithmeticOperatorUnitarySourceAudit,
    `RiemannGaussian.ArithmeticOperatorGaussianCoprimeAudit,
    `RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit,
    `RiemannGaussian.ArithmeticOperatorNonunitCrtAudit,
    `RiemannGaussian.ArithmeticOperatorCoprimeRepairAudit,
    `RiemannGaussian.ArithmeticOperatorPoleProjectionAudit,
    `RiemannGaussian.ArithmeticOperatorHeatFloorAudit,
    `RiemannGaussian.ArithmeticOperatorSelbergHierarchyAudit,
    `RiemannGaussian.ArithmeticOperatorSchurProjectionAudit,
    `RiemannGaussian.ArithmeticOperatorFareyFourierAudit,
    `RiemannGaussian.ArithmeticOperatorSchurJetAudit,
    `RiemannGaussian.ArithmeticOperatorIncompleteArcAudit,
    `RiemannGaussian.ArithmeticOperatorKloostermanPsdAudit,
    `RiemannGaussian.ArithmeticOperatorFloorApproximationAudit,
    `RiemannGaussian.ArithmeticOperatorPrimitiveCountAudit,
    `RiemannGaussian.ArithmeticOperatorFiniteGammaControl,
    `RiemannGaussian.ArithmeticOperatorGammaToleranceAudit,
    `RiemannGaussian.ArithmeticOperatorNonlinearFloorAudit,
    `RiemannGaussian.ArithmeticOperatorPolynomialFloorInverseAudit,
    `RiemannGaussian.ArithmeticOperatorOrderedGapGeometry,
    `RiemannGaussian.ArithmeticOperatorOrderedGapAudit]
  let env ← getEnv
  let mut modules : Array Json := #[]
  for target in targets do
    let mut seen := false
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    let mut reports : Array Json := #[]
    for i in [:env.header.moduleNames.size] do
      unless env.header.moduleNames[i]! == target do continue
      seen := true
      for ci in env.header.moduleData[i]!.constants do
        declarations := declarations+1
        if ci.isAxiom then throwError "Project-defined axiom: {ci.name}"
        let dependencies ← Lean.collectAxioms ci.name
        for ax in dependencies do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom in {ci.name}: {ax}"
        if ci.isTheorem then
          theorems := theorems+1
          reports := reports.push (Json.mkObj [
            ("theorem",toJson ci.name.toString),
            ("axioms",toJson (dependencies.map Name.toString))])
    unless seen do throwError "Missing imported module: {target}"
    modules := modules.push (Json.mkObj [("module",toJson target.toString),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingPrivateHelpers",toJson theorems),
      ("namespaceLinters",toJson (14 : Nat)),("theoremAxioms",Json.arr reports),
      ("rootRegistered",toJson false)])
    logInfo m!"Checked {target}: {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-roadmap"
  IO.FS.writeFile ".lake/arithmetic-operator-roadmap/axioms.json"
    (Json.mkObj [("modules",Json.arr modules)]).pretty
