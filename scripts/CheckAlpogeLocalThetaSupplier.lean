import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.DsExhaust
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.KTypesAbove
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.FinalB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCommensuratedKO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMirabolicHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationFromLibrary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDiscreteSeriesHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityRealHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalEquivalenceUnitaryGroupPQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerOneHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticRepresentationHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoFree
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RallisDM
import Development.AutomorphicArithmetic.ThetaCorrespondence.Linnik
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilEx
import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesAut
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesRep
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FinalB
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.CuspDecaySobolev
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HarishChandraModules
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HeckeLEntireAndNonzeroAtOne
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HermitianHassePrinciple
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.RealMetaplecticRepresentation
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.SchurOrthogonalitySquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteOfCuspOfConstTerm
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.FdTopB
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.SiegelEisensteinContinuation
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll

/-! # Closed sources for the local theta input package -/

namespace RiemannGaussian.AlpogeWindow

/-- The local theta inputs needed on the chosen period grid. -/
theorem archive_local_theta_inputs : GlobalTheory.FunPr.ThetaLocalInputs := by
  have doubling := ResidueKilled.dm_of_two GlobalTheory.RapidDecay.cuspRapidDecay
    PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation trivial
  exact {
    greenSeriesSt := PositivityTheory.Prw.greenSeriesSt_of PositivityTheory.Stage1.PM.greenCuspidal
    linnik := UpperTheory.Lit.linnik
    complexMultiplicationJSt := GlobalTheory.CompanionTheory.Published.complexMultiplicationJ
    cuspidalMirabolic := GlobalTheory.cuspidalMirabolic_holds
    weylBranching := PositivityTheory.Stage1.PM.weylBranching
    bernsteinUnitaryProductIrreducible := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
    zelevinskyPolynomialRing := PositivityTheory.Prw.zelevinskyPolynomialRing_of
      PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation
      (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation)
    bernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
    cuspTraceClass := PositivityTheory.Prw.cuspTraceClass_of PositivityTheory.Prw.dixmierMalliavinFactorisation_holds
    flathFactorisation := PositivityTheory.Prw.flathFactorisation_of CompanionTheory.Rg.Fl.B.flathTensorProduct
      CompanionTheory.Rg.Fl.B.unitaryIrreducibleAdmissible
    weilSiegelFormulaUnitary := UpperTheory.Lit.Sw47.weilUnitary
    rallisInnerProductConvergent := UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm doubling
      UpperTheory.Lit.Sw47.convergent UpperTheory.Lit.weilThetaConvergence
    doublingMethod := doubling
    unramifiedDoublingGL := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
    hermitianLocalGlobal := PositivityTheory.Stage1.PM.hermitianLocalGlobal
    quadraticClassFieldTheory := PositivityTheory.Stage1.PM.quadraticClassFieldTheory
    borelCasselman := PositivityTheory.Stage1.PM.borelCasselman
    radfordShufflePolynomial := PositivityTheory.Stage1.PM.radfordShufflePolynomial
    dixmierMalliavinFactorisation := GlobalTheory.dixmierMalliavinFactorisation_fromLibrary
    schurOrthogonalitySquareIntegrable := PositivityTheory.Stage1.PM.schurOrthogonalitySquareIntegrable
    heckeLPartialContinuation := PositivityTheory.Stage1.PM.heckeLPartialContinuation
    logDerOne := GlobalTheory.LogDerOneProof.logDerOne_holds
    kFiniteVectorsUnitary := GlobalTheory.KFinLinkPort.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
    discreteSeriesLowestKType := PositivityTheory.Prw.discreteSeriesLowestKType_holds
    holomorphicDiscreteSeries := GlobalTheory.HolDS.holomorphicDiscreteSeries_holds
    gKGlobalisation := GlobalTheory.gkGlobalisation_holds
    cuspBounded := PositivityTheory.Stage1.PM.cuspBounded
    strongApproxSU := GlobalTheory.StrongApproxSUProof.strongApproxSU
    heckeLEntireAndNonzeroAtOne := PositivityTheory.Stage1.PM.heckeLEntireAndNonzeroAtOne
    realMetaplecticRepresentation := PositivityTheory.Stage1.PM.realMetaplecticRepresentation
    cuspDecayBound := GlobalTheory.CuspGeo.cuspDecayBound
    gLHoweDuality := PositivityTheory.Stage1.PM.gLHoweDuality
    kudlaSplittingSplitUnitary := GlobalTheory.kudlaSplittingSplitUnitary
    metaplecticRepresentation := GlobalTheory.metaplecticRepresentation_holds
    harishChandraModules := PositivityTheory.Stage1.PM.harishChandraModules
    discreteSeriesCover := CompanionTheory.RgExh.discreteSeriesCover
    idealInvariantsOneOrbitSt := PositivityTheory.Prw.idealInvariantsOneOrbitSt_holds
    hermitianHassePrinciple := PositivityTheory.Stage1.PM.hermitianHassePrinciple
    stoneVonNeumann := PositivityTheory.Stage1.PM.stoneVonNeumann
    discreteSeriesUpqExists := CompanionTheory.RgDs.B.discreteSeriesUpqExists
    formalDegreeCompactDual := PositivityTheory.RgFd.B.formalDegreeCompactDual
    thetaRationalInvariance := PositivityTheory.Stage1.PM.thetaRationalInvariance
    discreteSeriesHermitianUnique := PositivityTheory.Prw.discreteSeriesHermitianUnique_holds
    discreteSeriesExists := CompanionTheory.RgDs.B.discreteSeriesExists
    harishChandraFinite := PositivityTheory.RgHf.harishChandraFinite
    cuspRapidDecay := GlobalTheory.RapidDecay.cuspRapidDecay
    weilRepresentationUnitaryPair := GlobalTheory.weilRepresentationUnitaryPair
    discreteSeriesCoverExists := CompanionTheory.RgDs.B.discreteSeriesCoverExists
    cuspDecaySobolev := PositivityTheory.Stage1.PM.cuspDecaySobolev
    casselmanWallach := PositivityTheory.CWB.casselmanWallach
    howeDualityReal := GlobalTheory.howeDualityReal_holds
    siegelSetUnitary := UpperTheory.Lit.siegelSetUnitary_of_core
    weilRepresentationExists := UpperTheory.Lit.weilRepresentationExists_pair }

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.archive_local_theta_inputs
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
