import RiemannGaussian
import Lean.Util.CollectAxioms

/-!
# Generate the compact proof-status dashboard

This script reads the compiled Lean environment, validates the theorem
constants used as public milestones, audits every project theorem's axiom
dependencies, and writes deterministic JSON and SVG artifacts.

Run it from the repository root with:

```bash
lake env lean scripts/GenerateProjectStatus.lean
```
-/

open Lean Elab Command

private structure Milestone where
  label : String
  lineOne : String
  lineTwo : String
  role : String
  theoremName : Name

private structure Point where
  x : Nat
  y : Nat

private def milestones : Array Milestone := #[
  {
    label := "Log-linear xi growth"
    lineOne := "xi growth"
    lineTwo := "R log R"
    role := "unconditional"
    theoremName := ``RiemannGaussian.riemannXi_logLinearGrowth
  },
  {
    label := "Gaussian Gram identity"
    lineOne := "Gaussian Gram"
    lineTwo := "identity"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal
  },
  {
    label := "Suzuki arithmetic-spectral identity"
    lineOne := "Suzuki identity"
    lineTwo := "arith. = spectral"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.riemannXiSuzukiArithmeticPPositive_eq_spectral_safe
  },
  {
    label := "Static signed xi contour"
    lineOne := "static signed"
    lineTwo := "xi contour"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.xiSpectralBlaschkeSignedContourWindow_eq_blaschke
  },
  {
    label := "Boundary heat vanishing is equivalent to RH"
    lineOne := "boundary heat = 0"
    lineTwo := "iff RH (reform.)"
    role := "equivalence"
    theoremName :=
      ``RiemannGaussian.riemannXiUpperHyperbolicBoundaryHeatAction_eq_zero_iff_rh
  },
  {
    label := "Poisson decay is equivalent to sublinear cumulative upper spectral height"
    lineOne := "Poisson decay iff"
    lineTwo := "H(T) = o(T) reduction"
    role := "reduction"
    theoremName :=
      ``RiemannGaussian.tendsto_safeAxisPoisson_toReal_zero_iff_upperSpectralHeight_sublinear
  },
  {
    label := "Smooth endpoint drift is summable and work is asymptotic to the logarithmic average plus log N"
    lineOne := "signed work - A_N"
    lineTwo := "- log N converges"
    role := "reduction"
    theoremName :=
      ``RiemannGaussian.tendsto_cumulativeMassErrorWork_sub_logAverage_sub_log
  },
  {
    label := "Finite phase-sensitive eta lower certificates converge at both complementary tilts to the common completed defect"
    lineOne := "finite eta bounds"
    lineTwo := "common paired limit"
    role := "reduction"
    theoremName :=
      ``RiemannGaussian.tendsto_pairedEtaCompletedLeadingLogFiniteLower_both
  }
]

private def milestonePoints : Array Point := #[
  { x := 20, y := 71 },
  { x := 180, y := 71 },
  { x := 340, y := 71 },
  { x := 500, y := 71 },
  { x := 20, y := 150 },
  { x := 180, y := 150 },
  { x := 340, y := 150 },
  { x := 500, y := 150 }
]

private def projectPrefix : Name := `RiemannGaussian

private def isProjectModule (moduleName : Name) : Bool :=
  projectPrefix.isPrefixOf moduleName

private def moduleOfDeclaration? (env : Environment)
    (declarationName : Name) : Option Name := do
  let moduleIndex <- env.getModuleIdxFor? declarationName
  env.header.moduleNames[moduleIndex.toNat]?

private def isProjectDeclaration (env : Environment)
    (declarationName : Name) : Bool :=
  (moduleOfDeclaration? env declarationName).any isProjectModule

private def isStandardAxiom (axiomName : Name) : Bool :=
  axiomName == ``propext ||
    axiomName == ``Classical.choice ||
    axiomName == ``Quot.sound

/-- The kernel constant used for unresolved proof terms, assembled so the
source-level gate can reserve its literal spelling for forbidden uses. -/
private def placeholderAxiomName : Name :=
  .str .anonymous ("sor" ++ "ryAx")

private def xmlEscape (value : String) : String :=
  (((value.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;")
    |>.replace "\"" "&quot;"

private def milestoneToJson (milestone : Milestone) : Json :=
  Json.mkObj [
    ("label", .str milestone.label),
    ("role", .str milestone.role),
    ("status", .str "proved"),
    ("theorem", .str milestone.theoremName.toString)
  ]

private def completedNodeSvg (milestone : Milestone) (point : Point) : String :=
  let theoremName := xmlEscape milestone.theoremName.toString
  s!"  <g class=\"proved {xmlEscape milestone.role}\">\n" ++
    s!"    <rect x=\"{point.x}\" y=\"{point.y}\" width=\"145\" height=\"54\" rx=\"9\"/>\n" ++
    s!"    <title>{theoremName}</title>\n" ++
    s!"    <text x=\"{point.x + 72}\" y=\"{point.y + 23}\">{xmlEscape milestone.lineOne}</text>\n" ++
    s!"    <text x=\"{point.x + 72}\" y=\"{point.y + 41}\">{xmlEscape milestone.lineTwo}  ✓</text>\n" ++
    "  </g>\n"

private def renderSvg (moduleCount declarationCount theoremCount : Nat) : String :=
  let nodes := (milestones.zip milestonePoints).foldl
    (fun output milestonePoint =>
      output ++ completedNodeSvg milestonePoint.1 milestonePoint.2) ""
  "<svg xmlns=\"http://www.w3.org/2000/svg\" role=\"img\" " ++
      "aria-labelledby=\"title description\" viewBox=\"0 0 1000 235\">\n" ++
    "  <title id=\"title\">Lean-verified RiemannGaussian theorem inventory</title>\n" ++
    "  <desc id=\"description\">An inventory of checked analytic results, " ++
      "equivalences, bridges, and reductions. The boxes are not a proof chain. " ++
      "No checked implication crosses the displayed conjecture-strength gap to RH.</desc>\n" ++
    "  <defs>\n" ++
    "    <marker id=\"arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" " ++
      "markerWidth=\"6\" markerHeight=\"6\" orient=\"auto-start-reverse\">\n" ++
    "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#8b949e\"/>\n" ++
    "    </marker>\n" ++
    "    <style>\n" ++
    "      .bg { fill: #0d1117; stroke: #30363d; }\n" ++
    "      text { fill: #e6edf3; font-family: ui-monospace, SFMono-Regular, " ++
      "Menlo, Consolas, monospace; font-size: 12px; text-anchor: middle; }\n" ++
    "      .heading { font-size: 17px; font-weight: 700; text-anchor: start; }\n" ++
    "      .metrics { fill: #8b949e; font-size: 11px; text-anchor: end; }\n" ++
    "      .proved rect { fill: #12261a; stroke: #3fb950; stroke-width: 1.5; }\n" ++
    "      .proved.equivalence rect { fill: #211735; stroke: #a371f7; }\n" ++
    "      .proved.bridge rect { fill: #111f35; stroke: #58a6ff; }\n" ++
    "      .proved.reduction rect { fill: #102a2c; stroke: #39c5cf; }\n" ++
    "      .open rect { fill: #2d210d; stroke: #d29922; stroke-width: 1.8; }\n" ++
    "      .goal rect { fill: #161b22; stroke: #8b949e; stroke-width: 1.5; " ++
      "stroke-dasharray: 5 4; }\n" ++
    "      .open text { fill: #f2cc60; font-weight: 700; }\n" ++
    "      .goal text { fill: #c9d1d9; font-weight: 700; }\n" ++
    "      .open-edge { fill: none; stroke: #d29922; stroke-width: 1.5; " ++
      "stroke-dasharray: 5 4; marker-end: url(#arrow); }\n" ++
    "      .section { fill: #8b949e; font-size: 10px; font-weight: 700; " ++
      "text-anchor: start; }\n" ++
    "      .gap-label { fill: #d29922; font-size: 10px; font-weight: 700; }\n" ++
    "      .frontier { fill: #f2cc60; font-size: 11px; text-anchor: start; }\n" ++
    "    </style>\n" ++
    "  </defs>\n" ++
    "  <rect class=\"bg\" x=\"0.75\" y=\"0.75\" width=\"998.5\" " ++
      "height=\"233.5\" rx=\"12\"/>\n" ++
    "  <text class=\"heading\" x=\"20\" y=\"30\">Lean-checked theorem inventory — RH remains open</text>\n" ++
    s!"  <text class=\"metrics\" x=\"980\" y=\"28\">Lean {Lean.versionString} · " ++
      s!"{moduleCount} modules · {declarationCount} declarations · {theoremCount} theorems</text>\n" ++
    "  <text class=\"metrics\" x=\"980\" y=\"47\">0 placeholder dependencies · " ++
      "0 project axioms · frontier standard-only</text>\n" ++
    "  <text class=\"section\" x=\"20\" y=\"64\">UNCONDITIONAL RESULTS AND IDENTITIES</text>\n" ++
    "  <text class=\"section\" x=\"20\" y=\"143\">EQUIVALENCES AND REDUCTIONS — NOT A PROOF CHAIN</text>\n" ++
    "  <line x1=\"670\" y1=\"62\" x2=\"670\" y2=\"207\" stroke=\"#30363d\"/>\n" ++
    "  <text class=\"gap-label\" x=\"765\" y=\"94\">UNPROVED MATHEMATICS</text>\n" ++
    "  <path class=\"open-edge\" d=\"M840 139 H853\"/>\n" ++
    nodes ++
    "  <g class=\"open\">\n" ++
    "    <rect x=\"690\" y=\"108\" width=\"150\" height=\"62\" rx=\"10\"/>\n" ++
    "    <text x=\"765\" y=\"133\">arithmetic rigidity</text>\n" ++
    "    <text x=\"765\" y=\"153\">CONJECTURE-STRENGTH</text>\n" ++
    "  </g>\n" ++
    "  <g class=\"goal\">\n" ++
    "    <rect x=\"855\" y=\"114\" width=\"125\" height=\"50\" rx=\"9\"/>\n" ++
    "    <text x=\"917\" y=\"144\">RH</text>\n" ++
    "  </g>\n" ++
    "  <text class=\"frontier\" x=\"20\" y=\"220\">Inventory, not proximity meter. Open: " ++
      "a uniform finite-prefix inequality that separates complementary off-line tilts.</text>\n" ++
    "</svg>\n"

run_cmd do
  let env <- getEnv
  let moduleCount := env.header.moduleNames.countP isProjectModule
  let mut declarationCount := 0
  let mut theoremCount := 0
  let mut projectAxiomNames : Array Name := #[]
  let mut placeholderDependentDeclarations : Array Name := #[]
  let mut nonstandardAxiomNames : Array Name := #[]

  for h : moduleIndex in [0:env.header.moduleNames.size] do
    unless isProjectModule env.header.moduleNames[moduleIndex] do
      continue
    for declarationInfo in env.header.moduleData[moduleIndex]!.constants do
      let declarationName := declarationInfo.name
      declarationCount := declarationCount + 1
      if declarationInfo.isAxiom then
        projectAxiomNames := projectAxiomNames.push declarationName
      if declarationInfo.isTheorem then
        theoremCount := theoremCount + 1
      let axioms <- Lean.collectAxioms declarationName
      if axioms.contains placeholderAxiomName then
        placeholderDependentDeclarations :=
          placeholderDependentDeclarations.push declarationName
      for axiomName in axioms do
        unless isStandardAxiom axiomName ||
            nonstandardAxiomNames.contains axiomName do
          nonstandardAxiomNames := nonstandardAxiomNames.push axiomName

  unless projectAxiomNames.isEmpty do
    throwError "project-defined axioms found: {projectAxiomNames}"
  unless placeholderDependentDeclarations.isEmpty do
    throwError "placeholder-dependent project declarations found: {placeholderDependentDeclarations}"
  unless nonstandardAxiomNames.isEmpty do
    throwError "nonstandard theorem axioms found: {nonstandardAxiomNames}"

  for milestone in milestones do
    let some declarationInfo := env.find? milestone.theoremName
      | throwError "missing project milestone theorem: {milestone.theoremName}"
    unless isProjectDeclaration env milestone.theoremName do
      throwError "milestone is not declared by this project: {milestone.theoremName}"
    unless declarationInfo.isTheorem do
      throwError "project milestone is not a theorem: {milestone.theoremName}"
    let axioms <- Lean.collectAxioms milestone.theoremName
    let unexpectedAxioms := axioms.filter (fun axiomName => !isStandardAxiom axiomName)
    unless unexpectedAxioms.isEmpty do
      throwError "milestone has nonstandard axioms: {milestone.theoremName}: {unexpectedAxioms}"

  let statusJson := Json.mkObj [
    ("schemaVersion", toJson 4),
    ("generator", .str "scripts/GenerateProjectStatus.lean"),
    ("leanVersion", .str Lean.versionString),
    ("compiledProjectModules", toJson moduleCount),
    ("compiledProjectDeclarations", toJson declarationCount),
    ("projectTheorems", toJson theoremCount),
    ("projectAxioms", toJson projectAxiomNames.size),
    ("placeholderDependentDeclarations",
      toJson placeholderDependentDeclarations.size),
    ("nonstandardTheoremAxioms", .arr #[]),
    ("rhImplied", .bool false),
    ("presentation", .str "verified theorem inventory; milestones are not a proof chain"),
    ("statusNote", .str
      ("Lean proves exact arithmetic--spectral and Gaussian/Weil bridges, " ++
        "RH-equivalent detectors, and a fixed positive paired-eta Laplace " ++
        "measure whose transform vanishes at every nontrivial zeta zero. " ++
        "Complementary tilts produce a positive horizontal-defect density. " ++
        "The explicit support and gap partial sums telescope with remainder " ++
        "(2N+1)^(-s). A restricted-tail measure gives closed finite gap-error " ++
        "bounds with complementary exponents sigma and 1-sigma; these are " ++
        "distinct for an off-critical zero. The support-minus-gap Euler " ++
        "second-difference series is exactly 2*E(s)-1 and equals -1 at a " ++
        "zero, giving an exact half-endpoint plus second-difference-tail " ++
        "formula at both complementary evaluations. A checked integral-test " ++
        "estimate makes the remaining Euler tail one full endpoint power " ++
        "smaller. Lean normalizes this to the exact complex limit -1/2 and " ++
        "the positive scaled-norm limit 1/2 at exponents sigma and 1-sigma. " ++
        "A generic theorem proves that independent eventual two-sided " ++
        "comparability of the two raw errors forces sigma=1-sigma. Under RH " ++
        "each zero equals its reflected partner, so Lean proves that the " ++
        "global comparison principle is exactly equivalent to Mathlib's RH. " ++
        "Lean realizes the actual finite paired-eta polynomial's Gaussian " ++
        "norm as an explicit finite arithmetic Gram sum. It now also constructs " ++
        "the finite positive logarithmic eta measure, identifies its Laplace " ++
        "transform with E_N(s)/s, and proves that the normalized eta Gaussian " ++
        "norm is exactly a positive double integral over that measure, including " ++
        "all integrability, Fubini, and interval-expansion steps. Lean now " ++
        "differentiates this Gram form twice in sigma: its first derivative is " ++
        "the negative first logarithmic-time moment and its second derivative is " ++
        "the positive second moment. For every nonempty truncation and positive " ++
        "Gaussian time both moments are strictly positive, so the raw profile is " ++
        "strictly decreasing and strictly convex. Cauchy--Schwarz gives the exact " ++
        "first-moment-squared versus zeroth-times-second-moment determinant, and " ++
        "Lean derives the corresponding second logarithmic derivative and global " ++
        "log-convexity. Thus equality at complementary tilts holds exactly at " ++
        "sigma=1/2. Lean now constructs the exact eta completion factor " ++
        "C(s)=s(1-s)GammaR(s)/(1-2*2^(-s)), proves C(s)E(s)=xi(s) locally " ++
        "throughout 0<Re(s)<1, and identifies the existing regular correction " ++
        "with C'/C. At every nontrivial zero of arbitrary multiplicity m, the " ++
        "first nonzero eta coefficients at rho and 1-conj(rho) satisfy the exact " ++
        "completion-weighted conjugate relation forced by xi. This completed " ++
        "identity is compatible with off-critical zeros. Lean now proves every " ++
        "logarithmic-time eta moment integrable in the positive half-plane and " ++
        "identifies it with the corresponding iterated Laplace derivative. At a " ++
        "zero the Laplace partition has the exact zeta multiplicity, its leading " ++
        "moment is nonzero, and the completed partner identity is a literal relation " ++
        "between the two explicit leading moments. Lean further decomposes each " ++
        "moment into the eta support and omitted logarithmic gaps and proves the " ++
        "complete half-line value n!/s^(n+1). At a zero of multiplicity m, the " ++
        "gap moments match that elementary value exactly for k<m and first differ " ++
        "at k=m; the completed partner identity is an exact relation between those " ++
        "first defects. Each gap moment is now an absolutely convergent sum over the " ++
        "literal omitted intervals. Lean computes the positive real envelope as " ++
        "n!/sigma^(n+1) and proves a strict saving from the first gap equal to " ++
        "(log 3-log 2)(log 2)^n exp(-sigma log 3). Completion symmetry now gives " ++
        "an exact reciprocal-weight ratio for the two nonzero leading defects and " ++
        "bounds their common positive completed magnitude by the explicit envelope " ++
        "at both complementary tilts. Lean now preserves phase in arbitrary finite " ++
        "support prefixes and bounds the remaining order-n moment tail by " ++
        "exp(-(1-theta)sigma log(2N+1)) n!/(theta sigma)^(n+1). The resulting " ++
        "nonnegative finite lower certificates converge to the exact nonzero defect " ++
        "norm and are eventually positive. At complementary zeros their completed " ++
        "versions converge to the same positive magnitude. No uniform finite-prefix " ++
        "inequality forcing the horizontal displacement to vanish is proved, " ++
        "and no current theorem implies RH.")),
    ("milestones", .arr (milestones.map milestoneToJson)),
    ("frontier", Json.mkObj [
      ("label", .str "Arithmetic-to-zero-location rigidity"),
      ("status", .str "open"),
      ("target", .str (
        "Prove a uniform tilt-separating inequality for the finite phase-sensitive " ++
        "eta moment prefixes that excludes complementary off-critical tilts, " ++
        "or force the exact " ++
        "detector limit to vanish without discarding zero contributions"))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
