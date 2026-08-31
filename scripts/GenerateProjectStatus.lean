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
    label := "The eta odd-heat trajectory retains an exact three-colour zero sum"
    lineOne := "eta heat trajectory"
    lineTwo := "3-colour zero sum"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_zero_one_eq_integral_mixedChannelZeroSumAt
  },
  {
    label := "External Montgomery--Taylor simple-zero benchmark"
    lineOne := "external simple zeros"
    lineTwo := "HD(1) > 2/3"
    role := "external"
    theoremName :=
      ``RiemannGaussian.externalZeta23_montgomeryTaylor_simple_projectFiniteWindows
  },
  {
    label := "The exact Zeta23 defect bounds literal eta negative inertia"
    lineOne := "eta negative inertia"
    lineTwo := "exact HD(1) defect"
    role := "external"
    theoremName :=
      ``RiemannGaussian.externalZeta23_montgomeryTaylor_etaBlockNegativeInertia
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
    "  <desc id=\"description\">Checked project results, identities, an attributed " ++
      "external baseline, and equivalences. The boxes are not a proof chain. No project " ++
      "theorem improves the external zero-proportion baseline or proves RH.</desc>\n" ++
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
    "      .proved.external rect { fill: #20220f; stroke: #d2a822; }\n" ++
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
      "0 project axioms · milestones standard-only</text>\n" ++
    "  <text class=\"section\" x=\"20\" y=\"64\">CHECKED RESULTS, IDENTITIES, AND ATTRIBUTED BASELINE</text>\n" ++
    "  <text class=\"section\" x=\"20\" y=\"143\">FURTHER CHECKED MILESTONES — NOT A PROOF CHAIN</text>\n" ++
    "  <line x1=\"670\" y1=\"62\" x2=\"670\" y2=\"207\" stroke=\"#30363d\"/>\n" ++
    "  <text class=\"gap-label\" x=\"765\" y=\"94\">UNPROVED MATHEMATICS</text>\n" ++
    "  <path class=\"open-edge\" d=\"M840 139 H853\"/>\n" ++
    nodes ++
    "  <g class=\"open\">\n" ++
    "    <rect x=\"690\" y=\"108\" width=\"150\" height=\"62\" rx=\"10\"/>\n" ++
    "    <text x=\"765\" y=\"133\">eta arithmetic bound</text>\n" ++
    "    <text x=\"765\" y=\"153\">NO NEW PROPORTION</text>\n" ++
    "  </g>\n" ++
    "  <g class=\"goal\">\n" ++
    "    <rect x=\"855\" y=\"114\" width=\"125\" height=\"50\" rx=\"9\"/>\n" ++
    "    <text x=\"917\" y=\"144\">RH</text>\n" ++
    "  </g>\n" ++
    "  <text class=\"frontier\" x=\"20\" y=\"220\">Current fact: no RiemannGaussian " ++
      "certificate improves the imported exact HD(1) zeta baseline.</text>\n" ++
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
    ("schemaVersion", toJson 9),
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
      ("The build rechecks the pinned external Zeta23 unconditional two-thirds and exact " ++
        "multiplicity-aware Montgomery--Taylor HD(1) simple-zero theorems, proves in Lean that " ++
        "HD(1) > 2/3, and derives the corresponding project-native simple finite-window form and " ++
        "exact negative-inertia bound for " ++
        "the literal signed eta block. RiemannGaussian has exact analytic, eta, " ++
        "heat, matrix, and contour infrastructure, but no unconditional eta certificate " ++
        "currently improves that external zeta-zero proportion. Conditional threshold " ++
        "interfaces and generic finite models are not counted as achieved proportions.")),
    ("externalBaselines", .arr #[
      Json.mkObj [
        ("source", .str "anthropics/zeta-23-lean"),
        ("commit", .str "2bafb8c88f177284a2123b5fefa2ff84e2365eb6"),
        ("theorem", .str
          "RiemannGaussian.externalZeta23_twoThirds_distinctCritical"),
        ("constant", .str "2/3"),
        ("status", .str "unconditional; rechecked")
      ],
      Json.mkObj [
        ("source", .str "anthropics/zeta-23-lean"),
        ("commit", .str "2bafb8c88f177284a2123b5fefa2ff84e2365eb6"),
        ("theorem", .str
          "RiemannGaussian.externalZeta23_montgomeryTaylor_simpleCritical"),
        ("constant", .str "Zeta23.ThmD.HD 1"),
        ("comparisonTheorem", .str
          "RiemannGaussian.externalZeta23_HD_one_gt_two_thirds"),
        ("projectSimpleFiniteWindowTheorem", .str
          "RiemannGaussian.externalZeta23_montgomeryTaylor_simple_projectFiniteWindows"),
        ("distinctCriticalTheorem", .str
          "RiemannGaussian.externalZeta23_montgomeryTaylor_distinctCritical"),
        ("distinctDenominatorTheorem", .str
          "RiemannGaussian.externalZeta23_montgomeryTaylor_distinctDenominator"),
        ("projectFiniteWindowTheorem", .str
          "RiemannGaussian.externalZeta23_montgomeryTaylor_projectFiniteWindows"),
        ("etaBlockNegativeInertiaTheorem", .str
          "RiemannGaussian.externalZeta23_montgomeryTaylor_etaBlockNegativeInertia"),
        ("status", .str "unconditional; rechecked")
      ]
    ]),
    ("milestones", .arr (milestones.map milestoneToJson)),
    ("frontier", Json.mkObj [
      ("label", .str "Actual eta zero-proportion certification"),
      ("status", .str "open"),
      ("target", .str
        ("Prove an unconditional eta-arithmetic inequality that yields a zeta " ++
          "zero-proportion strictly above the imported exact HD(1) baseline. " ++
          "No such theorem is currently present; 13/18 and 18/18 remain targets."))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
