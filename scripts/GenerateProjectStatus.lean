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
    label := "The exact phase family proves the actual reciprocal-logarithm edge strip with denominator 23000"
    lineOne := "zero-free strip"
    lineTwo := "explicit 1/log"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.nontrivialZetaZero_mem_phaseContact_reciprocal_log_strip
  },
  {
    label := "Explicit edge windows contain at most one actual zero counting multiplicity"
    lineOne := "edge zero windows"
    lineTwo := "multiplicity <= 1"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.sum_multiplicity_le_one_in_signedEdgeWindow
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
    label := "Uncapped project improvement beyond the preceding certificate"
    lineOne := "literal simple zeros"
    lineTwo := "HD(1) < C₀ < C₁"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.Zeta23InverseSampling.externalZeta23_montgomeryTaylor_uncapped_strictly_stronger
  },
  {
    label := "Every hypothetical right-half zero forces its negative multiplicity into an actual finite ordinary-prime band; the opposite arithmetic bound remains open"
    lineOne := "finite prime band"
    lineTwo := "zero source = -m"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.tendsto_zetaRightHalfOrdinaryPrimeBandFilter_re
  },
  {
    label := "Five powers of two give the exact phase optimiser a uniform arithmetic floor 1/120 for 1 < sigma <= 5/4"
    lineOne := "phase arithmetic floor"
    lineTwo := "uniform >= 1/120"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.phaseContactExact_arithmetic_floor
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
  { x := 500, y := 150 },
  { x := 20, y := 229 },
  { x := 180, y := 229 },
  { x := 340, y := 229 }
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
      "aria-labelledby=\"title description\" viewBox=\"0 0 1000 315\">\n" ++
    "  <title id=\"title\">Lean-verified RiemannGaussian theorem inventory</title>\n" ++
    "  <desc id=\"description\">Checked project results, identities, an attributed " ++
      "external baseline, ordered project zero-proportion improvements, and equivalences. The boxes " ++
      "are not a proof chain. The 13/18 target and RH remain unproved.</desc>\n" ++
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
      "height=\"313.5\" rx=\"12\"/>\n" ++
    "  <text class=\"heading\" x=\"20\" y=\"30\">Lean-checked theorem inventory — RH remains open</text>\n" ++
    s!"  <text class=\"metrics\" x=\"980\" y=\"28\">Lean {Lean.versionString} · " ++
      s!"{moduleCount} modules · {declarationCount} declarations · {theoremCount} theorems</text>\n" ++
    "  <text class=\"metrics\" x=\"980\" y=\"47\">0 placeholder dependencies · " ++
      "0 project axioms · milestones standard-only</text>\n" ++
    "  <text class=\"section\" x=\"20\" y=\"64\">CHECKED RESULTS, IDENTITIES, AND ATTRIBUTED BASELINE</text>\n" ++
    "  <text class=\"section\" x=\"20\" y=\"143\">FURTHER CHECKED MILESTONES — NOT A PROOF CHAIN</text>\n" ++
    "  <line x1=\"670\" y1=\"62\" x2=\"670\" y2=\"287\" stroke=\"#30363d\"/>\n" ++
    "  <text class=\"gap-label\" x=\"765\" y=\"94\">UNPROVED MATHEMATICS</text>\n" ++
    "  <path class=\"open-edge\" d=\"M840 139 H853\"/>\n" ++
    nodes ++
    "  <g class=\"open\">\n" ++
    "    <rect x=\"690\" y=\"108\" width=\"150\" height=\"62\" rx=\"10\"/>\n" ++
    "    <text x=\"765\" y=\"133\">signed prime band</text>\n" ++
    "    <text x=\"765\" y=\"153\">one-sided bound OPEN</text>\n" ++
    "  </g>\n" ++
    "  <g class=\"goal\">\n" ++
    "    <rect x=\"855\" y=\"114\" width=\"125\" height=\"50\" rx=\"9\"/>\n" ++
    "    <text x=\"917\" y=\"144\">RH</text>\n" ++
    "  </g>\n" ++
    "  <text class=\"frontier\" x=\"20\" y=\"300\">The finite prime band retains the exact zero source. " ++
      "Its independent signed bound remains open; the local phase reserve does not prove RH.</text>\n" ++
    "</svg>\n"

run_cmd do
  unless milestones.size == milestonePoints.size do
    throwError "every milestone must have exactly one visible inventory position"
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
    ("schemaVersion", toJson 11),
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
      ("The external two-thirds and Montgomery--Taylor baselines and the literal simple-zero " ++
      "constants HD(1) < C0 < C1 remain checked. The exact nonnegative phase optimiser is unique " ++
      "for its fixed shift and linear cost, including infinite integer-frequency competitors. Its " ++
      "actual zeta height budget proves a reciprocal-logarithm edge margin with denominator " ++
      "23000*log(abs(gamma)+22). Retaining the triangular phase-return multiplicities improves " ++
      "the general arithmetic floor by N*(N+1)/2 at a positive block source. Five powers of two " ++
      "give the exact optimiser a uniform floor 1/120 for 1 < sigma <= 5/4, and an explicit d/120 " ++
      "reserve in its actual local zero inequality. This bounded gain leaves the global signed " ++
      "bound open. The preceding contact-doubling theorem explains why an angle and its double " ++
      "cannot both be contacts. Actual prime Gram " ++
      "matrices have full finite rank after every finite prime prefix. Every hypothetical " ++
      "right-half zero has an exact finite ordinary-prime band whose normalized signed value tends " ++
      "to its negative analytic multiplicity. All omitted analytic modes, proper prime powers, and " ++
      "arithmetic tails are controlled. The independent one-sided bound for this retained signed " ++
      "band remains open. The quadratic alternative independently bounds the whole mixed product " ++
      "and the same-prime contribution, leaving a nonzero source on distinct-prime products. The " ++
      "exact completed eta Euler endpoint explains the earlier positive power source. Suzuki " ++
      "work-floor criteria now have complete analytic implications to RH, but their arithmetic " ++
      "antecedents remain unproved. These are separate results and reductions, not a completed " ++
      "proof chain or a new zero-proportion certificate. No RH proof or mathematical-priority " ++
      "claim is made. Detailed scope and proof histories are in " ++
      "docs/eta-current-reconstruction-plan.md.")),
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
    ("projectAdvances", .arr #[
      Json.mkObj [
        ("theorem", .str
          "RiemannGaussian.Zeta23InverseSampling.externalZeta23_montgomeryTaylor_uncapped_strictly_stronger"),
        ("constant", .str "C0, C1 with Zeta23.ThmD.HD 1 < C0 < C1"),
        ("numerator", .str "Zeta23.N0simple T (2*T)"),
        ("denominator", .str "Zeta23.Ncount T (2*T)"),
        ("comparisonTheorem", .str
          "RiemannGaussian.Zeta23InverseSampling.montgomeryTaylor_affine_constant_strict_mono"),
        ("status", .str "unconditional; strictly improves preceding project certificate")
      ]
    ]),
    ("milestones", .arr (milestones.map milestoneToJson)),
    ("frontier", Json.mkObj [
      ("label", .str "Independent signed prime-band bound"),
      ("status", .str "open"),
      ("target", .str
        ("For every hypothetical zero right of one half, prove an independent signed inequality " ++
        "beating its source after the proved error allowances. The reference carrier is the actual " ++
        "finite ordinary-prime band: b_N=(3/2-beta)^(N+1)*Re(B_N) tends to -m. One fixed positive " ++
        "margin above -m at arbitrarily large orders would suffice; neither an all-order norm bound " ++
        "nor a full prime-pair asymptotic is required. That independent arithmetic estimate remains " ++
        "open. The exact phase contact geometry supplies a bounded local reserve, not the missing " ++
        "global bound. The completed quadratic and eta identities remain available; further " ++
        "decomposition is paused unless it yields a useful signed comparison."))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
