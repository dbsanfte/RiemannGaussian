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
    label := "Complete binomial energies retain all phases; the exact optimiser has arithmetic floor exp(-4*(sigma-1)*log(2))/40 for 1 < sigma <= 5/4"
    lineOne := "phase arithmetic floor"
    lineTwo := "scale + full energy"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.phaseContactExact_binomial_scaled_arithmetic_floor
  },
  {
    label := "The actual infinite eta curvature has Gaussian integral norm at most 2*sqrt(pi/tau)*exp(-(log 2)^2/(8*tau)), uniformly over all positive vertical lines and centers for 0 < tau <= log(2)/32; the complete normalized reflection-source inequality remains open"
    lineOne := "eta curvature heat bound"
    lineTwo := "uniform in line + center"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.norm_integral_pairedEta_curvature_gaussian_le
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
  { x := 340, y := 229 },
  { x := 500, y := 229 }
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
    "    <text x=\"765\" y=\"133\">Signed Suzuki source</text>\n" ++
    "    <text x=\"765\" y=\"153\">ceiling OPEN</text>\n" ++
    "  </g>\n" ++
    "  <g class=\"goal\">\n" ++
    "    <rect x=\"855\" y=\"114\" width=\"125\" height=\"50\" rx=\"9\"/>\n" ++
    "    <text x=\"917\" y=\"144\">RH</text>\n" ++
    "  </g>\n" ++
    "  <text class=\"frontier\" x=\"20\" y=\"300\">All poles and both strip sides are retained. The independent source ceiling remains unproved; " ++
      "the remaining pole, energy and favorable remainder terms must stay coupled.</text>\n" ++
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
      "23000*log(abs(gamma)+22). A general real test retains its full return autocorrelation " ++
      "and compares each lag with the actual prime-power amplitude. Binomial trigonometric " ++
      "tests retain the complete frequency energy, and a frequency and its double force an extra " ++
      "source. Keeping the prime scale gives the exact optimiser a floor exp(-4*(sigma-1)*log(2))/40 " ++
      "for 1 < sigma <= 5/4. Its actual zero tests retain d*exp(-13*d*log(2))/40 and the stronger " ++
      "phase-sensitive energy reserve. This bounded gain leaves the global signed " ++
      "bound open. The actual Suzuki carrier now satisfies norm-square = imaginary part almost " ++
      "everywhere, with its exceptional real denominator zeros proved countable. Its full " ++
      "two-time arithmetic Gram and every finite complex time test have exact integrable signed " ++
      "phase representations. Both separated channels now have exact local reflected-pair " ++
      "residues at every xi node, including multiple and nonreal nodes. Their signed mixed Gram " ++
      "has removable xi-node singularities and exactly zero sufficiently small circle integrals. " ++
      "The full mixed boundary Gram now splits into two absolutely integrable channels after " ++
      "one common real-node subtraction. Both genuine symmetric principal values exist, " ++
      "including at multiple real nodes, and the subtraction's auxiliary complex poles have " ++
      "an exact partial fraction identity. The global xi logarithmic-derivative difference is " ++
      "now an absolutely convergent genuine multiplicity-weighted Cauchy series: analytic and " ++
      "mirror remainders both vanish. Reflection gives its signed Poisson representation. " ++
      "For Im z >= 1/2 the upper carrier denominator is nonzero for every nonnegative " ++
      "homotopy parameter; the actual carrier obeys norm-square <= imaginary part and norm <= 1. " ++
      "The reflected lower carrier has the corresponding estimates. Every mixed outer " ++
      "horizontal integral is bounded by 8/T for T >= 1 and tends to zero. The actual full " ++
      "spectral Cauchy windows converge to A'/A, and their existing raw remainder tends to zero. " ++
      "Subtracting the complete signed Blaschke contribution leaves the reflected critical " ++
      "and lower divisor with nonpositive imaginary part. Its positive Poisson reserves " ++
      "increase to the complete contribution; every upper carrier pole must pay for one unit " ++
      "plus every retained reserve. Arbitrary-order carrier poles have exact mixed circle " ++
      "residues. At a simple pole every finite complex test retains the reflected bilinear " ++
      "product divided by the full logarithmic-derivative slope. Complete finite Laurent " ++
      "subtraction now constructs the analytic remainder at every pole order. The actual " ++
      "rectangular mixed channel equals its explicit reflected xi source plus all genuine " ++
      "carrier-pole residues, with side integrability proved. Admissible upper rectangles " ++
      "exist at arbitrary heights and arbitrarily small positive bottom height. Their signed " ++
      "matrix comparison retains the full conjugate-transposed pole correction and all " ++
      "oriented side terms; variable outer top integrals obey 16/R bounds. For every pair " ++
      "without a repeated real node, the actual displaced bottom converges to the truncated " ++
      "real Gram, which exhausts to the full Gram. Complete zero principal parts permit " ++
      "real xi nodes on the bottom of the actual finite contour. Its real Gram identity " ++
      "retains every pole and conjugate-transposed entry. Each safe outer vertical piece " ++
      "obeys an 8/R bound once its coordinate passes both nodes; the combined signed safe " ++
      "sides cost at most 32/R, leaving two fixed-height strip segments. Keeping the canonical " ++
      "reflection difference inside the mixed channel gives an exact quartic denominator " ++
      "and safe outer error 512*Im(alpha)^2/R^3. Its reflected source is exactly minus the " ++
      "inverse multiplicity. The actual reflection Gram energy is strictly positive for " ++
      "each off-axis zero. Along every constructed admissible outer family, the full joint " ++
      "pole/strip correction converges to 2*pi/m plus that positive energy; separate pole " ++
      "and strip limits are not assumed. An independent source ceiling with any vanishing " ++
      "allowance would suffice, without a prescribed strict source deficit. This ceiling, " ++
      "the independent Blaschke upper budget and the global signed arithmetic bound remain " ++
      "open; no new zeta zeros have been excluded. Pairing the complete xi divisor now " ++
      "confines every positive imaginary contribution to an actual reflected-zero Jensen " ++
      "disk. Past the observation ordinate plus one half, finite symmetric Cauchy heads " ++
      "decrease in imaginary part to the full logarithmic derivative. A finite local " ++
      "ordinate band of radius at least one half also bounds that imaginary part from " ++
      "above while retaining its negative terms. Every genuine upper carrier pole must " ++
      "reach the unit threshold in every such local band and lie inside an actual Jensen " ++
      "disk. The literal carrier is bounded by one outside the disk union, including " ++
      "inside the zero strip and at totalized xi-node values. No local budget below one " ++
      "is presumed globally. The fixed-window analytic tail now has nonpositive imaginary " ++
      "part through the removed xi divisor, giving a full complex derivative bound by " ++
      "four times its central signed mass divided by observation height. At genuine upper " ++
      "carrier poles the finite slope error is at most 4*(Im(q_T)-1)/Im(c) and tends to zero. " ++
      "A positive finite margin proves simplicity and an inverted complex disk encloses " ++
      "the full weighted residue with its reflected phase retained. For every fixed finite " ++
      "simple pole set one window eventually works for all finite weight families; the " ++
      "total radius tends to zero for each fixed family. The signed matrix upper bound " ++
      "retains the combined complex centers; these slope disks require simple poles. " ++
      "The actual carrier now also has a full paired-eta quotient whose denominator " ++
      "is eta' + (1+L)*eta, with the explicit completion correction L. Its finite " ++
      "denominator retains odd/even coefficients and the exact weights 1+L-log(n). " ++
      "The finite arithmetic quotient converges uniformly on compact sets avoiding " ++
      "the actual carrier denominator, with eventual nonvanishing and continuity " ++
      "proved. On admissible rectangles strictly inside the open spectral strip, " ++
      "finite arithmetic contours recover the full complex weighted xi source and " ++
      "carrier-pole sum, including all higher orders. Subtracting the exact xi source " ++
      "gives signed upper bounds for complete fixed pole groups with arbitrarily " ++
      "small positive errors. The same completion and finite coefficients now work in " ++
      "the positive half-plane away from one and the dyadic factor zeros. Their " ++
      "spectral exceptions are countable on height one half; compatible vertical " ++
      "sides and arbitrarily large rectangles are constructed. Both complete strip " ++
      "segments have their arithmetic limits, including the endpoints. A positive " ++
      "bottom lift preserves every genuine carrier pole in the real-bottom rectangle. " ++
      "One bottom recovers the full complex joint correction for every finite weight " ++
      "family, with the lifted contour's exact xi source subtracted. Along constructed " ++
      "expanding contours, growing common eta truncations recover the actual signed " ++
      "reflection correction with error below 1/(n+1). This is an adapted diagonal " ++
      "approximation, not a uniform estimate for independent contour and truncation " ++
      "sizes. Actual expanding contours can now have negative dyadic cosines on both " ++
      "vertical sides. The completion factor stays uniformly nonzero; on each complete " ++
      "strip segment, minus its logarithmic derivative has real part between log(2)/2 " ++
      "and 2*log(2)/3. Every complex weighted finite carrier has a centered dyadic error " ++
      "bounded by log(2)/2 times the weight norm and its own quadratic energy. The signed " ++
      "eta/derivative interaction and true denominator remain intact. " ++
      "These phase choices preserve the complete source-plus-energy recovery limit. " ++
      "Every selected truncation has proved nonzero denominators on all observation " ++
      "paths, with genuine weighted path integrability for each regular truncation. " ++
      "Completing a complex square now gives an independent one-sided bound for the " ++
      "signed eta remainder without denominator separation. Matching opposite sine " ++
      "quadrants to the actual side orientations bounds its integrated negative part " ++
      "by 512*Im(alpha)^2/(log(2)*R^4), uniformly in regular truncations. This part " ++
      "tends to zero along constructed expanding contours. The exact joint correction " ++
      "retains the complete pole term plus nonnegative strip energy minus the signed " ++
      "remainder. Removing only the vanishing adverse part keeps the favorable " ++
      "remainder coupled and preserves the original source-plus-energy limit. " ++
      "Clearing the full eta denominator now gives an analytic expression with " ++
      "quadratic local height growth and a fixed safe-center floor. Its exact " ++
      "multiplicity is the genuine denominator order plus two at each dyadic " ++
      "exception. Moving-disk Jensen bounds actual genuine carrier-pole multiplicity " ++
      "in each fixed strip window by log(C*(abs(T)+4)^2)/log(18/17), on both sides. " ++
      "This controls local counts, not the signed weighted residues or strip energy. " ++
      "For every positive arithmetic height at least two, the full cleared denominator " ++
      "now has a canonical analytic unit with a polynomial upper bound and fixed " ++
      "center floor. Its normalized complex logarithm and logarithmic derivative are " ++
      "bounded by logarithmic height on the unit disk, with an explicit positive " ++
      "lower bound for the unit. An exact carrier identity retains the literal eta " ++
      "numerator, full pole product and analytic phase. Admissible left strip segments " ++
      "satisfy its regularity conditions through both endpoints. The separate absolute " ++
      "envelope has a large polynomial cost and does not control the signed pole product. " ++
      "The full complex parameter circle is now evaluated exactly, with genuine trace " ++
      "integrability away from its explicit denominator-zero threshold. It preserves " ++
      "the local source coefficient at every xi zero and gives a bounded projection " ++
      "of the original carrier. Both projected strip integrals are integrable through " ++
      "all cutoff crossings and have combined bound 64*Im(alpha)^2/(r*R^4). The " ++
      "complete original correction differs by at most this amount from every " ++
      "genuine pole residue coupled to both signed large-value strip integrals. " ++
      "No global holomorphy of the cutoff or bound for that retained expression is claimed. " ++
      "The actual entire numerator and denominator now define a globally real-smooth " ++
      "carrier bounded by 1/(2*r), with a continuous exact Wronskian area source through " ++
      "all genuine poles and common zeros. For fixed positive smoothing radius and heat " ++
      "time, both signed Gaussian area terms together are bounded by " ++
      "4*R^2/r*exp(-tau*R^2/4) and their exhausting rectangle integrals tend to zero. " ++
      "The original reflection weight still has shrinking-circle source -2*pi*i/m, " ++
      "also with the moving Gaussian evaluated at the node. Its weighted density " ++
      "retains the complete bulk. Geometric excision now evaluates the actual four-rectangle " ++
      "improper area as the outer boundary plus 2*pi*i*B(beta)/m. The full weighted " ++
      "outer boundary has a Gaussian decay bound and tends to zero, so the iterated " ++
      "area limit is exactly that source, with strictly positive imaginary part at " ++
      "a hypothetical right-half zero. An independent signed upper bound below this " ++
      "source is open; one fixed positive smoothing radius would suffice. " ++
      "The same full signed density now has an exact eta expression on the complete " ++
      "completion domain, including genuine carrier poles and common xi zeros. The " ++
      "common completion factor cancels; its first logarithmic correction cancels " ++
      "from the Wronskian, leaving eta'^2-eta*eta''-Q'*eta^2 with full complex phase. " ++
      "The correction Q remains in the denominator. Literal finite eta prefixes " ++
      "recover both signed density terms pointwise through every genuine upper " ++
      "carrier pole of arbitrary order. Polynomial curvature convergence includes " ++
      "common zeros, while quotient convergence excludes common numerator/denominator " ++
      "zeros. No finite-sum/area/puncture limit exchange or contradictory bound is proved. " ++
      "The bare eta curvature now has an exact bilinear logarithmic-gap expansion, " ++
      "with parity signs and integer-product phases retained. Gaussian averaging has " ++
      "a cutoff-independent bound for all finite complex coefficient families bounded " ++
      "by one. Cauchy derivative estimates supply a polynomial dominator, so the " ++
      "Gaussian integral of the actual infinite eta curvature has norm at most " ++
      "2*sqrt(pi/tau)*exp(-(log 2)^2/(8*tau)) for 0 < tau <= log(2)/32, " ++
      "uniformly over every positive vertical line and every center. Its averages " ++
      "vanish even along arbitrary moving positive lines and centers. This justified " ++
      "prefix/Gaussian integral exchange concerns bare curvature only. The completion " ++
      "curvature, variable smoothing denominator, reflection weight and companion " ++
      "Gaussian term remain coupled in the open source inequality. " ++
      "An exact weighted-current identity now retains the full normalization " ++
      "derivative, complex phase and completion curvature. Its pointwise signed " ++
      "upper expression applies to the actual reflection density through genuine " ++
      "upper carrier poles, with all eta conditions discharged. At each such pole " ++
      "the normalization derivative cancels the entire signed quadratic interaction. " ++
      "The full source also equals 2*i*r^2*(S*U'-U*S') along arithmetic vertical " ++
      "lines on the completion domain away from common zeros. Here S is the actual " ++
      "smooth carrier, 0 <= U <= 1/r^2 and normSq(S)=U-r^2*U^2. The companion " ++
      "heat term is retained. These are exact pointwise identities and value bounds; " ++
      "no bound for their global coupled variation or new area-limit exchange is proved. " ++
      "Removing smoothing is singular at genuine carrier poles, where the exact " ++
      "source is -2/r^2*conj(E'/A). No area or pole-sum limit interchange is asserted. " ++
      "The independent source ceiling is still open; no zero exclusion follows. " ++
      "The preceding contact-doubling theorem explains why an angle and its double " ++
      "cannot both be contacts. Actual prime Gram " ++
      "matrices have full finite rank after every finite prime prefix. Every hypothetical " ++
      "right-half zero has an exact finite ordinary-prime band whose normalized signed value tends " ++
      "to its negative analytic multiplicity. All omitted analytic modes, proper prime powers, and " ++
      "arithmetic tails are controlled. The independent one-sided bound for this retained signed " ++
      "band remains open. The quadratic alternative independently bounds the whole mixed product " ++
      "and the same-prime contribution, leaving a nonzero source on distinct-prime products. The " ++
      "exact completed eta Euler endpoint explains the earlier positive power source. Suzuki " ++
      "work-floor criteria now have complete analytic implications to RH. Exact divisor " ++
      "minorants now certify the finite mass potential at its actual minimizing center; other " ++
      "centers pay the full exponential convexity cost. An eventual finite certificate floor " ++
      "would imply RH. The unrestricted finite maximum is now proved equal to that same " ++
      "potential, and every optimizer is characterized by zero prime-power slack. A " ++
      "stronger lower-certificate theorem needs constraints only on prime powers. A " ++
      "nonnegative comparison mass matching finitely many basis observations bounds all " ++
      "coefficient choices in that weight span at once. Explicit finite Mobius coefficients " ++
      "now attain the optimum on complete quotient cells for every endpoint and center. " ++
      "At most twice the integer square root of the endpoint many cells suffice. Their " ++
      "coupled slope and intercept jumps cancel in value at the endpoint center. This " ++
      "removes approximation loss without supplying an independent lower bound. A " ++
      "right-half zero now forces arbitrarily low potentials on mass-balanced cells, " ++
      "using both signal orientations and actual local minima. Their full entropy " ++
      "correction is independently bounded by 1/(N*sqrt(N)), with uniform decay proved. " ++
      "A signed endpoint floor on only those cells would imply RH. The general Landau " ++
      "compensator now permits any nonnegative locally integrable subexponential " ++
      "allowance. Its genuine Laplace response is analytic at every positive damping " ++
      "and is subtracted without losing the zero residue. Over all sufficiently large " ++
      "cutoffs, a one-sided bound by C(epsilon)*N^epsilon for every epsilon>0 suffices " ++
      "for the exact potential or literal logarithmic average, including finite heads " ++
      "and the full gap error. Every right-half zero would force negative excursions " ++
      "of some positive power size. Exact positive delay averages now prove that the actual " ++
      "Suzuki signal recovers within [a,4096*a] for every sufficiently large a. Every deep " ++
      "excursion has a genuine local minimum within fixed multiples of its own time. " ++
      "The growing subpolynomial allowance now needs only mass-balanced cells, including " ++
      "the finite head, affine correction, and full entropy error. A one-sided subpolynomial " ++
      "upper bound on the literal logarithmic average at those cells also suffices. Every " ++
      "right-half zero would force positive-power negative excursions on balanced cells " ++
      "themselves. Complete blocks between balanced physical cutoffs N and N+L now " ++
      "satisfy the independent bound abs(B_(N+L)-B_N) <= (L+1)^2/(N*sqrt(N)). The exact " ++
      "centered prime moment retains the full block entropy and all cross interactions. " ++
      "Uniform variation tends to zero on every fixed power length scale below N^(3/4). " ++
      "The global floor remains open: neither a sufficiently dense covering by balanced " ++
      "endpoints nor control of long blocks and accumulated decreases is proved. " ++
      "An exact logarithmic Dirichlet-convolution identity now couples the centered " ++
      "prime moment to the complete signed Mobius logarithmic convolution and the " ++
      "full prime-pair coefficient at its original product cutoff. Arbitrary finite " ++
      "real and complex tests preserve the identity, as do the actual work blocks " ++
      "and evaluation at the exact mass center. This is an arithmetic identity, not " ++
      "a new estimate for the global signed remainder. " ++
      "A local source audit identifies its genuine Dirichlet response as zeta''/zeta " ++
      "plus the centered logarithmic derivative. At multiplicity m its quadratic " ++
      "source is m*(m-1), while the full pair subtraction retains -m for fixed " ++
      "centers. The local error is uniform in all centers, and every convergent " ++
      "complex weight retains the explicit moving-center contribution. The separate " ++
      "convolution can be small at a simple zero; this is not a global bound. " ++
      "The earlier o(sqrt(N)) bound does not imply it. These are separate results and reductions, not a completed " ++
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
      ("label", .str "Independent signed Suzuki source ceiling"),
      ("status", .str "open"),
      ("target", .str
        ("For every hypothetical zero right of one half, prove an independent signed inequality " ++
        "beating its source after the proved error allowances. The active smooth-area " ++
        "target is an independent signed upper bound below the positive imaginary source " ++
        "of the complete Gaussian reflection area. Geometric excision and outer-boundary " ++
        "decay prove its iterated limit 2*pi*i*B(beta)/m through all carrier poles. One " ++
        "fixed positive smoothing radius suffices; the opposite arithmetic bound is open. " ++
        "The original unsmoothed target remains an eventual ceiling 2*pi/m+o(1) for the " ++
        "complete finite eta pole/strip correction along actual expanding contours. " ++
        "The full source-plus-positive-energy limit " ++
        "and vanishing common truncation error are proved, including on favorable " ++
        "dyadic phases. The signed completed eta remainder now has negative part at most " ++
        "512*Im(alpha)^2/(log(2)*R^4), uniformly in regular truncations, and this adverse " ++
        "part tends to zero. The complete pole term plus quadratic strip energy minus " ++
        "the favorable remainder still needs an independent source ceiling. Actual " ++
        "carrier-pole multiplicities in fixed strip windows now have a logarithmic " ++
        "bound at both signs of the ordinate, with all dyadic extras separated exactly. " ++
        "The analytic unit now has proved logarithmic variation and an explicit polynomial " ++
        "inverse bound on positive-height local disks. Its separate norm cost is too large " ++
        "for the quartic weight; numerator and pole-product phases must stay coupled. " ++
        "The signed weighted residues remain uncontrolled. No decay " ++
        "of the whole remainder or new zero exclusion is asserted. An alternative route is a one-sided " ++
        "subpolynomial lower allowance for the exact Suzuki mass-moment " ++
        "potential: for every epsilon>0, B_N >= -C(epsilon)*N^epsilon eventually on " ++
        "mass-balanced cutoffs. Controlled recovery and the general subexponential " ++
        "compensator prove this implies RH. " ++
        "Finite heads and the full gap error are discharged. The divisor " ++
        "identity, exact mass-center evaluation, and full cost of another center are checked. " ++
        "The unrestricted finite certificate maximum equals the potential, with equality " ++
        "characterized on all prime powers. A class comparison theorem now tests every " ++
        "coefficient choice from finite basis observations. Explicit finite Mobius " ++
        "coefficients attain the optimum on at most 2*floor(sqrt(N)) complete quotient " ++
        "cells with zero approximation loss. Unconditional positive-delay moment bounds " ++
        "control actual recovery times; every deep excursion has a balanced minimum at a " ++
        "comparable logarithmic time. Their nonlinear entropy correction is at most " ++
        "1/(N*sqrt(N)) and uniformly tends to zero. Every right-half zero would force " ++
        "positive-power negative excursions on those cells. Complete balanced blocks " ++
        "now have an independent quadratic variation bound (L+1)^2/(N*sqrt(N)), " ++
        "uniformly vanishing on power length scales below N^(3/4). This local control " ++
        "does not bound long blocks or accumulated decreases. Prove the independent " ++
        "balanced-cell subpolynomial potential floor or a subpolynomial upper bound on " ++
        "the literal signed logarithmic average at those cells. The balance condition and " ++
        "finite inversion do not provide that estimate. The exact logarithmic convolution " ++
        "now retains the Mobius sum and full prime-pair subtraction in the same actual " ++
        "moment, for arbitrary finite tests, but its signed quantitative bound is open. " ++
        "The separate convolution's quadratic local source vanishes at a simple zero; " ++
        "the full pair subtraction retains the nonzero linear multiplicity source. " ++
        "A uniform local center estimate does not close the cutoff bound. The finite " ++
        "prime-band criterion, phase energy and scale-dependent floor, and complete eta identities remain available; " ++
        "none supplies the missing global estimate."))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
