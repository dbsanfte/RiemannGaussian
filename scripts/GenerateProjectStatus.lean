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
    label := "Every actual nontrivial zeta zero lies strictly between 1/(10*log(abs(t)+2)) and its complement at every height. Retaining the negative completion constant gives all admissible phase families a log(2)/2 reserve per unit mass. The existing exact family then excludes more than six fifths of the previous edge width, with a proved 59/90000 source gap after all errors. Interior right-half zeros remain unexcluded and RH remains open"
    lineOne := "zero-free strip"
    lineTwo := "all heights"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.nontrivialZetaZero_mem_completionReserve_strip
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
    label := "Every nonsquarefree arithmetic term has an independent geometric allowance, including every prime square and every overlap with the quadratic prime sieve. Exact shared-prime intersection weights give a uniform finite-square bound, and proved dominated convergence includes all prime squares in the full infinite series. At each hypothetical right-half zero the entire normalized contribution is bounded by C(rho)*lambda^N, where lambda=2*sqrt(u)/(1+sqrt(u))<1. The full source survives on squarefree coefficients in the physical window and (6/7)^N Fourier region, retaining the exact signed reflection and all finite errors. The surviving strict signed bound is open. No additional zeros are excluded, and RH remains open"
    lineOne := "all repeated primes"
    lineTwo := "independent decay"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.exists_zetaRightHalfSquarefreeWindowReflection_error_bound
  },
  {
    label := "Prime support strengthens every admissible positive phase family's Stechkin transfer to 1-c*exp(-(tau-sigma)*log(2)), at least 6/5 of the preceding factor for 1<sigma<=5/4. The unchanged exact family has actual Stechkin work at least exp(-4*(sigma-1)*log(2))/60. Its complete finite phase energy and the negative completion reserve reach the literal zero budget together. The logarithmic height cost and the global signed bound remain open; the uniform zero-free strip is unchanged"
    lineOne := "phase arithmetic floor"
    lineTwo := "support + full energy"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.phaseContactExact_stechkin_one_sixtieth_floor
  },
  {
    label := "For every Re(s)>0 and odd cutoff X>=norm(s), the actual normalized eta tail is within 3*norm(s)/(2*X) of one half. Exact complex adjacent ratios and signed inverse variation are retained. Arbitrary moving arguments with norm(s)/X tending to zero are covered; the independent arithmetic prefix bound remains open"
    lineOne := "eta tail error"
    lineTwo := "uniform in height"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.norm_pairedEtaCoreNormalizedTail_sub_half_le_scale
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
      "earlier local zeta height budget proves a reciprocal-logarithm edge margin with denominator " ++
      "23000*log(abs(gamma)+22). The complete reflected Stechkin budget improved this " ++
      "to 64*log(abs(gamma)+22). A horizontal comparison now halves the genuine Gamma " ++
      "allowance for every admissible phase family and further improves the denominator " ++
      "to 24*log(abs(gamma)+22), with an exact 8/3 increase in the excluded edge width and " ++
      "literal zeta nonvanishing. The exact complex eta Euler center 1/2+s/4 now excludes " ++
      "squared ordinates at most three, removing the height restriction from the edge strip. " ++
      "The complete signed eta expansion and explicit remainder hold at every cutoff. " ++
      "Exact adjacent ratios now bound the actual eta tail by 2*X^(-Re(s)) for X>=norm(s), " ++
      "with normalized error at most 3*norm(s)/(2*X). The complex boundary and signed " ++
      "inverse variation remain coupled; arbitrary moving arguments and cutoffs with " ++
      "norm(s)/X tending to zero share the Euler half-endpoint limit. " ++
      "A general real test retains its full return autocorrelation " ++
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
      "heat term is retained. Those pointwise identities alone do not bound the " ++
      "global coupled variation. " ++
      "The normalized xi mass is now globally real smooth through common zeros " ++
      "and genuine carrier poles, and its eta identity includes both. The full " ++
      "spectral source has a global horizontal variation identity. On every fixed " ++
      "finite horizontal interval avoiding the two reflection nodes, all terms are " ++
      "integrable and integration by parts evaluates the actual current boundary. " ++
      "The complete density integral plus 4*i*r^2 times its retained signed mass " ++
      "variation has norm at most C/r, with an explicit weight budget C independent " ++
      "of r. This gives a signed upper bound and a vanishing combined error as r " ++
      "grows on each fixed interval. The budget is not controlled uniformly through " ++
      "shrinking reflection punctures or exhaustion; no bound for the signed mass " ++
      "variation or new zero exclusion is proved. " ++
      "Retaining the cubic zero of U*S now cancels both reflection double poles: " ++
      "the exact current is globally real smooth, with node differential " ++
      "-B(node)/m^3 times conjugation independently of r. The full source, signed " ++
      "mass variation and complete remainder are locally integrable through both " ++
      "nodes. Their ordinary finite area identity has all Fubini and derivative " ++
      "hypotheses discharged. The two current edges obey the independent bound " ++
      "256*Im(alpha)^2/(r*R^2) for every nonnegative heat time and vanish with R. " ++
      "The remaining signed pair has an ordinary expanding-area limit equal to " ++
      "the original positive reflected source, with no puncture parameter. An " ++
      "independent upper bound for this pair remains open; local integrability " ++
      "does not make the earlier C/r budget uniform near a node. " ++
      "A single actual carrier chart now works for every smoothing parameter. " ++
      "The full remainder's leading local term is a second angular harmonic with " ++
      "coefficient 4*i*B(node)/m^3 and quadratic scale 1/m^2. A quarter-turn negates " ++
      "the full radial kernel, so its genuinely integrable centered-disk integral " ++
      "is exactly zero. Freezing the two smooth coefficients leaves a uniform " ++
      "C/abs(z-node) bound; the companion heat term obeys the same integrable " ++
      "bound. Dominated convergence proves signed remainder decay through the " ++
      "reflected node on every fixed eligible compact region and upper rectangle " ++
      "as smoothing grows. The entire source plus 4*i*r^2 times its signed mass " ++
      "variation therefore tends to zero on each fixed sufficiently wide upper " ++
      "rectangle after removing the current edges. This is not a bound on the " ++
      "mass variation, absolute remainder decay, or an interchange with the " ++
      "expanding-area limit; the independent source ceiling remains open. " ++
      "The retained signed mass variation itself now has smoothing limit " ++
      "2*pi*i*B(beta)/m on every fixed sufficiently wide upper rectangle. " ++
      "Its imaginary part is eventually above half of that positive source " ++
      "under the hypothetical right-half zero. The exact rescaled xi-field " ++
      "profile at beta+w/r is proportional to (1+conj(w)/w)/" ++
      "(1+normSq(w)/m^2)^3. The local coefficient derivative vanishes only " ++
      "after being retained in the exact chart. Perpendicular directions " ++
      "cancel the second angular harmonic but leave twice the constant " ++
      "component. Increasing smoothing alone therefore does not provide " ++
      "the required source deficit. No weak-measure convergence or exchange " ++
      "of this pointwise profile with an area integral is asserted. " ++
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
    ("globalPhaseBudget", Json.mkObj [
      ("identityTheorem", .str "RiemannGaussian.zetaPhase_primeWork_add_globalZeros_eq"),
      ("boundTheorem", .str
        "RiemannGaussian.phase_shifted_source_add_primeWork_le_global_split"),
      ("finiteWindowTheorem", .str
        "RiemannGaussian.phase_finite_primeWork_le_global_zero_defect"),
      ("analyticAllowance", .str "1+log(sigma+abs(t)) for sigma>=1"),
      ("familyScope", .str
        "Nonnegative summable coefficients with summable logarithmic height cost; integer families need only a summable logarithmic frequency moment. Finite and infinite support are included"),
      ("sourceScope", .str
        "Full analytic multiplicity of every nontrivial zero, for every positive shift from one. Exact global zero mass and signed Gamma correction remain available"),
      ("status", .str
        "Unconditional analytic budget improvement; the independent source-beating arithmetic lower bound remains open. No new explicit numerical zero region is asserted")
    ]),
    ("horizontalPhaseBudget", Json.mkObj [
      ("identityTheorem", .str
        "RiemannGaussian.zetaPhase_horizontal_primeWork_add_zeroMass_add_gamma_eq"),
      ("finiteWindowTheorem", .str
        "RiemannGaussian.zetaPhase_horizontal_finite_primeWork_add_zeroMass_add_gamma_le"),
      ("completionSignTheorem", .str
        "RiemannGaussian.strictMonoOn_re_zetaGlobalRegularCorrection"),
      ("negativeBackgroundTheorem", .str
        "RiemannGaussian.zetaHorizontalPoissonSummand_neg_of_far"),
      ("familyScope", .str
        "Nonnegative summable coefficients and arbitrary real frequencies; no logarithmic frequency moment. The whole signed zero sum is formed within each frequency block before summing the blocks"),
      ("analyticContribution", .str
        "The complete Gamma difference is retained as a nonnegative reserve on the left. The right side is the exact elementary pole difference"),
      ("status", .str
        "Unconditional paired identity and finite-window inequality. The signed zero background changes sign and cannot be discarded. No independent source-beating bound or new zero exclusion is proved")
    ]),
    ("stechkinPhaseBudget", Json.mkObj [
      ("identityTheorem", .str
        "RiemannGaussian.zetaPhase_stechkin_primeWork_add_zeroMass_eq"),
      ("boundTheorem", .str
        "RiemannGaussian.phase_shifted_source_add_primeWork_le_stechkin_split"),
      ("finiteWindowTheorem", .str
        "RiemannGaussian.zetaPhase_stechkin_source_add_finite_primeWork_le"),
      ("arithmeticTransferTheorem", .str
        "RiemannGaussian.zetaPhase_stechkin_primeWork_bounds"),
      ("pairSignTheorem", .str "RiemannGaussian.zetaStechkinPoissonSummand_nonneg"),
      ("coefficientTheorem", .str "RiemannGaussian.classical_le_zetaStechkinWeight"),
      ("analyticAllowance", .str
        "(1-c)*(1+log(sigma+abs(t))), c=sigma/sqrt(1+4*sigma^2)>=1/sqrt(5)"),
      ("familyScope", .str
        "All nonnegative summable phase families with summable logarithmic height cost; arbitrary real frequencies and finite or infinite support. Integer families may use a logarithmic frequency moment"),
      ("sourceScope", .str
        "Full analytic multiplicity of every selected right-half zero at every positive shift; its distinct critical reflection pays the full subtraction. Fixed points are counted once in the complete zero mass"),
      ("status", .str
        "Classical comparison formalized for the actual global identity. Analytic allowance reduced and previous arithmetic floors transfer with factor 1-c. Its three-height consequence now proves the explicit Stechkin edge region. The source-beating bound throughout the remaining right half-strip and RH remain open")
    ]),
    ("stechkinEulerBoundary", Json.mkObj [
      ("abelLimitTheorem", .str
        "RiemannGaussian.tendsto_zetaPhase_stechkin_primeWork_sub_pole_boundary"),
      ("identityTheorem", .str "RiemannGaussian.zetaPhase_stechkin_boundary_identity"),
      ("sourceTheorem", .str "RiemannGaussian.zetaPhase_stechkin_boundary_source_le"),
      ("dominationTheorem", .str
        "RiemannGaussian.exists_re_logDeriv_riemannZeta₁_euler_bound"),
      ("actualZeroBoundTheorem", .str
        "RiemannGaussian.tsum_zetaGlobalPoissonSummand_euler_le"),
      ("familyScope", .str
        "All nonnegative summable coefficient families with summable a(n)*log(1+abs(omega(n))); arbitrary real frequencies including zero and accumulation at zero. The family is fixed during each Abel limit"),
      ("sourceScope", .str
        "Full analytic multiplicity m/(1-Re(rho)) of a selected right-half zero at a frequency equal to one; all actual reflected zero blocks remain nonnegative"),
      ("retainedInformation", .str
        "Full complex pole-removed response and completion comparison, exact signed real identity, complete zero mass, multiplicity, and subtraction of the entire pole family before the limit"),
      ("status", .str
        "Boundary passage proved using the actual Stechkin reciprocal-logarithm zero-free margin. Complete mass and real derivative dominators are now 325 and 326 times log(abs(t)+26), for 1<=sigma<=3 and abs(t)>=5. Positivity of the unregularized prime work does not supply the required signed lower bound after pole subtraction")
    ]),
    ("stechkinZeroFree", Json.mkObj [
      ("stripTheorem", .str "RiemannGaussian.nontrivialZetaZero_mem_half_log_strip_all_heights"),
      ("nonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_half_log_margin_all_heights"),
      ("comparisonTheorem", .str "RiemannGaussian.zetaStechkinZeroMargin_lt_half_log"),
      ("widthRatioTheorem", .str "RiemannGaussian.zetaHalfLogZeroMargin_eq_mul_stechkin"),
      ("sourceTheorem", .str "RiemannGaussian.zetaThreePhase_half_log_source_add_primeWork_le"),
      ("completionTheorem", .str "RiemannGaussian.re_zetaGlobalRegularCorrection_le_half_log"),
      ("allFamilyTheorem", .str "RiemannGaussian.phase_shifted_source_add_primeWork_le_stechkin_half_log"),
      ("margin", .str "1/(24*log(abs(t)+22))"),
      ("heightDomain", .str "Every ordinate; actual nontrivial zeros satisfy t^2>3"),
      ("previousFullMargin", .str "1/(64*log(abs(t)+22))"),
      ("widthRatio", .str "8/3"),
      ("completionAllowance", .str "log(sigma+abs(t))/2 for sigma>=1, replacing 1+log(sigma+abs(t))"),
      ("familyScope", .str "All nonnegative summable families of real frequencies with the stated logarithmic height moment; normalized shifted form for all summable integer-frequency families with logarithmic moment"),
      ("arithmeticInput", .str
        "The exact classical square 3+4*cos(theta)+cos(2*theta)=2*(1+cos(theta))^2 makes the complete actual Stechkin prime work nonnegative; no coefficient search or unproved floor"),
      ("status", .str
        "Unconditional strict edge exclusion for literal zeta zeros at every height, with every analytic and arithmetic premise discharged. The exact excluded width is 8/3 times the preceding Stechkin width. The centered Euler eta argument discharges the former height-one premise. No claim of a best published region; higher interior zeros remain unexcluded and RH remains open")
    ]),
    ("phaseHalfLogZeroFree", Json.mkObj [
      ("stripTheorem", .str "RiemannGaussian.nontrivialZetaZero_mem_phase_half_log_strip"),
      ("nonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_phase_half_log_margin"),
      ("comparisonTheorem", .str "RiemannGaussian.zetaHalfLogZeroMargin_lt_phase"),
      ("widthRatioTheorem", .str "RiemannGaussian.zetaPhaseHalfLogZeroMargin_eq_twice"),
      ("sourceTheorem", .str "RiemannGaussian.phaseContactExact_half_log_source_add_primeWork_le"),
      ("budgetTheorem", .str "RiemannGaussian.phaseContactExact_half_log_zero_budget"),
      ("arithmeticFloorTheorem", .str "RiemannGaussian.phaseContactExact_stechkin_binomial_floor"),
      ("scaledSourceTheorem", .str "RiemannGaussian.phaseContactExact_half_log_scaled_zero_source"),
      ("allFamilyTheorem", .str "RiemannGaussian.phase_shifted_source_add_primeWork_le_stechkin_half_log"),
      ("margin", .str "1/(12*log(abs(t)+22))"),
      ("previousMargin", .str "1/(24*log(abs(t)+22))"),
      ("widthRatio", .str "2"),
      ("heightDomain", .str "Every ordinate; the actual eta zero equation gives t^2>3"),
      ("family", .str "The previously proved exact phase optimizer, with all nine coefficients unchanged; no coefficient search"),
      ("retainedInformation", .str "Exact phase source, excess analytic multiplicity, complete signed Stechkin prime work, full frequency costs, and the independent binomial prime-power reserve at its actual sampling scale"),
      ("status", .str "Unconditional wider exclusion for literal zeta zeros, with every arithmetic and analytic premise discharged. This doubles the preceding edge width at every height. The interior signed prime-band inequality and the global RH objective remain open; no best published region is claimed")
    ]),
    ("completionReserveZeroFree", Json.mkObj [
      ("completionTheorem", .str "RiemannGaussian.re_zetaGlobalRegularCorrection_add_log_two_le_half_log"),
      ("allFamilyTheorem", .str "RiemannGaussian.phase_shifted_source_add_primeWork_add_completionReserve_le"),
      ("completeZeroMassTheorem", .str "RiemannGaussian.zetaPhase_stechkin_primeWork_add_zeroMass_add_completionReserve_le"),
      ("budgetTheorem", .str "RiemannGaussian.phaseContactExact_completionReserve_zero_budget"),
      ("allowanceTheorem", .str "RiemannGaussian.zetaCompletionReserve_allowance_le"),
      ("strictGapTheorem", .str "RiemannGaussian.zetaCompletionReserve_allowance_add_gap_le"),
      ("stripTheorem", .str "RiemannGaussian.nontrivialZetaZero_mem_completionReserve_strip"),
      ("nonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_completionReserve_margin"),
      ("comparisonTheorem", .str "RiemannGaussian.six_fifths_phaseHalfLog_margin_lt_completionReserve"),
      ("margin", .str "1/(10*log(abs(t)+2))"),
      ("previousMargin", .str "1/(12*log(abs(t)+22))"),
      ("widthRatio", .str "Strictly greater than 6/5 at every real ordinate"),
      ("heightDomain", .str "Every ordinate; the proved eta constraint t^2>3 implies log(abs(t)+2)>6/5 at actual nontrivial zeros"),
      ("completionReserve", .str "(1-c)*log(2)/2 times total coefficient mass; the actual signed completion, full zero sum, and prime work are retained before the bound"),
      ("familyScope", .str "All nonnegative summable real-frequency families with the stated logarithmic height moment; shifted form for all admissible integer-frequency families"),
      ("instantiation", .str "The existing exact phase optimizer, with unchanged coefficients and independently proved nonnegative prime work; no coefficient search"),
      ("source", .str "11/625"),
      ("allowance", .str "At most (61/360)*d*L-(79/172800)*d, hence at most 61/3600 when d*L<=1/10"),
      ("strictSourceGap", .str "59/90000 after all completion and quadratic pole costs"),
      ("status", .str "Unconditional wider exclusion for literal zeta zeros, with every arithmetic and analytic premise discharged in the new edge region. The independent signed bound for the remaining right-half zeros and the full RH objective remain open; no best published region is claimed")
    ]),
    ("squarefreeSignedSource", Json.mkObj [
      ("variableRadiusTheorem", .str "RiemannGaussian.exists_zetaEntireMultiplier_radius_filter_bound"),
      ("prefixIdentityTheorem", .str "RiemannGaussian.zetaMoebiusLogTailCoefficient_eq_vonMangoldt_add_prefix"),
      ("prefixSeriesTheorem", .str "RiemannGaussian.hasSum_zetaDivisibilityPrefixFilter"),
      ("factorWeightTheorem", .str "RiemannGaussian.exists_zetaDivisibilityPrefixFilter_expWeight_bound"),
      ("intersectionTheorem", .str "RiemannGaussian.primeSquareIntersection_dvd_iff"),
      ("sharedPrimeWeightTheorem", .str "RiemannGaussian.zetaPrimeExpWeight_primeSquareIntersection"),
      ("squareSummabilityTheorem", .str "RiemannGaussian.summable_primeSquareWeight"),
      ("squareOverlapTheorem", .str "RiemannGaussian.sum_primeSquareIntersection_weight_le"),
      ("primeOverlapTheorem", .str "RiemannGaussian.prod_one_add_primeSquareCorrectedWeight_le"),
      ("exactMaskTheorem", .str "RiemannGaussian.primeSquareSurvivorMask_mul_eq"),
      ("exactTransformTheorem", .str "RiemannGaussian.primeSquareSurvivorTransform_indicator"),
      ("completeSeriesTheorem", .str "RiemannGaussian.hasSum_primeSquareSurvivorTransform"),
      ("uniformOverlapTheorem", .str "RiemannGaussian.norm_primeSquareSurvivorTransform_le"),
      ("actualPrefixTheorem", .str "RiemannGaussian.hasSum_zetaPrimeSquarePrefixFilter"),
      ("leakageIdentityTheorem", .str "RiemannGaussian.zetaPrimeSquareCoefficient_eq_prefix_add_leakage"),
      ("leakageBoundTheorem", .str "RiemannGaussian.norm_zetaPrimeSquareLeakageCoefficient_le"),
      ("finiteSquareBoundTheorem", .str "RiemannGaussian.exists_zetaPrimeSquareFilter_bound"),
      ("infiniteSquareLimitTheorem", .str "RiemannGaussian.tendsto_zetaPrimeSquareFilter"),
      ("infiniteSquareBoundTheorem", .str "RiemannGaussian.exists_zetaNonsquarefreeFilter_bound"),
      ("exactSeriesSplitTheorem", .str "RiemannGaussian.zetaMoebiusSievedPrimeFilter_eq_squarefree_add_nonsquarefree"),
      ("actualRadiusTheorem", .str "RiemannGaussian.zetaRightHalfSquareSieveRadius_bounds"),
      ("strictRateTheorem", .str "RiemannGaussian.zetaRightHalfSquareSieveRate_bounds"),
      ("actualCutoffCostTheorem", .str "RiemannGaussian.exp_primePatternCutoff_sqrt_le"),
      ("normalizedDeletionBoundTheorem", .str "RiemannGaussian.exists_zetaRightHalfNonsquarefree_error_bound"),
      ("normalizedDeletionDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfNonsquarefreeFilter"),
      ("fullSquarefreeSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfSquarefreeFilter"),
      ("arithmeticErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfSquarefreeFilter_error_bound"),
      ("unchangedSurvivorCoefficientTheorem", .str "RiemannGaussian.zetaRightHalfSquarefreeWindowCoefficient_eq"),
      ("survivorSupportTheorem", .str "RiemannGaussian.zetaRightHalfSquarefreeWindowCoefficient_support"),
      ("complexSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfSquarefreeWindowFourierCarrier"),
      ("signedSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfSquarefreeWindowReflectionWork"),
      ("reflectionIdentityTheorem", .str "RiemannGaussian.zetaRightHalfSquarefreeWindowFourierCarrier_re_eq_reflection"),
      ("finiteErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfSquarefreeWindowReflection_error_bound"),
      ("totalErrorDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfSquarefreeWindowTotalError"),
      ("familyScope", .str "Every finite first-power prime family through R, arbitrary finite square families with unrestricted overlaps, every divisor cutoff D>=1, polynomial filter and moment order, and abs(y)>1. Dominated convergence then includes every prime square in the full actual infinite arithmetic series"),
      ("radiusAndWeight", .str "Any 0<r<1 gives sigma=3/2-r, tau=1-r/2>1/2, delta=(1-r)/2>0 and w(P)=exp(-tau*log(P)); the moment cost is r^(-N), retaining the exact weighted polynomial norm"),
      ("exactIntersection", .str "P(W,V)=prod(W\\V)*prod(V)^2; its divisibility condition is exactly prod(W)|n and prod(V)^2|n, including all shared primes"),
      ("fullOverlapCost", .str "M=sum_{n>=0}w(n)^2 is summable. Shared primes contribute b(p)=w(p)*(1+w(p)); all square intersections cost at most exp(M)*prod_{p in W}b(p), uniformly over every square family. The entire signed transform costs at most 2*(1+exp(M))*exp(2*M)*exp(4*sqrt(R))"),
      ("actualSeriesBound", .str "The literal repeated-prime response, including its prime-power correction, has norm at most C(y,r)*D*exp(4*sqrt(R))*r^(-N)*sum_k(norm(p_k)*r^(-k)), uniformly over all square families and in the proved all-prime-square limit"),
      ("actualCutoff", .str "The quadratic prime sieve is retained: u=3/2-Re(rho), q=u^(-1/4), D_N=floor(q^N), R_N=floor(N*log(q)/8)^2, selecting every prime through R_N"),
      ("actualRate", .str "r=(1+sqrt(u))/2 and lambda=sqrt(u)/r=2*sqrt(u)/(1+sqrt(u)), with 0<lambda<1. The whole normalized nonsquarefree response is bounded by C(rho)*lambda^N tending to zero"),
      ("survivor", .str "Exactly the previous surviving coefficients on squarefree integers, and zero elsewhere. Every nonzero window index satisfies 2*N/5<=log(n)<=8*N, n>D_N^2, at least two distinct primes, and at most one prime through R_N"),
      ("source", .str "Re(C_N)=-2*W_N exactly, u^(N+1)*C_N tends to -m_rho, and u^(N+1)*W_N tends to m_rho/2; the full analytic multiplicity is retained"),
      ("completeAllowance", .str "(C1*(1+N^4)*(sqrt(u))^N+C2*lambda^N+zetaAveragedWindowError(p,N,y))/2 tends to zero, including original head, prime powers, the quadratic prime union, every square overlap, physical shells, and complementary centered Fourier interactions"),
      ("informationRetained", .str "Exact signed masks, all shared-prime corrections and factors, original full arithmetic series, squarefree coefficients, physical phases, centered complex Fourier products, odd reflection and analytic multiplicity precede companion bounds"),
      ("remainingObligation", .str "One independent strict upper bound below m_rho/2 for the whole normalized squarefree signed correlation at arbitrarily late orders for every hypothetical right-half zero"),
      ("status", .str "Every nonsquarefree contribution is independently controlled and the complete signed source remains squarefree, with all errors discharged. The strict surviving arithmetic bound is open. No additional zeta zeros are excluded; the all-height edge strip is unchanged and RH remains open")
    ]),
    ("quadraticPrimeSieve", Json.mkObj [
      ("exactPatternTheorem", .str "RiemannGaussian.primePairSieve_eq_signed_patterns"),
      ("originalSieveTheorem", .str "RiemannGaussian.zetaMoebiusPrimePatternFilter_eq_sieve"),
      ("completeSeriesTheorem", .str "RiemannGaussian.hasSum_zetaMoebiusPrimePatternFilter"),
      ("overlapCostTheorem", .str "RiemannGaussian.sum_prime_pattern_lcm_cost_le"),
      ("cutoffCostTheorem", .str "RiemannGaussian.primePatternSieveCost_le_exp_sqrt"),
      ("actualUnionBoundTheorem", .str "RiemannGaussian.exists_zetaMoebiusPrimePatternFilter_cutoff_bound"),
      ("actualCostTheorem", .str "RiemannGaussian.primePatternSieveCost_actual_le"),
      ("cofinalCutoffTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfPrimePatternCutoff"),
      ("normalizedBoundTheorem", .str "RiemannGaussian.exists_zetaRightHalfPrimePattern_error_bound"),
      ("actualDeletionDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfPrimePatternFilter"),
      ("survivorSupportTheorem", .str "RiemannGaussian.zetaRightHalfQuadraticWindowCoefficient_support"),
      ("complexSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfQuadraticWindowFourierCarrier"),
      ("signedSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfQuadraticWindowReflectionWork"),
      ("reflectionIdentityTheorem", .str "RiemannGaussian.zetaRightHalfQuadraticWindowFourierCarrier_re_eq_reflection"),
      ("finiteErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfQuadraticWindowReflection_error_bound"),
      ("totalErrorDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfQuadraticWindowTotalError"),
      ("familyScope", .str "Every finite set of selected primes, every polynomial filter and moment order, every divisor cutoff, and each fixed ordinate with abs(y)>1; each full arithmetic series includes all multiples and valuations"),
      ("exactIdentity", .str "1_{count(selected primes dividing n)>=2}*F(n)=sum_{T subset S,card(T)>=2}sum_{U subset S\\T}(-1)^card(U)*1_{prod(T union U)|n}*F(n), for every complex F and every n"),
      ("weightedCost", .str "B(S)=(1+sum_{p in S}log(p))*prod_{p in S}(1+2*A(p)); all signed-pattern intersection costs sum to at most B(S), with A(P)=P^(-1/2)*sum_{g|P}g^(-1/2)"),
      ("cutoffCost", .str "B(S)<=(1+R^2)*exp(8*sqrt(R)) whenever all selected primes are at most R"),
      ("actualCutoff", .str "u=3/2-Re(rho), q=u^(-1/4), c=log(q)/8, D_N=floor(q^N), R_N=floor(c*N)^2; every prime through R_N is selected and R_N tends to infinity"),
      ("actualOverlapBudget", .str "B(S_N)<=(1+c^4*N^4)*q^N; this is proved for the complete actual union, with no remaining coefficient-mass premise"),
      ("normalizedDeletionBound", .str "The whole union response has bound C(rho)*(1+N^4)*(sqrt(u))^N tending to zero"),
      ("survivor", .str "2*N/5<=log(n)<=8*N, n>D_N^2, at least two distinct prime divisors overall, and at most one prime divisor among all primes through R_N"),
      ("completeAllowance", .str "(C*(1+N^4)*(sqrt(u))^N+zetaAveragedWindowError(p,N,y))/2 tends to zero; original head, prime powers, every prime-pattern overlap, both physical shells, and full complementary Fourier interaction are included"),
      ("informationRetained", .str "Exact signed divisibility patterns and all intersection factors, full convergent arithmetic series, original coefficient masks, centered complex Fourier products, odd reflection work and full analytic multiplicity are connected before companion norm estimates"),
      ("limitation", .str "The proved overlap budget controls the deleted union, not the whole remaining collection. The prime cutoff grows quadratically with N while the physical indices grow exponentially"),
      ("status", .str "A complete independently controlled simultaneous deletion with every error discharged and full signed source preserved. Its remaining strict arithmetic upper bound is open. No additional zeta zeros are excluded, the all-height edge margin is unchanged, and RH remains open")
    ]),
    ("lcmWindowFactorBound", Json.mkObj [
      ("exactPhaseTheorem", .str "RiemannGaussian.zetaPrimeFeature_lcm_mul_gcd"),
      ("offsetTheorem", .str "RiemannGaussian.zetaMultipleLogOffset_eq_log_factor_sub_gcd"),
      ("jointMassTheorem", .str "RiemannGaussian.sum_Icc_inv_sqrt_lcm_le"),
      ("divisorPairingTheorem", .str "RiemannGaussian.sum_divisors_inv_sqrt_le_four_mul_fourthRoot"),
      ("factorDecayTheorem", .str "RiemannGaussian.lcmSqrtFactorMass_le_four_div_fourthRoot"),
      ("largeFactorMassTheorem", .str "RiemannGaussian.sqrt_mul_lcmSqrtFactorMass_le_four"),
      ("multiplierTheorem", .str "RiemannGaussian.norm_zetaMoebiusMultipleMultipliers_le_lcm"),
      ("allFamilyBoundTheorem", .str "RiemannGaussian.exists_zetaMoebiusMultipleFamily_lcm_bound"),
      ("largeFactorResponseTheorem", .str "RiemannGaussian.exists_zetaMoebiusMultipleFilter_large_factor_bound"),
      ("actualWindowFamilyTheorem", .str "RiemannGaussian.exists_zetaRightHalfWindowFactorFamily_bound"),
      ("enlargedBudgetTheorem", .str "RiemannGaussian.exists_zetaRightHalfWindowFactorFamily_budget_bound"),
      ("allowanceDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfWindowFactorAllowance"),
      ("actualFamilyDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfWindowFactorFamily"),
      ("factorMass", .str "A(P)=P^(-1/2)*sum_{g|P}g^(-1/2), with exact multiplicativity on coprime products and A(P)<=4*P^(-1/4) for every positive P"),
      ("jointEstimate", .str "sum_{1<=d<=D}lcm(d,P)^(-1/2)<=2*sqrt(D)*A(P); sqrt(D)*A(P)<=4 whenever D^2<=P"),
      ("weightedCost", .str "kappa(P)=min(3,(1+log(P))*A(P)); the genuine all-factor-family bound is C(y)*sqrt(D)*norm(p)_1*sum(norm(w(P))*kappa(P))"),
      ("familyScope", .str "Every finite complex family of positive mixed-prime factors, with arbitrary prime support, valuations and overlaps. In the actual logarithmic window, the bound becomes C(rho)*(1+8N)*sum(norm(w(P)))"),
      ("enlargedBudget", .str "For factors in 2*N/5<=log(P)<=8*N, total coefficient mass at most D_N^3*sqrt(D_N) has normalized bound C*(1+8N)*(u^(1/8))^N, which tends to zero"),
      ("arithmeticScope", .str "Each factor response is the full convergent signed Moebius-tail series over all of its multiples, including the logarithmic companion. It is not a singleton physical coefficient"),
      ("informationRetained", .str "Exact complex gcd/lcm phase identity, full logarithmic offset, common-divisor quotient cutoffs, all surviving signed arithmetic terms and arbitrary complex family weights remain available before companion norm bounds"),
      ("limitation", .str "The estimate does not identify or bound the whole surviving union. An exact collective representation and a proved affordable overlap budget, or direct signed cancellation, are still needed"),
      ("status", .str "Stronger independent arithmetic control of the actual large-factor building blocks; the existing full signed Fourier source is unchanged. No additional zeta zeros are excluded, the all-height edge margin is unchanged, and RH remains open")
    ]),
    ("averagedSymbolWindow", Json.mkObj [
      ("symbolMassTheorem", .str "RiemannGaussian.sum_inv_sq_cyclicDifferenceSymbol_le"),
      ("centeredBoundTheorem", .str "RiemannGaussian.norm_centeredFourierPart_le_averaged_gap"),
      ("arithmeticMassTheorem", .str "RiemannGaussian.sum_norm_zetaArithmeticWindowSamples_le"),
      ("generalRateTheorem", .str "RiemannGaussian.tendsto_zetaArithmeticWindowCenteredPart_compl"),
      ("regionInclusionTheorem", .str "RiemannGaussian.zetaAveragedResonantModes_subset"),
      ("exactRatesTheorem", .str "RiemannGaussian.zetaQuarterAveragedGapError_six_sevenths_eq"),
      ("allFamilyBoundTheorem", .str "RiemannGaussian.norm_zetaArithmeticFilter_sub_averaged_window_le"),
      ("allFamilyDecayTheorem", .str "RiemannGaussian.tendsto_zetaArithmeticFilter_sub_averaged_window"),
      ("complexSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfAveragedWindowFourierCarrier"),
      ("signedSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfAveragedWindowReflectionWork"),
      ("reflectionIdentityTheorem", .str "RiemannGaussian.zetaRightHalfAveragedWindowFourierCarrier_re_eq_reflection"),
      ("finiteErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfAveragedWindowReflection_error_bound"),
      ("totalErrorDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfAveragedWindowTotalError"),
      ("generalEstimate", .str "For every positive cyclic modulus and every frequency set with symbol norm at least delta>0, the normalized inverse-square symbol mass is at most 2/delta; the whole centered interaction is at most (4/delta)*norm(a)_1*norm(Delta^2 f)_1"),
      ("familyScope", .str "All moving complex coefficient families dominated by the actual divisor-log majorant, with arbitrary moment order, fixed polynomial filter and ordinate; no coefficient search or cancellation hypothesis"),
      ("arithmeticMass", .str "The window 2*N/5<=log(n)<=8*N has weighted coefficient mass at most (20/21)^N times the summable majorant mass at 9/8"),
      ("rateCriterion", .str "r>160/189; a shrinking concrete choice is r=6/7. This is a sufficient condition, with no optimality claim"),
      ("threshold", .str "(6/7)^N, contained in the previous (14/15)^N symbol region"),
      ("frequencyErrorRates", .str "(80/81)^N for the complete interior second difference and (5/9)^N for the cyclic boundary, including both centering terms"),
      ("completeAllowance", .str "(C1*(sqrt(u))^N+C2*(u^(1/8))^N+zetaAveragedWindowError(p,N,y))/2 tends to zero, with the original head, prime powers, cubic sieve overlaps, both physical shells, and whole complementary Fourier interaction included"),
      ("informationRetained", .str "Actual symbol density is kept until its summed estimate; the unchanged cubic-sieved window coefficients, divisor/cofactor separation, full centered Fourier products, reflection partners, signs, phases and analytic multiplicity survive together"),
      ("status", .str "A smaller frequency region contains the complete hypothetical-zero source. Its independent signed upper bound remains open; localization alone does not control the retained arithmetic correlation. No additional zeta zeros are excluded, the all-height edge margin is unchanged, and RH remains open")
    ]),
    ("moebiusScaleSieve", Json.mkObj [
      ("scaleIdentityTheorem", .str "RiemannGaussian.zetaPrimeFeature_lcm_eq_offset"),
      ("divisorWeightTheorem", .str "RiemannGaussian.norm_zetaPrimeFeature_le_inv_sqrt"),
      ("offsetBoundTheorem", .str "RiemannGaussian.norm_zetaPrimeFeature_lcm_mul_offset_le"),
      ("prefixTheorem", .str "RiemannGaussian.sum_inv_sqrt_Icc_le"),
      ("multiplierTheorem", .str "RiemannGaussian.norm_zetaMoebiusMultipleMultipliers_le_sqrt"),
      ("allFamilyBoundTheorem", .str "RiemannGaussian.exists_zetaMoebiusMultipleFamily_sqrt_bound"),
      ("cubicFamilyTheorem", .str "RiemannGaussian.exists_zetaRightHalfMoebiusMultipleFamily_cubic_bound"),
      ("cubicSieveTheorem", .str "RiemannGaussian.exists_zetaRightHalfMoebiusSieve_cubic_bound"),
      ("exactRateTheorem", .str "RiemannGaussian.zetaMoebiusHeadGrowth_sqrt_cubic_rate"),
      ("actualBudgetTheorem", .str "RiemannGaussian.zetaRightHalfCubicSieve_budget"),
      ("thresholdTheorem", .str "RiemannGaussian.three_mul_natLog_le_natLog_cube"),
      ("actualSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfCubicSievedPrimeTail"),
      ("supportTheorem", .str "RiemannGaussian.zetaRightHalfCubicWindowCoefficient_support"),
      ("windowSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfCubicWindowFourierCarrier"),
      ("signedSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfCubicWindowReflectionWork"),
      ("finiteErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfCubicWindowReflection_error_bound"),
      ("totalErrorDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfCubicWindowTotalError"),
      ("multiplierBounds", .str "2*sqrt(D) and 4*sqrt(D) for the two actual entire multipliers on Re(s)>=1/2, uniformly over every positive factor"),
      ("familyScope", .str "All finite complex factor families, with arbitrary factor sizes, valuations and overlaps; actual arithmetic series require positive mixed-prime factors. The full bound is C(y)*sqrt(D)*norm(p)_1*sum(norm(w(P)))"),
      ("cubicBudget", .str "At the unchanged cutoff D_N=floor(q^N), q=u^(-1/4), every coefficient mass at most D_N^3 has independently decaying normalized bound C*(u^(1/8))^N"),
      ("actualThreshold", .str "Nat.log 2 (D_N^3), at least 3*Nat.log 2 D_N with integer rounding retained. Every eligible mixed-prime factor below it belongs to the explicit sieve"),
      ("retainedSupport", .str "2*N/5<=log(n)<=8*N and D_N^2<n, at least two distinct prime factors, and every distinct prime-pair product at least the enlarged threshold"),
      ("completeAllowance", .str "(C1*(sqrt(u))^N+C2*(u^(1/8))^N+zetaLogWindowFourierError(p,N,y))/2 tends to zero; the original head, prime powers, all sieve overlaps, both physical shells, and complementary Fourier products are included"),
      ("informationRetained", .str "Exact divisor/offset complex factorization, the actual signed multiple-sector multipliers, all grouped overlap coefficients before their norms, and the full surviving centered Fourier and cyclic odd-reflection correlation"),
      ("status", .str "A stronger independent arithmetic bound supports a larger actual deletion. The full multiplicity source survives and its strict signed upper bound is open. The sieve threshold still grows only linearly with N while the physical index grows exponentially. No additional zeta zeros are excluded; the all-height edge margin is unchanged and RH remains open")
    ]),
    ("sievedLogWindow", Json.mkObj [
      ("generalTiltTheorem", .str "RiemannGaussian.norm_zetaPrimeLogKernel_le_tilt"),
      ("lowerRateTheorem", .str "RiemannGaussian.norm_zetaPrimeLogKernel_le_lower_chernoff"),
      ("upperRateTheorem", .str "RiemannGaussian.norm_zetaPrimeLogKernel_le_upper_chernoff"),
      ("allFamilyBoundTheorem", .str "RiemannGaussian.norm_zetaArithmeticFilter_sub_window_le"),
      ("allFamilyDecayTheorem", .str "RiemannGaussian.tendsto_zetaArithmeticFilter_sub_window"),
      ("finiteSupportTheorem", .str "RiemannGaussian.zetaLogWindow_subset_band"),
      ("cutoffSquareTheorem", .str "RiemannGaussian.zetaLogWindow_gt_moebiusCutoff_sq"),
      ("factorSeparationTheorem", .str "RiemannGaussian.zetaLogWindow_quotient_gt_moebiusCutoff"),
      ("signedHeadTheorem", .str "RiemannGaussian.zetaRightHalfWindowCoefficient_eq_neg_prefix"),
      ("physicalIdentityTheorem", .str "RiemannGaussian.zetaRightHalfWindowFourierCarrier_eq_physical"),
      ("complexSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfWindowFourierCarrier"),
      ("signedSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfWindowReflectionWork"),
      ("finiteErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfWindowReflection_error_bound"),
      ("totalErrorDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfWindowTotalError"),
      ("window", .str "2*N/5<=log(n)<=8*N"),
      ("previousBand", .str "N*log(2)/4<log(n)<=32*N*log(2)"),
      ("divisorSeparation", .str "At every positive order each retained product exceeds the square of the unchanged moving cutoff. The exact negative finite-head coefficient pairs every divisor d<=D with a cofactor n/d>D; all signs and full product weights remain available"),
      ("referenceMass", .str "The genuine summable divisor-logarithm majorant at real abscissa 17/16"),
      ("shellRates", .str "(15/16)^N and (3/4)^N, including the complete polynomial offset factors (1/2)^k and 8^k"),
      ("generalRate", .str "endpoint*exp(1-(Re(s)-tau)*endpoint), with positive endpoint and the appropriate lower/upper tilt direction"),
      ("familyScope", .str "Every complex coefficient family bounded by the original divisor majorant, including arbitrarily moving cutoffs and sieves; a fixed polynomial filter and ordinate in each limit"),
      ("retainedInformation", .str "All signed coefficients inside the window, complete pole-jet polynomial, original cofinal sieve, every centered Fourier product, full multiplicity, and the exact cyclic odd-reflection profile"),
      ("status", .str "Independent decay of all discarded physical shells and complementary Fourier products, with full source preserved on smaller finite support. Slower geometric shell rates still suffice because the whole allowance vanishes. The strict signed bound within this window is open; the uniform zero-free margin is unchanged and RH remains open")
    ]),
    ("stechkinSupportFloor", Json.mkObj [
      ("exactWeightTheorem", .str "RiemannGaussian.zetaStechkinPrimeWeight_eq_supportFactor"),
      ("allFamilyTheorem", .str "RiemannGaussian.zetaPhase_stechkin_primeWork_ge_supportFactor"),
      ("improvementTheorem", .str "RiemannGaussian.six_fifths_weight_gap_le_zetaStechkinSupportFactor"),
      ("fullEnergyTheorem", .str "RiemannGaussian.zetaPhase_stechkin_binomial_energy_support_floor"),
      ("energyCeilingTheorem", .str "RiemannGaussian.zetaPhase_binomial_energy_le_mass"),
      ("phaseMaximumTheorem", .str "RiemannGaussian.phaseContactExactSupportEnergy_le_at_zero"),
      ("floorTheorem", .str "RiemannGaussian.phaseContactExact_stechkin_one_sixtieth_floor"),
      ("fullSourceTheorem", .str "RiemannGaussian.zetaPhase_source_add_supportEnergy_add_completionReserve_le"),
      ("finiteEnergyTheorem", .str "RiemannGaussian.phaseContactExactSupportEnergy_eq"),
      ("zeroBudgetTheorem", .str "RiemannGaussian.phaseContactExact_completionReserve_support_energy_zero_budget"),
      ("uniformSourceTheorem", .str "RiemannGaussian.phaseContactExact_completionReserve_support_floor_zero_budget"),
      ("nonvanishingTestTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_completion_support_energy"),
      ("supportFactor", .str "1-c*exp(-(tau-sigma)*log(2)); strictly larger than 1-c for every sigma>=1"),
      ("quantitativeImprovement", .str "At least 2/3 and at least (6/5)*(1-c) for 1<=sigma<=5/4"),
      ("actualFloor", .str "exp(-4*(sigma-1)*log(2))/60 for the actual Stechkin prime work, 1<sigma<=5/4"),
      ("energyCeiling", .str "For every degree N, centered energy is at most (4^N-choose(2*N,N))*total mass, uniformly over all real frequencies and all phases. The exact family's support energy is largest at zero phase"),
      ("familyScope", .str "All nonnegative summable coefficient families with arbitrary real frequencies and nonnegative phase kernels; source budget also requires the genuine logarithmic height moment"),
      ("retainedInformation", .str "Exact support-dependent weight ratio before monotonicity; full mixed binomial energy before its uniform lower bound; selected analytic multiplicity, negative completion reserve, and signed auxiliary pole subtraction in the all-family source theorem"),
      ("instantiation", .str "The existing exact phase optimizer, with unchanged coefficients; its finite energy is an explicit function of the sampling line and all linked phases"),
      ("status", .str "Stronger unconditional arithmetic floor and necessary zero inequality. Strict violation of the explicit finite energy budget proves literal zeta nonvanishing, but that test is not proved throughout the right half-strip. The fixed-degree reserve has a uniform mass-normalized ceiling; this is not an upper bound on the complete prime work. The uniform margin remains 1/(10*log(abs(t)+2)); RH remains open")
    ]),
    ("centeredEulerZeroFree", Json.mkObj [
      ("identityTheorem", .str "RiemannGaussian.pairedEtaCore_eq_centered_euler"),
      ("errorTheorem", .str "RiemannGaussian.norm_pairedEtaCore_sub_centered_euler_le"),
      ("tailIdentityTheorem", .str "RiemannGaussian.pairedEtaCore_tail_eq_centered_euler"),
      ("tailErrorTheorem", .str "RiemannGaussian.norm_pairedEtaCore_tail_sub_centered_euler_le"),
      ("polynomialExclusionTheorem", .str "RiemannGaussian.pairedEtaCore_ne_zero_of_centered_euler"),
      ("zeroConstraintTheorem", .str "RiemannGaussian.nontrivialZetaZero_centered_euler_constraint"),
      ("heightTheorem", .str "RiemannGaussian.nontrivialZetaZero_im_sq_gt_three"),
      ("nonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_im_sq_le_three"),
      ("error", .str "norm(eta(s)-(1/2+s/4)) <= norm(s)*norm(s+1)/(4*(Re(s)+1)), Re(s)>0"),
      ("etaZeroFreeRegion", .str "Re(s)>0 and Im(s)^4+Re(s)^2*Im(s)^2 < 4*(Re(s)+1)^3"),
      ("zetaHeightExclusion", .str "Every actual nontrivial zero satisfies Im(rho)^2>3"),
      ("informationPreserved", .str "Both complex endpoint powers, opposite triangular-kernel orientations, absolute convergence, and an exact remainder at every cutoff"),
      ("status", .str "Unconditional analytic low-height exclusion and removal of the edge theorem's height restriction; no numerical certificate or coefficient search. The norm remainder grows quadratically at large height and does not exclude the remaining interior zeros. RH remains open")
    ]),
    ("etaUniformTail", Json.mkObj [
      ("ratioTheorem", .str "RiemannGaussian.cpow_add_one_eq_pairedEtaAdjacentRatio_mul"),
      ("variationTheorem", .str "RiemannGaussian.norm_pairedEtaAdjacentInverse_sub_le"),
      ("finiteIdentityTheorem", .str "RiemannGaussian.pairedEtaCorePartialSum_sub_eq_adjacent"),
      ("tailIdentityTheorem", .str "RiemannGaussian.pairedEtaCore_tail_eq_adjacent"),
      ("tailBoundTheorem", .str "RiemannGaussian.norm_pairedEtaCore_tail_le_two"),
      ("zeroConstraintTheorem", .str "RiemannGaussian.norm_pairedEtaCorePartialSum_zero_le_two"),
      ("normalizedMultiplierTheorem", .str "RiemannGaussian.norm_pairedEtaCoreNormalizedTail_sub_adjacent_le"),
      ("normalizedErrorTheorem", .str "RiemannGaussian.norm_pairedEtaCoreNormalizedTail_sub_half_le_scale"),
      ("movingArgumentTheorem", .str "RiemannGaussian.tendsto_pairedEtaCoreNormalizedTail_of_norm_div_endpoint_zero"),
      ("domain", .str "Re(s)>0 and odd cutoff X=2*N+1>=norm(s)"),
      ("tailBound", .str "norm(eta(s)-eta_N(s)) <= 2*X^(-Re(s))"),
      ("normalizedError", .str "norm(X^s*(eta(s)-eta_N(s))-1/2) <= 3*norm(s)/(2*X)"),
      ("previousNormalizedError", .str "norm(s)*norm(s+1)/X"),
      ("movingArguments", .str "For arbitrary filters, eventually positive real parts and norm(s)/X tending to zero imply the normalized tail tends to 1/2; heights may be unbounded and real parts may approach zero"),
      ("informationPreserved", .str "Exact complex ratio q=exp(-s*log((x+1)/x)), inverse multiplier 1/(1+q), both boundary phases, all three neighboring phases in each signed remainder, and proved absolute convergence"),
      ("status", .str "Unconditional analytic error improvement for the actual eta carrier at unbounded heights. The required independent signed arithmetic prefix bound remains open. No additional interior zero exclusion or RH proof is claimed")
    ]),
    ("etaReflectedAdjacent", Json.mkObj [
      ("denominatorTheorem", .str "RiemannGaussian.one_add_pairedEtaAdjacentRatio_ne_zero"),
      ("reflectionIdentityTheorem", .str "RiemannGaussian.pairedEtaAdjacentRatio_mul_conj_reflected"),
      ("inverseIdentityTheorem", .str "RiemannGaussian.pairedEtaAdjacentInverse_reflected_sum"),
      ("radialContrastTheorem", .str "RiemannGaussian.eta_complementary_exp_contrast_le"),
      ("sectorTheorem", .str "RiemannGaussian.pairedEtaReflectedAdjacentProduct_sector"),
      ("normTheorem", .str "RiemannGaussian.pairedEtaReflectedAdjacentProduct_norm_le_re"),
      ("oddChannelTheorem", .str "RiemannGaussian.pairedEtaReflectedAdjacentProduct_im_sq_le"),
      ("finiteFamilyTheorem", .str "RiemannGaussian.sum_pairedEtaReflectedAdjacentProduct_norm_le_re"),
      ("infiniteFamilyTheorem", .str "RiemannGaussian.tsum_pairedEtaReflectedAdjacentProduct_norm_le_re"),
      ("allCutoffIdentityTheorem", .str "RiemannGaussian.pairedEtaCore_tail_eq_adjacent_of_re_pos"),
      ("completedMomentTheorem", .str "RiemannGaussian.pairedEtaFiniteCompletedMoment_zero_eq_adjacent"),
      ("completedPairTheorem", .str "RiemannGaussian.pairedEtaFiniteCompletedMomentPair_zero_eq_adjacent"),
      ("completedErrorTheorem", .str "RiemannGaussian.norm_pairedEtaFiniteCompletedMoment_zero_add_adjacent_le"),
      ("domain", .str "0<Re(s)<1 and every positive real x, with unrestricted height and no x>=norm(s) assumption for the sector"),
      ("mixedProduct", .str "P=g(s,x)*conj(g(1-conj(s),x)), g(s,x)=1/(1+exp(-s*log((x+1)/x)))"),
      ("bound", .str "Re(P)>0 and 2*sqrt(Re(s)*(1-Re(s)))*norm(P)<=Re(P)"),
      ("familyScope", .str "All nonnegative finite families and all families with summable weighted mixed magnitudes; the bound controls the sum of individual magnitudes before summing the complex terms"),
      ("identityDomain", .str "Re(s)>0, every natural cutoff; the signed adjacent variation series is absolutely convergent"),
      ("informationPreserved", .str "Exact reflected ratio product, full mixed inverse and odd channel, actual power endpoints, all signed variations, and the original completed zeroth moments and signed pair"),
      ("status", .str "Unconditional sector estimate and exact all-cutoff summation for the actual eta endpoints. The mixed-product estimate does not bound the signed difference of completed channel energies or the full finite-range variation. The independent source-beating arithmetic inequality and RH remain open; no additional zero exclusion is claimed")
    ]),
    ("eulerSourceDecay", Json.mkObj [
      ("curvatureTheorem", .str
        "RiemannGaussian.exists_norm_deriv_logDeriv_riemannXi_euler_polynomial_bound"),
      ("signedIdentityTheorem", .str
        "RiemannGaussian.suzukiXiSmoothCarrierSource_eq_curvature_safe"),
      ("absoluteIntegralBoundTheorem", .str
        "RiemannGaussian.exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_euler_bound"),
      ("movingCutoffTheorem", .str
        "RiemannGaussian.tendsto_setIntegral_suzukiGammaShiftWeightedArithmeticSource_euler"),
      ("remainingStripTheorem", .str
        "RiemannGaussian.tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_zero_strip"),
      ("domain", .str "Im(z)>=1/2, equivalently Re(s)>=1; no extra buffer or height cutoff"),
      ("rate", .str "C(rho,c,tau)/r^2 for r>=1, fixed real c and fixed tau>0"),
      ("retainedInformation", .str
        "Exact complex source-curvature identity, complete divisor with analytic multiplicity, original reflection weight and variable denominator, arbitrary moving spatial cutoffs"),
      ("status", .str
        "Unconditional bound for the complete closed Euler half-plane. The original hypothetical-zero source remains in 0<=Im(z)<1/2. Its independent signed arithmetic ceiling and RH remain open; no new zero exclusion")
    ]),
    ("compactSourceDecay", Json.mkObj [
      ("signedIdentityTheorem", .str
        "RiemannGaussian.suzukiXiSmoothCarrierSource_eq_logDerivative_difference"),
      ("integrabilityTheorem", .str
        "RiemannGaussian.locallyIntegrable_suzukiXi_logDerivative_difference"),
      ("absoluteIntegralBoundTheorem", .str
        "RiemannGaussian.exists_integral_norm_suzukiGammaShiftArithmeticSource_compact_bound"),
      ("allWeightFamilyTheorem", .str
        "RiemannGaussian.exists_suzukiGammaShiftArithmeticSource_compact_all_weight_bound"),
      ("reflectedExteriorBoundTheorem", .str
        "RiemannGaussian.exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_outside_ball_bound"),
      ("movingNodeSourceTheorem", .str
        "RiemannGaussian.tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_reflected_ball"),
      ("compactRate", .str "C_K/r on every fixed compact K in Im(z)>=0, including all zeros and carrier poles"),
      ("weightedExteriorRate", .str "C/(r*epsilon^2) outside the reflected epsilon-ball, with C independent of the selected right-half zero, epsilon and r on each fixed compact region"),
      ("familyScope", .str
        "All measurable complex weights on a fixed compact region with a common norm budget; the same constant works for changing families"),
      ("status", .str
        "Independent absolute bounds inside the strip. On a fixed eligible rectangle the full hypothetical-zero source remains in any moving reflected neighborhood with r*epsilon(r)^2 tending to infinity, including shrinking neighborhoods. The signed arithmetic ceiling through that node and RH remain open; no new zero exclusion")
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
        "The complete remainder now has vanishing signed integral on each fixed " ++
        "upper rectangle as smoothing grows, including through its reflected node. " ++
        "The current edges also vanish, leaving the signed normalized mass variation. " ++
        "No independent bound below the source for that variation is proved. " ++
        "Its signed smoothing limit is now proved to equal the full positive " ++
        "source on every fixed eligible rectangle. The actual rescaled node " ++
        "profile retains a constant angular term after perpendicular phase " ++
        "coupling. The actual infinite eta quartic numerator now has an independent " ++
        "signed Gaussian upper bound: its positive part tends to zero on every " ++
        "line Re(s)>3/4 and along bounded moving families with a fixed margin. " ++
        "The exact negative phase square and the positive-power allowance are " ++
        "proved with all integrability and improper boundaries discharged. " ++
        "Completion, the variable denominator and the reflection weight remain " ++
        "outside that estimate; the full right-half-strip extension is open. " ++
        "A separate exact shifted Gamma representation now removes its completion-curvature " ++
        "error in L1 on the entire upper half-plane as smoothing grows, for each fixed " ++
        "positive Gaussian time. The actual mass vanishes quadratically at both reflection " ++
        "nodes, giving a global integrable dominator with the original weight retained. " ++
        "This error also vanishes on arbitrary moving spatial cutoffs in that half-plane. " ++
        "The companion heat term now also vanishes in global L1, leaving one weighted " ++
        "normalized arithmetic quartic. A rectangle-independent boundary bound permits " ++
        "simultaneous spatial cutoff and smoothing growth at fixed positive Gaussian time. " ++
        "The actual zero-free edge estimate now bounds logarithmic curvature polynomially " ++
        "on the entire closed Euler half-plane. An exact radial curvature identity gives " ++
        "the full reflection-weighted arithmetic density a global L1 bound C/r^2 on " ++
        "Im(z)>=1/2, including its boundary. This removes the earlier fixed positive " ++
        "buffer. The full selected source remains in 0<=Im(z)<1/2, including for " ++
        "arbitrary eligible moving rectangles. A new exact factorization through the " ++
        "full logarithmic Wronskian gives a locally integrable simple-pole majorant " ++
        "even inside the zero strip. The entire unweighted arithmetic source has " ++
        "compact absolute integral at most C_K/r through every zero and carrier pole. " ++
        "All measurable complex weights with common norm budget inherit this bound. " ++
        "The full reflected source outside an epsilon-ball has bound C/(r*epsilon^2), " ++
        "uniform in the selected right-half zero, radius and smoothing on each fixed compact region. Thus the " ++
        "selected source persists inside moving reflected neighborhoods whenever " ++
        "r*epsilon(r)^2 tends to infinity; its independent local signed ceiling " ++
        "remains open. The arithmetic density " ++
        "keeps its variable denominator and reflection phase; the first completion " ++
        "derivative is still in its denominator. A new exact normalized Gaussian square " ++
        "retains this denominator drift and both endpoint currents. The actual mass and " ++
        "carrier have one positive unit-scale rescaling denominator. Differentiating " ++
        "their quadratic relation supplies a continuous derivative-energy majorant " ++
        "through all zeros. The complete drift allowance, with its squared smoothing " ++
        "factor, therefore has integral tending to zero on every fixed compact subset " ++
        "of an upper horizontal line. Both scaled endpoint currents vanish, and the " ++
        "normalized arithmetic Gaussian integral is eventually below every positive " ++
        "ceiling on a fixed finite interval. The singular complex reflection weight " ++
        "and growing intervals are not included in this estimate. The independent " ++
        "reflected band ceiling is still open. The full weighted arithmetic density now " ++
        "has an exact node chart retaining the analytic coefficient derivative and the " ++
        "quadratic-displacement Gamma term. Its rescaled profile is positive and radial " ++
        "at a hypothetical upper reflected zero, uniformly over all angles at a fixed " ++
        "nonzero rescaled radius. Every normalized finite complex angular mixture with " ++
        "bounded total absolute weight retains a positive core, with one threshold even " ++
        "for changing and growing families. This is an obstruction to that method, " ++
        "not an independent source ceiling or a weighted area limit exchange. " ++
        "The needed deficit must come from an independent arithmetic " ++
        "estimate, not from assuming the retained mass decreases with smoothing. " ++
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
        "control actual recovery times. Variable damping now proves positive recovery " ++
        "in every sufficiently late interval [a,K*a] for every fixed K>1, with the " ++
        "complete signed moment, both geometric tails, finite delay span and rounding " ++
        "retained. Every deep excursion has a balanced minimum between t/K and K*t. " ++
        "A balanced-cell floor of order N^delta would therefore give an eventual " ++
        "literal signal floor of order exp(epsilon*t) for every epsilon>delta, " ++
        "removing the previous fixed exponent factor 4096. The arithmetic floor " ++
        "remains an unproved premise. Their nonlinear entropy correction is at most " ++
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
        "A uniform local center estimate does not close the cutoff bound. The global xi " ++
        "Poisson identity now retains every zero's multiplicity and all signed prime work " ++
        "for arbitrary admissible finite or infinite phase families. A proved Gamma " ++
        "estimate gives the analytic allowance 1+log(sigma+abs(t)), replacing the previous " ++
        "local 448*log(abs(t)+22) cost on its domain. Every nontrivial zero and positive " ++
        "shift are covered. Nonnegative kernels transport this to every finite arithmetic " ++
        "window. The independent lower bound that beats this reduced budget remains open. " ++
        "A complete horizontal subtraction now retains the Gamma difference as a " ++
        "nonnegative reserve. Uniform bounds for each signed zero block permit every " ++
        "summable nonnegative coefficient family and arbitrary real frequencies, with " ++
        "no logarithmic frequency moment. No exchange of the zero and frequency sums " ++
        "is assumed. The paired finite prime window plus the complete signed zero " ++
        "response and Gamma reserve is bounded by the exact pole difference. The " ++
        "selected zero is positive at its ordinate but distant zero contributions " ++
        "have a proved negative sign. Their compensating background remains open; " ++
        "removing the positive analytic allowance does not remove that obligation. " ++
        "A partial Stechkin subtraction now pairs the genuine critical reflections " ++
        "before estimating sign. Every omitted pair is nonnegative and every selected " ++
        "right-half zero retains its full multiplicity source. All admissible phase " ++
        "families have logarithmic allowance multiplied by 1-sigma/sqrt(1+4*sigma^2), " ++
        "and previous nonnegative arithmetic floors transfer with the same factor. " ++
        "This classical comparison does not supply the missing arithmetic floor. " ++
        "The complete prime work minus its entire pole family now has an exact Abel " ++
        "limit at the Euler boundary for every fixed admissible real-frequency family. " ++
        "Uniform logarithmic domination follows from the existing zero-free strip. " ++
        "The boundary identity preserves the signed completion and full selected " ++
        "source m/(1-Re(rho)), including zero-frequency pole cancellation. The " ++
        "independent lower bound for this regularized arithmetic remains open. " ++
        "A concrete three-height consequence now excludes every literal zero from " ++
        "the closed edges of width 1/(24*log(abs(t)+22)). The complex eta Euler " ++
        "center now excludes squared ordinates at most three, so the former " ++
        "height-one premise follows from the actual zero equation. Its exact " ++
        "signed remainder and quantitative bound hold at every cutoff. " ++
        "Exact adjacent-ratio summation now controls the eta tail uniformly at " ++
        "unbounded heights: its normalized error is at most 3*norm(s)/(2*X) " ++
        "for X>=norm(s), and every moving family with norm(s)/X tending to zero " ++
        "has half-endpoint limit. The independent finite-prefix arithmetic " ++
        "inequality is still missing. " ++
        "The signed trigonometric square and a new half-logarithm Gamma budget " ++
        "discharge all premises, widening the previous 1/(64*log(abs(t)+22)) " ++
        "edges by exactly 8/3. The completion improvement uses a height-dependent " ++
        "horizontal comparison and applies to every admissible phase family. " ++
        "The existing boundary mass and real derivative constants 325 and 326 " ++
        "remain valid on their stated domains. Zeros farther inside the strip " ++
        "remain unexcluded; this does not establish the full RH-strength inequality. " ++
        "The finite prime-band criterion, phase energy and scale-dependent floor, and " ++
        "complete eta identities remain available; none supplies the missing global estimate."))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
