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
    label := "Independent heat crosses 5/36 exactly beyond the 13/18 ceiling"
    lineOne := "independent heat"
    lineTwo := "crossing iff >13/18"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.DegreeFourMomentModel.thirteen_eighteen_lt_certificate_iff_exists_heat
  },
  {
    label := "The complete eta reserve inherits a nonnegative explicit upper-sector floor"
    lineOne := "complete reserve"
    lineTwo := "explicit floor"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.eventually_pairedEtaGeometricUpperWindowNonnegativeReserveGapLower_le_fullDecorrelationReserve
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
    "  <text class=\"section\" x=\"20\" y=\"143\">FURTHER CHECKED MILESTONES — NOT A PROOF CHAIN</text>\n" ++
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
      "prove the explicit full-reserve floor large enough for a certificate; no improved proportion yet.</text>\n" ++
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
        "versions converge to the same positive magnitude. Each finite prefix is " ++
        "also a signed derivative of the genuine finite eta Laplace partition. Lean " ++
        "forms the full complex completed partner residual, rewrites it exactly as " ++
        "the two discarded tails, bounds it by their completion-weighted envelopes, " ++
        "and proves that it tends to zero. Lean now chooses the tail split at each " ++
        "cutoff as theta_N=(n+1)/(sigma log(2N+1)), proves its eventual admissibility, " ++
        "and derives the full-exponent envelope exp(-sigma log(2N+1)+(n+1)) n! " ++
        "(log(2N+1)/(n+1))^(n+1). This sharper envelope tends to zero, gives convergent " ++
        "eventually valid and positive finite lower certificates, and bounds the " ++
        "completed residual at both complementary tilts. Lean now inserts the exact " ++
        "eta completion into the positive-measure Laplace energy and proves that the " ++
        "resulting pointwise quantity is |xi(s)|^2 throughout the open strip. This " ++
        "gives an exact complementary equality between completion-weighted sums of " ++
        "the squared tilted cosine and sine moments of the same arithmetic measure. " ++
        "Every finite Gaussian window is genuinely integrable, nonnegative, and " ++
        "symmetric under sigma <-> 1-sigma. The ordinate-dependent completion weight " ++
        "does not itself yield a zero-location constraint. Lean now proves the raw " ++
        "Gaussian Gram identity directly for the fixed infinite eta measure: its norm " ++
        "is an explicit nonnegative double integral with kernel exp(-sigma(t+u)) " ++
        "exp(-(t-u)^2/(4 tau)). Combining this with the completed symmetry isolates " ++
        "the raw complementary Gram difference exactly as the common completed energy " ++
        "integrated against the difference of reciprocal completion weights, with no " ++
        "remainder. The eta measure is nonzero and concentrated at positive logarithmic " ++
        "time, so Lean proves that the raw Gram is strictly decreasing in sigma and " ++
        "derives the complete global distortion sign: positive left of one half, zero " ++
        "exactly at one half, and negative right of one half. This zero-centered sign " ++
        "is unconditional but does not constrain zeros. Lean now localizes the fixed " ++
        "infinite Gram at every ordinate gamma and derives its exact arithmetic kernel: " ++
        "the positive envelope is multiplied by cos(gamma*(u-t)). The localized " ++
        "reciprocal-weight distortion is exactly the complementary difference of these " ++
        "oscillatory kernels. Positive phase preserves strict antitonicity in sigma, " ++
        "while negative phase strictly reverses it; at every nontrivial zero the " ++
        "localized energy integrand vanishes at its center. Lean now bounds the phase " ++
        "loss by sqrt(pi/tau)*2*gamma^2*tau times the square of the exact tilted eta " ++
        "mass. Thus the localized norm and completion distortion converge to their " ++
        "zero-centered counterparts with O(sqrt tau) error as tau tends to zero from " ++
        "the right. This short-time estimate suppresses, rather than resolves, the " ++
        "zero-defining cancellation. At the opposite scale, Lean proves by dominated " ++
        "convergence that the localized norm divided by sqrt(pi/tau) tends exactly to " ++
        "the squared eta partition value at its center. This normalized limit vanishes " ++
        "at every nontrivial zero, at its complementary tilt, and for the localized " ++
        "completion distortion. Lean now expands the literal eta product moments at " ++
        "a zero of exact multiplicity m: all difference moments below order 2m vanish, " ++
        "and the order-2m moment is (-1)^m choose(2m,m) times the squared norm of the " ++
        "first nonzero eta log moment. A sharp global exponential Taylor remainder " ++
        "gives an integrable product-measure majorant. Dominated convergence therefore " ++
        "proves that tau^m times the localized norm divided by sqrt(pi/tau) tends to " ++
        "the explicit strictly positive coefficient choose(2m,m)|M_m|^2/(4^m m!). " ++
        "The complementary norm has the partner coefficient as its actual limit, and " ++
        "the actual scaled completion-distortion limit is their difference. Completion " ++
        "symmetry gives an exact weighted balance, and Lean proves that the coefficient " ++
        "difference vanishes exactly when the two explicit completion weights agree. " ++
        "Lean now packages this comparison into a nonvanishing analytic reflection " ++
        "multiplier B(s) for the literal positive eta Laplace partition P(s). Throughout " ++
        "the open strip it proves P(1-s)=B(s)P(s), reciprocal and conjugation laws for " ++
        "B, and its explicit spectral--Gamma--eta factorization. Its squared norm is " ++
        "exactly the complementary completion-weight ratio. Thus the actual first " ++
        "distortion coefficient vanishes exactly when |B(rho)|^2=1, and the critical " ++
        "line implies this unit-norm equation. Lean now differentiates B throughout " ++
        "the open strip and cancels the apparent endpoint poles by the digamma " ++
        "recurrence. Its logarithmic derivative is a symmetric shifted-digamma term " ++
        "plus two explicit dyadic resolvents. The same-ordinate log norm is exactly " ++
        "antisymmetric about one half, and its horizontal derivative is the real part " ++
        "of that pole-free expression. Four exact positive Euler-series terms, a " ++
        "checked Euler-constant bound, and two disk-resolvent estimates now prove the " ++
        "slope strictly positive across the whole open strip whenever |Im(s)|>=8. " ++
        "Thus the multiplier log norm is strictly increasing and its unit-norm equation " ++
        "is equivalent to Re(s)=1/2 throughout that high-ordinate region. Lean also " ++
        "evaluates the multiplier norm exactly on Re(s)=1 and proves its square strictly " ++
        "greater than one at every nonzero ordinate away from the explicit dyadic " ++
        "resonances. A holomorphic reciprocal extension turns those resonances into zeros " ++
        "and has norm strictly below one on the complete outer boundary. Combining this " ++
        "with the high-ordinate result and the maximum-modulus principle closes the compact " ++
        "low-height rectangle. Thus throughout the entire open critical strip the " ++
        "multiplier norm is below one left of Re(s)=1/2, equal to one exactly there, and " ++
        "above one to its right. Lean now proves that at every nontrivial zero the exact " ++
        "partner-to-original leading Gaussian coefficient ratio is |B(rho)|^2. Hence the " ++
        "coefficient ordering, and equivalently the sign of their difference, detects the " ++
        "side of the critical line exactly. At absolute ordinate at least 8, Lean sharpens " ++
        "the horizontal log-norm slope to the explicit lower bound 1/200 and derives " ++
        "(1/100)|Re(rho)-1/2| <= |log(a(rho#)/a(rho))| for the two positive leading " ++
        "coefficients. Lean now bounds that ratio without completion symmetry: a positive " ++
        "finite phase-sensitive lower certificate L_N(rho) and the complementary explicit " ++
        "first-gap envelope U(rho#) give a(rho#)/a(rho) <= (U/L_N)^2. The lower " ++
        "certificate is eventually positive, so right-half high-ordinate zeros satisfy the " ++
        "eventual explicit displacement bound Re(rho)-1/2 <= 100*log((U/L_N)^2). No " ++
        "theorem makes this coarse upper bound vanish. Lean now also puts finite " ++
        "prefix-plus-tail upper certificates on both moments. The resulting lower and " ++
        "upper squared quotients eventually enclose a(rho#)/a(rho), both converge to the " ++
        "exact ratio, and the enclosure width tends to zero. The balanced near-sharp " ++
        "version retains the full horizontal exponent. Lean proves that every valid finite " ++
        "upper endpoint is nevertheless strictly above 1 for a right-half zero, even on " ++
        "the critical line, so upper<=1 is a vacuous target. The intrinsic self-slack " ++
        "(V_N(rho)/L_N(rho))^2-1 tends to zero, and allowing it reduces exactly to eventual " ++
        "finite-upper monotonicity V_N(rho#)<=V_N(rho). For closed-right-half zeros that " ++
        "eventual comparison is equivalent to the critical-line equation. No current " ++
        "theorem proves its arithmetic direction. Lean now uses the vanishing of every " ++
        "eta log moment below the exact zero multiplicity m to recenter the leading " ++
        "moment at a_N=log(2N+1). The exact centered tail has the unconditional envelope " ++
        "exp(-Re(rho)*a_N)*m!/Re(rho)^(m+1), with no logarithmic-power loss and no cutoff " ++
        "condition. Lean proves this is strictly smaller than the balanced near-sharp " ++
        "envelope whenever the latter applies. The resulting centered lower and upper " ++
        "certificates enclose the exact nonzero defect for every N, converge to it, and " ++
        "have width at most twice the centered tail. Lean now inserts these centered " ++
        "prefixes into the completed partner identity. Their full complex finite residual " ++
        "is exactly a signed sum of the two literal centered tails; its explicit " ++
        "completion-weighted envelope tends to zero and is strictly smaller than the old " ++
        "near-sharp residual envelope whenever both former cutoffs apply. Exact " ++
        "polarization writes the two completed finite prefix norm-square difference as " ++
        "|R_N|^2+2*Re(D_N*conj(R_N)), isolating the only sign-bearing cross-phase. Lean " ++
        "now translates the discarded tail by a_N=log(2N+1), proves the shifted measure " ++
        "is almost everywhere supported on positive time, and proves absolute " ++
        "integrability of its Laplace and separated Fourier--Laplace moments. The rho " ++
        "and 1-conj(rho) tails become complementary real tilts of this same measure at " ++
        "one frequency. Conjugation is exactly frequency reversal plus the relative " ++
        "phase exp(2*I*rho.im*a_N). The completed residual is a common unit phase times " ++
        "one explicit shifted coupled core and therefore has exactly its norm. Lean " ++
        "combines the two complementary moments into one absolutely integrable " ++
        "function on the common shifted measure. After extracting exp(-u/2), horizontal " ++
        "displacement delta=rho.re-1/2 occurs only through the reciprocal tilts " ++
        "exp(delta*u) and exp(-delta*u) in one oscillatory interference factor. The " ++
        "residual norm is exactly the norm of that single integral. Lean now proves " ++
        "the eta-specific cutoff transport mu_N=head_N+translate(Delta_N,mu_(N+1)), " ++
        "where the head is Lebesgue measure on (0,w_N] and 0<w_N<Delta_N exposes the " ++
        "omitted arithmetic gap. Every shifted Laplace and Fourier moment inherits an " ++
        "exact finite binomial recurrence. Completion and phase transport align the " ++
        "two complementary tilts, giving the actual residual work law " ++
        "R_N-R_(N+1)=head_N+sum_(j<m) choose(m,j)Delta_N^(m-j)C_(j,N+1). The top " ++
        "successor order is exactly R_(N+1). Lean now closes every lower order j<m: " ++
        "the complete centered moment vanishes, so its infinite centered tail is " ++
        "exactly the negative of its literal finite prefix at both complementary " ++
        "zeros. Thus the actual residual work law contains only one explicit head " ++
        "interval and a finite sum of finite eta-prefix couplings, with completion, " ++
        "parity, conjugation, and phase retained. Lean now derives a sharp asymptotic " ++
        "for every literal centered eta tail: after multiplication by the complex " ++
        "odd-endpoint power, the order-k tail converges to k!/(2*s^(k+1)) throughout " ++
        "Re(s)>0. The proof promotes the exact Euler second-difference remainder to " ++
        "locally uniform convergence and transports it through every holomorphic " ++
        "derivative. The corresponding endpoint-scaled norm has a strictly positive " ++
        "limit, providing a checked nondegenerate rate-separation input. Lean applies " ++
        "that input to the exact completed residual. For Re(rho)>1/2, scaling at the " ++
        "slower partner rate makes its norm converge to an explicit strictly positive " ++
        "completion-weighted constant, so the actual phase-bearing residual is " ++
        "eventually nonzero. Reflection covers Re(rho)<1/2: every off-line pair has " ++
        "one eventually nonzero orientation. This remains compatible with the proved " ++
        "unscaled convergence to zero. Lean now moves to the critical square-root " ++
        "scale and proves that the normalized residual tends to positive infinity at " ++
        "every right-half off-line zero. Hence a global eventual O((2N+1)^(-1/2)) " ++
        "residual bound forces every zero onto the line. Under RH, the explicit " ++
        "two-tail envelope proves that bound, so the global rate criterion is exactly " ++
        "equivalent to RH. Its forward arithmetic direction is not proved: the needed " ++
        "critical-scale control must still be derived from the finite residual work " ++
        "identity without assuming zero locations. Lean now names that exact finite " ++
        "one-step work W_N, proves sum_(q<L) W_(N+q)=R_N-R_(N+L), and passes L to " ++
        "infinity to reconstruct R_N. A uniform bound on (2N+1)^(1/2) times the sum " ++
        "of the norms of every finite work tail therefore implies the critical-scale " ++
        "residual bound and RH. This absolute coercivity premise is not proved and " ++
        "may be stronger than necessary; it exposes one explicit finite-arithmetic " ++
        "route to the required rate. Lean now restores the full complex endpoint " ++
        "phase in the off-line residual asymptotic. For Re(rho)>1/2 it proves " ++
        "(2N+1)^(rho#)R_N tends to an explicit nonzero completion-weighted Gamma " ++
        "constant, with rho#=1-conj(rho). The faster original tail vanishes at this " ++
        "complex normalization. This phase-bearing limit is not yet a signed work " ++
        "asymptotic. Lean now supplies the missing quantitative input: at every " ++
        "order k and every Re(s)>0, the complex-endpoint-normalized literal " ++
        "centered tail differs from k!/(2*s^(k+1)) by at most an explicit " ++
        "constant times (2N+1)^(-1), uniformly for every cutoff N. The proof " ++
        "derives the zeroth-order Euler remainder and propagates it through all " ++
        "derivatives by a Cauchy estimate. Lean now combines the exact triangular " ++
        "cutoff transport law with these sharp tails and proves the actual finite " ++
        "work asymptotic. At a hypothetical right-half zero, (2N+1)^(rho#+1)W_N " ++
        "tends to 2*rho# times the nonzero complex residual constant. The head and " ++
        "every transported order below m-1 vanish; the unique m-1 term survives. " ++
        "At the universal critical work scale this has a stronger consequence: " ++
        "for every right-half off-line zero, (2N+1)^(3/2)|W_N| tends to positive " ++
        "infinity. Reflection covers the opposite half-strip. Therefore an " ++
        "eventual O((2N+1)^(-3/2)) bound for the literal finite head-plus-prefix " ++
        "work at every nontrivial zero forces RH. Lean now splits that work exactly " ++
        "into a subtop hierarchy and one top transported moment. The subtop part--" ++
        "the new head and every order below m-1--vanishes at the critical 3/2 scale. " ++
        "The top part simplifies literally to m*Delta_N*C_(m-1,N+1), carries the " ++
        "entire nonzero partner-scale limit, and diverges at the critical scale for " ++
        "every right-half off-line zero. Thus a universal critical bound for this " ++
        "single finite coupled prefix transport forces RH. Lean now uses the exact " ++
        "factorization T_N=m*Delta_N*C_(m-1,N+1) and the proved limit " ++
        "(2N+1)*Delta_N -> 2 to remove the last deterministic transport factor. " ++
        "It proves that critical 3/2 boundedness of T_N is exactly equivalent, " ++
        "locally and globally, to square-root boundedness of the one literal " ++
        "phase-retaining prefix C_(m-1,N+1). The global prefix bound implies RH. " ++
        "Lean now identifies that prefix, in norm, with one absolutely integrable " ++
        "critical-half interference integral over the shifted positive eta-tail " ++
        "measure. Its explicit factor retains the two reciprocal horizontal tilts, " ++
        "completion coefficients, cutoff phase, and ordinate oscillation. The direct " ++
        "positive-measure triangle envelope is also proved, but it discards the " ++
        "required phase cancellation. The half-power arithmetic cancellation estimate " ++
        "is not proved. Lean now squares the one-measure representation without " ++
        "losing phase. The top-prefix norm square is exactly the product-measure " ++
        "integral of a symmetric Hermitian kernel. Its integral is nonnegative even " ++
        "though the kernel can change sign. The phase-free absolute product kernel " ++
        "dominates it, and their integral difference is a proved nonnegative phase-" ++
        "cancellation defect satisfying the exact ledger |C|^2+defect=(integral " ++
        "|f|)^2. Endpoint-scaled Hermitian Gram boundedness is exactly equivalent, " ++
        "locally and globally, to the square-root prefix bound. Estimating this signed " ++
        "Gram mass without zero-location assumptions remains the isolated frontier. " ++
        "Lean now splits the interference integral into its reflected-partner and " ++
        "conjugate-original components P_N and Q_N. It proves |C|^2=(|P_N|-|Q_N|)^2" ++
        "+A_N with a nonnegative anti-alignment defect A_N. Each component norm is " ++
        "exactly a completion weight times the corresponding literal order-(m-1) " ++
        "centered tail. Since their complementary decay exponents add to one, Lean " ++
        "proves an explicit fixed bound for (2N+1)A_N at every cutoff. Thus the entire " ++
        "cross-phase contribution is unconditionally controlled, and the prefix/Gram " ++
        "frontier is exactly equivalent to endpoint-scaled squared amplitude balance " ++
        "between the two completion-weighted centered-tail norms. That amplitude " ++
        "estimate, without zero-location assumptions, is the isolated frontier. " ++
        "Lean now transports the sharp centered-tail asymptotics through both exact " ++
        "component norms. At every hypothetical right-half zero, the slower partner-" ++
        "normalized signed amplitude difference tends to an explicit strictly positive " ++
        "constant, its squared normalization has the corresponding positive limit, " ++
        "and the exact endpoint-scaled amplitude imbalance tends to positive infinity. " ++
        "This proves the sharp obstruction but does not supply the independent " ++
        "arithmetic boundedness theorem needed to exclude it. Lean now proves the " ++
        "positive-odd-endpoint p-series threshold and uses reflection to classify the " ++
        "whole mismatch sequence: its sum over all cutoffs is finite exactly when the " ++
        "zero is on the critical line. On the line every mismatch is literally zero; " ++
        "off the line the sharp slower exponent makes the nonnegative series diverge. " ++
        "Universal summability is explicitly proved equivalent to RH. This is a " ++
        "Hilbert-space closure interface, not a proof of its arithmetic direction. " ++
        "Lean now uses the vanishing of the complete order-(m-1) moments to replace " ++
        "both infinite centered tails exactly by literal finite centered prefixes. " ++
        "Writing their completion-weighted magnitudes as A_N and B_N, the signed " ++
        "finite energy difference E_N=A_N^2-B_N^2 divided by the total amplitude " ++
        "S_N=A_N+B_N equals A_N-B_N even when S_N=0. Thus the amplitude mismatch " ++
        "is exactly (E_N/S_N)^2. The numerator is also polarized into top-prefix " ++
        "Gram energy plus one explicit finite cross phase. Lean now proves every " ++
        "centered finite prefix is one literal centered Laplace integral over the " ++
        "finite positive eta logarithmic measure. The two complementary completed " ++
        "features are integrable on that common measure and integrate to the finite " ++
        "partner terms. Their signed energy difference E_N is exactly the integral " ++
        "of one explicit integrable real rank-one Gram kernel over the product " ++
        "measure, with the product exchange and conjugation fully justified. Lean " ++
        "now defines the consecutive energy work J_N=E_N-E_(N+1) and proves its " ++
        "exact decomposition into signed increment energy plus successor cross flux. " ++
        "Its absolute value is bounded by the two increment energies and the two " ++
        "increment--successor norm products. Both component amplitudes tend to zero, " ++
        "so finite work sums telescope to E_N; after division by S_N their squares " ++
        "converge exactly to the original amplitude mismatch. Lean now expands every " ++
        "individual centered tail across one cutoff as the new eta support interval " ++
        "plus a triangular successor hierarchy. Below zero multiplicity, complete-" ++
        "moment vanishing replaces every tail by a finite prefix and cancels the top " ++
        "successor order. Thus both component increments, and hence the absolute " ++
        "energy-work bound, contain only one explicit head interval and strictly lower " ++
        "finite centered prefixes. The checked cutoff-shift limit now gives each such " ++
        "term at least one extra endpoint power. Lean consequently proves absolute " ++
        "summability of both completed component increments, their increment energies " ++
        "and successor cross-flux products, and the signed energy work J_N. Every tail " ++
        "has a genuine HasSum reconstruction of E_N and, after division by the fixed " ++
        "total amplitude, of E_N/S_N. This is unconditional but does not prove RH: " ++
        "the normalizing amplitude tends to zero, so the remaining theorem must control " ++
        "that vanishing denominator. Lean now proves a general weighted-tail lemma: " ++
        "summability of (2N+1)|J_N| forces (2N+1)|E_N| to vanish. The amplitude " ++
        "imbalance is pointwise at most |E_N| and its checked endpoint scaling diverges " ++
        "at every off-critical zero. Consequently the first-moment work series is " ++
        "summable exactly on the critical line, and universal summability is equivalent " ++
        "to RH and to normalized-energy square-summability. Lean now uses the explicit " ++
        "extra cutoff-shift power once more after squaring: both component increments " ++
        "have summable odd-endpoint-weighted norm squares, so the signed increment " ++
        "energy I_N has an unconditional finite first moment. Since J_N=I_N+F_N, the " ++
        "successor cross flux F_N has a finite first moment exactly when J_N does. Thus " ++
        "the entire remaining critical first-moment obstruction is isolated in the " ++
        "flux. Lean now returns that scalar to the finite positive eta measure. One " ++
        "explicit real Hermitian kernel pairs each head-plus-prefix arithmetic " ++
        "increment with its completed successor feature, and its integral is exactly " ++
        "F_N. The kernel is integrable and bounded by an explicit phase-free envelope. " ++
        "Subtracting |F_N| from the envelope integral gives a checked nonnegative " ++
        "cancellation reserve and the exact ledger |F_N|+reserve_N=integral envelope_N. " ++
        "Partner reflection swaps both components and makes the signed energy, work, " ++
        "increment energy, and flux odd, while |F_N| is invariant. Lean now splits " ++
        "each finite work into its unique degree-one leading transport and a remainder " ++
        "whose head and strict lower hierarchy all have shift degree at least two " ++
        "(with the head itself leading at multiplicity one). The two endpoint decays " ++
        "prove unconditionally that the remainder flux R_N has a finite critical first " ++
        "absolute moment. Since F_N=L_N+R_N, leading-flux summability is equivalent " ++
        "to full-flux summability, locally to the critical-line equation, and " ++
        "universally to RH. Lean now expands L_N without assuming simplicity. At " ++
        "multiplicity one it is a product integral coupling the translated new head " ++
        "to the successor prefix. At higher multiplicity it is a product integral " ++
        "coupling the adjacent centered orders m-2 and m-1 on the successor finite " ++
        "eta measure, with the one remaining shift factor. Both kernels are genuinely " ++
        "integrable and a multiplicity-selected integral equals L_N exactly. Lean now " ++
        "factors the higher-multiplicity kernel pointwise into a positive shift scale, " ++
        "an almost-everywhere negative odd centered monomial, one cosine phase, and one " ++
        "complementary horizontal-tilt bracket. The bracket vanishes identically on the " ++
        "critical line; off the line it has one explicit crossover and its sign is the " ++
        "oriented distance from that point. Lean now compresses the two completed finite " ++
        "eta-prefix terms into a reflection-equivariant two-coordinate feature and " ++
        "proves that their signed energy is its quadratic form against a fixed Hermitian " ++
        "hyperbolic signature matrix. The transpose conjugate-pair block is exactly a " ++
        "positive real rank-one block minus a positive imaginary rank-one block, while " ++
        "the ordinary Hermitian Gram has a plus sign and is positive semidefinite. This " ++
        "feature is now packed over arbitrary finite cutoff families and the genuine " ++
        "finite symmetric spectral zero windows, retaining analytic multiplicity. The " ++
        "complete window matrix splits exactly as onLine + (offReal - offImag); all three " ++
        "constituent blocks have their required positive-semidefinite proofs and the full " ++
        "matrix is Hermitian. Every constituent and full window block now has a literal " ++
        "zero-cardinality rank bound, and reflection proves #full=#critical+2*#upper. " ++
        "A checked spectral-subspace inertia theorem further proves that the off-line " ++
        "difference has positive index at most #upper and the complete window has " ++
        "positive index at most #critical+#upper. The on-line and off-line traces are " ++
        "now exact squared-coordinate sums, and the complete squared Frobenius mass " ++
        "is an explicit coherent multiplicity-weighted zero sum. The checked rank--trace " ++
        "theorem is now instantiated on these literal blocks. Its multiplicity-aware " ++
        "refinement retains one nonlinear k_c(m_rho*||v_rho||^2) term for every actual " ++
        "critical zero. The coherent Frobenius mass is now exactly the signed double " ++
        "zero-pair correlation sum m_rho*m_sigma*Re(<v_sigma,v_rho>^2), retaining " ++
        "complex phase. It is now split exactly as F=D+O, with positive diagonal " ++
        "D=sum m_rho^2*||v_rho||^4 and signed distinct-pair interference O. Frobenius " ++
        "positivity gives O>=-D, and the multiplicity ledger is rewritten directly in " ++
        "D and O. Opening every packed feature into its two literal completed-prefix " ++
        "channels proves that all mixed channels cancel: each feature correlation is " ++
        "twice the sum of its partner--partner and aligned-conjugate--conjugate terms. " ++
        "Both D and O, and the ledger itself, now use these same-channel eta variables. " ++
        "The two channels are further compressed to one original completed-prefix Gram " ++
        "kernel H: the feature correlation is exactly twice " ++
        "H(sigma#,rho#)+star(H(sigma,rho)). The original channel is now factored as " ++
        "W_rho*M_rho,j, separating each fixed completion weight W from the finite " ++
        "cutoff-centered eta moment. The resulting Gram kernel is a product of two W " ++
        "weights and the finite arithmetic moment correlation B. The masses and ledger " ++
        "now expose this factorization. Every centered moment is further expanded into " ++
        "its literal retained logarithmic interval atoms, so B is an exact finite " ++
        "cutoff/interval triple sum throughout the masses and terminal ledger. " ++
        "A checked finite integration-by-parts recurrence now evaluates every atom " ++
        "as an odd-endpoint complex power minus an even-endpoint complex power with " ++
        "explicit polynomial log coefficients. The full ledger is therefore a finite " ++
        "arithmetic endpoint correlation with no interval integrals remaining. Lean " ++
        "also proves the weighted Montgomery--Vaughan Hilbert inequality with constant " ++
        "26 and specializes it to the separated frequencies log(k+1). The multi-cutoff " ++
        "eta zero-window block now has an exact matrix-valued cutoff work law. The " ++
        "arithmetic feature increment is identified with the existing head-plus-prefix " ++
        "work and its leading/remainder split. Transporting that split through every " ++
        "matrix entry gives exact leading and remainder currents. Each individual zero " ++
        "contributes rank at most two to either current, and each finite-window current " ++
        "has rank at most twice the number of represented zeros. Lean now identifies the " ++
        "existing finite Gaussian arithmetic quadratic with a literal kernel matrix and " ++
        "proves the proper-time kernel exp(-u*(lambda_i-lambda_j)^2) positive semidefinite " ++
        "for u>0. Schur compression at the exact eta cutoff nodes log(2*N+1) has a checked " ++
        "entrywise derivative, commutes with the genuine multiplicity-weighted zero sum, " ++
        "preserves the on-line/off-line decomposition and Hermitian symmetry, and carries " ++
        "the leading/remainder matrix-current law through every heat time. Lean now proves both " ++
        "the oriented square-root representation and the direct odd proper-time identity " ++
        "integral Delta*exp(-u*Delta^2) du=Delta^(-1), with coincident nodes explicitly removed " ++
        "before integration. The direct kernel reverses sign under index swap and turns every " ++
        "complex-symmetric source into a skew-symmetric transform. The centered eta cutoff nodes " ++
        "log(2*N+1) have checked gap 1/(2*K), so Montgomery--Vaughan with constant 26 applies " ++
        "directly to the odd-heat bilinear form. Lean applies it blockwise to both rank-one terms " ++
        "in each genuine zero's leading current, retains analytic multiplicity and the exact " ++
        "complex signed spectral-window sum, and only then proves a coarse sum-of-envelopes norm " ++
        "bound. Both same-colour block sums vanish and the mixed-colour blocks are negatives. " ++
        "The full direct odd-heat trajectory is now retained before integration. At every heat " ++
        "scale its surviving block is exactly the signed zero sum of three literal cross-colour " ++
        "eta forms; same-colour cancellation holds pointwise. The reciprocal-gap Hilbert block " ++
        "is proved to be the positive-time integral of that richer phase-, colour-, multiplicity-, " ++
        "and scale-resolved carrier. Lean now also constructs the continuous spectral heat flow " ++
        "of every finite Hermitian matrix. The u^(-1/2)-weighted signed current is genuinely " ++
        "integrable and its normalized integral is exactly n_+-n_-; the ordinary heat trace " ++
        "converges to the zero index, giving exact positive-inertia recovery. This abstract " ++
        "matrix theorem is not yet connected to eta arithmetic or a zeta-zero proportion. " ++
        "Lean now also proves the exact ordered cross-scale projection identity, factors every " ++
        "leakage as a transition Gram, and retains separate first-projection and second-compression " ++
        "losses in a two-stage heat ledger. At equal scales both losses are positive semidefinite " ++
        "and their traces are exact transition Frobenius masses. This remains finite matrix " ++
        "algebra. The complete signed spectral heat flow is now instantiated on the literal " ++
        "multiplicity-weighted eta zero-window matrix. Its signed current is integrable, its " ++
        "normalized integral is the exact signature, its ordinary heat trace recovers nullity, " ++
        "and the resulting exact positive-inertia expression obeys the checked critical-plus-upper " ++
        "zero-count bound. This is a richer representation of the current certificate, not an " ++
        "improved zero proportion. The eta leakage transitions have not yet been arithmetically " ++
        "evaluated. Every decidable packed cutoff/colour coordinate selection now defines a " ++
        "checked Hermitian idempotent projection of that eta spectral heat. Its ordered leakage " ++
        "is expanded entrywise as the exact finite path sum through omitted coordinates and is " ++
        "simultaneously factored as the cross-scale transition Gram. Same-scale positivity, the " ++
        "zero-transition criterion, exact Frobenius trace mass, and the longer-time trace-balance " ++
        "ledger are all checked. This is finite coordinate compression, not yet the infinite " ++
        "logarithmic-time eta support operator. The literal eta window now also carries the full " ++
        "matrix hierarchy A^k*exp(-u*A^2). Products add order and scale, every even-order flow is " ++
        "positive semidefinite, and differentiation raises trace order by two with a negative sign. " ++
        "Every finite family of orders and scales forms a checked positive-semidefinite Gram matrix; " ++
        "each entry is exactly the combined higher moment and the cross-scale trace product. At " ++
        "zero heat scale the first three traces are now identified with dimension, signed trace, " ++
        "and squared Frobenius mass. On the literal eta window the order-two value, and hence the " ++
        "negative initial ordinary-heat slope, is exactly the evaluated endpoint diagonal plus " ++
        "signed off-diagonal arithmetic correlation. Every positive-time eta heat moment is now " ++
        "also a genuinely convergent series of all parity-compatible matrix-power traces. Every " ++
        "coefficient is now opened further as an ordered closed path through the literal eta " ++
        "cutoff/colour coordinates, with each edge still a complex multiplicity-weighted zero " ++
        "sum. The length-two path is exactly the existing endpoint arithmetic ledger. Higher " ++
        "paths and genuinely mixed scales have not yet been estimated from eta arithmetic. " ++
        "At cubic order, coordinate compression now retains three distinct ordered paths: a gap " ++
        "at either separator and gaps at both. The one-gap pair is adjoint with equal real traces " ++
        "at equal scale; the two-gap path is a positive weighted transition Gram. Every eta entry " ++
        "is the corresponding retained/omitted double coordinate sum. " ++
        "A generic shift-difference argument now proves that a finite sum of distinct unit-circle " ++
        "geometric modes cannot converge to zero unless every coefficient vanishes. Lean packages " ++
        "this as linear independence of the corresponding full geometric sequences. This is the " ++
        "finite phase-rigidity lemma needed for geometric sampling of the sharp eta cutoff asymptotics. " ++
        "Lean now performs that sampling for every odd base q>1 at the exact cutoff (q^n-1)/2. " ++
        "The sampled odd endpoint is q^n, the cutoff tends to infinity, and the multiplicity-minus-one " ++
        "finite eta prefix at every nontrivial zero has an explicit nonzero complex limit after " ++
        "normalization by the nth power of one fixed mode. A phase collision for two distinct " ++
        "frequencies is now proved possible at at most one prime base. Hence every finite injective " ++
        "frequency family has an odd prime base with pairwise distinct normalized modes. The raw " ++
        "inverse mode restores the real coordinate in its norm, so one odd prime now separates the " ++
        "complete modes across any finite zeta-zero window. Their first window-cardinality coordinates " ++
        "form a checked nonsingular Vandermonde matrix. Lean now row-scales the literal multiplicity-" ++
        "aware centered eta-prefix matrix, proves its entrywise convergence to a nonzero diagonal " ++
        "multiple of that Vandermonde block, passes the limit through the determinant, and removes " ++
        "the exact row scaling. Hence one odd prime makes every sufficiently late square block of " ++
        "literal eta prefixes nonsingular. Lean now identifies the corresponding completed original-" ++
        "channel matrix as a nonzero diagonal scaling of that literal block and its aligned channel " ++
        "as the entrywise conjugate. A fixed complex-linear projection recovers the aligned channel " ++
        "from the actual packed even/odd hyperbolic feature. Thus one odd prime makes all sufficiently " ++
        "late packed features of every finite zeta-zero window linearly independent. Scaling each " ++
        "zero column by its positive square-root analytic multiplicity now gives a coordinate Gram " ++
        "equal to the sum of the literal multiplicity-weighted Hermitian v*v blocks. It is positive " ++
        "semidefinite and eventually has rank exactly the number of represented distinct zeros. It " ++
        "is kept distinct from the complex-symmetric signed block. On every nonnegative symmetric " ++
        "window Lean now proves Gram=onLine+offReal+offImag while Signed=onLine+offReal-offImag. " ++
        "Thus Gram-Signed is twice the positive imaginary block and Gram+Signed is twice the positive " ++
        "on-line-plus-real block. Pulling the same synthesis matrix C back to zero-index space gives " ++
        "K=C^*C. Actual packed-feature linear independence makes C injective, so one odd prime makes " ++
        "K and its inverse positive definite at every sufficiently late block. Lean now pulls the " ++
        "signed coordinate block back as B=C^*Signed*C. Congruence gives K^2-B and K^2+B positive " ++
        "semidefinite. The normalized A=K^-1*B*K^-1 is Hermitian with I-A and I+A positive " ++
        "semidefinite. Lean now proves P*C^*=C^T for the reflected-zero permutation P and " ++
        "Signed=C*C^T. Therefore B=K*P*K and complete whitening gives A=P, with A^2=I and trace " ++
        "equal to the number of fixed reflection indices. This shows that full whitening cancels " ++
        "the eta amplitudes. Lean now retains m0=Re tr(K) and m1=Re tr(PK). These are exactly the " ++
        "positive Hermitian and signed literal eta traces, with m0-m1 twice the imaginary off-line " ++
        "mass and m0+m1 twice the on-line-plus-real mass. Hence -m0<=m1<=m0, and every nonempty " ++
        "eventually separated window has m0>0 and m1/m0 in [-1,1]. Lean now defines the cross-scale " ++
        "carrier M_nm=P*(C_n^*C_m)=C_n^T*C_m, proves M_nm^T=M_mn, and expands every same-scale " ++
        "moment Re tr((P*K)^r) as a complete ordered closed zero-index path sum with literal " ++
        "multiplicity-weighted eta edges. Order zero is the represented-zero count and order one is " ++
        "m1. The two-step cross-scale word is an exact symmetric double-edge sum. The mixed " ++
        "hierarchy now has a checked positive normalized Hankel realization, but positive K makes " ++
        "P*K invertible, so that spectrum has the wrong zero-atom semantics. Reflection-parity " ++
        "compression supplies the correct off-line nullity and exact eta-weighted colour masses. " ++
        "Lean now extracts its uniform normalized nonnegative eigenvalue atoms. Every power and " ++
        "heat moment is an exact normalized trace of E+*K*E+, zero mass is the upper off-line-pair " ++
        "fraction, and the resulting certificate is the literal critical-zero fraction. Strict " ++
        "improvement over 13/18 is exactly a normalized ordinary-heat crossing below 5/36. Writing " ++
        "W=C*E+, Lean transfers every positive moment from W^*W to W*W^*. The latter is exactly " ++
        "the positive on-line-plus-off-line-real coordinate block; ordinary heat transfers with " ++
        "one explicit cardinality padding correction. Its convergent even closed-path series now " ++
        "retains every intermediate packed coordinate and both eta edge colours. The arithmetic " ++
        "crossing estimate has not yet been proved. " ++
        "Separately, every " ++
        "finite nonnegative weighted model with moments (1,1,4/3,2,13/4) now has a checked " ++
        "certificate at least 13/18. An explicit nonnegative three-atom model attains equality, " ++
        "so this degree-four information class has a sharp ceiling below one. Its moments are " ++
        "the zero-scale jet of a checked continuous weighted heat hierarchy, but no theorem " ++
        "derives them from the eta window. The quadratic witness is now retained through heat " ++
        "time as an exact linear combination of orders zero through four. Its scale-dependent " ++
        "certificate is monotone from 13/18 and converges to the exact model certificate. The " ++
        "sharp three-atom model nonetheless stays exactly at 13/18 at every nonnegative scale, " ++
        "because both nonzero atoms are roots of the witness. Hence heat-damping this same " ++
        "collapsed channel does not supply independent information. The ordinary heat trace is " ++
        "now retained as a genuinely independent channel. It is strictly above zero mass at every " ++
        "finite scale and converges to zero mass. Lean proves that the certificate exceeds 13/18 " ++
        "exactly when this trace crosses below 5/36 at some nonnegative scale; the sharp model " ++
        "stays strictly above 5/36 at every finite scale. " ++
        "Distinct separated eta atoms now have strict pairwise decorrelation. Finite injective " ++
        "unit-mode blocks have an exact positive phase gap and uniform O(M^-2) distinct-pair " ++
        "squared coherence. Explicitly normalized literal eta-prefix vectors and their coherence " ++
        "converge to that model, giving a uniform eventual 4/M^2+epsilon bound on finite " ++
        "same-real-part zero layers. The two hyperbolic coordinates are now proved to be an " ++
        "injective realification of the completed complex eta channel, and normalized packed " ++
        "same-layer coherence inherits the same bound. A common tilt now transports arbitrary " ++
        "real layers to modes of exact radius q^(sigma-Re(rho)). At the critical tilt, reflected " ++
        "off-line modes keep one phase and reciprocal radii. Their exact cross-correlation is the " ++
        "window length, their signed two-coefficient norm ledger retains the full interference " ++
        "term, and every literal off-line critical-shifted pair has strictly positive Gram " ++
        "reserve beyond length one. More quantitatively, every complex combination is bounded " ++
        "below by determinant over trace times its coefficient norm, and that constant is proved " ++
        "positive. The actual upper frame atom is half the injective " ++
        "realification of its completed-channel sum. After lossless recovery and common critical " ++
        "tilt, that actual atom is exactly the two normalized literal eta-prefix columns with " ++
        "their distinct nonzero cutoff-dependent completion coefficients. The literal two-column " ++
        "Gram coefficient converges to the positive reciprocal-mode constant, so every sufficiently " ++
        "late pair has one half-limit coercive bound uniform in both coefficients. Substituting the " ++
        "actual moving coefficients proves an explicit positive lower bound for the recovered upper " ++
        "frame channel. The common critical tilt is now absorbed through its explicit positive " ++
        "coordinate energy, while half-realification is proved exactly norm-preserving after " ++
        "recovery. Thus the literal packed upper atom itself inherits a positive lower bound in the " ++
        "certificate metric. The packed correlation of two upper atoms is now the exact real part " ++
        "of their complex reflection-sum correlation, and that carrier expands into four named " ++
        "completed original-channel eta Gram kernels. Its actual multiplicity-weighted reserve is " ++
        "exactly the full Hermitian Gram reserve plus the squared imaginary correlation. The " ++
        "critical tilt now retains its inverse squared-modulus recovery metric: the two reflection " ++
        "colours form a 2x2 normalized-prefix metric correlation matrix, its contraction against " ++
        "the moving completion coefficients is the original unweighted correlation, and every " ++
        "entry converges to an explicit shifted-mode metric correlation. Bounding this matrix " ++
        "carrier now begins with an exact evaluation: the recovery metric cancels the critical " ++
        "tilt, every limit entry is a finite geometric sum of raw decay modes, and all four literal " ++
        "entries eventually obey norm(entry)*norm(relativeMode-1)<2+epsilon simultaneously over " ++
        "the upper window. Contracting this bound against the moving completion coefficients and " ++
        "retaining all four colours now gives an explicit eventual envelope for every actual " ++
        "unweighted complex and packed real upper-pair correlation. Lean now combines its square " ++
        "with both strictly positive transported atom-coercivity bounds. Every actual " ++
        "multiplicity-weighted upper-pair reserve eventually dominates the resulting " ++
        "coercivity-product-minus-envelope-square expression, simultaneously over the finite " ++
        "upper window, and the inequality is summed over all ordered distinct upper pairs. The " ++
        "complete reserve is now split exactly into four atom-colour sectors, every sector is " ++
        "nonnegative, and its upper sector is exactly that ordered-distinct sum. Consequently the " ++
        "maximum of zero and the explicit upper lower bound is an eventual floor for the complete " ++
        "certificate reserve. Substitution into the checked certificate theorems now gives the " ++
        "literal floor targets: after one odd-prime choice and at every sufficiently late block, " ++
        "the strict floor inequality implies a proportion above 13/18 and the endpoint floor " ++
        "inequality implies 18/18. Neither inequality is yet proved.")),
    ("milestones", .arr (milestones.map milestoneToJson)),
    ("frontier", Json.mkObj [
      ("label", .str "Arithmetic-to-zero-location rigidity"),
      ("status", .str "open"),
      ("target", .str (
        "Prove the checked nonnegative full-reserve floor from the upper " ++
        "coercivity-product-minus-correlation-envelope-square sum large enough to establish " ++
        "(31*N-36)*potential<36*floor on an eventually separated geometric window. " ++
        "The checked exact identity mass^2=potential+reserve makes this equivalent to " ++
        "the frame-moment premise sufficient to beat 13/18, while the endpoint bound " ++
        "(N-1)*potential<=floor is sufficient for finite-window 18/18. " ++
        "Lean already proves F_N=L_N+R_N, the critical " ++
        "summability of R_N, the exact cosine/crossover factorization of the higher-" ++
        "multiplicity L_N kernel, the finite on-line/off-line block decomposition, " ++
        "the required divisor-count rank and positive-index bounds, exact scalar " ++
        "trace/Frobenius identities, their checked coarse and multiplicity-aware " ++
        "rank--trace closures, the exact phase-preserving zero-pair expansion of the " ++
        "coherent Frobenius mass, and its positive-diagonal plus signed-off-diagonal " ++
        "decomposition inside the literal multiplicity ledger. Each packed-feature " ++
        "correlation is further reduced to the two same-channel completed eta-prefix " ++
        "correlations, with every mixed channel proved to cancel. Those two channels " ++
        "are further identified with one original completed-prefix Gram kernel at the " ++
        "original and reflected zero pairs. Fixed completion weights are further factored " ++
        "away from a finite cutoff-centered eta-moment Gram kernel, and that kernel is " ++
        "expanded exactly into a finite triple sum over literal retained eta intervals. " ++
        "Every interval is further evaluated into explicit odd--even endpoint complex " ++
        "powers with finite polynomial logarithmic coefficients. The packed cutoff " ++
        "family also obeys an exact entrywise matrix work law which splits into literal " ++
        "leading and remainder currents. Both per-zero currents have checked rank at " ++
        "most two, with aggregate rank at most twice the window cardinality. That matrix " ++
        "law is now transported through a continuous positive-semidefinite Gaussian " ++
        "proper-time kernel at the exact eta cutoff nodes; the compressed genuine zero " ++
        "sum, signed block decomposition, Hermitian symmetry, and entrywise derivative " ++
        "are all checked. Both direct odd and oriented square-root heat integrals produce the " ++
        "reciprocal logarithmic-gap kernel exactly, and the Montgomery--Vaughan constant-26 " ++
        "estimate is proved in that heat form for the separated nodes log(2*N+1). The transform " ++
        "acts entrywise on the actual matrix work and preserves its leading/remainder split. " ++
        "Its application to the two actual rank-one leading terms is now checked blockwise. " ++
        "The complete block remains the exact multiplicity-weighted complex signed zero sum, " ++
        "with same-colour cancellation and mixed-colour antisymmetry retained before the coarse " ++
        "sum-of-envelopes norm bound. The underlying direct odd-heat family is also retained " ++
        "pointwise: at every proper time the surviving block is the exact three-colour signed " ++
        "zero sum, and its positive-time integral is the reciprocal-gap block. The abstract " ++
        "finite Hermitian signed heat flow now reconstructs positive inertia exactly from its " ++
        "continuous trace/current observables. Its finite two-projection calculus now retains " ++
        "ordered cross-scale transition Grams and separates the two nonnegative same-scale " ++
        "leakage masses exactly. The literal eta zero-window matrix now carries the complete " ++
        "signed spectral heat trajectory, exact signature integral, nullity limit, positive-inertia " ++
        "reconstruction, and continuous critical-plus-upper count bound. Arbitrary retained " ++
        "cutoff/colour coordinates now also have exact omitted-coordinate cross-scale path sums, " ++
        "transition-Gram factorizations, and same-scale mass-balance ledgers. Higher and mixed-scale " ++
        "eta spectral moments now form an exact positive Gram with a checked derivative hierarchy. " ++
        "Their zero-scale order-one and order-two boundary values are now exactly the checked eta " ++
        "trace and endpoint-expanded coherent Frobenius ledgers; the order-two ledger is also the " ++
        "negative initial heat slope. The complete positive-time hierarchy is now a checked " ++
        "convergent series of parity-compatible matrix-power traces, so the ordinary eta heat " ++
        "channel retains every even coherent power rather than collapsing at positive scale. Each " ++
        "power trace is now an exact ordered closed eta path sum; its edge factors retain cutoff, " ++
        "colour, phase, zero multiplicity, and path order. The length-two path recovers the checked " ++
        "endpoint ledger. The cubic coordinate-compression ledger separately retains both ordered " ++
        "one-gap paths and the two-gap path; the former pair by adjunction and the latter is " ++
        "positive semidefinite at equal scale. Their literal retained/omitted double path sums are " ++
        "checked, while their aggregate arithmetic estimate remains open. A generic finite " ++
        "geometric-phase rigidity theorem now proves, by repeated shift differences, that distinct " ++
        "unit-circle modes have linearly independent full sequences. The sharp complex eta-tail " ++
        "asymptotic is now sampled at exact geometric odd endpoints q^n for every odd q>1, and the " ++
        "literal lower-moment finite prefix at each zeta zero has a checked nonzero complex geometric " ++
        "limit. Lean now proves that collisions for any distinct frequency pair occur at at most one " ++
        "prime, and therefore selects one odd prime base with distinct normalized modes across any " ++
        "finite injective frequency family. The raw inverse decay mode retains the real coordinate " ++
        "through its exact norm, allowing one odd prime to separate the entire finite zeta-zero " ++
        "window without an explicit layer partition. The first window-cardinality mode coordinates " ++
        "form a nonsingular Vandermonde matrix. Lean now transfers that block through the sharp " ++
        "complex eta asymptotics: the row-scaled literal prefix matrices converge to a nonzero " ++
        "diagonal multiple of the Vandermonde, so all sufficiently late unscaled square eta-prefix " ++
        "blocks have nonzero determinant. The corresponding completed original-channel matrix is a " ++
        "nonzero diagonal scaling, its aligned channel is the entrywise complex conjugate, and one " ++
        "fixed complex-linear projection extracts that channel from the actual packed even/odd " ++
        "hyperbolic features. Therefore every finite zeta-zero window has one odd prime base for " ++
        "which all sufficiently late packed certificate features are linearly independent. Lean " ++
        "retains analytic multiplicity through positive square-root column weights and forms the " ++
        "coordinate synthesis matrix times its conjugate transpose. This is exactly the sum of the " ++
        "multiplicity-weighted Hermitian v*v blocks, is positive semidefinite, and eventually has " ++
        "rank equal to the number of represented distinct zeros. The positive Gram and the distinct " ++
        "complex-symmetric signed block now satisfy an exact joint colour ledger: their difference " ++
        "is twice the positive off-line-imaginary block and their sum is twice the positive on-line-" ++
        "plus-real block. Both combinations are positive semidefinite. Pulling the same synthesis " ++
        "matrix C back to zero-index space gives K=C^*C; its injectivity makes K and its inverse " ++
        "positive definite for one odd prime at all sufficiently late blocks. The signed pullback " ++
        "B=C^*Signed*C obeys K^2-B and K^2+B positive semidefinite. Its normalization " ++
        "A=K^-1*B*K^-1 is Hermitian with I-A and I+A positive semidefinite. The reflected-zero " ++
        "permutation P satisfies P*C^*=C^T, so Signed=C*C^T, B=K*P*K, and complete whitening " ++
        "collapses exactly to A=P. It squares to I and its trace counts fixed reflection indices. " ++
        "Lean now retains K coupled to P through m0=Re tr(K) and m1=Re tr(PK), identifies these " ++
        "with the positive and signed literal eta traces, and proves the exact colour identities " ++
        "m0-m1=2*offImag and m0+m1=2*(onLine+offReal). The normalized balance lies in [-1,1] on " ++
        "every nonempty separated window. The cross-scale carrier M_nm=P*(C_n^*C_m)=C_n^T*C_m " ++
        "now retains both scales and satisfies M_nm^T=M_mn. Every Re tr((P*K)^r) is exactly a " ++
        "complete ordered closed path sum of literal multiplicity-weighted eta edges; the two-step " ++
        "cross-scale word is an exact symmetric double-edge sum. Lean now constructs the packed " ++
        "Hermitian carrier S=C*P*C^* and its exact metric support Q=C*K^-1*C^*. Whenever K is " ++
        "positive definite, Q is positive semidefinite, Hermitian, and idempotent, QS=SQ=S, and " ++
        "tr(Q) is the represented distinct-zero count. Every supported moment Re tr(Q*S^r), " ++
        "including order zero, equals Re tr((P*K)^r). Flattening arbitrary finite families of " ++
        "supported powers now gives a positive-semidefinite Hankel Gram with exactly those moments " ++
        "as entries. Lean normalizes it by the distinct-zero count N and mean positive eta mass " ++
        "m0/N: nu_r=N^-1*(N/m0)^r*Re tr((P*K)^r). Every finite normalized Hankel matrix is positive " ++
        "semidefinite, nu_0=1, nu_1=m1/m0, and nu_(a+b)^2<=nu_(2a)*nu_(2b). Lean now proves " ++
        "that P*K is invertible whenever K is positive definite, so its spectral zero atom cannot " ++
        "encode off-line zeros. The correct count channel is retained by the orthogonal positive " ++
        "reflection projections E+=(I+P)/2 and E-=(I-P)/2. Their traces are exactly critical+upper " ++
        "and upper respectively, and 1-2*tr(E-)/N is the literal critical-zero proportion. The " ++
        "eta-weighted carriers E+*K*E+ and E-*K*E- are positive semidefinite. Under positive " ++
        "definiteness of K, the first has nullity exactly equal to the upper off-line-pair count, " ++
        "the second has that exact rank, and their traces recover the on-line-plus-real and " ++
        "off-line-imaginary eta masses. Lean now extracts the normalized uniform eigenvalue-atom " ++
        "model of E+*K*E+. Its nodes are nonnegative, every ordinary and heat moment is an exact " ++
        "normalized matrix trace, and its zero mass is precisely the upper off-line-pair fraction. " ++
        "Thus its certificate is the literal critical-zero fraction, with strict improvement over " ++
        "13/18 equivalent to one normalized ordinary-heat crossing below 5/36. Lean now factors " ++
        "the carrier as W^*W for W=C*E+ and transports its nonzero spectrum to W*W^*, exactly the " ++
        "positive on-line-plus-off-line-real coordinate block. Positive moments agree, and ordinary " ++
        "heat differs by one exact zero-padding cardinality. A checked coloured closed-path series " ++
        "retains the intermediate packed coordinate and on-line/off-line-real choice at every edge. " ++
        "Its rank is now exactly critical plus upper-off-line. Finite Cauchy--Schwarz gives the " ++
        "effective-rank bound rtrace^2<=rank*frobSq, while the first two moments are exactly the " ++
        "real length-one and length-two coloured path sums. The explicit inequality " ++
        "31*N*Re(path2)<36*Re(path1)^2 is sufficient for a proportion above 13/18; the endpoint " ++
        "ceiling N*Re(path2)<=Re(path1)^2 is sufficient for every represented zero to be critical. " ++
        "The two paths are now opened as a literal reflection-even eta frame: one weighted atom " ++
        "per critical zero and one real-coordinate atom per upper off-line pair. The first path is " ++
        "its weighted squared-norm mass and the second is its full weighted frame potential. Every " ++
        "pair term is a checked nonnegative squared real eta correlation, with both atom colours " ++
        "retained. Lean now splits diagonal self-mass from distinct-pair correlation and proves " ++
        "mass^2=potential+reserve, where every colour-resolved reserve summand is nonnegative by " ++
        "complex Cauchy--Schwarz. The 13/18 and endpoint premises are exactly equivalent to the " ++
        "corresponding lower bounds on this reserve. A square-root-weighted synthesis now identifies " ++
        "the frame Gram with the coordinate carrier; full checked rank makes the literal atoms " ++
        "linearly independent at separated blocks. Thus every distinct pair has strict positive " ++
        "Gram-determinant reserve, and the total reserve is positive exactly for at least two atoms. " ++
        "Long finite unit-mode blocks now retain their exact complex geometric-sum correlation and " ++
        "obey |corr|^2*|conj(w)z-1|^2<=4. A finite injective mode family has a positive minimum " ++
        "phase gap and hence uniform O(M^-2) distinct-pair squared coherence; one odd prime " ++
        "instantiates this on same-real-part zeta-zero layers. Explicit nonzero row and common " ++
        "coordinate normalization now transports the actual finite eta prefixes, their complex " ++
        "correlations, norms, and squared coherences to that phase model. Every distinct pair in a " ++
        "finite same-real-part layer therefore has the uniform eventual 4/M^2+epsilon bound. The " ++
        "two hyperbolic coordinates are an injective realification with exact reconstruction, " ++
        "correlation, and norm laws; the literal critical packed feature is exactly this " ++
        "realification. Normalized packed same-layer coherence inherits the complex bound. One " ++
        "common tilt now transports arbitrary layers to shifted modes with exact radius " ++
        "q^(sigma-Re(rho)); correlations, norms, and both complex and packed coherences converge " ++
        "with that colour retained. At the critical tilt, every reflected off-line pair has a " ++
        "shared phase and reciprocal radii on opposite sides of one. The actual upper frame atom " ++
        "is half the realification of the reflection-summed completed channel and reconstructs " ++
        "that complex sum exactly. The two underlying critical-shifted modes are now identified " ++
        "with an exact reciprocal-radius pair: their cross-correlation is the window length, their " ++
        "arbitrary signed combination has an exact interference ledger and cannot cancel, and the " ++
        "literal off-line pair has strictly positive Gram reserve beyond length one. Its full " ++
        "quadratic form is now bounded below by the explicit positive determinant-over-trace " ++
        "constant times the coefficient norm. The actual frame is now joined exactly to that " ++
        "interface: after coordinate recovery and critical tilt, each upper atom is the two " ++
        "normalized literal prefix columns with explicit nonzero cutoff-dependent completion " ++
        "coefficients. Lean now proves the finite two-column Gram coefficient converges to the " ++
        "positive mode constant and obtains an eventual half-limit lower bound simultaneously for " ++
        "all coefficient pairs. It therefore applies to the actual moving completion coefficients, " ++
        "giving a quantitative lower bound and strict noncollapse of every late recovered upper " ++
        "frame channel. Lean now also pays the nonunitary common-tilt cost explicitly: pointwise " ++
        "weighting is bounded by its finite coordinate energy, and the packed upper-atom norm is " ++
        "exactly the unweighted recovered-channel norm. Dividing by that positive energy transfers " ++
        "coercivity and strict noncollapse to the literal certificate frame metric. The correlation " ++
        "of two literal upper atoms is now exactly the real part of a complex reflection-sum " ++
        "correlation. That carrier expands into four completed original-channel eta Gram kernels, " ++
        "and its weighted certificate reserve is exactly a full Hermitian Gram reserve plus the " ++
        "squared imaginary correlation. Lean now inserts the exact inverse squared-modulus metric " ++
        "for the critical tilt. The two reflection colours form a 2x2 normalized-prefix correlation " ++
        "matrix whose completion-coefficient contraction is the original unweighted correlation; " ++
        "each entry converges to its explicit shifted-mode metric correlation. The recovery metric " ++
        "now cancels the critical tilt in that limit, making every entry a finite geometric sum of " ++
        "raw eta decay modes. Since every relative mode lies inside the unit disk, all four literal " ++
        "matrix entries eventually satisfy the simultaneous gap-times-correlation bound 2+epsilon " ++
        "over the finite upper window. Lean now contracts these bounds with the exact moving " ++
        "completion coefficients without freezing any " ++
        "coefficient: every actual unweighted complex upper-pair correlation and its packed real " ++
        "part are eventually bounded by the explicit four-term coefficient-gap envelope. Lean " ++
        "now compares its square with both positive atom-coercivity lower bounds, obtaining an " ++
        "eventual lower bound for every actual weighted upper-pair reserve and its ordered-distinct " ++
        "aggregate. The complete reserve is now exactly split into four nonnegative colour sectors, " ++
        "and the upper sector is that aggregate. Hence max(0,upperLower) is an eventual lower bound " ++
        "for the full certificate reserve. One odd-prime choice now also discharges positive " ++
        "definiteness eventually, and Lean proves that the two literal floor inequalities imply " ++
        "respectively >13/18 and 18/18. It remains to prove either antecedent; the next audit asks " ++
        "whether coordinate blocks longer than the zero-window cardinality strengthen the floor. " ++
        "An abstract degree-four " ++
        "nonnegative moment model now yields " ++
        "a universal 13/18 certificate, and a checked three-atom model proves that bound sharp for " ++
        "the five-moment information class. The witness-weighted heat refinement is monotone and " ++
        "converges to the exact certificate, but the sharp model saturates it at every scale. This " ++
        "does not instantiate the eta window. The independent ordinary heat trace now separates " ++
        "strict improvement exactly: it crosses below 5/36 at some nonnegative scale if and only if " ++
        "the certificate is greater than 13/18, while the sharp model never crosses at finite scale. " ++
        "What is not yet proved is either quantitative literal decorrelation premise (and hence the " ++
        "coordinate carrier's arithmetic crossing), another " ++
        "independent observable nonzero on " ++
        "the sharp root channels, the additional normalized " ++
        "moments, a phase-preserving aggregate estimate for the paired cubic one-gap channel, higher " ++
        "closed-path coefficients, or genuinely mixed " ++
        "heat scales, an estimate for the transition paths, or a cross-zero estimate " ++
        "strong enough to improve that triangle bound. The required signed " ++
        "finite-endpoint correlation estimate and the multiplicity-one head " ++
        "estimate remain unproved; the resulting first-moment criterion is equivalent " ++
        "to RH"))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
