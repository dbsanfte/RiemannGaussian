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
    label := "Exact pole geometry gives an improved multiplicity-sensitive zero-free strip"
    lineOne := "zero-free strip"
    lineTwo := "explicit 1/log"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.nontrivialZetaZero_mem_signedQuadratic_strip
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
    label := "Quantitative harmonic Moebius cancellation bounds the accumulated signed product coefficients across an entire actual inner-truncated inverse region, with every integer remainder retained; the completed quadratic current remains open"
    lineOne := "harmonic Moebius"
    lineTwo := "inverse coefficients"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.exists_pairedEtaInverseInnerCapCoefficient_cubic_rate
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
  { x := 180, y := 229 }
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
    "    <text x=\"765\" y=\"133\">signed eta flux</text>\n" ++
    "    <text x=\"765\" y=\"153\">summability OPEN</text>\n" ++
    "  </g>\n" ++
    "  <g class=\"goal\">\n" ++
    "    <rect x=\"855\" y=\"114\" width=\"125\" height=\"50\" rx=\"9\"/>\n" ++
    "    <text x=\"917\" y=\"144\">RH</text>\n" ++
    "  </g>\n" ++
    "  <text class=\"frontier\" x=\"20\" y=\"300\">Harmonic cancellation bounds signed inverse coefficients; " ++
      "the full inverse-energy estimate and uniform current bound remain open.</text>\n" ++
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
      ("The external two-thirds and Montgomery--Taylor baselines and the checked literal " ++
        "simple-zero constants HD(1) < C0 < C1 remain in the library. The active theorem " ++
        "program proves a uniform critical heat error of 32h on the actual eta support " ++
        "and a full phase-matrix lower bound with explicit dimension cost 32m. The " ++
        "continuous support/gap transfer is exactly the literal eta/gap spectral " ++
        "correlation, with both Fubini exchanges and normalization checked. Independent " ++
        "finite cutoff errors, half-tilted commutator kernel norms, mixed phase inner " ++
        "products, and critical limits are also checked. The critical boundary law " ++
        "now retains bounded Lipschitz complex tests with an explicit error, and " ++
        "its logarithmic distribution limit is proved. The actual complex displacement " ++
        "has the joint cubic-phase and moving-tilt limit, with an explicit phase " ++
        "comparison error and moving-tilt tail bound. A phase-independent polynomial " ++
        "majorant justifies the full Gaussian heat limit; every fixed mixed matrix " ++
        "entry converges, and its limiting Gram has an explicit integral-of-squares " ++
        "formula and real/complex positivity. The actual rescaled overlap now has " ++
        "an exact triangular period average and Wallis inverse-square integral. " ++
        "At every real scale 0 < epsilon <= 1 and lower cutoff 0 < a <= 1, " ++
        "the actual infinite tail has error at most 4*epsilon/a + epsilon/a^2; " ++
        "the signed primitive identity is retained. Exact logarithmic-tail transport " ++
        "and harmonic cutoff cancellation now prove the actual scalar limit " ++
        "D_(1/2)(r)/r - log(1/r) -> gamma_E - log(pi/2), including every constant " ++
        "complex test. The full complex two-endpoint finite-part limit is now " ++
        "proved: W/r - R*integral(F) -> (gamma_E-1)*F(0) + " ++
        "(1-log(pi/2)+d)*F(1), when log(1/r)-R -> d. Its uniform remainder " ++
        "retains the test bound, Lipschitz constant, and scale offset. The Gaussian " ++
        "specialization explicitly includes -log(v). The reflection-closed quadratic/cubic " ++
        "phase now has a proved actual-displacement finite part: its boundary-test " ++
        "comparison error is at most h*exp(4*abs(lambda))*" ++
        "[v^2*(abs(beta)+abs(alpha)*(6+v))/R+3*h]. The complex test retains an explicit " ++
        "Lipschitz constant linear in abs(v) and its exact reflection identity. " ++
        "Gaussian domination after subtraction is now proved for the actual damped complex " ++
        "finite part, with a global cubic polynomial majorant. The complete second-order " ++
        "polynomial heat law evaluates its endpoint coefficient using the logarithmic " ++
        "Gaussian cosine moment. Exact leading-profile reflection then proves the signed " ++
        "limit J(kappa)-exp(-2*lambda)*J(kappa+beta+3*alpha). The full actual mixed " ++
        "polynomial-phase matrix now has its second-order and signed endpoint limits. " ++
        "The sum of absolute entry errors tends to zero for each fixed finite family; " ++
        "simultaneous entry error epsilon gives the explicit cost card(iota)^2*epsilon. " ++
        "The completed-current audit now proves direct signed-heat insertion is zero " ++
        "in both literal multiplicity branches, including the restored head coordinate. " ++
        "Two ordered actual heat commutators instead have an exact negative gap-return " ++
        "pairing with the completed current. Both branches are genuinely integrable " ++
        "at fixed positive intermediate time; the reflected polynomial family discharges " ++
        "all phase and moving-tilt hypotheses. The infinite intermediate-time gap integral " ++
        "is now absolutely convergent at positive total tilt, with Fubini retaining the " ++
        "ordered complex phases and both actual multiplicity carriers. At equal positive " ++
        "tilts and zero probe phases, the exact normalization 8*pi*h^2/M(a), with M(a) " ++
        "the proved positive exponential gap mass, reconstructs the endpoint-damped " ++
        "current as h tends to infinity. Removing the tilt then recovers the original " ++
        "leading flux at each fixed zero and cutoff. The exact normalized gap multiplier " ++
        "and its signed defect integral now give the quantitative error " ++
        "B_N*[a*L_N+(M2(a)/M(a)+2*L_N^2)/h^2], where B_N is the actual absolute " ++
        "completed-kernel mass and L_N=log(2*N+5) bounds both physical times. The actual " ++
        "second gap moment is at most 2/a^3, and for 0<a<=1 its normalized ratio is at " ++
        "most 2/(M(1)*a^3), with M(1)>0 proved. The actual completed kernel mass is now " ++
        "bounded at every cutoff by C_rho*(1+log(2*N+5))^(2*m)/(N+1), with " ++
        "C_rho=2*m*[W_partner/(1-Re(rho))^2+W_rho/Re(rho)^2]. The proof retains " ++
        "the translated simple-zero head and the adjacent centered moments, and " ++
        "substitution supplies the fully explicit arithmetic reconstruction error. " ++
        "The simultaneous tilt a_N=(N+1)^(-2) and width h_N=(N+1)^4 now give the " ++
        "all-cutoff error D_rho*(1+log(2*N+5))^(2*m+2)/(N+1)^3, with " ++
        "D_rho=C_rho*(3+2/M(1)). The odd-weighted norm errors are summable, and the " ++
        "weighted complex error series is retained. A single proved finite error " ++
        "budget bounds the difference of the return and original current's finite " ++
        "first absolute moments at every terminal cutoff. A uniform bound for either " ++
        "moment still requires the signed arithmetic estimate. The actual completed gap " ++
        "return now has an exact continuous heat-composition formula. Full-line composition " ++
        "at a common phase retains exp(a^2*h^2-a*(t+u)) and the broader Gaussian, while " ++
        "the gap return subtracts both the actual eta-support return and the nonpositive-time " ++
        "correction. Both completed multiplicity carriers have full three-time integrability " ++
        "for a>=0 and h>0, including zero tilt, with arbitrary ordered phases retained. " ++
        "A separate actual-gap Gaussian normalization is now proved at zero tilt. Decreasing " ++
        "test masses on consecutive logarithmic intervals bound the gap mass g_h(0) between " ++
        "1/4-log(2)/(4*sqrt(pi)*h) and 1/4, hence by at least 1/8 for h>=2. " ++
        "The actual translated gap mass has error at most 3*c/(2*sqrt(pi)*h) for c>=0. " ++
        "Normalization 4*sqrt(pi)*h/g_h(0) retains the exact midpoint multiplier and " ++
        "gives error at most 13*(1+L)^2/h on the physical window. With zero tilt and " ++
        "h_N=2*(N+1)^2, both actual completed-current branches have weighted error at most " ++
        "13*C_rho*(1+log(2*N+5))^(2*m+2)/(N+1)^2. Its series is summable, and " ++
        "the first absolute moments differ by the explicit finite budget obtained from " ++
        "that majorant. No exponential tilt amplification enters this schedule. The actual " ++
        "cumulative colour A(t) now satisfies abs(A(t)-log(pi/2))<=9*exp(-t) for t>=0. " ++
        "An exact, integrable signed primitive correction then gives " ++
        "abs(g_h(c)-1/4-(c-log(pi/2))/(4*sqrt(pi)*h))<=2*(1+c)^3/h^3 " ++
        "for h>0 and c>=0. Normalizing by g_h(0) cancels the Wallis constant at first " ++
        "order. Both original completed-current branches, including the physical translated " ++
        "head, have their actual midpoint moment M as coefficient: " ++
        "norm(R(h)-J-M/(sqrt(pi)*h))<=19*C_rho*(1+L_N)^(2*m+3)/((N+1)*h^2) " ++
        "for h>=2. The exact signed defect remains available before its norm estimate. " ++
        "The midpoint coefficient is now evaluated in actual finite completed eta moments " ++
        "in both branches. For m>=2 it is L_N*J+(m-1)*delta_(N+1)*Re(Gamma_(m-1,m-1)+Gamma_(m-2,m)); " ++
        "the simple head retains both cutoff origins and its two raised moment pairs. " ++
        "The functional equation isolates a finite reflection defect times the nonzero " ++
        "leading completed moment, with both signed tails retained. It does not make the " ++
        "defect vanish. The actual lower-order zero-tail bounds now prove " ++
        "abs(M_rho(N))<=2*m*(1+L_N)/(N+1)*" ++
        "[Q_partner^2*(2*N+3)^(-(1-Re(rho)))+Q_rho^2*(2*N+3)^(-Re(rho))], " ++
        "where Q_rho=abs(c_rho)+abs(D_rho)+abs(c_rho)*m!/Re(rho)^(m+1), " ++
        "c_rho is the actual completion factor times rho, and D_rho its nonzero leading " ++
        "completed moment. This is a proved arithmetic endpoint gain for the midpoint, " ++
        "not a uniform weighted bound on the original current. At linear width h_N=2*(N+1), " ++
        "the odd-weighted midpoint term is now proved summable using both positive zero " ++
        "coordinates. The remaining weighted defect is at most " ++
        "(19/2)*C_rho*(1+L_N)^(2*m+3)/(N+1)^2. Adding the explicit midpoint majorant " ++
        "gives a summable bound for the full weighted reconstruction error, with both its " ++
        "norm series and signed complex series retained. Its total sum bounds all finite " ++
        "error sums and the difference of the return and current's first absolute moments. " ++
        "The original current now also has an explicit completed Euler endpoint expression " ++
        "with summable odd-weighted arithmetic error. Below the actual multiplicity, each " ++
        "finite moment is the negative genuine tail; its phased Euler error has an extra " ++
        "inverse-cutoff power. The signed pair error retains both product positions and " ++
        "both completion channels. The actual simple-zero head evaluates exactly as a " ++
        "difference of endpoint exponentials. In the repeated-zero branch the common " ++
        "endpoint Fourier phase cancels at the complex product level, leaving two proved " ++
        "positive coefficients with complementary horizontal decay rates. The unchanged " ++
        "linear-width return differs from this same endpoint expression by a summable " ++
        "weighted error, and every finite error sum is bounded by the explicit sum of the " ++
        "arithmetic and heat majorants. Both factors of the original leading current now " ++
        "retain their actual zero-tail decay, giving the weighted pointwise bound " ++
        "4*m*(Q_partner^2*d_partner(N)^2+Q_rho^2*d_rho(N)^2). At a critical-line " ++
        "zero both original real current branches cancel exactly. For every actual zero " ++
        "the return's first absolute moment through cutoff K is now at most " ++
        "C_rho*(K+1)^abs(2*Re(rho)-1), with the positive-displacement denominator " ++
        "handled separately from exact critical-line cancellation. C_rho is explicit in " ++
        "the finite heat budget, completion moments, multiplicity, and displacement. " ++
        "The exponent is strictly less than one, so this same actual moment divided by " ++
        "K+1 tends to zero unconditionally. Its bound without cutoff normalization " ++
        "remains open; that growth estimate alone gives no zero-location constraint. " ++
        "Both actual multiplicity branches now share " ++
        "the signed principal term delta_N*[A_partner*exp(-2*(1-sigma)*L_N)-" ++
        "A_rho*exp(-2*sigma*L_N)], with both actual completion coefficients proved " ++
        "strictly positive. The simple head differs from half the actual logarithmic " ++
        "step at the successor endpoint by an explicit complex defect of size at most " ++
        "D_head*rho_decay(N)/(N+1)^2. Its full two-channel odd-weighted product error " ++
        "is summable. The common endpoint phase cancels exactly at the complex product " ++
        "level before real parts are taken. The unchanged current and linear-width " ++
        "return differ from this same principal expression by summable weighted " ++
        "errors. One explicit convergent sum of the heat, Euler, and head majorants " ++
        "bounds every difference of their first absolute moments. The principal " ++
        "term itself is not bounded independently of cutoff. At a hypothetical actual " ++
        "off-critical zero, the exact signed principal factorization now isolates " ++
        "the slower positive completion coefficient A_dom. The relative faster " ++
        "channel tends to zero, leaving the eventual odd-weighted lower bound " ++
        "c_floor*(N+1)^(e-1), with e=abs(2*Re(rho)-1)>0 and " ++
        "c_floor=(A_dom/5)*5^(e-1)>0. A finite initial-segment allowance and the " ++
        "proved principal error budget give the all-cutoff actual-return bound " ++
        "S_R(rho,K)>=(c_floor/e)*(K+1)^e-D_rho. Consequently the original " ++
        "weighted first absolute moment eventually lies between " ++
        "(c_floor/(2*e))*(K+1)^e and its previously proved C_rho*(K+1)^e " ++
        "upper bound, and tends to infinity under that off-critical hypothesis. " ++
        "The displacement exponent is therefore sharp for the unchanged return. " ++
        "That conditional growth argument alone excludes no off-critical zero. Classical " ++
        "Moebius inversion now gives an exact finite multiplicative constraint on " ++
        "the original completed eta tails. The literal odd-even Dirichlet " ++
        "coefficients convolved with mu are supported exactly at one and two. " ++
        "Regrouping finite divisor fibers gives eta prefixes at floor(M/d), " ++
        "each split into the original paired prefix and its exact odd last term. " ++
        "At every actual zero, the completed zeroth prefix is the negative " ++
        "genuine tail. Their signed aggregate with weights mu(d)*d^(-rho), " ++
        "retaining all endpoint corrections, equals the same nonzero source " ++
        "pairedEtaXiCompletionFactor(rho)*(1-2*2^(-rho)) for every M>=2. " ++
        "Each actual completed divisor term now has the uniform-in-divisor bound " ++
        "C_rho*M^(-Re(rho)), where C_rho=norm(X_rho)*(norm(rho)/Re(rho)+1)*2^Re(rho). " ++
        "The actual diagonal energy is at most C_rho^2*M^(1-2*Re(rho)). " ++
        "The full complex off-diagonal sum equals the source norm squared minus " ++
        "that diagonal energy, and both reflected completion channels remain " ++
        "in an exact signed-pair identity. At a hypothetical actual zero with " ++
        "Re(rho)>1/2, the diagonal tends to zero while the off-diagonal sum " ++
        "tends to the strictly positive source norm squared. Thus the latter " ++
        "cannot be dropped. A further arithmetic estimate now controls the " ++
        "full-period correlation of each fixed odd/even divisor pair. Multiplying " ++
        "each original completed term by its exact complex divisor-times-odd-endpoint " ++
        "power leaves the parity phase mu(d)*X_rho*a(floor(M/d))/2, with error " ++
        "at most 2*H_rho*d/M, where H_rho=norm(X_rho)*norm(rho)*norm(rho+1). " ++
        "For odd d and even e, these leading complex pair phases cancel over " ++
        "every period of length 2*d*e. The actual normalized pair average starting " ++
        "at A>=1 has norm at most H_rho*norm(X_rho)*(d+e)/A+4*H_rho^2*d*e/A^2. " ++
        "The original signed completion pair retains both channel error bounds; " ++
        "its fixed-divisor period average tends to zero at every actual zero. " ++
        "The physical endpoint normalizers, divisor sizes, and period length " ++
        "are explicit. The literal quotient parity matrix now has exact " ++
        "covariance gcd(d,e)^2/(d*e) when both reduced divisors are odd and zero " ++
        "otherwise, with arbitrary-window error at most 4*d*e/L. " ++
        "sum_Icc_pairedEtaDivisorParityCovariance_le_log bounds the whole " ++
        "covariance sum by 2*D*(1+log D). The actual completed family retains " ++
        "both physical endpoint powers in its exact complex Gram. " ++
        "pairedEtaCompletedMoebiusFamilyMeanSquare_le bounds its mean square " ++
        "by norm(X)^2*D*(1+log D)/2+norm(X)^2*D^4/L+" ++
        "2*H*norm(X)*D^3/A+4*H^2*D^4/A^2, for positive A and L. " ++
        "pairedEtaCompletedMoebiusFamilyMeanSquare_le_growing consequently " ++
        "gives K_rho*D*(1+log D) for D>=1 and D^3<=A,L, with " ++
        "K_rho=2*norm(X)^2+2*H*norm(X)+4*H^2. " ++
        "pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute_le_growing " ++
        "retains the original signed reflection channels and bounds their " ++
        "first absolute average by (K_partner+K_rho)*D*(1+log D) in the same " ++
        "cubic range, without assuming a simple or critical-line zero. " ++
        "The individual endpoint powers are now removed from the actual " ++
        "zeroth-order forward Moebius terms. " ++
        "norm_pairedEtaCompletedMoebiusTerm_physical_sub_endpoint_le bounds " ++
        "the complex difference from a common M^rho normalization by B_rho*d/M " ++
        "for every 1<=d<=M, with B_rho=2*norm(rho)*TermConstant(rho). " ++
        "The complete difference is retained as a complex divisor sum and has " ++
        "norm at most B_rho*D^2/M. The unmodified family retains the original " ++
        "complex pair kernel. " ++
        "Exact finite Fourier inversion now proves the literal quotient family's " ++
        "spectrum from its divisor periods. Integer annihilator divisibility " ++
        "gives frequency separation on Q=2*(D!)^2*(4*D^2+L), and finite " ++
        "sampling duality bounds window energy by S*(4*D^2+L) times its " ++
        "complete signed gcd energy, with S=4+16*pi^2. The auxiliary grid " ++
        "cancels. pairedEtaCompletedMoebiusFamilyMeanSquare_le_quadratic " ++
        "gives K2_rho*D*(1+log D) for D>=1 and D^2<=A,L, where " ++
        "K2_rho=5*S*norm(X)^2+8*H^2. " ++
        "pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic proves " ++
        "mean square at most C2_rho*D*(1+log D)*A^(-2*Re(rho)) in this " ++
        "enlarged quadratic range, with C2_rho=2*K2_rho+2*B_rho^2. " ++
        "pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_quadratic " ++
        "bounds the actual signed first absolute average by D*(1+log D)*" ++
        "(C2_partner*A^(-2*(1-Re(rho)))+C2_rho*A^(-2*Re(rho))), retaining both " ++
        "original completion channels without a simplicity hypothesis. " ++
        "Exact binomial center transport now extends the quadratic range to " ++
        "every moment k below the actual analytic zero multiplicity. " ++
        "pairedEtaMomentParityCoefficient_eq evaluates its complex coefficient " ++
        "alpha_k=k!/rho^k. " ++
        "norm_pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero_le " ++
        "bounds norm(M^rho*(U_k-alpha_k*T_0)) by R_k*d/M at every physical " ++
        "divisor and every center between log(M) and log(M+1), with explicit R_k. " ++
        "The full complex family difference consequently has norm at most " ++
        "R_k*D^2/M. pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic " ++
        "proves the original family mean square at its actual center log(M+1) " ++
        "is at most C_k*D*(1+log D)*A^(-2*Re(rho)), where " ++
        "C_k=2*norm(alpha_k)^2*C2_rho+2*R_k^2, for D>=1 and D^2<=A,L. " ++
        "pairedEtaSignedCompletedMomentOriginalMeanAbsolute_adjacent_le_quadratic " ++
        "includes the actual adjacent repeated-zero orders, preserving both " ++
        "completion channels and their complementary decay rates. " ++
        "pairedEtaMomentInverseCenter_mem_interval proves the translated " ++
        "center log(M+1)-log(d) lies between log(q) and log(q+1), q=floor(M/d). " ++
        "norm_pairedEtaCompletedMomentInversePartialTerm_sub_zero_le bounds " ++
        "the actual inverse-entry difference, after multiplication by q^rho, " ++
        "by d^(-Re(rho))*R_k*D^2/q for D<=q. The full inner range equals the " ++
        "original inverse term exactly. Joint control now estimates both actual " ++
        "inverse divisor sums on a physical rectangle. " ++
        "pairedEtaCompletedMomentInverseRectangle_eq_atoms groups them at " ++
        "the exact product n=d*e, with coefficient w(n)=sum_(d<=E,e<=D,de=n) " ++
        "mu(e), retaining the original powers and both center translations. " ++
        "card_Icc_product_collision_le_gcd counts the actual factor collisions, " ++
        "and sum_sq_pairedEtaInverseProductCoefficient_le_log_sq proves " ++
        "sum_(n<=E*D) w(n)^2 <= E*D*(1+log E)^2. The absolute coefficient " ++
        "mass is at most E*D. Every full gcd-covariance row is bounded by " ++
        "the squared harmonic sum, so the exact signed complete-period energy " ++
        "is at most (1+log(E*D))^2 times the retained coefficient energy. " ++
        "The literal quotient periods prove its Fourier support and separation. " ++
        "norm_pairedEtaMomentPhysicalRatio_sub_one_le bounds the actual " ++
        "ratio error by 2*norm(rho)*n/M. The complete rectangle has complex " ++
        "parity amplitude beta_k=X_rho*alpha_k/2 and normalized error at most " ++
        "Gamma_k*(E*D)^2/M, with Gamma_k=2*(H_k+norm(rho)*norm(beta_k)). " ++
        "pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic " ++
        "bounds the unmodified original rectangle at center log(M+1) by " ++
        "Crect_k*E*D*(1+log E)^2*(1+log(E*D))^2*A^(-2*Re(rho)), for " ++
        "E,D>=1, (E*D)^2<=A,L, and k below the full analytic multiplicity. " ++
        "Here Crect_k=10*S*norm(beta_k)^2+2*Gamma_k^2. " ++
        "pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_adjacent_le_quadratic " ++
        "retains the actual adjacent orders and both reflected completion " ++
        "channels with their complementary physical decay rates. The full " ++
        "hyperbolic inverse range d*e<=M, interactions between rectangles, " ++
        "and the unchanged weighted head and mixed current sums still require " ++
        "an independent global cancellation estimate. " ++
        "These estimates do not improve the zero-free strip or prove the " ++
        "original uniform weighted current bound. A separate exact dyadic " ++
        "recurrence controls the entire " ++
        "growing divisor family at each physical cutoff: E(M)=-r*O(floor(M/2)) " ++
        "and O(M)=C+r*O(floor(M/2)) for M>=2, with r=2^(-rho) and " ++
        "C=X_rho*(1-2*r). Since abs(r)<1, B=norm(X_rho)+norm(C)/(1-abs(r)) " ++
        "bounds every odd aggregate, and abs(r)*B bounds every even aggregate. " ++
        "All four full complex parity block sums factor exactly into the " ++
        "corresponding aggregate pairs and have cutoff-independent bounds, " ++
        "including the original signed reflected completion channels. These " ++
        "bounds take the norm after each whole block sum; they do not bound " ++
        "arbitrary divisor feature weights or the original weighted cutoff sum. " ++
        "Finite odd-divisor inversion now reconstructs the original zeroth " ++
        "completed moment exactly as the sum of d^(-rho)*O(floor(2*N/d)) " ++
        "over odd d<=2*N. The original simple-zero current is consequently " ++
        "the exact signed head/inverse sum with both completion channels retained. " ++
        "Taking termwise norms incurs W(M)=sum over odd d<=M of norm(d^(-rho)). " ++
        "The proved bounds M^(1-Re(rho))/2<=W(M)<=(M+1)^(1-Re(rho))/(1-Re(rho)) " ++
        "show that this weight cost diverges at every actual zero, including " ++
        "the critical line. This diagnoses the triangle estimate; it does not " ++
        "show divergence of the original signed current or rule out cancellation " ++
        "in the exact inverse sum. Grouping the entire divided-cutoff-one block " ++
        "at cutoff 4*K now gives the complex main term " ++
        "X_rho*(2*K)^(1-rho)*(2^(1-rho)-1)/(2*(1-rho)), with error at most " ++
        "norm(X_rho)*norm(rho)*(2*K)^(-Re(rho))/2. Its Mellin coefficient " ++
        "is nonzero throughout the critical strip, and the norm of this whole " ++
        "completed inverse block tends to infinity after all its phases are summed. " ++
        "The complementary divided cutoffs have the opposite complex main term " ++
        "with error at most norm(X_rho)*((norm(rho)/Re(rho)+1)*(4*K)^(-Re(rho)) " ++
        "+norm(rho)*(2*K)^(-Re(rho))/2). Their exact sum is the original " ++
        "zeroth completed moment with its actual zero-prefix decay. This proves " ++
        "a cross-cutoff cancellation constraint; it does not exclude off-critical " ++
        "zeros or supply the signed weighted-current bound. An independent arithmetic " ++
        "input now gives an explicit zero-location bound. The literal eta mass proves " ++
        "norm(eta(s))<=norm(s)/Re(s). On rectangles of dyadic imaginary period " ++
        "2*pi/log(2), the factor is bounded away from zero on the boundary; maximum " ++
        "modulus for the entire pole-removed function Z1(s) then yields " ++
        "norm(Z1(s))<=8*(abs(Im(s))+20)^2 throughout 1/2<=Re(s)<=3/2, including " ++
        "all interior dyadic resonances. Cauchy's estimate gives " ++
        "norm(deriv Z1(s))<=32*(abs(Im(s))+21)^2 on 3/4<=Re(s)<=5/4. " ++
        "Mathlib's classical three-four-one prime-product inequality, these actual " ++
        "bounds, and reflection prove delta(Im(rho))<=Re(rho)<=1-delta(Im(rho)) " ++
        "for every nontrivial zero, where delta(y)=min(1/4,abs(y)^5/" ++
        "(16*3200^3*64^4*(abs(y)+21)^10)). Positivity of the original eta mass " ++
        "rules out a zero ordinate, so this explicit margin is positive at every " ++
        "actual zero. The original return consequently satisfies " ++
        "S_R(rho,K)<=C_rho*(K+1)^(1-2*delta(Im(rho))) in both multiplicity " ++
        "branches. This exponent lies in [1/2,1) and still allows cutoff growth. " ++
        "The zero margin is deliberately weak; no improvement over classical " ++
        "analytic zero-free regions or novelty priority is claimed. The full Moebius " ++
        "transform now also evaluates every centered moment order. Its divisor d " ++
        "keeps the center a-log(d), divided cutoff floor(M/d), and exact odd " ++
        "endpoint polynomial. With c=X_rho*rho and Q_k the existing moment " ++
        "antiderivative polynomial, the aggregate is exactly " ++
        "c*(Q_k(-a)-2*2^(-rho)*Q_k(log(2)-a)) for M>=2. An explicit " ++
        "polynomial envelope bounds all cutoffs at every fixed center. Finite " ++
        "inversion with both cutoff and center translations recovers every " ++
        "original completed moment; both current branches consequently have " ++
        "exact signed inverse formulas, including the double divisor sum at " ++
        "adjacent orders for repeated zeros. The inverse weights and moving " ++
        "centers are still uncontrolled in the weighted current estimate. " ++
        "A separate multiplicity argument now strengthens the zero margin. The " ++
        "entire pole-removed zeta function retains the full analytic multiplicity m. " ++
        "The higher-order Schwarz lemma on the eta-bounded quarter-radius disc " ++
        "gives norm(Z1(2-Re(rho)+i*Im(rho)))<=8*(abs(Im(rho))+21)^2*" ++
        "(8*(1-Re(rho)))^m when Re(rho)>=15/16. Combining this actual small " ++
        "value with the same prime-product inequality yields " ++
        "(1-Re(rho))^(4*m-3)>=abs(Im(rho))^5/" ++
        "(16*3200^3*8^(4*m+4)*(abs(Im(rho))+21)^10). The explicit margin " ++
        "Delta_m(y) is the minimum of 1/16 and the positive (4*m-3)-th root " ++
        "of that ratio. Every actual zero satisfies " ++
        "Delta_m(Im(rho))<=Re(rho)<=1-Delta_m(Im(rho)). Lean proves " ++
        "Delta_1(y)=delta(y) and Delta_m(y)>delta(y) for m>=2 and y!=0. " ++
        "Thus the original return has a strictly smaller proved exponent for " ++
        "repeated zeros, while the simple-zero bound is unchanged. The exponent " ++
        "1-2*Delta_m(Im(rho)) remains in [7/8,1). This improves the repository's " ++
        "previous bound; no improvement over classical zero-free regions or " ++
        "novelty priority is claimed. Height-adapted actual finite eta prefixes " ++
        "and their proved tails now give norm(eta(s))<=6*T^epsilon/epsilon " ++
        "when 0<epsilon<=1/2, Re(s)>=1-epsilon, and T>=max(3,norm(s)). " ++
        "Variable-width dyadic rectangles carry this bound through every " ++
        "dyadic resonance. At width 1/L, L=log(abs(y)+21)>2, the actual " ++
        "zero disc has norm(Z1)<=72*(abs(y)+21)*L^2, and Schwarz gives " ++
        "norm(Z1(2-Re(rho)+i*y))<=576*(abs(y)+21)*L^3*(1-Re(rho)) " ++
        "when Re(rho)>=1-1/(16*L). Positive real eta mass also improves " ++
        "the pole estimate to norm(zeta(1+x))<=4/x for 0<x<=1/2. The resulting " ++
        "three-four-one constraint gives delta_log(y)=abs(y)^5/" ++
        "(C*(abs(y)+21)^5*L^14), C=144*4^3*576^4, as a positive " ++
        "two-sided margin at every actual zero. Above abs(y)>=21 the " ++
        "margin is at least 1/(32*C*L^14). Lean proves delta_log(y) " ++
        "strictly exceeds the earlier ordinate-only delta(y) for y!=0. " ++
        "The refined margin max(Delta_m(y),delta_log(y)) preserves both " ++
        "independent estimates and gives the original return exponent " ++
        "1-2*max(Delta_m(y),delta_log(y)), strictly smaller for every " ++
        "actual simple zero. It still lies in [7/8,1). This is weaker " ++
        "than the classical reciprocal-logarithm zero-free region. The signed " ++
        "local logarithmic derivative now improves this margin to " ++
        "delta_signed(y)=abs(y)/(1800000*(abs(y)+1)*log(abs(y)+22)). " ++
        "At every real ordinate the actual translated unit disc for Z1 has " ++
        "norm bound 8*(abs(y)+22)^2 and center floor 1/16 from the safe-line " ++
        "Moebius series. A zero-free sphere of radius between 3/4 and 7/8 " ++
        "permits complete canonical zero removal. Jensen bounds its full " ++
        "multiplicity count by 32*log(abs(y)+22); Borel-Caratheodory and " ++
        "Cauchy bound the residual logarithmic derivative by 320 times that " ++
        "logarithm. The complete regular remainder is bounded by 448 times " ++
        "the logarithm, while every local zero stays in the exact signed pole " ++
        "sum. The genuine multiplicity m contributes -m/(x+1-Re(rho)) " ++
        "to the negative real zeta logarithmic derivative at 1+x+i*Im(rho). " ++
        "The actual convergent von Mangoldt series proves signed three-height " ++
        "3-4-1 positivity. The real-axis bound preserves the leading pole " ++
        "coefficient one: 1/x+28224 for 0<x<=1/28224. Choosing x=4*(1-Re(rho)) " ++
        "and reflecting yields the explicit positive delta_signed margin " ++
        "at both edges for every actual zero. For abs(y)>=1 it is at least " ++
        "1/(3600000*log(abs(y)+22)). Lean proves delta_signed(y)>delta_log(y) " ++
        "at every nonzero ordinate. The maximum with all previous bounds " ++
        "preserves multiplicity information and transports to the unchanged " ++
        "Gaussian return with its original C_rho. The exponent strictly " ++
        "decreases at every actual simple zero but remains in [7/8,1). " ++
        "The exact-pole refinement now applies the local decomposition at " ++
        "height zero on 0<x<=1/4, giving 1/x+448*log(22), and retains " ++
        "the pole's real Cauchy kernel x/(x^2+y^2) at nonzero height. " ++
        "The full signed prime estimate yields 8*m-7 <= " ++
        "56448*log(abs(y)+22)*d+357*d^2/y^2 for d=1-Re(rho)<=1/24. " ++
        "A positive rational subsolution and reflection give " ++
        "delta_quad(m,y)=min(1/24,q*abs(y)/(56448*log(abs(y)+22)*abs(y)+19*q)), " ++
        "where q=8*m-7 for every actual positive analytic multiplicity. " ++
        "Lean proves delta_quad(m,y)>31*delta_signed(y) for y!=0, and " ++
        "delta_quad(m,y)>=1/(56458*log(abs(y)+22)) for abs(y)>=1. " ++
        "The maximum with every preceding margin gives the original " ++
        "current and Gaussian return the exponent 1-2*Delta(m,y), " ++
        "strictly smaller at every actual simple zero and still in [7/8,1). " ++
        "The complete signed zeroth-order inverse energy retains its proved " ++
        "finite weighted transport budget under this bound. " ++
        "This formalises the classical reciprocal-logarithm shape with " ++
        "conservative explicit constants; no novelty priority or improvement " ++
        "over the literature is claimed. An additional local geometric " ++
        "constraint now holds: at abs(y)>=1, " ++
        "put D=1/(6000*log(abs(y)+22)). Every finite set of actual zeros " ++
        "with 1-D<=Re(rho)<1 and abs(Im(rho)-y)<=D has total analytic " ++
        "multiplicity at most one. Reflection gives the same count for " ++
        "0<Re(rho)<=D. The exact complex selected pole sum and its " ++
        "complete complement reconstruct the common local sum before " ++
        "the real prime estimate is taken. Thus any zero in these windows " ++
        "is simple and unique. Distinct zeros in the common right-edge " ++
        "layer at the first zero's ordinate have separation greater than D. " ++
        "Near either edge, simplicity is discharged in the original " ++
        "current's full head inverse formula. These local constraints do " ++
        "not improve the preceding all-zero strip or current exponent. " ++
        "An independent Gaussian reciprocal contour is now checked for the " ++
        "actual function. Put L(y)=log(abs(y)+22) and e(y)=1/(500000*L(y)). " ++
        "Every local divisor point at abs(y)>=2 leaves distance at least " ++
        "3*e(y) from the shifted strip. The normalized residual logarithm " ++
        "has norm at most 40*L(y) on the 5/8 disc; the complete canonical " ++
        "factor cost is at most 32*L(y)*log(2/e(y)), with the exact complex " ++
        "factorization retained. The resulting reciprocal height bound is " ++
        "B_h(y)=16*(abs(y)+1)*exp(40*L(y)+32*L(y)*log(1000000*L(y))). " ++
        "A positive compact floor c for norm(Z1(1+i*y)), abs(y)<=2, is " ++
        "proved, and the eta derivative bound gives w0=min(1/8,c/33856). " ++
        "The genuine reciprocal extension (s-1)/Z1(s) is analytic and " ++
        "bounded by B(T)=max(6/c,B_h(T)) on abs(Re(s)-1)<=w(T), " ++
        "abs(Im(s))<=T, where w(T)=min(w0,e(T)). For " ++
        "T>=max(2,exp(1/(500000*w0))), w(T)=e(T). For T>=2 and a,tau>=0, " ++
        "the actual truncated right-line integral of exp(a*s+tau*s^2)/zeta(s) " ++
        "is bounded by 2*T*B(T)*exp(a*(1-w)+tau*(1-w)^2) plus " ++
        "4*w*B(T)*exp(a*(1+w)+tau*(1+w)^2-tau*T^2). The complete complex " ++
        "contour identity retains both oriented horizontal errors. " ++
        "The actual Gaussian Moebius sum S_tau(a)=sum_n mu(n)*" ++
        "exp(-(a-log(n))^2/(4*tau)) is now proved summable for tau>0. " ++
        "At every sigma>1 its full reciprocal integral equals " ++
        "sqrt(pi/tau)*S_tau(a), with individual integrability, full " ++
        "integrability, and absolute sum-integral exchange discharged. " ++
        "Let D(sigma)=sum_n norm(mu(n)/n^sigma), a proved finite mass. " ++
        "The two infinite tails outside (-T,T] have total norm at most " ++
        "D(sigma)*sqrt(2*pi/tau)*exp(a*sigma+tau*sigma^2-tau*T^2/2). " ++
        "At sigma=1+w(T), adding this tail bound to the two finite-contour " ++
        "terms and dividing by sqrt(pi/tau) bounds abs(S_tau(a)) for " ++
        "a>=0,tau>0,T>=2. The exact arithmetic contour identity retains " ++
        "every complex correction. The unit-time height choice T=a now " ++
        "gives an unconditional eventual cancellation rate. The original " ++
        "eta bound gives D(1+w(T))<=4/w(T), eventually at most " ++
        "2000000*L(T). Put C=max(6/c,16), P=C*(3+4000000*sqrt(2*pi))*exp(2), " ++
        "and G=33000001+abs(log(P)); these are fixed constants. The full " ++
        "reciprocal envelope is at most C*exp(33000000*L(T)^2). At T=a>=22 " ++
        "beyond the proved width threshold, abs(S_1(a)) is at most " ++
        "exp(a-a/(500000*L(a))+G*L(a)^2). Since L(a)^3/a tends to zero, " ++
        "the final actual bound is eventually " ++
        "abs(S_1(a))<=exp(a-a/(1000000*log(a+22))). The threshold is " ++
        "proved to exist, without an asserted numerical starting point. " ++
        "Lean also proves S_1(log(X))/X tends to zero. The actual weighted " ++
        "family W_s,tau(a)=sum_n mu(n)*n^(-s)*exp(-(a-log(n))^2/(4*tau)) " ++
        "is now absolutely summable for every complex s and tau>0. " ++
        "The normalized source F(a)=S_1(a)/exp(a) has a proved global " ++
        "bound. For K_s(v)=exp((1-2*s)*v-v^2/4), exact heat transport gives " ++
        "integral F(a+v)*K_s(v) dv = sqrt(2*pi)*exp((s-1)*a+2*s^2)*W_s,2(a). " ++
        "Individual integrability, summable norm integrals, the complete " ++
        "arithmetic exchange, and dominated convergence are discharged. " ++
        "The terminal theorem complexGaussianMoebiusSum_two_normalized_tendsto_zero " ++
        "proves exp((s-1)*a)*W_s,2(a) tends to zero for every fixed complex s. " ++
        "Its norm consequence is W_s,2(log(X))=o(X^(1-Re(s))). " ++
        "The full normalization phase is retained. The Gaussian cancellation " ++
        "rate is now proved for every fixed positive heat time tau, including " ++
        "arbitrarily small times. Its cumulative source U_tau(a)=integral_{u<=a} " ++
        "S_tau(u) du has U_tau(a)/exp(a) tending to zero. Let M_mu(M) be the " ++
        "ordinary finite Moebius sum, g_tau(v)=exp(-v^2/(4*tau)), and " ++
        "A_tau=sqrt(4*pi*tau). The exact full arithmetic exchange gives " ++
        "U_tau(a)=integral g_tau(v)*M_mu(floor(exp(a+v))) dv. The literal " ++
        "cutoff error is at most exp(a)*integral g_tau(v)*abs(exp(v)-1) dv+A_tau. " ++
        "A positive heat time makes the normalized integral error as small " ++
        "as prescribed; integer rounding is retained. The terminal ordinary " ++
        "theorem moebiusFinitePrefix_div_tendsto_zero proves M_mu(M)/M tends " ++
        "to zero without Gaussian smoothing. Exact discrete Abel summation " ++
        "then proves (M+1)^(s-1)*P_s(M) tends to zero for the actual finite " ++
        "P_s(M)=sum_{1<=n<=M} mu(n)*n^(-s), for each fixed s with 0<Re(s)<1. " ++
        "For every eps>0, norm(P_s(M))<=eps*(M+1)^(1-Re(s))+C_s,eps at all M. " ++
        "The original quotient block D_s(M,q)=sum_{d<=M,M/d=q} mu(d)*d^(-s) " ++
        "equals P_s(M/q)-P_s(M/(q+1)), retaining integer division and phase. " ++
        "One remainder gives norm(D_s(M,q))<=eps*(floor(M/q)+1)^(1-Re(s))+C " ++
        "for every M and q>0. The actual completed zeroth moment block " ++
        "equals D_rho(M,q)*X_rho*etaPrefix(q), including odd last endpoints. " ++
        "The theorem exists_pairedEtaCompletedMoebius_divided_block_remainder " ++
        "retains its completion and the proved factor " ++
        "norm(X_rho)*(norm(rho)/Re(rho)+1)*q^(-Re(rho)). A quantitative " ++
        "shrinking-heat argument now specifies the finite remainder. " ++
        "The normalized absolute cutoff error is at most 9*sqrt(tau) for " ++
        "0<tau<=1/4. The complete cumulative contour bound retains its " ++
        "negative-center Dirichlet integral and all three contour terms. " ++
        "At A(h)=10^15*h^3, T=exp(h), tau=exp(-h), the full contour " ++
        "majorant is at most P*exp(A(h)-h), with a fixed explicit P. " ++
        "The theorem abs_moebiusLogPrefix_cubic_le_eventually gives " ++
        "abs(M_mu(floor(exp(A(h)))))<=C_mu*exp(A(h)-h/2) eventually. " ++
        "One H>=22 gives abs(M_mu(M))<=C_mu*exp(-h/2)*M+exp(A(h)) " ++
        "for every h>=H and integer M. Exact complex Abel summation " ++
        "retains both costs. Put p=1-Re(s), Z_s=sum_n(n+1)^(-Re(s)-1), " ++
        "and C_s=C_mu*(1+norm(s)/p)+(1+norm(s)*Z_s). For every " ++
        "critical-strip s, norm(P_s(M))<=C_s*(M+1)^p*exp(-h/2) " ++
        "when M+1>=exp(2*A(h)/p). The literal quotient coefficient " ++
        "satisfies norm(D_s(M,q))<=2*C_s*U^p*exp(-h/2) for q>0, " ++
        "U=floor(M/q)+1>=exp(2*A(h)/p). The terminal actual theorem " ++
        "exists_pairedEtaCompletedMoebius_divided_block_cubic_rate " ++
        "retains its completion and the same unpaired eta endpoint " ++
        "factor. A common H works for all weights and zeros; the weight " ++
        "dependence remains in C_s and the cutoff. H is existential, " ++
        "without a numerical starting cutoff. The bound retains a " ++
        "positive power scale and proves no fixed power saving. " ++
        "The full finite hyperbola identity now gives an accumulated harmonic bound. " ++
        "For H_mu(D)=sum_{d<=D}mu(d)/d, one H>=22 gives " ++
        "abs(H_mu(D))<=(6+4*C_mu)*exp(-h/8) for h>=H and D>=exp(2*A(h)). " ++
        "The literal ordered harmonic prefixes tend to zero; no unordered " ++
        "or absolute convergence of this series is asserted. On the original " ++
        "inner-truncated physical region e*d<=M, d<=D, the signed product " ++
        "coefficients satisfy sum_{n<=M}c_D(n)=M*H_mu(D)-R(M,D), with " ++
        "every signed Euclidean remainder retained and abs(R(M,D))<=D. " ++
        "The theorem exists_pairedEtaInverseInnerCapCoefficient_cubic_rate " ++
        "therefore gives abs(sum c_D(n))<=(6+4*C_mu)*exp(-h/8)*M+D " ++
        "at every M when D>=exp(2*A(h)). Exact grouping " ++
        "retains the original completed complex atoms before this linear " ++
        "coefficient estimate. It is not an absolute coefficient-mass bound " ++
        "or a quadratic completed-current estimate. " ++
        "Smaller blocks, the complete two-divisor inverse, and " ++
        "both reflected mixed energies still need a stronger joint estimate. " ++
        "This does not improve the zero margin or " ++
        "the current's positive exponent. The uniform cutoff-independent " ++
        "bound for the original current's weighted absolute moment remains open. These " ++
        "auxiliary estimates do not supply the signed completed eta cancellation required " ++
        "for RH. No 13/18 certificate or RH proof is claimed.")),
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
      ("label", .str "Signed completed eta cancellation"),
      ("status", .str "open"),
      ("target", .str
        ("Prove first absolute-moment summability of the actual completed eta leading " ++
          "flux at every nontrivial zero, preserving completion weights, multiplicity, " ++
          "and the simple-zero head term. The new positive support/gap heat estimates " ++
          "do not discharge this RH-equivalent signed arithmetic obligation."))
    ]),
    ("goal", .str "A complete Lean-verified proof of the Riemann hypothesis")
  ]

  liftIO <| IO.FS.createDirAll "docs"
  liftIO <| IO.FS.writeFile "docs/proof-status.json"
    (Json.compress statusJson ++ "\n")
  liftIO <| IO.FS.writeFile "docs/proof-status.svg"
    (renderSvg moduleCount declarationCount theoremCount)
