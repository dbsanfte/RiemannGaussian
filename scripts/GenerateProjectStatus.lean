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
    label := "Uncapped project improvement beyond the preceding certificate"
    lineOne := "literal simple zeros"
    lineTwo := "HD(1) < C₀ < C₁"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.Zeta23InverseSampling.externalZeta23_montgomeryTaylor_uncapped_strictly_stronger
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
    "    <text x=\"765\" y=\"133\">signed eta flux</text>\n" ++
    "    <text x=\"765\" y=\"153\">summability OPEN</text>\n" ++
    "  </g>\n" ++
    "  <g class=\"goal\">\n" ++
    "    <rect x=\"855\" y=\"114\" width=\"125\" height=\"50\" rx=\"9\"/>\n" ++
    "    <text x=\"917\" y=\"144\">RH</text>\n" ++
    "  </g>\n" ++
    "  <text class=\"frontier\" x=\"20\" y=\"220\">Eta + prime positivity: stronger repeated-zero margin; " ++
      "positive return exponent; uniform weighted bound open.</text>\n" ++
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
        "are explicit. A separate exact dyadic recurrence now controls the entire " ++
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
        "novelty priority is claimed. No uniform transfer estimate " ++
        "to the original current's weighted absolute moment is proved. These " ++
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
