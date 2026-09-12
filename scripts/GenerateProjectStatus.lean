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
    label := "For every fixed 0<A<1/(140*log(2)), there is a finite coefficient-dependent T(A)>=2 such that actual zeta is nonzero on Re(s)>=1-A*log(log(abs(Im(s))))/log(abs(Im(s))) above T(A). Full-radius signed control bounds the actual residual by 2*E_k/delta_k, retaining possible zeros on the outer sphere and the exact selected radial correction. The derivative order grows as floor(log(log(abs(t)+2))/b), with b>log(2). All moving radius, Euler center and doubled-height costs are controlled on the same schedule; the full normalized budget tends to 140*C*b<1. Both zero-strip edges, complete height bands, and larger marked squarefree arithmetic discs are proved. Thresholds are unevaluated. The independent signed ordinary-prime bound and RH remain open; no optimized published constant or numerical threshold is claimed"
    lineOne := "zero-free: log-log"
    lineTwo := "0<A<1/(140log2)"
    role := "unconditional"
    theoremName :=
      ``RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_nonvanishing
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
    label := "The complete ordered lcm mass has linear cutoff cost with every divisor correction and pair multiplicity retained. The full ordinary-prime correction has exactly three entries per prime and also has linear cost. All pointwise bounded complex divisor-weight families through D_N^3 now have independent error C(rho)*eta^N with eta<1. Their exact unit interaction retains the multiplicity source. This enlarges the complete correlation's divisor range; the independent signed upper bound for the live large-prime tail remains open, and no additional zero is excluded"
    lineOne := "linear lcm cost"
    lineTwo := "families through D_N^3"
    role := "bridge"
    theoremName :=
      ``RiemannGaussian.RoughDivisorLinear.exists_cubic_cutoff_error_bound
  },
  {
    label := "Prime support strengthens every admissible positive phase family's Stechkin transfer to 1-c*exp(-(tau-sigma)*log(2)), at least 6/5 of the preceding factor for 1<sigma<=5/4. The unchanged exact family has actual Stechkin work at least exp(-4*(sigma-1)*log(2))/60. Its complete finite phase energy and the negative completion reserve reach the literal zero budget together. The global signed bound remains open. This phase-transfer estimate alone supplies no further zero exclusion; the current region is displayed separately"
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

/-- Metadata for the closed all-order power estimate, kept separate from
the environment audit to keep the generated command manageable. -/
private def uniformDerivativePowerToolkit : Json :=
  Json.mkObj [
    ("role", .str "Closed classical finite derivative bounds with a single coefficient uniform in order, specialized to the actual complex Dirichlet terms with every analytic hypothesis discharged"),
    ("positiveLagSumTheorem", .str "RiemannGaussian.FiniteLagPowerBounds.weighted_positive"),
    ("negativeLagSumTheorem", .str "RiemannGaussian.FiniteLagPowerBounds.weighted_negative"),
    ("exactAnalyticCountTheorem", .str "RiemannGaussian.AnalyticDerivativeCutoff.count_eq"),
    ("longShiftTheorem", .str "RiemannGaussian.AnalyticDerivativeCutoff.length_lt_ideal"),
    ("completeWeightedStepTheorem", .str "RiemannGaussian.DerivativePowerStep.weighted_budget_le"),
    ("completeSquareBoundTheorem", .str "RiemannGaussian.DerivativePowerStep.argument_le_squares"),
    ("closedRecursionTheorem", .str "RiemannGaussian.UniformDerivativePowerBound.budget_bound"),
    ("genericPhaseTheorem", .str "RiemannGaussian.UniformDerivativePowerBound.phase_bound"),
    ("actualRatioTheorem", .str "RiemannGaussian.UniformDirichletPowerBound.ratio_amp_le_four"),
    ("originalDirichletTheorem", .str "RiemannGaussian.UniformDirichletPowerBound.feature_bound"),
    ("uniformOriginalDirichletTheorem", .str "RiemannGaussian.UniformDirichletPowerBound.uniform_bound"),
    ("exponents", .str "At derivative order k+2: alpha_k=1/(2^(k+2)-2), p_k=2^(-k), beta_k=1-2^(-k). The exact successor identities are all proved"),
    ("analyticCutoff", .str "u=ell^(-2*alpha_(k+1)), H=ceil(u). For 0<ell<=1, 1<=u<=H<=2*u; H>L implies L<u. One exact mathematical rule applies at every order and scale"),
    ("completeStep", .str "The full triangular sum retains every scaled lag through the positive and negative power-sum estimates. The complete successor radicand is at most 258*M^2+256*E^2, with M=A^p_(k+1)*L*ell^alpha_(k+1), E=L^beta_(k+1)*ell^(-alpha_(k+1)). This is at most (32*(M+E))^2"),
    ("genericScope", .str "For every k,L, ell>0 and A>=1, D_k with the analytic cutoff is at most 32*(A^p_k*L*ell^alpha_k+L^beta_k*ell^(-alpha_k)). The bound applies to every genuine derivative family on its original closed interval with positive top derivative between ell and A*ell, uniformly over all prefixes N<=L. No top-derivative monotonicity is assumed"),
    ("completeCases", .str "The square-root base has coefficient 32 for every positive scale. The large-scale branch is covered by the leading term, the rounded count exceeding the length cap by the complementary term, and the empty cap separately. No short-interval or large-scale case is omitted"),
    ("actualDirichletScope", .str "For sigma=Re(s)>=0, t=Im(s)>0, X>0, natural a>=X and a+N<=2*X, ell_k=t*(k+1)!/(2*X)^(k+2). For all k, norm(sum_(n<N) zetaPrimeFeature(s,a+n))<=32*(4*N*ell_k^alpha_k+N^beta_k*ell_k^(-alpha_k))*zetaPrimeExpWeight(sigma,a). The constants are independent of derivative order"),
    ("retainedInformation", .str "The exact arbitrary-cutoff recurrence, original overlap identities, both derivative sign parities and real damping remain upstream. The intermediate feature_bound retains the actual dyadic ratio A_k=2^(k+2); only uniform_bound applies the proved A_k^p_k<=4"),
    ("literature", .str "Classical higher-derivative exponential-sum method, motivated by Yang, JMAA 2024, Section 2, https://arxiv.org/html/2301.03165v2#S2. The coefficient 32 is a coarse proved constant; historical novelty and the paper's optimized constants are not claimed"),
    ("limitations", .str "The complete actual-zeta finite power bound, uniform truncation tail and small-block prefix are now proved in zetaDyadicPowerToolkit. The complete near-one line estimate is now proved in zetaNearOneLineToolkit. The complete local zero detector now proves every fixed logarithmic coefficient eventually in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit. Constants and height thresholds must still be controlled jointly when derivative order grows with height. Extra prime, sieve and moment weights need independent variation or correlation control. These upstream estimates are used by the stronger region in zetaArbitraryLogZeroFreeToolkit; the fixed-ordinate signed prime bound and RH remain open"),
    ("documentation", .str "docs/uniform-dirichlet-power-bound.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.FiniteLagPowerBounds.positive_sum",
      .str "RiemannGaussian.FiniteLagPowerBounds.negative_sum_integral",
      .str "RiemannGaussian.FiniteLagPowerBounds.negative_sum",
      .str "RiemannGaussian.FiniteLagPowerBounds.weighted_positive",
      .str "RiemannGaussian.FiniteLagPowerBounds.weighted_negative",
      .str "RiemannGaussian.DerivativePowerExponents.denominator_ge_two",
      .str "RiemannGaussian.DerivativePowerExponents.alpha_pos",
      .str "RiemannGaussian.DerivativePowerExponents.alpha_le_half",
      .str "RiemannGaussian.DerivativePowerExponents.alpha_zero",
      .str "RiemannGaussian.DerivativePowerExponents.alpha_succ",
      .str "RiemannGaussian.DerivativePowerExponents.alpha_balance",
      .str "RiemannGaussian.DerivativePowerExponents.amp_pos",
      .str "RiemannGaussian.DerivativePowerExponents.amp_le_one",
      .str "RiemannGaussian.DerivativePowerExponents.amp_zero",
      .str "RiemannGaussian.DerivativePowerExponents.amp_succ",
      .str "RiemannGaussian.DerivativePowerExponents.beta_nonneg",
      .str "RiemannGaussian.DerivativePowerExponents.beta_le_one",
      .str "RiemannGaussian.DerivativePowerExponents.beta_zero",
      .str "RiemannGaussian.DerivativePowerExponents.beta_succ",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.ideal_pos",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.count_eq",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.one_le_ideal",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.ideal_le_count",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.count_le_twice",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.length_lt_ideal",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.ideal_mul",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.ideal_positive_power",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.ideal_negative_power",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.count_positive_power",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.count_negative_power",
      .str "RiemannGaussian.AnalyticDerivativeCutoff.inv_count_le",
      .str "RiemannGaussian.DerivativePowerEnvelope.main_nonneg",
      .str "RiemannGaussian.DerivativePowerEnvelope.error_nonneg",
      .str "RiemannGaussian.DerivativePowerEnvelope.main_square",
      .str "RiemannGaussian.DerivativePowerEnvelope.error_square",
      .str "RiemannGaussian.DerivativePowerEnvelope.main_ge_length",
      .str "RiemannGaussian.DerivativePowerEnvelope.error_ge_length",
      .str "RiemannGaussian.DerivativePowerEnvelope.nonneg",
      .str "RiemannGaussian.DerivativePowerEnvelope.base_bound",
      .str "RiemannGaussian.DerivativePowerStep.weighted_budget_le",
      .str "RiemannGaussian.DerivativePowerStep.argument_le",
      .str "RiemannGaussian.DerivativePowerStep.argument_le_squares",
      .str "RiemannGaussian.DerivativePowerStep.successor_bound",
      .str "RiemannGaussian.UniformDerivativePowerBound.budget_bound",
      .str "RiemannGaussian.UniformDerivativePowerBound.phase_bound",
      .str "RiemannGaussian.UniformDirichletPowerBound.ratio_amp_le_four",
      .str "RiemannGaussian.UniformDirichletPowerBound.feature_bound",
      .str "RiemannGaussian.UniformDirichletPowerBound.uniform_bound"
    ])
  ]

/-- Metadata for the complete zeta power bound and the proved small-block range. -/
private def zetaDyadicPowerToolkit : Json :=
  Json.mkObj [
    ("role", .str "Complete finite power bounds for the actual zeta function through exact dyadic eta reconstruction and the proved height-uniform tail, allowing every derivative-order selection; complete small-block prefixes have a uniform height-power bound"),
    ("exactBlockPartitionTheorem", .str "RiemannGaussian.DirichletDyadicBlocks.prefix_pow_two"),
    ("exactEtaTruncationTheorem", .str "RiemannGaussian.DirichletDyadicBlocks.eta_pow_two_eq_blocks"),
    ("exactTransitionTheorem", .str "RiemannGaussian.DirichletPowerParameters.transition_balance"),
    ("positiveFactorialCostTheorem", .str "RiemannGaussian.DirichletPowerCoefficients.factor_positive_power_le_two"),
    ("negativeFactorialCostTheorem", .str "RiemannGaussian.DirichletPowerCoefficients.factor_negative_power_le_two"),
    ("actualBlockProfileTheorem", .str "RiemannGaussian.DirichletBlockPowerProfile.bound"),
    ("completeSmallPrefixTheorem", .str "RiemannGaussian.DirichletCriticalRange.prefix_bound"),
    ("exactZetaReconstructionTheorem", .str "RiemannGaussian.ZetaDyadicTruncation.reconstruction"),
    ("signedTailTheorem", .str "RiemannGaussian.ZetaDyadicTruncation.remainder_eq_adjacent"),
    ("actualTailBoundTheorem", .str "RiemannGaussian.ZetaDyadicTruncation.remainder_bound"),
    ("automaticCutoffTheorem", .str "RiemannGaussian.ZetaDyadicTruncation.depth_scale"),
    ("logarithmicBlockCountTheorem", .str "RiemannGaussian.ZetaDyadicTruncation.depth_le_log"),
    ("completeZetaBoundTheorem", .str "RiemannGaussian.ZetaDyadicPowerBound.canonical_bound"),
    ("widthNormalizedZetaBoundTheorem", .str "RiemannGaussian.ZetaDyadicPowerBound.simple_bound"),
    ("powerProfile", .str "At derivative order k+2, alpha_k=1/(2^(k+2)-2), p_k=2^(-k), beta_k=1-p_k. P_k(sigma,t,X)=256*t^alpha_k*X^(1-sigma-(k+2)*alpha_k)+64*t^(-alpha_k)*X^(beta_k-sigma+(k+2)*alpha_k). The exact factorial profile remains available before applying the uniform constants"),
    ("completeBudget", .str "For every natural-valued order selection r(j), E_j=min(2^(j*(1-sigma)),P_(r(j))(sigma,t,2^j)); B_J=sum_(j<J) E_j. The right-hand side contains only explicit real powers and finite sums, with no unknown phase sum, zeta value or arithmetic cancellation premise"),
    ("canonicalDepth", .str "J=Nat.log 2 (ceil(norm(s))+1). Lean proves norm(s)<=2^(J+1)+1, 2^J<norm(s)+2 and J<=log(norm(s)+2)/log(2)"),
    ("actualZetaScope", .str "For every s=sigma+i*t with 0<sigma<1, t>0, and every order selection, norm(zeta(s)) <= (B_(J+1)+2^(1-sigma)*B_J+(2^(J+1))^(-sigma)+2*(2^(J+1)+1)^(-sigma))/(2^(1-sigma)-1), with canonical J. A coarser theorem gives 6*(B_(J+1)+1)/(1-sigma). Arbitrary cutoffs with the literal tail-scale condition are also allowed"),
    ("retainedInformation", .str "Exact positive-index dyadic partition, complex eta multiplier, negative final endpoint and signed adjacent-ratio tail remain upstream. The finite coupled expression is bounded before any downstream separation of its prefixes. All original Dirichlet damping and factorial factors remain explicit"),
    ("smallBlockRange", .str "On sigma_k=1-(k+2)*alpha_k, v_k=2*(k+2)*alpha_k-p_k>0 and theta_k=1/(k+p_k)>0 satisfy theta_k*v_k=2*alpha_k. Every complete prefix with 2^J<=t^theta_k has norm<=320*J*t^alpha_k. For k>=1, the balanced lines lie in [1/2,1)"),
    ("nextProofTarget", .str "The complete actual-zeta line bound, Gaussian strip localization and signed local zero detector now give every fixed positive logarithmic coefficient in zetaArbitraryLogZeroFreeToolkit. The joint order-height argument now proves the specified log-log region in zetaLogLogZeroFreeToolkit, with complete center and radius costs discharged. The independent signed prime bound remains"),
    ("literature", .str "Classical higher-derivative block strategy motivated by Yang, JMAA 2024, Section 3, https://arxiv.org/html/2301.03165v2#S3. The existing adjacent-ratio eta tail supplies the formal truncation, with its explicit 1/(1-sigma) cost retained. No optimized published constants or historical novelty are claimed"),
    ("limitations", .str "The complete near-one line estimate is now proved in zetaNearOneLineToolkit, with its explicit eta width cost and constants uniform in order and height. The complete local zero detector now proves every fixed logarithmic coefficient eventually in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit. Extra prime, sieve and moment weights need separate control. These upstream estimates are used by the stronger region in zetaArbitraryLogZeroFreeToolkit; the fixed-ordinate signed prime bound and RH remain open"),
    ("documentation", .str "docs/zeta-dyadic-power-bound.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.DirichletDyadicBlocks.feature_eq_cpow",
      .str "RiemannGaussian.DirichletDyadicBlocks.feature_mul",
      .str "RiemannGaussian.DirichletDyadicBlocks.weight_eq_rpow",
      .str "RiemannGaussian.DirichletDyadicBlocks.prefix_succ",
      .str "RiemannGaussian.DirichletDyadicBlocks.block_eq_Ico",
      .str "RiemannGaussian.DirichletDyadicBlocks.prefix_pow_two",
      .str "RiemannGaussian.DirichletDyadicBlocks.eta_pair_eq_features",
      .str "RiemannGaussian.DirichletDyadicBlocks.eta_eq_prefix",
      .str "RiemannGaussian.DirichletDyadicBlocks.eta_pow_two_eq_blocks",
      .str "RiemannGaussian.DirichletPowerParameters.denominator_ge_order",
      .str "RiemannGaussian.DirichletPowerParameters.order_mul_alpha_le_one",
      .str "RiemannGaussian.DirichletPowerParameters.line_nonneg",
      .str "RiemannGaussian.DirichletPowerParameters.line_lt_one",
      .str "RiemannGaussian.DirichletPowerParameters.half_le_line_succ",
      .str "RiemannGaussian.DirichletPowerParameters.amp_alpha_identity",
      .str "RiemannGaussian.DirichletPowerParameters.slope_eq",
      .str "RiemannGaussian.DirichletPowerParameters.slope_pos",
      .str "RiemannGaussian.DirichletPowerParameters.transition_pos",
      .str "RiemannGaussian.DirichletPowerParameters.transition_balance",
      .str "RiemannGaussian.DirichletPowerCoefficients.factor_pos",
      .str "RiemannGaussian.DirichletPowerCoefficients.factorial_le_double_power",
      .str "RiemannGaussian.DirichletPowerCoefficients.double_power_exponent_le_one",
      .str "RiemannGaussian.DirichletPowerCoefficients.factor_positive_power_le_two",
      .str "RiemannGaussian.DirichletPowerCoefficients.factor_negative_power_le_two",
      .str "RiemannGaussian.DirichletPowerCoefficients.lowerScale_eq_factor",
      .str "RiemannGaussian.DirichletPowerCoefficients.scale_power",
      .str "RiemannGaussian.DirichletBlockPowerProfile.profile_nonneg",
      .str "RiemannGaussian.DirichletBlockPowerProfile.exactProfile_le",
      .str "RiemannGaussian.DirichletBlockPowerProfile.exact_bound",
      .str "RiemannGaussian.DirichletBlockPowerProfile.bound",
      .str "RiemannGaussian.DirichletCriticalRange.profile_on_line",
      .str "RiemannGaussian.DirichletCriticalRange.profile_le_on_range",
      .str "RiemannGaussian.DirichletCriticalRange.block_bound",
      .str "RiemannGaussian.DirichletCriticalRange.prefix_bound",
      .str "RiemannGaussian.ZetaDyadicTruncation.factor_eq",
      .str "RiemannGaussian.ZetaDyadicTruncation.reconstruction",
      .str "RiemannGaussian.ZetaDyadicTruncation.remainder_eq_adjacent",
      .str "RiemannGaussian.ZetaDyadicTruncation.remainder_bound",
      .str "RiemannGaussian.ZetaDyadicTruncation.factor_lower",
      .str "RiemannGaussian.ZetaDyadicTruncation.factor_lower_pos",
      .str "RiemannGaussian.ZetaDyadicTruncation.zeta_norm_le",
      .str "RiemannGaussian.ZetaDyadicTruncation.depth_scale",
      .str "RiemannGaussian.ZetaDyadicTruncation.depth_length_lt",
      .str "RiemannGaussian.ZetaDyadicTruncation.depth_le_log",
      .str "RiemannGaussian.ZetaDyadicPowerBound.trivial_block_bound",
      .str "RiemannGaussian.ZetaDyadicPowerBound.block_bound",
      .str "RiemannGaussian.ZetaDyadicPowerBound.blockBudget_nonneg",
      .str "RiemannGaussian.ZetaDyadicPowerBound.prefixBudget_nonneg",
      .str "RiemannGaussian.ZetaDyadicPowerBound.prefixBudget_le_succ",
      .str "RiemannGaussian.ZetaDyadicPowerBound.prefix_bound",
      .str "RiemannGaussian.ZetaDyadicPowerBound.eta_prefix_bound",
      .str "RiemannGaussian.ZetaDyadicPowerBound.zeta_bound",
      .str "RiemannGaussian.ZetaDyadicPowerBound.canonical_bound",
      .str "RiemannGaussian.ZetaDyadicPowerBound.simple_bound"
    ])
  ]

private def zetaNearOneLineToolkit : Json :=
  Json.mkObj [
    ("role", .str "Complete actual-zeta line estimate with the classical derivative-test exponent, all block ranges and the full eta tail discharged, uniformly in derivative order and absolute height at least two"),
    ("adjacentSecantTheorem", .str "RiemannGaussian.DerivativeOrderComparison.adjacent_identity"),
    ("allOrderComparisonTheorem", .str "RiemannGaussian.DerivativeOrderComparison.order_comparison"),
    ("completeTransitionWindowTheorem", .str "RiemannGaussian.DirichletTransitionWindows.profile_le_on_window"),
    ("windowCoverageTheorem", .str "RiemannGaussian.DirichletTransitionWindows.window_cover"),
    ("completeScaleSelectionTheorem", .str "RiemannGaussian.DirichletFullRange.exists_order_bound"),
    ("logarithmicBlockCountTheorem", .str "RiemannGaussian.ZetaNearOneLineBudget.canonical_count_le"),
    ("dischargedFiniteBudgetTheorem", .str "RiemannGaussian.ZetaNearOneLineBudget.exists_prefix_budget_bound"),
    ("actualZetaLineTheorem", .str "RiemannGaussian.ZetaNearOneLineBound.bound_abs"),
    ("displacementFormTheorem", .str "RiemannGaussian.ZetaNearOneLineBound.bound_displacement"),
    ("scope", .str "For k>=1, alpha_k=1/(2^(k+2)-2), delta_k=(k+2)*alpha_k and sigma_k=1-delta_k: abs(t)>=2 implies norm(zeta(sigma_k+i*t))<=32768/delta_k*abs(t)^alpha_k*log(abs(t)). No finite-budget, order-selection or tail premise remains"),
    ("exactComparison", .str "alpha_r-alpha_(r+1)=theta_(r+1)*(delta_r-delta_(r+1)); alpha_r+theta_(r+1)*(delta_k-delta_r)<=alpha_k for every r<=k. Both delta and theta decrease. Exact profile exponents and complementary balance remain named upstream identities"),
    ("completeBudget", .str "Every positive scale X<=4t has a proved order r<=k with profile<=512*t^alpha_k. The canonical budget B_(J+1)<=512*(J+1)*t^alpha_k and J+1<=8*log(t). The eta tail and endpoint are fully included"),
    ("costs", .str "The constant 32768 is coarse and uniform in k and abs(t)>=2. The eta division cost 1/delta_k remains explicit; no optimized published coefficient is claimed"),
    ("retainedInformation", .str "Exact complex eta multiplier, signed final endpoint and full adjacent-ratio tail remain in zetaDyadicPowerToolkit. Both terms of each derivative profile are kept until their endpoint comparison. Conjugation covers both signs of the ordinate"),
    ("nextProofTarget", .str "The complete positive-log vertical integral and finite signed windows are proved in zetaSechLogarithmicToolkit. The alternative canonical local-disc route now proves every fixed logarithmic coefficient and transports it in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit; the separate full signed vertical limit must retain its negative mass"),
    ("literature", .str "Classical changing-order strategy in Yang, JMAA 2024, Section 3, https://arxiv.org/html/2301.03165v2#S3. The repository eta tail gives a different truncation with an explicit width cost. External stronger regions remain unformalized targets, not assumptions"),
    ("limitations", .str "No larger zero-free region is proved by this line estimate alone. Additional prime, sieve and moment weights need independent control. The fixed-ordinate signed ordinary-prime bound and RH remain open. No historical novelty or optimized published constants are claimed"),
    ("documentation", .str "docs/zeta-near-one-line-bound.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.DerivativeOrderComparison.delta_eq_one_sub_line",
      .str "RiemannGaussian.DerivativeOrderComparison.delta_pos",
      .str "RiemannGaussian.DerivativeOrderComparison.alpha_succ_le_half",
      .str "RiemannGaussian.DerivativeOrderComparison.delta_succ_le",
      .str "RiemannGaussian.DerivativeOrderComparison.delta_antitone",
      .str "RiemannGaussian.DerivativeOrderComparison.transition_succ_le",
      .str "RiemannGaussian.DerivativeOrderComparison.transition_antitone",
      .str "RiemannGaussian.DerivativeOrderComparison.transition_zero",
      .str "RiemannGaussian.DerivativeOrderComparison.adjacent_identity",
      .str "RiemannGaussian.DerivativeOrderComparison.order_comparison",
      .str "RiemannGaussian.DerivativeOrderComparison.amp_le_delta",
      .str "RiemannGaussian.DerivativeOrderComparison.half_le_line",
      .str "RiemannGaussian.DirichletTransitionWindows.profile_on_later_line",
      .str "RiemannGaussian.DirichletTransitionWindows.complementary_balance",
      .str "RiemannGaussian.DirichletTransitionWindows.profile_le_on_window",
      .str "RiemannGaussian.DirichletTransitionWindows.window_cover",
      .str "RiemannGaussian.DirichletTransitionWindows.exists_order_bound",
      .str "RiemannGaussian.DirichletFullRange.profile_le_above_height",
      .str "RiemannGaussian.DirichletFullRange.exists_order_bound",
      .str "RiemannGaussian.ZetaNearOneLineBudget.norm_le_height_add_one",
      .str "RiemannGaussian.ZetaNearOneLineBudget.canonical_scale_le",
      .str "RiemannGaussian.ZetaNearOneLineBudget.canonical_count_le",
      .str "RiemannGaussian.ZetaNearOneLineBudget.exists_block_order",
      .str "RiemannGaussian.ZetaNearOneLineBudget.exists_prefix_budget_bound",
      .str "RiemannGaussian.ZetaNearOneLineBound.bound",
      .str "RiemannGaussian.ZetaNearOneLineBound.bound_abs",
      .str "RiemannGaussian.ZetaNearOneLineBound.bound_displacement"
    ])
  ]

private def zetaSechLogarithmicToolkit : Json :=
  Json.mkObj [
    ("role", .str "Complete all-height logarithmic profiles, genuinely integrable full positive vertical zeta averages and finite signed windows through the divisor, retaining the entire negative logarithmic mass"),
    ("allHeightTheorem", .str "RiemannGaussian.ZetaNearOneLogProfile.all_height_bound"),
    ("positiveLogTheorem", .str "RiemannGaussian.ZetaNearOneLogProfile.posLog_bound"),
    ("exactLogProfileTheorem", .str "RiemannGaussian.ZetaNearOneLogProfile.profile_eq_log"),
    ("logarithmicShiftTheorem", .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.profile_shift_le"),
    ("fullPositiveIntegrabilityTheorem", .str "RiemannGaussian.ZetaSechVerticalBound.integrable_integrand"),
    ("fullPositiveIntegralTheorem", .str "RiemannGaussian.ZetaSechVerticalBound.integral_bound_simple"),
    ("positiveTruncationLimitTheorem", .str "RiemannGaussian.ZetaSechVerticalBound.truncation_tendsto"),
    ("zeroOrdinateNullityTheorem", .str "RiemannGaussian.ZetaSechSignedWindows.ae_vertical_ne_zero"),
    ("signedWindowIntegrabilityTheorem", .str "RiemannGaussian.ZetaSechSignedWindows.intervalIntegrable_signed"),
    ("exactSignDecompositionTheorem", .str "RiemannGaussian.ZetaSechSignedWindows.window_exact"),
    ("negativeMassRetainedBoundTheorem", .str "RiemannGaussian.ZetaSechSignedWindows.window_bound_with_negative"),
    ("signedWindowBoundTheorem", .str "RiemannGaussian.ZetaSechSignedWindows.window_bound_simple"),
    ("negativeWindowMonotonicityTheorem", .str "RiemannGaussian.ZetaSechSignedWindows.negative_window_mono"),
    ("scope", .str "For every k>=1 and real t,a: sigma_k=1-delta_k, H(t)=abs(t)+2, M_k(t)=log(32768/delta_k)+alpha_k*log(H(t))+log(log(H(t))). The full integral of log^+ norm(zeta(sigma_k+i*(t+a*u)))/(2*cosh(u)^2) is at most 2*M_k(t)+6*abs(a)/H(t). Every ordered finite signed-log window obeys this same upper bound"),
    ("completeHeightRange", .str "The short eta prefix and complete tail give norm(zeta(s))<=16/(1-Re(s)) for abs(Im(s))<=2 and 1/2<=Re(s)<1. The near-one line theorem then extends to all ordinates using H(y)=abs(y)+2. No full-tail pointwise bound is inferred from a finite-height hypothesis"),
    ("exactSignInformation", .str "The actual signed integrand equals the positive integrand minus the nonnegative negative integrand. Every finite signed window equals that exact difference of genuine integrals and is bounded above by 2*M_k(t)+2*B_k(t,a) minus its full negative mass. Negative mass increases with symmetric window size"),
    ("shiftCost", .str "B_k(t,a)=(alpha_k+1/log(H(t)))*abs(a)/H(t)<=3*abs(a)/H(t). Two concave-log tangent inequalities pay for every shift. The explicit order cost log(32768/delta_k) remains in the profile"),
    ("kernelCost", .str "The original density K(u)=1/(2*cosh(u)^2) is retained. The downstream envelope exp(-abs(u)) has exact mass and absolute first moment 2. Exact moments of K itself are not computed in this slice"),
    ("zeroSingularities", .str "Real analyticity and Mathlib meromorphic log integrability prove genuine integrability through zeros on every finite interval. For a!=0 the zero ordinates are countable and null, so the assigned real-log value at zero is immaterial. At a=0 the formulas use Mathlib real log; a constant zero parametrization is not an ordinary log potential"),
    ("nextProofTarget", .str "The finite-disc alternative now proves every fixed positive logarithmic zero-free coefficient in zetaArbitraryLogZeroFreeToolkit. Complete canonical factors retain the coupled pole correction, actual Gaussian strip growth bounds the residual, and the complete prime budget has its fixed-order limit. The downstream joint-order budget now proves the specified log-log width in zetaLogLogZeroFreeToolkit. Next retain the signed prime envelope in the smaller arithmetic domain and seek the independent ordinary-prime bound. The full signed vertical limit remains open on the contour route; retain its negative mass and multiplicities"),
    ("literature", .str "Yang, JMAA 2024, Section 4, https://arxiv.org/html/2301.03165v2#S4. The repository proof uses its all-height eta bound and a coarse complete Laplace envelope. No optimized published numerical constant or zero-free region is imported as an assumption"),
    ("limitations", .str "Full-line integrability of the negative logarithmic part and a finite full signed limit are not proved. No larger zero-free region follows from these estimates alone. The fixed-ordinate signed ordinary-prime bound and RH remain open. No historical novelty is claimed"),
    ("documentation", .str "docs/zeta-sech-vertical-bound.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.ZetaNearOneLogProfile.eta_prefix_bound",
      .str "RiemannGaussian.ZetaNearOneLogProfile.low_height_bound",
      .str "RiemannGaussian.ZetaNearOneLogProfile.two_le_height",
      .str "RiemannGaussian.ZetaNearOneLogProfile.all_height_bound",
      .str "RiemannGaussian.ZetaNearOneLogProfile.coefficient_ge_two",
      .str "RiemannGaussian.ZetaNearOneLogProfile.one_le_majorant",
      .str "RiemannGaussian.ZetaNearOneLogProfile.profile_eq_log",
      .str "RiemannGaussian.ZetaNearOneLogProfile.profile_nonneg",
      .str "RiemannGaussian.ZetaNearOneLogProfile.posLog_bound",
      .str "RiemannGaussian.ZetaNearOneLogProfile.continuous_positiveLog",
      .str "RiemannGaussian.ZetaNearOneLogProfile.positiveLog_le",
      .str "RiemannGaussian.SechVerticalKernel.density_nonneg",
      .str "RiemannGaussian.SechVerticalKernel.continuous_density",
      .str "RiemannGaussian.SechVerticalKernel.density_le_exp",
      .str "RiemannGaussian.SechVerticalKernel.integrable_abs_extension",
      .str "RiemannGaussian.SechVerticalKernel.integrable_exp_abs",
      .str "RiemannGaussian.SechVerticalKernel.integrable_abs_mul_exp",
      .str "RiemannGaussian.SechVerticalKernel.integral_exp_abs",
      .str "RiemannGaussian.SechVerticalKernel.integral_abs_mul_exp",
      .str "RiemannGaussian.SechVerticalKernel.integrable_affine",
      .str "RiemannGaussian.SechVerticalKernel.integral_affine",
      .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.log_le_tangent",
      .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.height_shift_le",
      .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.shiftCost_nonneg",
      .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.shiftCost_le",
      .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.profile_shift_le",
      .str "RiemannGaussian.ZetaLogarithmicShiftAllowance.positiveLog_shift_le",
      .str "RiemannGaussian.ZetaSechVerticalBound.integrand_eq",
      .str "RiemannGaussian.ZetaSechVerticalBound.integrand_nonneg",
      .str "RiemannGaussian.ZetaSechVerticalBound.continuous_integrand",
      .str "RiemannGaussian.ZetaSechVerticalBound.integrand_le",
      .str "RiemannGaussian.ZetaSechVerticalBound.integrable_integrand",
      .str "RiemannGaussian.ZetaSechVerticalBound.integral_bound",
      .str "RiemannGaussian.ZetaSechVerticalBound.integral_bound_simple",
      .str "RiemannGaussian.ZetaSechVerticalBound.truncation_tendsto",
      .str "RiemannGaussian.ZetaSechSignedWindows.analyticAt_vertical",
      .str "RiemannGaussian.ZetaSechSignedWindows.countable_zero_ordinates",
      .str "RiemannGaussian.ZetaSechSignedWindows.ae_vertical_ne_zero",
      .str "RiemannGaussian.ZetaSechSignedWindows.intervalIntegrable_log",
      .str "RiemannGaussian.ZetaSechSignedWindows.signedIntegrand_eq",
      .str "RiemannGaussian.ZetaSechSignedWindows.signed_eq_positive_sub_negative",
      .str "RiemannGaussian.ZetaSechSignedWindows.negativeIntegrand_nonneg",
      .str "RiemannGaussian.ZetaSechSignedWindows.intervalIntegrable_signed",
      .str "RiemannGaussian.ZetaSechSignedWindows.intervalIntegrable_negative",
      .str "RiemannGaussian.ZetaSechSignedWindows.window_exact",
      .str "RiemannGaussian.ZetaSechSignedWindows.window_bound_with_negative",
      .str "RiemannGaussian.ZetaSechSignedWindows.window_bound",
      .str "RiemannGaussian.ZetaSechSignedWindows.window_bound_simple",
      .str "RiemannGaussian.ZetaSechSignedWindows.negative_window_mono"
    ])
  ]

private def fullRadiusZeroFreeToolkit : Json :=
  Json.mkObj [
    ("role", .str "The actual zeta detector uses the entire strip-width radius without assuming its outer boundary is zero-free"),
    ("boundarySequenceTheorem", .str "RiemannGaussian.AnalyticDiscBoundarySequence.exists_sphere_tendsto"),
    ("generalCanonicalTheorem", .str "RiemannGaussian.AnalyticDiscCanonicalControl.exists_controlled_decomp"),
    ("actualFullDiscTheorem", .str "RiemannGaussian.ZetaNearOneFullDisc.analyticOnNhd_translated"),
    ("actualSignedBoundTheorem", .str "RiemannGaussian.ZetaNearOneFullRadius.neg_logDeriv_re_le_sub_zero"),
    ("actualPrimeTheorem", .str "RiemannGaussian.ZetaFullRadiusPrimeBudget.source_le_budget"),
    ("pointwiseContradictionTheorem", .str "RiemannGaussian.ZetaFullRadiusPrimeBudget.one_le_cost_of_zero_near"),
    ("actualZeroFreeTheorem", .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_strip"),
    ("arithmeticTransportTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_response_bound"),
    ("geometry", .str "For k>=2, delta_k<=2/7. Every center x with 0<x<=delta_k/4 has its entire radius-delta_k disc in the proved Gaussian strip. A complete finite divisor gives positive zero-free radii r_n<delta_k tending to delta_k, whether or not the outer sphere contains zeros"),
    ("signedEndpoint", .str "For every selected actual zero with d=x+1-beta<delta_k, Re(-logDeriv(zeta,c))<=2*E_k/delta_k-m_rho*(1/d-d/delta_k^2). The complete complex canonical identity is retained on each approximating circle; the source multiplicity and radial correction pass together to the endpoint"),
    ("primeBudget", .str "B_k(x,t)=1344*log(22)+(8*E_k(x,t)+2*E_k(x,2*t))/delta_k. Actual three-height prime positivity gives 4*m_rho*(1/d-d/delta_k^2)<=3/x+B_k. At x=6*u, an actual zero in margin u with 28*u<delta_k forces 14*u*B_k+392*(u/delta_k)^2>=1"),
    ("jointLimit", .str "Along k=floor(log(log(abs(t)+2))/b), u=C*log(log(abs(t)+2))/log(abs(t)+2), b>log(2), the whole budget satisfies u*B_k->10*C*b and its normalized contradiction cost tends to 140*C*b. The condition k>=2 holds eventually on the same schedule"),
    ("region", .str "For every fixed 0<A<1/(140*log(2)), actual nontrivial zeros eventually satisfy A*log(log(abs(t)))/log(abs(t))<beta<1-A*log(log(abs(t)))/log(abs(t)). Each coefficient has a finite existential unevaluated threshold. Complete bands and marked squarefree arithmetic transport use the same larger range"),
    ("nextProofTarget", .str "Retain the angular boundary growth profile beyond the uniform maximum, or prove stronger near-one growth using additional exponential-sum machinery. Neither a wider squarefree disc nor known subexponential prime-number-theorem errors alone gives the independent signed ordinary-prime lower bound"),
    ("limitations", .str "No optimum coefficient, numerical starting height, historically novel zero-free region or RH proof is claimed. The full chosen radius is delta_k; the result does not assert it is the largest possible analytic disc. The independent signed ordinary-prime lower bound and growing-set phase envelope remain open"),
    ("documentation", .str "docs/zeta-full-radius-zero-free.md"),
    ("newPublicTheorems", .arr #[
      .str "RiemannGaussian.AnalyticDiscBoundarySequence.exists_sphere_between",
      .str "RiemannGaussian.AnalyticDiscBoundarySequence.exists_sphere_tendsto",
      .str "RiemannGaussian.AnalyticDiscCanonicalControl.exists_controlled_decomp",
      .str "RiemannGaussian.ZetaNearOneFullDisc.delta_le_two_sevenths",
      .str "RiemannGaussian.ZetaNearOneFullDisc.disc_geometry",
      .str "RiemannGaussian.ZetaNearOneFullDisc.analyticOnNhd_translated",
      .str "RiemannGaussian.ZetaNearOneFullDisc.norm_translated_le",
      .str "RiemannGaussian.ZetaNearOneFullRadius.controlled_decomp_at_radius",
      .str "RiemannGaussian.ZetaNearOneFullRadius.neg_logDeriv_re_le_at_radius",
      .str "RiemannGaussian.ZetaNearOneFullRadius.neg_logDeriv_re_le_sub_zero_at_radius",
      .str "RiemannGaussian.ZetaNearOneFullRadius.neg_logDeriv_re_le",
      .str "RiemannGaussian.ZetaNearOneFullRadius.neg_logDeriv_re_le_sub_zero",
      .str "RiemannGaussian.ZetaFullRadiusPrimeBudget.source_le_budget",
      .str "RiemannGaussian.ZetaFullRadiusPrimeBudget.one_le_cost_of_zero_near",
      .str "RiemannGaussian.ZetaFullRadiusPrimeBudget.budget_abs",
      .str "RiemannGaussian.ZetaFullRadiusPrimeBudget.cost_abs"
    ])
  ]

private def caratheodoryZeroFreeToolkit : Json :=
  Json.mkObj [
    ("role", .str "Sharp classical center derivative control, propagated through the actual canonical zeta residual to a larger proved zero-free coefficient range"),
    ("generalTheorem", .str "RiemannGaussian.AnalyticDiscCaratheodory.norm_deriv_zero_le"),
    ("logarithmicTheorem", .str "RiemannGaussian.AnalyticDiscLogarithm.norm_logDeriv_center_le_sharp"),
    ("actualResidualTheorem", .str "RiemannGaussian.ZetaNearOneCanonical.exists_controlled_decomp"),
    ("actualRegionTheorem", .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_strip"),
    ("arithmeticTransportTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_response_bound"),
    ("retainedInformation", .str "Schwarz is applied directly to f/(2*M-f) at the center. The entire complex derivative survives; complete signed zero poles remain coupled to their canonical corrections and actual multiplicities"),
    ("generalBound", .str "For M,R>0, holomorphic f on the open radius-R disc, f(0)=0 and Re(f)<=M, norm(f'(0))<=2*M/R. A nonvanishing analytic g with norm(g)<=exp(B) and -log(norm(g(0)))<=C therefore satisfies norm(logDeriv(g,0))<=2*(B+C)/R when B+C>0"),
    ("actualCost", .str "The sharp center estimate is used by the subsequent full-radius toolkit, which bounds the actual residual by 2*E_k/delta_k and gives limiting cost 140*C*b. The earlier intermediate-radius canonical estimate remains available as its own weaker theorem"),
    ("nextAnalyticTarget", .str "Bellotti's published Vinogradov--Korobov proof uses a near-one zeta growth exponent proportional to (1-sigma)^(3/2). Its uniform exponential-sum and Vinogradov mean-value input is not proved by the repository's present derivative recursion. The external region is a research restriction pending its own complete Lean proof"),
    ("limitations", .str "This is a classical analytic estimate and a concrete improvement to this repository's theorem, not a novel zero-free region in the literature. Neither an optimized published constant nor a numerical threshold is reproduced. The independent signed ordinary-prime bound and RH remain open"),
    ("documentation", .str "docs/zeta-caratheodory-zero-free.md"),
    ("newPublicTheorems", .arr #[
      .str "RiemannGaussian.AnalyticDiscCaratheodory.norm_deriv_zero_le",
      .str "RiemannGaussian.AnalyticDiscLogarithm.norm_logDeriv_center_le_sharp"
    ])
  ]

private def zetaLogLogZeroFreeToolkit : Json :=
  Json.mkObj [
    ("role", .str "Unconditional actual zero-free width A*log(log(abs(t)))/log(abs(t)) for every fixed 0<A<1/(140*log(2)), with the entire moving-order, center, radius and actual prime budget discharged"),
    ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_strip"),
    ("literalNonvanishingTheorem", .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_nonvanishing"),
    ("completeBandTheorem", .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_common_margin"),
    ("allLogarithmicPowersTheorem", .str "RiemannGaussian.LogLogDerivativeSchedule.pow_log_div_width_tendsto"),
    ("exactLeadingSplitTheorem", .str "RiemannGaussian.ZetaLogLogCorrection.allowance_eq"),
    ("fullMovingCenterTheorem", .str "RiemannGaussian.ZetaLogLogCorrection.center_log_le"),
    ("fullCorrectionDecayTheorem", .str "RiemannGaussian.ZetaLogLogCorrection.normalized_correction_tendsto"),
    ("exactTwoHeightLeadingTheorem", .str "RiemannGaussian.ZetaLogLogBudget.leading_identity"),
    ("generalEvaluationLimitTheorem", .str "RiemannGaussian.ZetaLogLogBudget.normalized_allowance_tendsto"),
    ("completeBudgetLimitTheorem", .str "RiemannGaussian.ZetaLogLogBudget.cost_tendsto"),
    ("actualScheduledExclusionTheorem", .str "RiemannGaussian.ZetaLogLogExclusion.exists_eventual_margin"),
    ("fullCoefficientTransferTheorem", .str "RiemannGaussian.ZetaLogLogWidth.eventually_le_smoothed"),
    ("widthImprovementTheorem", .str "RiemannGaussian.ZetaLogLogWidth.eventually_dominates_logarithmic"),
    ("actualArithmeticRadiusTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_radius_spec"),
    ("allMarkedArithmeticTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_response_bound"),
    ("strongerFixedMarkDecayTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_coefficient_scaled_decay"),
    ("jointSchedule", .str "H(t)=abs(t)+2, L(t)=log(H(t)), ell(t)=log(L(t)), k(t)=floor(ell(t)/b), b>log(2), alpha_k=1/(2^(k+2)-2), delta_k=(k+2)*alpha_k, u(t)=C*ell(t)/L(t), x(t)=6*u(t). The same growing order, height and center are used in every estimate"),
    ("fullWidthPowerSaving", .str "For every b>log(2), p=log(2)/b<1 and 1/delta_(k(t))<=4*L(t)^p. Every fixed natural n has ell(t)^n/(L(t)*delta_(k(t)))->0. The original leading ratio ell(t)/(k(t)+2)->b includes the natural floor and order offset"),
    ("exactCorrection", .str "E_k(x,v)=alpha_k*L(v)+R_k(x,v), where R_k=log(32768/delta_k)+14+log(L(v))+log(1+1/x). The full actual Euler center logarithm satisfies log(1+1/x(t))<=log(1+1/(6*C))+ell(t), and log(32768/delta_(k(t)))<=log(131072)+p*ell(t)"),
    ("generalEvaluationDecay", .str "For every fixed D>0 and evaluation v(t) with eventually log(L(v(t)))>=0 and L(v(t))<=D*L(t), the complete normalized correction u(t)*R_(k(t))(x(t),v(t))/delta_(k(t))->0. If L(v(t))/L(t)->q, then u(t)*E_(k(t))(x(t),v(t))/delta_(k(t))->C*b*q. The actual first and doubled ordinates both have q=1"),
    ("actualPrimeLimit", .str "B_k(x,t)=1344*log(22)+(8*E_k(x,t)+2*E_k(x,2*t))/delta_k. The whole actual budget satisfies u(t)*B_(k(t))(x(t),t)->10*C*b. The full-radius contradiction cost 14*u(t)*B_(k(t))(x(t),t)+392*(u(t)/delta_(k(t)))^2 tends to 140*C*b"),
    ("actualContradiction", .str "An actual zero with 1-Re(rho)<=u(Im(rho)) forces the full-radius cost to be at least one. Along the joint schedule k>=2, u>0 and 28*u<delta all hold eventually. For every 140*C*log(2)<1 choose log(2)<b<1/(140*C), making the complete cost eventually below one. All analytic multiplicity, prime and geometric conditions are discharged"),
    ("ordinaryCoefficientRange", .str "For every fixed 0<A<1/(140*log(2)), choose A<C<1/(140*log(2)). The smoothed logarithmic ratio tends to one, so the ordinary width for A is eventually bounded by the smoothed width for C. This preserves the full open coefficient range, without a fixed fractional loss. The coefficient limit is not claimed optimal"),
    ("completeBand", .str "The width w_A(H)=A*log(log(H))/log(H) is positive and antitone for H>=exp(exp(1)) and tends to zero. Its actual eventual zero theorem therefore gives the same width for every zero below H at sufficiently large H, including the complete low divisor. The elementary monotonicity height is not the zero-exclusion threshold"),
    ("actualRadius", .str "For every eligible coefficient and sufficiently large abs(y), the actual quotient zeta(s)/zeta(2*s) is analytic on a neighborhood of the full closed disc of radius R_A(y)=1+A*log(log(2*abs(y)+3))/(2*log(2*abs(y)+3)) about 3/2+i*y. Both poles and all doubled-denominator zeros are excluded first"),
    ("arithmeticGain", .str "Every finite excluded prime set, valid squarefree mark, complex polynomial and moment order receives the genuine Cauchy bound with its signed two-harmonic envelope retained. For every fixed 0<=A<B<1/(140*log(2)) and fixed valid marks, at sufficiently large abs(y), R_A(y)<R_B(y) and the full marked response times R_A(y)^N tends to zero"),
    ("nextProofTarget", .str "Use the larger proved bands and arithmetic discs while retaining the growing-set prime-phase envelope and the separate ordinary-prime source. Seek an independent signed estimate or a richer identity for that source. Stronger published Vinogradov--Korobov bounds remain a possible source of tools and narrower edge domains"),
    ("literature", .str "The higher-derivative and Littlewood strategy is classical; see Yang, JMAA 2024, https://arxiv.org/html/2301.03165v2. The repository uses its own complete eta, Gaussian and canonical-factor chain with coarse constants. No optimized published coefficient, finite starting height or external zero-free axiom is claimed"),
    ("limitations", .str "Each coefficient has an existential unevaluated threshold. The displayed coefficient range is a proved sufficient range, not an optimum. The full squarefree quotient differs from the separate ordinary-prime source; stronger fixed-mark decay does not give a uniform growing-prime-set envelope or the independent cofinal signed lower bound. RH remains open; no historical novelty claim"),
    ("documentation", .str "docs/zeta-log-log-zero-free.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.LogLogDerivativeSchedule.index_atTop",
      .str "RiemannGaussian.LogLogDerivativeSchedule.index_div_log",
      .str "RiemannGaussian.LogLogDerivativeSchedule.log_div_index",
      .str "RiemannGaussian.LogLogDerivativeSchedule.exponent_lt_one",
      .str "RiemannGaussian.LogLogDerivativeSchedule.delta_le_one",
      .str "RiemannGaussian.LogLogDerivativeSchedule.inverse_delta_le_power",
      .str "RiemannGaussian.LogLogDerivativeSchedule.power_index_le",
      .str "RiemannGaussian.LogLogDerivativeSchedule.inverse_delta_le",
      .str "RiemannGaussian.LogLogDerivativeSchedule.log_width_le",
      .str "RiemannGaussian.LogLogDerivativeSchedule.pow_log_div_width_tendsto",
      .str "RiemannGaussian.ZetaLogLogScale.level_atTop",
      .str "RiemannGaussian.ZetaLogLogScale.order_atTop",
      .str "RiemannGaussian.ZetaLogLogScale.level_div_order",
      .str "RiemannGaussian.ZetaLogLogScale.width_pos",
      .str "RiemannGaussian.ZetaLogLogScale.width_tendsto_zero",
      .str "RiemannGaussian.ZetaLogLogScale.pow_level_div_width_tendsto",
      .str "RiemannGaussian.ZetaLogLogScale.width_div_delta_tendsto",
      .str "RiemannGaussian.ZetaLogLogScale.width_mul_level_div_delta_tendsto",
      .str "RiemannGaussian.ZetaLogLogScale.width_eq_margin",
      .str "RiemannGaussian.ZetaLogLogScale.shift_eq_six_width",
      .str "RiemannGaussian.ZetaLogLogScale.abs_invariance",
      .str "RiemannGaussian.ZetaLogLogCorrection.allowance_eq",
      .str "RiemannGaussian.ZetaLogLogCorrection.log_width_nonneg",
      .str "RiemannGaussian.ZetaLogLogCorrection.correction_nonneg",
      .str "RiemannGaussian.ZetaLogLogCorrection.center_log_le",
      .str "RiemannGaussian.ZetaLogLogCorrection.correction_le",
      .str "RiemannGaussian.ZetaLogLogCorrection.normalized_correction_tendsto",
      .str "RiemannGaussian.ZetaLogLogBudget.scale_double_bounds",
      .str "RiemannGaussian.ZetaLogLogBudget.leading_identity",
      .str "RiemannGaussian.ZetaLogLogBudget.normalized_allowance_tendsto",
      .str "RiemannGaussian.ZetaLogLogBudget.width_mul_budget_tendsto",
      .str "RiemannGaussian.ZetaLogLogBudget.cost_tendsto",
      .str "RiemannGaussian.ZetaLogLogExclusion.exists_schedule",
      .str "RiemannGaussian.ZetaLogLogExclusion.cost_abs",
      .str "RiemannGaussian.ZetaLogLogExclusion.exists_eventual_margin_of_schedule",
      .str "RiemannGaussian.ZetaLogLogExclusion.exists_eventual_margin",
      .str "RiemannGaussian.ZetaLogLogWidth.two_le_baseHeight",
      .str "RiemannGaussian.ZetaLogLogWidth.log_lower",
      .str "RiemannGaussian.ZetaLogLogWidth.width_pos",
      .str "RiemannGaussian.ZetaLogLogWidth.width_antitone",
      .str "RiemannGaussian.ZetaLogLogWidth.width_tendsto_zero",
      .str "RiemannGaussian.ZetaLogLogWidth.scale_div_log_tendsto",
      .str "RiemannGaussian.ZetaLogLogWidth.eventually_le_smoothed",
      .str "RiemannGaussian.ZetaLogLogWidth.eventually_dominates_logarithmic",
      .str "RiemannGaussian.ZetaLogLogZeroFree.coefficientLimit_pos",
      .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_right_margin",
      .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_strip",
      .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_common_margin",
      .str "RiemannGaussian.ZetaLogLogZeroFree.exists_eventual_nonvanishing",
      .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_radius_spec",
      .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_response_bound",
      .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_coefficient_scaled_decay"
    ])
  ]

private def zetaArbitraryLogZeroFreeToolkit : Json :=
  Json.mkObj [
    ("role", .str "Unconditional actual zero-free width A/log(abs(t)) for every fixed A>0, with coefficient-dependent eventual thresholds; complete local signed factorization and actual arithmetic radius transport"),
    ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_strip"),
    ("literalNonvanishingTheorem", .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_nonvanishing"),
    ("completeBandTheorem", .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_common_margin"),
    ("exactComplexSplitTheorem", .str "RiemannGaussian.AnalyticDiscSignedDerivative.logDeriv_center_eq"),
    ("coupledSignTheorem", .str "RiemannGaussian.AnalyticDiscSignedDerivative.kernel_re_nonneg"),
    ("actualResidualTheorem", .str "RiemannGaussian.ZetaNearOneCanonical.exists_controlled_decomp"),
    ("actualSignedSourceTheorem", .str "RiemannGaussian.ZetaNearOneSignedBound.neg_logDeriv_re_le_sub_zero"),
    ("actualPrimeBudgetTheorem", .str "RiemannGaussian.ZetaNearOnePhaseConstraint.source_le_budget"),
    ("fullBudgetLimitTheorem", .str "RiemannGaussian.ZetaNearOneBudgetLimit.budget_div_scale"),
    ("actualContradictionTheorem", .str "RiemannGaussian.ZetaNearOneExclusion.one_le_cost_of_zero_near"),
    ("actualArithmeticRadiusTheorem", .str "RiemannGaussian.SquarefreeArbitraryLog.exists_eventual_radius_spec"),
    ("allMarkedResponseTheorem", .str "RiemannGaussian.SquarefreeArbitraryLog.exists_eventual_response_bound"),
    ("strongerFixedMarkDecayTheorem", .str "RiemannGaussian.SquarefreeArbitraryLog.exists_eventual_coefficient_scaled_decay"),
    ("localParameters", .str "For k>=1, alpha_k=1/(2^(k+2)-2), delta_k=(k+2)*alpha_k, H(t)=abs(t)+2, M_k(t)=log(32768/delta_k)+alpha_k*log(H(t))+log(log(H(t))), E_k(x,t)=M_k(t)+14+log(1+1/x). For abs(t)>=2 and 0<x<=delta_k/4, actual zeta is analytic on the whole disc of radius delta_k/2 about c=1+x+i*t and nonzero at its center"),
    ("completeCanonicalGeometry", .str "A proved zero-free sphere has delta_k/4<r<3*delta_k/8. Complete canonical removal preserves boundary norms exactly and increases center norm. The nonzero analytic residual has norm(logDeriv(g,0))<=2*E_k/r<=8*E_k/delta_k. No boundary-zero or center-floor hypothesis remains"),
    ("retainedCoupledKernel", .str "logDeriv(zeta,c)=logDeriv(g,0)+sum_a m_a*(-1/a+conj(a)/r^2). The real coupled kernel is (-Re(a)/normSq(a))*(1-normSq(a)/r^2). Every actual local zero lies left of the center, so every coupled term is nonnegative. The correction is not separated into a zero-count error"),
    ("fullSelectedSource", .str "For an actual zero rho=beta+i*t and d=x+1-beta<delta_k/4: Re(-logDeriv(zeta,c))<=8*E_k(x,t)/delta_k-m_rho*(1/d-16*d/delta_k^2). Analytic multiplicity is retained and proved at least one"),
    ("completePrimeBudget", .str "B_k(x,t)=1344*log(22)+(32*E_k(x,t)+8*E_k(x,2*t))/delta_k. Actual three-height prime positivity gives 4*m_rho*(1/d-16*d/delta_k^2)<=3/x+B_k(x,t)"),
    ("fixedOrderLimit", .str "For every fixed k and C>0, x(t)=6*C/log(H(t)) gives B_k(x(t),t)/log(H(t))->40/(k+2), including the complete moving Euler center cost. If u=C/log(H(t)), then cost=14*u*B_k(x(t),t)+6272*u^2/delta_k^2 tends to 560*C/(k+2)"),
    ("contradiction", .str "Any actual zero with 1-beta<=u and 28*u<delta_k forces cost>=1. For each fixed C>0 choose one fixed natural k>=1 with k+2>560*C; all geometric conditions hold eventually and cost<1 eventually. This excludes the smoothed-log margin C/log(H(t)). Use C=2*A and log(abs(t)+2)<=2*log(abs(t)) to get every ordinary-log coefficient A"),
    ("quantifiers", .str "For every fixed A>0 there exists T(A)>=2 such that all actual nontrivial zeros above T(A) satisfy A/log(abs(Im(rho)))<Re(rho)<1-A/log(abs(Im(rho))). Literal zeta nonvanishing on the closed right edge is also proved, with a possibly enlarged coefficient-dependent threshold. No common T for all A or order-height limit exchange is asserted"),
    ("completeBandAndRadius", .str "For every fixed A>0 and all sufficiently large H, A/log(H) is positive, below 1/4, and bounds both edges of every actual zero below H. Thus the actual squarefree quotient has full analytic disc radius 1+A/(2*log(2*abs(y)+3)) about 3/2+i*y at all sufficiently large abs(y), with poles and denominator zeros excluded"),
    ("arithmeticGain", .str "All finite excluded prime sets, valid squarefree marks, complex polynomials and orders receive the genuine Cauchy bound with their signed two-harmonic envelope intact. For any fixed 0<=A<B, at sufficiently large abs(y), the radius for A is strictly smaller than the actual radius for B and its entire geometric scale times each fixed marked response tends to zero"),
    ("nextProofTarget", .str "The joint order-height budget and specified log-log region are now proved and transported in zetaLogLogZeroFreeToolkit. Retain the signed prime envelope in the resulting smaller domain and seek an independent bound for the separate ordinary-prime source"),
    ("literature", .str "Yang, JMAA 2024, https://arxiv.org/html/2301.03165v2 motivates the changing-order strategy. Higher-derivative bounds, canonical factorization, Borel-Caratheodory and prime phase positivity are classical techniques. No optimized published numerical constant or external zero-free theorem is imported as an assumption"),
    ("limitations", .str "This fixed-coefficient toolkit has coefficient-dependent unevaluated thresholds. The downstream growing-order proof now supplies a specified log-log region in zetaLogLogZeroFreeToolkit. Growing excluded prime sets still carry their signed phase envelope. Stronger decay of the full squarefree quotient is not the independent lower bound for the separate fixed-ordinate ordinary-prime source. RH remains open; no historical novelty claim"),
    ("documentation", .str "docs/zeta-arbitrary-log-zero-free.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.order_ne_top",
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.exists_zeroFree_sphere",
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.exists_decomp",
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.divisor_sphere_eq_zero",
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.norm_eq_on_sphere",
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.norm_le",
      .str "RiemannGaussian.AnalyticDiscCanonicalBounds.center_norm_le",
      .str "RiemannGaussian.AnalyticDiscLogarithm.exists_logarithm",
      .str "RiemannGaussian.AnalyticDiscLogarithm.exp_mul_center",
      .str "RiemannGaussian.AnalyticDiscLogarithm.re_le",
      .str "RiemannGaussian.AnalyticDiscLogarithm.norm_logDeriv_center_le",
      .str "RiemannGaussian.AnalyticDiscSignedDerivative.factor_center",
      .str "RiemannGaussian.AnalyticDiscSignedDerivative.zero_of_divisor_ne_zero",
      .str "RiemannGaussian.AnalyticDiscSignedDerivative.logDeriv_center_eq",
      .str "RiemannGaussian.AnalyticDiscSignedDerivative.kernel_re",
      .str "RiemannGaussian.AnalyticDiscSignedDerivative.kernel_re_nonneg",
      .str "RiemannGaussian.AnalyticDiscSignedDerivative.kernel_neg_real",
      .str "RiemannGaussian.ZetaNearOneCanonical.translated_zero",
      .str "RiemannGaussian.ZetaNearOneCanonical.analyticOnNhd_translated",
      .str "RiemannGaussian.ZetaNearOneCanonical.norm_translated_le",
      .str "RiemannGaussian.ZetaNearOneCanonical.logDeriv_translated",
      .str "RiemannGaussian.ZetaNearOneCanonical.allowance_pos",
      .str "RiemannGaussian.ZetaNearOneCanonical.exists_controlled_decomp",
      .str "RiemannGaussian.ZetaNearOneSignedBound.coupledSum_re",
      .str "RiemannGaussian.ZetaNearOneSignedBound.divisor_re_neg",
      .str "RiemannGaussian.ZetaNearOneSignedBound.term_nonneg",
      .str "RiemannGaussian.ZetaNearOneSignedBound.coupledSum_nonneg",
      .str "RiemannGaussian.ZetaNearOneSignedBound.divisor_at_zero",
      .str "RiemannGaussian.ZetaNearOneSignedBound.source_le_sum",
      .str "RiemannGaussian.ZetaNearOneSignedBound.neg_logDeriv_re_le",
      .str "RiemannGaussian.ZetaNearOneSignedBound.neg_logDeriv_re_le_sub_zero",
      .str "RiemannGaussian.ZetaNearOnePhaseConstraint.source_le_budget",
      .str "RiemannGaussian.ZetaNearOnePhaseConstraint.zero_gap_constraint",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.scale_pos",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.scale_atTop",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.shift_pos",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.shift_tendsto_zero",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.scale_double_div",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.profile_div_scale",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.profile_double_div_scale",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.center_cost_div_scale",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.allowance_div_scale",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.allowance_double_div_scale",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.budget_div_scale",
      .str "RiemannGaussian.ZetaNearOneBudgetLimit.budget_abs",
      .str "RiemannGaussian.ZetaNearOneExclusion.margin_pos",
      .str "RiemannGaussian.ZetaNearOneExclusion.margin_tendsto_zero",
      .str "RiemannGaussian.ZetaNearOneExclusion.shift_eq_six_margin",
      .str "RiemannGaussian.ZetaNearOneExclusion.cost_tendsto",
      .str "RiemannGaussian.ZetaNearOneExclusion.margin_abs",
      .str "RiemannGaussian.ZetaNearOneExclusion.cost_abs",
      .str "RiemannGaussian.ZetaNearOneExclusion.exists_order",
      .str "RiemannGaussian.ZetaNearOneExclusion.one_le_cost_of_zero_near",
      .str "RiemannGaussian.ZetaNearOneExclusion.exists_eventual_margin",
      .str "RiemannGaussian.ZetaArbitraryLogZeroFree.scale_le_two_log_abs",
      .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_right_margin",
      .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_strip",
      .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_common_margin",
      .str "RiemannGaussian.ZetaArbitraryLogZeroFree.exists_eventual_nonvanishing",
      .str "RiemannGaussian.SquarefreeArbitraryLog.exists_eventual_radius_spec",
      .str "RiemannGaussian.SquarefreeArbitraryLog.exists_eventual_response_bound",
      .str "RiemannGaussian.SquarefreeArbitraryLog.exists_eventual_coefficient_scaled_decay"
    ])
  ]

private def zetaGaussianLocalJensenToolkit : Json :=
  Json.mkObj [
    ("role", .str "Actual near-one zeta bounds across a full strip and shrinking-disc Jensen zero estimates, with all strip growth, local analyticity and Euler center-value premises discharged"),
    ("exactGaussianCarrier", .str "G_t(s)=zeta_1(s)/(s+1)*exp((s-i*t)^2). Away from the original pole zeta_1(s)=(s-1)*zeta(s). The rational factor has norm at most one when Re(s)>=0, avoiding an additional height power. The exact inverse reconstruction remains a named theorem"),
    ("carrierGrowthTheorem", .str "RiemannGaussian.ZetaGaussianLocalizer.carrier_bounded"),
    ("fullStripMaximumTheorem", .str "RiemannGaussian.ZetaGaussianStrip.carrier_bound"),
    ("fullStripZetaTheorem", .str "RiemannGaussian.ZetaNearOneLocalDisc.full_strip_posLog_bound"),
    ("localDiscAnalyticityTheorem", .str "RiemannGaussian.ZetaNearOneLocalDisc.analyticOnNhd_disc"),
    ("localDiscZetaTheorem", .str "RiemannGaussian.ZetaNearOneLocalDisc.disc_posLog_bound"),
    ("exactMobiusTheorem", .str "RiemannGaussian.ZetaEulerReciprocalAllowance.inverse_eq_moebius"),
    ("fullReciprocalBoundTheorem", .str "RiemannGaussian.ZetaEulerReciprocalAllowance.inverse_zeta_bound"),
    ("explicitCenterAllowanceTheorem", .str "RiemannGaussian.ZetaNearOneJensen.center_log_bound"),
    ("exactJensenIdentityTheorem", .str "RiemannGaussian.ZetaNearOneJensen.jensen_identity"),
    ("completeWeightedDivisorTheorem", .str "RiemannGaussian.ZetaNearOneJensen.weighted_mass_bound"),
    ("selectedZeroSourceTheorem", .str "RiemannGaussian.ZetaNearOneJensen.zero_source_bound"),
    ("fullLocalMultiplicityTheorem", .str "RiemannGaussian.ZetaNearOneJensen.count_bound"),
    ("fullStripScope", .str "For every k>=1, sigma_k=1-delta_k<=Re(s)<=3/2 and abs(Im(s))>=2: log^+ norm(zeta(s))<=M_k(Im(s))+14, where H(t)=abs(t)+2 and M_k(t)=log(32768/delta_k)+alpha_k*log(H(t))+log(log(H(t))). The local version allows every center t with abs(t)>=2 and abs(Im(s)-t)<=1"),
    ("localDiscScope", .str "For every k>=1, abs(t)>=2, 0<x<=delta_k/4, c=1+x+i*t and R=delta_k/2: zeta is analytic on a neighborhood of the entire closed disc and nonzero at c. Zeros inside and on the boundary are allowed. The shift x may be arbitrarily small in this range"),
    ("exactDivisorInformation", .str "The signed boundary circle average equals the entire finite logarithmic divisor mass plus log norm(zeta(c)). Every term keeps its exact distance and analytic multiplicity. Each selected genuine zeta-zero term is bounded using the full nonnegative mass; no simple-zero assumption is introduced"),
    ("completeLocalAllowance", .str "A=M_k(t)+14+log(1+1/x). The full distance-weighted zero mass sum_a d_D(a)*log(R/norm(c-a)) is at most A. For 0<r<R the complete multiplicity count in closedBall(c,r) is at most A/log(R/r). A selected actual zero rho in D has m_rho*log(R/norm(c-rho))<=A"),
    ("growthPremise", .str "The independent coarse zeta bound gives norm(G_t(s))<=16*exp(3)*(1+(abs(t)+22)^2) throughout 1/2<=Re(s)<=3/2. This controls the complete infinite tails and is used only for the Phragmen-Lindelof growth hypothesis. The final bound comes from the sharper boundary data and is exp(M_k(t)+10)"),
    ("localInverseCost", .str "In the height-one window the inverse Gaussian has norm at most exp(1) and the inverse rational factor has norm at most 4. The final additive logarithmic cost 14 is coarse and uniform; the original alpha_k height exponent survives"),
    ("eulerCenterCost", .str "On all Re(s)>1 the genuine full Mobius L-series equals 1/zeta(s), and norm(1/zeta(s))<=1+1/(Re(s)-1). Integral comparison includes the zero-index convention and the complete p-series tail. At c the negative center logarithm is at most log(1+1/x)"),
    ("nextProofTarget", .str "The signed local logarithmic derivative, complete actual residual and prime phase exclusion are now proved in zetaArbitraryLogZeroFreeToolkit. They give every fixed positive logarithmic coefficient eventually and transport it to the actual marked squarefree response. The downstream joint-order budget now proves the specified log-log width in zetaLogLogZeroFreeToolkit. Next retain the signed prime envelope in the smaller arithmetic domain and seek the independent ordinary-prime bound"),
    ("alternativeRoute", .str "These finite-disc results do not require a separately constructed full signed vertical logarithmic integral. The complete positive integral and finite signed windows remain available in zetaSechLogarithmicToolkit; its full signed limit is still unproved"),
    ("literature", .str "The changing-order strategy is motivated by Yang, JMAA 2024, https://arxiv.org/html/2301.03165v2. Gaussian localization, Phragmen-Lindelof and Jensen are established techniques. No historical novelty or reproduction of optimized published constants is claimed"),
    ("limitations", .str "Jensen logarithmic weights alone do not give a zero exclusion. The downstream complete coupled logarithmic-derivative estimate now proves every fixed logarithmic coefficient eventually; see zetaArbitraryLogZeroFreeToolkit. The independent signed ordinary-prime bound in the fixed-ordinate, growing-moment RH contradiction and RH remain open"),
    ("documentation", .str "docs/zeta-gaussian-local-jensen.md"),
    ("publicTheorems", .arr #[
      .str "RiemannGaussian.ZetaGaussianLocalizer.regularized_eq",
      .str "RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero",
      .str "RiemannGaussian.ZetaGaussianLocalizer.norm_ratio_le_one",
      .str "RiemannGaussian.ZetaGaussianLocalizer.norm_regularized_le_zeta",
      .str "RiemannGaussian.ZetaGaussianLocalizer.norm_carrier",
      .str "RiemannGaussian.ZetaGaussianLocalizer.differentiableAt_carrier",
      .str "RiemannGaussian.ZetaGaussianLocalizer.norm_poleRemoved_le",
      .str "RiemannGaussian.ZetaGaussianLocalizer.norm_regularized_le",
      .str "RiemannGaussian.ZetaGaussianLocalizer.quadratic_gaussian_bound",
      .str "RiemannGaussian.ZetaGaussianLocalizer.carrier_bounded",
      .str "RiemannGaussian.ZetaGaussianStrip.norm_zeta_le_exp_profile",
      .str "RiemannGaussian.ZetaGaussianStrip.shiftCost_one_le_two",
      .str "RiemannGaussian.ZetaGaussianStrip.left_boundary",
      .str "RiemannGaussian.ZetaGaussianStrip.right_boundary",
      .str "RiemannGaussian.ZetaGaussianStrip.diffContOnCl_carrier",
      .str "RiemannGaussian.ZetaGaussianStrip.carrier_growth",
      .str "RiemannGaussian.ZetaGaussianStrip.carrier_bound",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.reconstruction",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.inverse_gaussian_bound",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.inverse_ratio_bound",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.one_le_abs_im",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.ne_one_of_window",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.local_norm_bound",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.local_posLog_bound",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.full_strip_posLog_bound",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.disc_geometry",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.analyticOnNhd_disc",
      .str "RiemannGaussian.ZetaNearOneLocalDisc.disc_posLog_bound",
      .str "RiemannGaussian.ZetaEulerReciprocalAllowance.pseries_mass_bound",
      .str "RiemannGaussian.ZetaEulerReciprocalAllowance.moebius_term_bound",
      .str "RiemannGaussian.ZetaEulerReciprocalAllowance.inverse_eq_moebius",
      .str "RiemannGaussian.ZetaEulerReciprocalAllowance.inverse_zeta_bound",
      .str "RiemannGaussian.ZetaEulerReciprocalAllowance.neg_log_norm_zeta_le",
      .str "RiemannGaussian.ZetaNearOneJensen.allowance_nonneg",
      .str "RiemannGaussian.ZetaNearOneJensen.center_ne_zero",
      .str "RiemannGaussian.ZetaNearOneJensen.center_log_bound",
      .str "RiemannGaussian.ZetaNearOneJensen.jensen_identity",
      .str "RiemannGaussian.ZetaNearOneJensen.circle_average_bound",
      .str "RiemannGaussian.ZetaNearOneJensen.weighted_mass_bound",
      .str "RiemannGaussian.ZetaNearOneJensen.divisor_term_nonneg",
      .str "RiemannGaussian.ZetaNearOneJensen.divisor_term_bound",
      .str "RiemannGaussian.ZetaNearOneJensen.zero_source_bound",
      .str "RiemannGaussian.ZetaNearOneJensen.count_bound"
    ])
  ]

/-- Static historical context is compiled separately from the live integrity audit. -/
@[noinline] private def historicalStatusNote : Json :=
  .str
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
      "docs/eta-current-reconstruction-plan.md.")

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
    ("statusNote", historicalStatusNote),
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
    ("signedPoleZeroFree", Json.mkObj [
      ("pointwiseSignTheorem", .str "RiemannGaussian.zetaStechkinPoleBudget_neg"),
      ("realFrequencyTheorem", .str "RiemannGaussian.zetaPhase_stechkinPole_le_constant"),
      ("integerFrequencyTheorem", .str "RiemannGaussian.phase_stechkinPole_le_constant"),
      ("allFamilySourceTheorem", .str "RiemannGaussian.phase_shifted_source_add_primeWork_add_signedPoleReserve_le"),
      ("budgetTheorem", .str "RiemannGaussian.phaseContactExact_signedPole_zero_budget"),
      ("allowanceTheorem", .str "RiemannGaussian.zetaSignedPole_allowance_le"),
      ("stripTheorem", .str "RiemannGaussian.nontrivialZetaZero_mem_signedPole_strip"),
      ("nonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_signedPole_margin"),
      ("comparisonTheorem", .str "RiemannGaussian.completionReserve_margin_scaled_lt_signedPole"),
      ("margin", .str "792/(7625*log(abs(t)+2)-2000)"),
      ("previousMargin", .str "1/(10*log(abs(t)+2))"),
      ("widthRatio", .str "Strictly greater than 1584/1525 at every real ordinate"),
      ("heightDomain", .str "Every ordinate. The eta constraint t^2>3 implies log(abs(t)+2)>13/10 for each actual nontrivial zero"),
      ("poleSign", .str "For 1<=sigma<=4/3 and t^2>=3, the complete signed pole term is strictly negative. This controls the full nonconstant countable phase sum, not merely an individual selected term"),
      ("familyScope", .str "All nonnegative summable real-frequency families with one designated zero mode and every other sampled ordinate having square at least three. All admissible integer-frequency families satisfy this at actual zero ordinates"),
      ("retainedInformation", .str "Full selected analytic multiplicity, complete signed prime work, negative completion constant and exact constant-pole subtraction; the richer full signed identity remains upstream"),
      ("source", .str "11/625, using the existing exact optimizer and shift 13/4 without coefficient changes"),
      ("allowance", .str "At most 11/625-(221/28080)*d when d*(7625*L-2000)<=792, L>=13/10 and c>=4/9. Both the arithmetic work and retained constant-pole reserve have proved nonnegative sign"),
      ("status", .str "Unconditional wider literal zero exclusion with all analytic and arithmetic hypotheses discharged. The independent signed bound in the remaining interior strip and RH remain open. No mathematical-priority or best-published-region claim")
    ]),
    ("poleReserveBootstrap", Json.mkObj [
      ("reserveTheorem", .str "RiemannGaussian.phaseContactExact_constantPoleReserve_gt"),
      ("strictBudgetTheorem", .str "RiemannGaussian.phaseContactExact_poleReserve_strict_zero_budget"),
      ("stepTheorem", .str "RiemannGaussian.zetaPoleReserveStep_lt_one_sub_re"),
      ("improvementTheorem", .str "RiemannGaussian.zetaSignedPole_margin_lt_reserveStep"),
      ("iterationTheorem", .str "RiemannGaussian.tendsto_zetaPoleReserveIterate"),
      ("fixedPointTheorem", .str "RiemannGaussian.zetaPoleReserveStep_fixed_unique"),
      ("stripTheorem", .str "RiemannGaussian.nontrivialZetaZero_mem_poleReserve_strip"),
      ("nonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_poleReserve_margin"),
      ("analyticTransportTheorem", .str "RiemannGaussian.analyticOnNhd_squarefreeEulerResponse_reserve"),
      ("arithmeticTransportTheorem", .str "RiemannGaussian.exists_squarefreeEuler_reserve_radius_bound"),
      ("heightAllowance", .str "L=max(13/10,log(abs(t)+2)); A=(366*L-113)/2160"),
      ("strictBudget", .str "11/625+(2/25)*d < A*d for every actual zero with d=1-Re(rho)<=4/39"),
      ("step", .str "F(delta)=min(4/39,(11/625+(2/25)*delta)/A)"),
      ("fixedMargin", .str "B=min(4/39,4752/(45750*L-35725))"),
      ("globalMargin", .str "max(792/(7625*log(abs(t)+2)-2000),B)"),
      ("radius", .str "1+min((abs(y)-1)/2,globalMargin(2*abs(y)+3)/2), strictly larger than the preceding radius at every actual zero ordinate"),
      ("arithmeticCost", .str "One constant for all smaller positive radii r, all eligible squarefree marks P and prime sets S, and all complex polynomial filters: C*squarefreeEulerBudget(3/2-r,S,P)*r^(-N)*sum_k norm(p_k)*r^(-k)"),
      ("status", .str "Unconditional wider literal zero exclusion and actual analytic/arithmetic transport. The increasing reserve iteration stops at an explicit fixed point no greater than 4/39. No claim that it reaches RH or controls the independent signed ordinary-prime tail; no historical novelty or best-published-region claim")
    ]),
    ("idealFermiReflection", Json.mkObj [
      ("allWindowTheorem", .str "RiemannGaussian.FermiLaplaceReflection.transform_reflected_pair_re_nonneg"),
      ("complexPartitionTheorem", .str "RiemannGaussian.FermiLaplaceReflection.transform_partition"),
      ("bilateralTheorem", .str "RiemannGaussian.FermiLaplaceReflection.transform_pair_eq_bilateral"),
      ("endpointTheorem", .str "RiemannGaussian.FermiLaplaceReflection.paired_endpoint_cancel"),
      ("gaussianBoundaryTheorem", .str "RiemannGaussian.GaussianFermiZeroPair.integral_half_boundary_re"),
      ("actualZeroBandTheorem", .str "RiemannGaussian.GaussianFermiZeroPair.nontrivial_zero_pair_re_nonneg_on_band"),
      ("signal", .str "f(u)=g(u)/(1+exp(-a*u)); F(z)=integral_(u>0) f(u)*exp(-z*u) du"),
      ("generalScope", .str "Every continuous real window with all real exponential moments and nonnegative one-sided cosine transform. For a>0, Re(F(z)+F(a-conj(z)))>=0 on 0<=Re(z)<=a"),
      ("actualInstantiation", .str "Every Gaussian g(u)=exp(-b*u^2), b>0; all integrability, entire continuation and boundary positivity hypotheses discharged"),
      ("zeroRegionTransport", .str "For sigma=1-zetaPoleReserveZeroMargin(H), every genuine zero with abs(Im(rho))<=abs(H) gives a nonnegative reflected pair at sigma+i*t, for every real t"),
      ("retainedInformation", .str "Exact shift partition, detailed balance, analytic bilateral transform and conjugation connecting it to the actual same-phase zero partner; leading endpoint coefficient cancels"),
      ("status", .str "Checked analytic component inspired by Bellotti-Trudgian-Yang arXiv:2603.21490v1, not a formalization of their numerical 4.896 region. The full zero side now has a literal convergent Fermi prime formula, exact poles and a general finite-phase budget with a proved outside allowance and explicit quarter-logarithm gamma bound. The subsequent independent Gaussian comparison proves the eventual width 3/(20*log(abs(t))) with all height costs discharged. The finite threshold is not numerically evaluated; the external 4.896 region, independent prime-tail bound and RH remain open")
    ]),
    ("gaussianFermiZeroTail", Json.mkObj [
      ("derivativeTheorem", .str "RiemannGaussian.GaussianFermiDerivativeBounds.abs_damped_orders_le_envelope"),
      ("integralBoundTheorem", .str "RiemannGaussian.GaussianFermiDerivativeBounds.integral_abs_dampedTwo_le"),
      ("complexFrequencyTheorem", .str "RiemannGaussian.GaussianFermiPairDecay.oscillatory_second_derivative"),
      ("pairDecayTheorem", .str "RiemannGaussian.GaussianFermiPairDecay.abs_physical_pair_re_le"),
      ("actualSummabilityTheorem", .str "RiemannGaussian.GaussianFermiZeroTail.summable_contribution"),
      ("outsideBoundTheorem", .str "RiemannGaussian.GaussianFermiZeroTail.abs_tsum_outside_le"),
      ("divisorTailLimitTheorem", .str "RiemannGaussian.GaussianFermiZeroTail.tendsto_divisorTail"),
      ("globalZeroSideTheorem", .str "RiemannGaussian.GaussianFermiZeroTail.global_zero_side_lower_bound"),
      ("dyadicTailTheorem", .str "RiemannGaussian.GaussianFermiZeroTailRate.divisorTail_le_majorant_tail"),
      ("geometricTailTheorem", .str "RiemannGaussian.GaussianFermiZeroTailRate.majorant_tail_geometric"),
      ("heightTailRateTheorem", .str "RiemannGaussian.GaussianFermiZeroTailRate.exists_divisorTail_sqrt_bound"),
      ("uniformAllowanceTheorem", .str "RiemannGaussian.GaussianFermiMovingAllowance.exists_uniform_allowance_bound"),
      ("movingScaleLimitTheorem", .str "RiemannGaussian.GaussianFermiMovingAllowance.tendsto_allowance_of_admissible"),
      ("uniformZeroSideTheorem", .str "RiemannGaussian.GaussianFermiMovingAllowance.exists_uniform_zero_side_bound"),
      ("eventualLowerBoundTheorem", .str "RiemannGaussian.GaussianFermiMovingAllowance.eventually_zero_side_ge_neg"),
      ("cost", .str "C(a,b,delta)=exp(1/2)*(34*b+2*(2*a+delta)^2+1)*sqrt(pi/(b/4)); b>0, delta>=0, delta^2<=b, -delta<=Re(z)<=a+delta"),
      ("globalBound", .str "For sigma=1-zetaPoleReserveZeroMargin(H), H>=max(2*abs(t),1), m(H)^2<=b: sum_rho multiplicity(rho)/2 * Re(F(s-rho)+F(s-(1-conj(rho)))) >= -4*C(2*sigma-1,b,1-sigma)*W(H)"),
      ("divisorTail", .str "W(H)=sum_(abs(Im(rho))>H) multiplicity(rho)/(1+Im(rho)^2), genuinely summable and at most C/sqrt(H) for all H>=1, using the unconditional 3/2 xi-growth estimate"),
      ("uniformAllowance", .str "For every H>=1 and every scale m(H)^2<=b<=1: 4*C(1-2*m(H),b,m(H))*W(H)<=K*log(H+2)/sqrt(H). One K>0 independent of height, scale and ordinate; the rate tends to zero"),
      ("uniformZeroSide", .str "On sigma=1-m(H), the signed outside sum is bounded in absolute value and the full zero sum below by the same vanishing allowance, uniformly for 2*abs(t)<=H and all m(H)^2<=b<=1"),
      ("retainedInformation", .str "Exact signed time derivatives, full-line integrations by parts, analytic complex reflection, conjugation for the physical real pair, all actual zeros with analytic multiplicity and paired normalization"),
      ("status", .str "Unconditional bound for the complete actual paired zero side, with a uniformly vanishing allowance. The exact Gaussian mixture and subsequent literal prime/pole evaluations transport it to a general finite-phase selected-zero budget, now with an explicit gamma upper bound uniform over shrinking scales. The subsequent independent Gaussian comparison proves the stronger eventual width 3/(20*log(abs(t))). The threshold is proved to exist, not numerically evaluated. The independent ordinary-prime-tail bound and RH remain open")
    ]),
    ("gaussianFermiExplicitMixture", Json.mkObj [
      ("densityRealityTheorem", .str "RiemannGaussian.GaussianFermiSpectralWeight.kernel_im"),
      ("densityPositivityTheorem", .str "RiemannGaussian.GaussianFermiSpectralWeight.density_nonneg"),
      ("densityMassTheorem", .str "RiemannGaussian.GaussianFermiSpectralWeight.integral_density"),
      ("characteristicTheorem", .str "RiemannGaussian.GaussianFermiSpectralWeight.integral_density_mul_cexp"),
      ("complexMixtureTheorem", .str "RiemannGaussian.GaussianFermiGaussianMixture.pair_eq_gaussian_average"),
      ("zeroIntegralNormTheorem", .str "RiemannGaussian.GaussianFermiZeroInterchange.summable_integral_norm_zeroIntegrand"),
      ("zeroAverageIntegrabilityTheorem", .str "RiemannGaussian.GaussianFermiZeroInterchange.integrable_tsum_zeroIntegrand"),
      ("wholeZeroInterchangeTheorem", .str "RiemannGaussian.GaussianFermiZeroInterchange.hasSum_integral_zeroIntegrand"),
      ("arithmeticIntegrabilityTheorem", .str "RiemannGaussian.GaussianFermiZeroMixture.integrable_density_arithmetic"),
      ("actualHasSumTheorem", .str "RiemannGaussian.GaussianFermiZeroMixture.hasSum_contribution_arithmetic_average"),
      ("actualIdentityTheorem", .str "RiemannGaussian.GaussianFermiZeroMixture.zero_side_eq_arithmetic_average"),
      ("arithmeticLowerBoundTheorem", .str "RiemannGaussian.GaussianFermiZeroMixture.exists_uniform_arithmetic_average_lower_bound"),
      ("density", .str "h(a,c,u)=exp(-c*u^2-(a/2)*u)/(1+exp(-a*u)); p(a,c,y)=Re(integral_R h(a,c,u)*exp(-i*y*u) du)/pi. For a,c>0: p>=0, integral_R p=1, and integral_R p(y)*exp(i*y*u) dy=2*h(a,c,u)"),
      ("complexIdentity", .str "For a>=0,b,c>0 and every complex z: F(a,b+c,z)+F(a,b+c,a-z)=(1/2)*integral_R p(a,c,y)*sqrt(pi/b)*exp((z-a/2-i*y)^2/(4*b)) dy"),
      ("arithmeticIdentity", .str "For sigma>=1/2,b,c>0,a=2*sigma-1,epsilon=1/(4*b): sum_rho contribution(b+c,sigma,t,rho)=sqrt(pi/b)/8*integral_R p(a,c,y)*gaussianArithmeticExplicitFormula(epsilon,t-y) dy. HasSum and absolute integrability are proved"),
      ("localization", .str "Every averaged complex Gaussian zero term has integral norm <=C*multiplicity(rho)/(1+Im(rho)^2). The actual inverse-square divisor theorem sums this bound before the interchange"),
      ("uniformArithmeticBound", .str "For sigma=1-m(H),H>=1,b,c>0,m(H)^2<=b+c<=1 and 2*abs(t)<=H: the exact normalized arithmetic average is >=-K*log(H+2)/sqrt(H), with one K independent of height, ordinate and scale split"),
      ("retainedInformation", .str "Full complex Fourier kernel, conjugation giving reality, exact unit mass, all complex Gaussian arguments, zero-localized norm estimates, original physical reflection, analytic multiplicities and all factors of two"),
      ("status", .str "Exact identification with the unconditional arithmetic Gaussian formula in averaged form. The kernel representation and entire zero-side interchange are closed. The subsequent prime/pole formula and general finite-phase budget close the literal prime evaluation and its sign; the gamma average now has an explicit quarter-logarithm upper bound. The subsequent independent Gaussian comparison proves the stronger eventual width 3/(20*log(abs(t))) with an existential threshold. No numerical threshold, external 4.896 proof, independent ordinary-prime-tail bound or RH proof")
    ]),
    ("gaussianFermiPrimePhase", Json.mkObj [
      ("complexCharacterTheorem", .str "RiemannGaussian.GaussianFermiCosineAverage.integral_density_shifted_phase"),
      ("cosineAverageTheorem", .str "RiemannGaussian.GaussianFermiCosineAverage.integral_density_cosine"),
      ("primeIntegralNormTheorem", .str "RiemannGaussian.GaussianFermiPrimeFormula.summable_integral_norm_density_primeSummand"),
      ("primeHasSumTheorem", .str "RiemannGaussian.GaussianFermiPrimeFormula.hasSum_primeSummand_average"),
      ("primeConvergenceTheorem", .str "RiemannGaussian.GaussianFermiPrimeFormula.summable_primeSummand"),
      ("primeNormalizationTheorem", .str "RiemannGaussian.GaussianFermiPrimeFormula.normalized_prime_average"),
      ("poleEvaluationTheorem", .str "RiemannGaussian.GaussianFermiPoleFormula.normalized_pole_average"),
      ("constantEvaluationTheorem", .str "RiemannGaussian.GaussianFermiPoleFormula.normalized_constant_average"),
      ("gammaIntegrabilityTheorem", .str "RiemannGaussian.GaussianFermiPoleFormula.integrable_density_digamma"),
      ("gammaSplitIndependenceTheorem", .str "RiemannGaussian.GaussianFermiPoleFormula.digammaAverage_eq_of_add_eq"),
      ("fullExplicitFormulaTheorem", .str "RiemannGaussian.GaussianFermiPoleFormula.zero_side_eq_poles_digamma_sub_prime"),
      ("literalPrimeBoundTheorem", .str "RiemannGaussian.GaussianFermiPoleFormula.exists_uniform_prime_pole_digamma_bound"),
      ("phaseExchangeTheorem", .str "RiemannGaussian.GaussianFermiPhaseBudget.hasSum_prime_phase"),
      ("phasePrimeSignTheorem", .str "RiemannGaussian.GaussianFermiPhaseBudget.prime_phase_nonneg"),
      ("exactFamilyInstanceTheorem", .str "RiemannGaussian.GaussianFermiPhaseBudget.exact_contact_prime_phase_nonneg"),
      ("selectedZeroBoundTheorem", .str "RiemannGaussian.GaussianFermiPhaseBudget.selected_zero_sum_le_full_add_allowance"),
      ("generalPhaseBudgetTheorem", .str "RiemannGaussian.GaussianFermiPhaseBudget.selected_zero_phase_budget"),
      ("primeSeries", .str "P(a,B,t)=sum_n Lambda(n)/sqrt(n)*exp(-B*log(n)^2-(a/2)*log(n))/(1+exp(-a*log(n)))*cos(t*log(n)); absolutely convergent for B>0,a>=0"),
      ("fullFormula", .str "For sigma>=1/2,a=2*sigma-1,B=b+c,b,c>0: sum_rho contribution(B,sigma,t,rho)=Pole(B,sigma,t)-log(pi)/4+D(a;b,c;t)-P(a,B,t). Pole=Re F(sigma+i*t)+Re F(sigma-1+i*t); D=sqrt(pi/b)/8*integral_R density(a,c,y)*gaussianDigammaIntegral(1/(4*b),t-y) dy"),
      ("gammaScope", .str "The literal gamma average is absolutely integrable and depends only on b+c. The subsequent spectral-moment argument proves D(t)<=log(5/4+abs(t))/4+7/(8*(5/4+abs(t))) for 0<a<=1,b,c>0,b+c<=1, uniformly over shrinking scales, and inserts it into the selected-zero phase budget"),
      ("phaseScope", .str "Every finite index set J, nonnegative weights w_j and real frequencies omega_j with sum_j w_j*cos(omega_j*x)>=0 for every real x. The exact contact family is a proved instance, without selecting new coefficients"),
      ("selectedZeroBudget", .str "For sigma=1-m(H),H>=1,m(H)^2<=B=b+c,b,c>0,2*abs(omega_j*t)<=H and every finite actual zero set S with abs(Im(rho))<=H: sum_j w_j*sum_(rho in S) contribution(B,sigma,omega_j*t,rho)<=sum_j w_j*(Pole(B,sigma,omega_j*t)-log(pi)/4+D(2*sigma-1;b,c;omega_j*t))+(sum_j w_j)*allowance(B,H)"),
      ("allowanceScope", .str "For B<=1 the existing allowance is at most K*log(H+2)/sqrt(H), so the phase allowance vanishes when total phase weight stays bounded and all evaluation ordinates satisfy the height restriction"),
      ("retainedInformation", .str "Full complex character before its real cosine, every prime-power coefficient, common positive amplitude before phase summation, exact scale recombination, analytic versus physical pole conjugation, all selected actual zeros and analytic multiplicities, exact inside/outside partition"),
      ("status", .str "The literal prime formula, pole evaluation and general finite-phase budget are proved. The subsequent gamma bound is explicit and uniform over shrinking scales. Subsequent signed pole and target-pair estimates and an independent Gaussian surplus prove the stronger eventual width 3/(20*log(abs(t))). Its threshold is existential. No numerical threshold, external 4.896 theorem, independent original ordinary-prime-tail bound, historical novelty or RH proof is claimed")
    ]),
    ("gaussianFermiGammaBound", Json.mkObj [
      ("curvatureTheorem", .str "RiemannGaussian.GaussianFermiSpectralMoment.tendsto_characteristic_deficit"),
      ("sincIdentityTheorem", .str "RiemannGaussian.GaussianFermiSpectralMoment.integral_momentApprox"),
      ("secondMomentIntegrabilityTheorem", .str "RiemannGaussian.GaussianFermiSpectralMoment.integrable_density_secondMoment"),
      ("secondMomentTheorem", .str "RiemannGaussian.GaussianFermiSpectralMoment.integral_density_secondMoment"),
      ("absoluteMomentTheorem", .str "RiemannGaussian.GaussianFermiSpectralMoment.integral_density_abs_le_sqrt"),
      ("actualDigammaTheorem", .str "RiemannGaussian.GaussianDigammaLogEnvelope.archimedeanDensity_le_log"),
      ("fullIntegralTheorem", .str "RiemannGaussian.GaussianDigammaLogEnvelope.gaussianDigammaIntegral_eq_full"),
      ("gaussianMomentTheorem", .str "RiemannGaussian.GaussianDigammaLogEnvelope.translated_gaussian_abs_moment"),
      ("centeredTangentTheorem", .str "RiemannGaussian.GaussianDigammaLogEnvelope.archimedeanDensity_le_tangent"),
      ("integratedTangentTheorem", .str "RiemannGaussian.GaussianDigammaLogEnvelope.gaussianDigammaIntegral_le_tangent"),
      ("actualMomentBoundTheorem", .str "RiemannGaussian.GaussianFermiGammaBound.digammaAverage_le_moment"),
      ("explicitGammaBoundTheorem", .str "RiemannGaussian.GaussianFermiGammaBound.digammaAverage_le_quarter_log"),
      ("uniformGammaBoundTheorem", .str "RiemannGaussian.GaussianFermiGammaBound.digammaAverage_le_uniform_quarter_log"),
      ("nonzeroOrdinateBoundTheorem", .str "RiemannGaussian.GaussianFermiGammaBound.digammaAverage_le_log_abs"),
      ("actualPhaseBudgetTheorem", .str "RiemannGaussian.GaussianFermiGammaBound.selected_zero_phase_log_budget"),
      ("moment", .str "For a,c>0 the actual nonnegative unit-mass spectral density satisfies integral_R y^2*density(a,c,y) dy=2*c+a^2/4 and integral_R abs(y)*density(a,c,y) dy<=sqrt(2*c+a^2/4). Finiteness is proved by positive squared-sinc approximants and Fatou before dominated convergence evaluates the second moment"),
      ("digammaTangent", .str "A=5/4+abs(t); Re digamma(1/4+i*r/2)<=log(A)+(abs(r-(t-y))+abs(y))/A. The translated Gaussian has exact mass sqrt(pi/epsilon) and absolute first moment 1/epsilon"),
      ("explicitBound", .str "For a,b,c>0 and A=5/4+abs(t): D(a;b,c;t)<=log(A)/4+(sqrt(2*c+a^2/4)/4+1/(4*sqrt(pi/(4*b))))/A. The preceding theorem retains the actual spectral first absolute moment"),
      ("uniformBound", .str "For 0<a<=1,b,c>0,b+c<=1: D(a;b,c;t)<=log(5/4+abs(t))/4+7/(8*(5/4+abs(t))). For t!=0 also D<=log(abs(t))/4+19/(16*abs(t)). These are upper bounds, not two-sided asymptotic equalities"),
      ("selectedZeroBudget", .str "For every admissible finite cosine test from gaussianFermiPrimePhase, with the additional total-scale bound B=b+c<=1: sum_j w_j*sum_(rho in S) contribution(B,1-m(H),omega_j*t,rho)<=sum_j w_j*(Pole(B,1-m(H),omega_j*t)+(log(5/4+abs(omega_j*t))-log(pi))/4+7/(8*(5/4+abs(omega_j*t))))+(sum_j w_j)*allowance(B,H)"),
      ("retainedInformation", .str "Exact characteristic curvature, nonnegative sinc approximants, full spectral second moment, actual absolute first moment before its square-root bound, original gamma density, comparison ordinate retained through both displacements, all positive Gaussian splits, every selected actual zero and analytic multiplicity"),
      ("status", .str "The gamma-estimation obligation is discharged in the actual general phase budget, uniformly over admissible shrinking scales. Subsequent signed pole and target-pair estimates and an independent Gaussian surplus prove the stronger eventual width 3/(20*log(abs(t))) with all height costs discharged. The threshold is existential, not numerically evaluated. No external 4.896 theorem, independent original ordinary-prime-tail bound, historical novelty or RH proof is claimed")
    ]),
    ("gaussianFermiResonantBudget", Json.mkObj [
      ("realLaplaceTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.transform_real_re"),
      ("monotonicityTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.transform_real_antitone"),
      ("exactPartitionTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.transform_real_partition"),
      ("targetReserveTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.real_pair_eq_halfGaussian_add_reserve"),
      ("targetPairLowerBoundTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.halfGaussian_le_real_pair"),
      ("poleReserveTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.pole_zero_eq_halfGaussian_sub_reserve"),
      ("constantPoleBoundTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.pole_zero_le_halfGaussian"),
      ("nonzeroPoleBoundTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.abs_polePair_le"),
      ("allFrequencyPoleTheorem", .str "RiemannGaussian.GaussianFermiLaplaceOrder.polePair_le_poleUpper"),
      ("partnerEqualityTheorem", .str "RiemannGaussian.GaussianFermiResonantBudget.contribution_conjugatePartner"),
      ("resonanceTheorem", .str "RiemannGaussian.GaussianFermiResonantBudget.contribution_at_ordinate"),
      ("distinctPairNormalizationTheorem", .str "RiemannGaussian.GaussianFermiResonantBudget.sum_partner_pair_eq"),
      ("fullMultiplicityLowerBoundTheorem", .str "RiemannGaussian.GaussianFermiResonantBudget.halfGaussian_le_partner_pair"),
      ("actualGaussianBudgetTheorem", .str "RiemannGaussian.GaussianFermiResonantBudget.resonant_pair_phase_bound"),
      ("gaussian", .str "G_B(x)=integral_(u>0) exp(-B*u^2-x*u) du, finite for B>0 and every real x, including negative damping. Both G_B and the real Fermi transform are decreasing in x"),
      ("signedTargetIdentity", .str "F(x)+F(a-x)=G_B(x)+[F(a-x)-F(a+x)]. For x>=0 the retained bracket is nonnegative, so the full pair is at least G_B(x)"),
      ("signedPoleIdentity", .str "For a=2*sigma-1: Pole(B,sigma,0)=G_B(sigma-1)-[F(3*sigma-2)-F(sigma)]. For sigma<=1 the retained bracket is nonnegative, so the full constant pole is at most G_B(sigma-1)"),
      ("poleEnvelope", .str "U(B,sigma,v)=G_B(sigma-1) if v=0, otherwise C(2*sigma-1,B,1-sigma)/v^2, with C from gaussianFermiZeroTail. For 1/2<=sigma<=1,B>0,(1-sigma)^2<=B: Pole(B,sigma,v)<=U(B,sigma,v)"),
      ("actualSource", .str "For an actual rho=beta+i*gamma with beta>1/2, its horizontal partner 1-conj(rho) is distinct and has the same analytic multiplicity. Summing both contributions gives exactly 2*Q(rho), hence at least multiplicity(rho)*G_B(sigma-beta) when beta<=sigma. No simplicity assumption"),
      ("generalBudget", .str "For every finite nonnegative cosine test with nonnegative weights w_j and real frequencies omega_j, and a selected index j0 with omega_j0=1: w_j0*multiplicity(rho)*G_B(sigma-beta)<=sum_j w_j*(U(B,sigma,omega_j*gamma)+(log(5/4+abs(omega_j*gamma))-log(pi))/4+7/(8*(5/4+abs(omega_j*gamma))))+(sum_j w_j)*allowance(B,H)"),
      ("domain", .str "Actual rho with beta>1/2; sigma=1-m(H),H>=1,B=b+c,b,c>0,m(H)^2<=B<=1,abs(gamma)<=H,2*abs(omega_j*gamma)<=H for every selected phase. The existing region proves beta<=sigma and nonnegativity of every remaining selected zero contribution"),
      ("retainedInformation", .str "Real damping before monotone comparison, exact opposite-signed Fermi reserves for target and pole, both distinct actual horizontal partners, genuine analytic multiplicity, exact factor of two, full frequency dependence, explicit gamma normalization and complete outside divisor allowance"),
      ("status", .str "An unconditional necessary Gaussian inequality for every admissible actual right-half zero and finite phase family. The subsequent independent Gaussian surplus and complete height-cost bounds now prove the stronger eventual width 3/(20*log(abs(t))). Its threshold is existential, not numerically evaluated. The external 4.896 theorem, independent original ordinary-prime-tail bound and RH remain open; no historical novelty or best-published-region claim")
    ]),
    ("gaussianFermiZeroFreeRegion", Json.mkObj [
      ("gaussianTangentTheorem", .str "RiemannGaussian.GaussianHalfLaplaceBounds.halfGaussian_tangent_lower"),
      ("gaussianReflectionTheorem", .str "RiemannGaussian.GaussianHalfLaplaceBounds.halfGaussian_reflection"),
      ("negativeDampingTheorem", .str "RiemannGaussian.GaussianHalfLaplaceBounds.halfGaussian_neg_upper"),
      ("exactDilationTheorem", .str "RiemannGaussian.GaussianHalfLaplaceBounds.halfGaussian_scale"),
      ("positiveProfileTheorem", .str "RiemannGaussian.GaussianHalfLaplaceBounds.halfGaussian_unit_three_twentieths_lower"),
      ("negativeProfileTheorem", .str "RiemannGaussian.GaussianHalfLaplaceBounds.halfGaussian_unit_neg_sixtythree_twohundredths_upper"),
      ("generalSurplusTheorem", .str "RiemannGaussian.GaussianFermiProfileSurplus.profile_surplus"),
      ("exactFamilySurplusTheorem", .str "RiemannGaussian.GaussianFermiProfileSurplus.exact_profile_surplus"),
      ("generalScaledSurplusTheorem", .str "RiemannGaussian.GaussianFermiProfileSurplus.scaled_profile_surplus"),
      ("actualScaledSurplusTheorem", .str "RiemannGaussian.GaussianFermiProfileSurplus.exact_scaled_profile_surplus"),
      ("actualMarginIntervalTheorem", .str "RiemannGaussian.GaussianFermiHeightBounds.normalized_margin_bounds"),
      ("admissibleScaleTheorem", .str "RiemannGaussian.GaussianFermiHeightBounds.scale_admissible"),
      ("allPoleGammaCostsTheorem", .str "RiemannGaussian.GaussianFermiHeightBounds.exact_phase_cost_le"),
      ("finiteHeightContradictionTheorem", .str "RiemannGaussian.GaussianFermiZeroFree.margin_lt_one_sub_re_of_allowance_lt_one"),
      ("unconditionalRightEdgeTheorem", .str "RiemannGaussian.GaussianFermiZeroFree.exists_eventual_right_margin"),
      ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.GaussianFermiZeroFree.exists_eventual_strip"),
      ("strictWidthComparisonTheorem", .str "RiemannGaussian.GaussianFermiZeroFree.old_margin_lt_fermi_width"),
      ("literalNonvanishingTheorem", .str "RiemannGaussian.GaussianFermiZeroFree.exists_eventual_nonvanishing"),
      ("literalImprovedRegionTheorem", .str "RiemannGaussian.GaussianFermiZeroFree.exists_eventual_improved_region"),
      ("gaussianBounds", .str "G_B(x)=integral_(u>0) exp(-B*u^2-x*u) du. G_B(x)>=sqrt(pi/B)/2-x/(2*B); G_B(x)+G_B(-x)=sqrt(pi/B)*exp(x^2/(4*B)); r*G_(B*r^2)(x*r)=G_B(x). In particular G_1(3/20)>=811/1000 and G_1(-63/200)<=109/100"),
      ("generalProfile", .str "Every 0<=a0<=37/200,a1>=79/250,M<=61/100 and 1/10<=mu<=21/200 satisfies a0*G_1(-3*mu)+M/12+1/400<=a1*G_1(3*(3/20-mu)). The existing exact contact family satisfies all coefficient bounds and has total mass at most one"),
      ("actualScale", .str "For t=abs(Im(rho)),L=log(t),H=48*t,m=m_old(H),B=1/(9*L^2),b=c=B/2: L>=2000 implies 1/10<=L*m<=21/200 and m^2<=B<=1. Every phase evaluation ordinate lies within H/2"),
      ("strictSurplus", .str "For d<=3/(20*L), the genuine Gaussian source is at least a0*G_B(-m)+M*L/4+3*L/400. All analytic multiplicities and both distinct horizontal partners are retained; multiplicity is at least one"),
      ("remainingCosts", .str "For L>=4000, every nonconstant exact-family pole is at most one; gamma costs sum to at most M*L/4+7. Total pole/gamma cost is at most a0*G_B(-m)+M*L/4+8. Once the actual full allowance E(B,H)<1, its weighted cost is at most one. Thus 3*L/400<=9 would be required, contradicting L>=4000"),
      ("unconditionalRegion", .str "There exists finite T>=1 such that every actual nontrivial zero with abs(Im(rho))>=T has 3/(20*log(abs(Im(rho))))<Re(rho)<1-3/(20*log(abs(Im(rho)))). The actual uniform allowance theorem discharges the tail condition"),
      ("literalRegion", .str "For all sufficiently large abs(Im(s)), Re(s)>=1-3/(20*log(abs(Im(s)))) implies riemannZeta(s)!=0. At the same sufficiently large ordinates the new width is proved strictly larger than m_old(Im(s))"),
      ("thresholdScope", .str "The finite threshold is existential and is not numerically evaluated. The condition log(t)>=4000 alone is not a certified full threshold: the existing complete divisor-tail allowance must also be below one. The explicit all-height reserve margin remains available"),
      ("retainedInformation", .str "Exact Gaussian reflection and dilation, all real damping integrability, general coefficient bounds before the existing exact-family instance, every small higher-frequency coefficient, both genuine horizontal partners, analytic multiplicity, original signed Fermi reserves upstream, full outside divisor and its uniform scale allowance"),
      ("status", .str "The first unconditional Fermi region has exact coefficient 3/20, both actual zero-strip edges, literal nonvanishing and proved strict improvement over the preceding reserve width. Its global monotone margin supplies larger analytic discs and stronger fixed-mark squarefree decay. The subsequent margin bootstrap proves coefficient 4/25, the sharper shifted-Gaussian bound proves 9/50, endpoint curvature with complete-band feedback proves 3/16, and positive cosine modulation now proves 24/125. The numerical thresholds, external 4.896 region, independent original signed ordinary-prime-tail bound and RH remain open. No historical novelty or best-published-region claim")
    ]),
    ("gaussianFermiArithmeticTransport", Json.mkObj [
      ("provedThresholdTheorem", .str "RiemannGaussian.zetaFermiHeightThreshold_spec"),
      ("oldMarginRetainedTheorem", .str "RiemannGaussian.zetaPoleReserve_margin_le_fermi"),
      ("globalBoundsTheorem", .str "RiemannGaussian.zetaFermiZeroMargin_bounds"),
      ("heightMonotonicityTheorem", .str "RiemannGaussian.zetaFermiZeroMargin_antitone_abs"),
      ("exactLowHeightTheorem", .str "RiemannGaussian.zetaFermiZeroMargin_eq_poleReserve_of_le"),
      ("actualAllHeightStripTheorem", .str "RiemannGaussian.nontrivialZetaZero_mem_fermi_strip"),
      ("literalNonvanishingTheorem", .str "RiemannGaussian.riemannZeta_ne_zero_of_fermi_margin"),
      ("exactEventualMarginTheorem", .str "RiemannGaussian.exists_eventual_fermiZeroMargin_eq"),
      ("radiusComparisonTheorem", .str "RiemannGaussian.squarefreeEulerReserveRadius_le_fermiRadius"),
      ("strictEventualRadiusGainTheorem", .str "RiemannGaussian.exists_eventual_squarefreeEulerFermiRadius_gain"),
      ("entireDiscSafetyTheorem", .str "RiemannGaussian.squarefreeEuler_fermi_disc_safe"),
      ("actualQuotientAnalyticityTheorem", .str "RiemannGaussian.analyticOnNhd_squarefreeEulerResponse_fermi"),
      ("allMarkedPolynomialBoundTheorem", .str "RiemannGaussian.exists_squarefreeEuler_fermi_radius_bound"),
      ("allSubRadiusRatesTheorem", .str "RiemannGaussian.tendsto_squarefreeEuler_scaled_response_fermi"),
      ("actualStrongerDecayTheorem", .str "RiemannGaussian.exists_eventual_squarefreeEuler_reserve_scaled_decay"),
      ("globalMargin", .str "Choose T0 from the proved eventual strip theorem, enlarged to at least exp(4000). Set c=m_old(T0) and m_F(t)=max(m_old(t),min(c,3/(20*log(max(T0,abs(t)))))). Then 0<m_F(t)<1/4, m_old(t)<=m_F(t), and m_F is antitone in absolute height. Below T0 it equals m_old exactly; eventually it equals 3/(20*log(abs(t))) and strictly exceeds m_old"),
      ("actualRegion", .str "Every actual nontrivial zero has m_F(Im(rho))<Re(rho)<1-m_F(Im(rho)). For s!=1, Re(s)>=1-m_F(Im(s)) implies riemannZeta(s)!=0. The chosen threshold is a witness of an unconditional proved theorem, not an additional zero-free hypothesis"),
      ("analyticRadius", .str "r_F(y)=1+min((abs(y)-1)/2,m_F(2*abs(y)+3)/2). For abs(y)>1 it lies above one, below abs(y) and below 9/8. The entire closed disc centered at 3/2+i*y avoids the actual numerator pole and every zero or pole of the doubled denominator. The quotient zeta(s)/zeta(2*s) is analytic on a neighbourhood of this disc"),
      ("strictRadiusGain", .str "The new radius never decreases the preceding reserve radius. Beyond a proved finite height, r_old(y)<r_F(y)=1+3/(40*log(2*abs(y)+3))"),
      ("uniformArithmeticBound", .str "One C_y>0 works for every 0<r<=r_F(y), finite prime set S, squarefree mark P with no prime factor in S, complex polynomial p and order N: norm(response)<=C_y*squarefreeEulerBudget(3/2-r,S,P)*r^(-N)*sum_(k in support(p)) norm(p_k)*r^(-k). This is the original complete squarefree series including ordinary primes"),
      ("strongerFixedMarkDecay", .str "For every fixed valid S,P,p and 0<=a<r_F(y), a^N*response(p,S,P,N,3/2+i*y) tends to zero as a complex number. Consequently, for all sufficiently large abs(y), the response multiplied by r_old(y)^N still tends to zero. The proof pays the entire fixed Euler and polynomial factors and uses the strict ratio (r_old(y)/r_F(y))^N"),
      ("retainedInformation", .str "Both actual zero-strip edges, full-height monotonicity, exact old margin below the threshold, exact eventual coefficient 3/20, literal poles and denominator zeros, original arithmetic marks, every polynomial coefficient and phase, and the radius-dependent Euler budget"),
      ("limitations", .str "Both finite height thresholds are existential and not numerically evaluated. Growing sieves and moving marks still carry their Euler budget, so a larger radius alone does not prove an improvement for their entire bound. Positive cosine modulation now proves the stronger eventual coefficient 24/125; the radius and arithmetic statements in this object still use the first Fermi width 3/20. The independent signed ordinary-prime-tail estimate, external 4.896 theorem and RH remain open")
    ]),
    ("gaussianFermiMarginBootstrap", Json.mkObj [
      ("decreasingDerivativeCostTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.integralCost_antitone_margin"),
      ("wholeOutsideCostTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.outside_cost_le_allowance"),
      ("generalSelectedZeroTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.selected_zero_sum_le_full_add_allowance"),
      ("retainedSignedPrimeBudgetTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.selected_zero_phase_budget_with_prime"),
      ("generalExactPhaseBudgetTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.selected_zero_phase_budget"),
      ("generalResonantBudgetTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.resonant_pair_phase_bound"),
      ("actualImprovedLineBudgetTheorem", .str "RiemannGaussian.GaussianFermiMarginBudget.fermi_resonant_pair_phase_bound"),
      ("positiveGaussianEnclosureTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.halfGaussian_unit_thirtythree_thousandths_lower"),
      ("negativeGaussianEnclosureTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.halfGaussian_unit_neg_nine_twentieths_upper"),
      ("generalProfileSurplusTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.profile_surplus"),
      ("generalScaledSurplusTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.scaled_profile_surplus"),
      ("actualScaledSurplusTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.exact_scaled_profile_surplus"),
      ("admissibleScaleTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.scale_admissible"),
      ("actualNormalizedIntervalTheorem", .str "RiemannGaussian.GaussianFermiBootstrapProfile.normalized_margin_bounds_of_eq"),
      ("finiteHeightContradictionTheorem", .str "RiemannGaussian.GaussianFermiBootstrapZeroFree.margin_lt_one_sub_re_of_allowance_lt_one"),
      ("unconditionalRightEdgeTheorem", .str "RiemannGaussian.GaussianFermiBootstrapZeroFree.exists_eventual_right_margin"),
      ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.GaussianFermiBootstrapZeroFree.exists_eventual_strip"),
      ("literalNonvanishingTheorem", .str "RiemannGaussian.GaussianFermiBootstrapZeroFree.exists_eventual_nonvanishing"),
      ("strictImprovementTheorem", .str "RiemannGaussian.GaussianFermiBootstrapZeroFree.exists_eventual_improved_region"),
      ("generalMarginDomain", .str "Any m with m_old(H)<=m<=1/4 and m<=Re(rho)<=1-m for every actual zero with abs(Im(rho))<=H; H>=1; b,c>0 and m^2<=B=b+c<=1. Every finite nonnegative cosine test with nonnegative coefficients is allowed, with its evaluation ordinates within H/2. The actual global Fermi strip and height monotonicity discharge the band condition at m=m_F(H)"),
      ("tailComparison", .str "C(1-2*m,B,m)=exp(1/2)*(34*B+2*(2-3*m)^2+1)*sqrt(pi/(B/4)) decreases as m increases through the admissible range at fixed B. Therefore 4*C(1-2*m,B,m)*divisorTail(H)<=E(B,H), where E is the original allowance. The whole actual outside divisor and all multiplicities are included"),
      ("signedPrimeRetention", .str "The stronger selected-zero budget retains selectedZeroSource+sum_j w_j*primeSum(1-2*m,B,omega_j*t)<=exactPoleGammaCost+(sum_j w_j)*E(B,H), without requiring a nonnegative cosine test. The sign-only budget is a separate downstream consequence. An independent stronger floor for this literal prime combination would improve the source bound by the same amount"),
      ("actualNormalization", .str "Set t=abs(Im(rho)),L=log(t),H=48*t,m=m_F(H),B=1/(9*L^2),b=c=B/2. Once m_F(H)=3/(20*log(H)) and L>=100000, elementary logarithmic bounds give 149/1000<=L*m<=3/20, hence m^2<=B<=1. The old margin is smaller, so its scale condition also holds"),
      ("gaussianEnclosures", .str "G_1(33/1000)>=1739/2000 and G_1(-9/20)<=121/100, proved from exact Gaussian reflection, the integrated exponential tangent and checked bounds on pi and exp"),
      ("generalProfile", .str "For all 0<=a0<=37/200,a1>=79/250,M<=61/100 and 149/1000<=mu<=3/20: a0*G_1(-3*mu)+M/12+1/20000<=a1*G_1(3*(4/25-mu)). The unchanged exact phase coefficients satisfy these bounds; no new family is fitted"),
      ("completeContradiction", .str "For d<=4/(25*L), exact dilation gives source>=a0*G_B(-m)+M*L/4+3*L/20000. All pole and gamma terms cost at most a0*G_B(-m)+M*L/4+8. Once the old E(B,H)<1, the weighted tail cost is at most one. Thus the actual budget would require 3*L/20000<=9, contradicting L>=100000. The genuine multiplicity is at least one"),
      ("unconditionalRegion", .str "There exists finite T>=1 such that every actual nontrivial zero with abs(Im(rho))>=T satisfies 4/(25*log(abs(Im(rho))))<Re(rho)<1-4/(25*log(abs(Im(rho)))). Literal zeta nonvanishing on the corresponding closed right edge and strict improvement over the preceding global Fermi margin are proved"),
      ("retainedInformation", .str "Any proved common band margin before the actual instance; exact prime phase recombination; all selected zeros and every omitted zero; both distinct horizontal partners and genuine analytic multiplicity; original signed target and pole reserves upstream; actual Gaussian scale; all higher-frequency coefficient mass; original uniform tail allowance"),
      ("thresholdScope", .str "The finite threshold is existential, not numerically evaluated. exp(100000) alone is insufficient: the earlier margin transition and original complete divisor-tail allowance must also have reached their proved eventual regimes"),
      ("status", .str "One unconditional feedback step improves the eventual coefficient from 3/20 to 4/25 with no larger outside error. The explicit all-height reserve region remains available, and the existing squarefree radius transport still uses the first Fermi coefficient 3/20. No convergence of repeated feedback to the critical line is proved. The original independent signed ordinary-prime-tail bound, external 4.896 theorem and RH remain open; no historical novelty or best-published-region claim")
    ]),
    ("fermiSharpZeroFree", Json.mkObj [
      ("role", .str "Unconditional wider actual zero exclusion from a retained Gaussian endpoint identity"),
      ("exactShiftTheorem", .str "RiemannGaussian.GaussianHalfLaplaceShift.halfGaussian_neg_shift"),
      ("sharpPoleBoundTheorem", .str "RiemannGaussian.GaussianHalfLaplaceShift.halfGaussian_neg_shift_upper"),
      ("positiveEnclosureTheorem", .str "RiemannGaussian.GaussianFermiSharpProfile.halfGaussian_unit_thirtyone_fourhundredths_lower"),
      ("negativeEnclosureTheorem", .str "RiemannGaussian.GaussianFermiSharpProfile.halfGaussian_unit_neg_three_eighths_upper"),
      ("generalSurplusTheorem", .str "RiemannGaussian.GaussianFermiSharpProfile.profile_surplus"),
      ("generalScaleTheorem", .str "RiemannGaussian.GaussianFermiSharpProfile.scaled_profile_surplus"),
      ("actualSurplusTheorem", .str "RiemannGaussian.GaussianFermiSharpProfile.exact_scaled_profile_surplus"),
      ("scaleAdmissibilityTheorem", .str "RiemannGaussian.GaussianFermiSharpProfile.scale_admissible"),
      ("finiteHeightContradictionTheorem", .str "RiemannGaussian.GaussianFermiSharpZeroFree.margin_lt_one_sub_re_of_allowance_lt_one"),
      ("unconditionalRightEdgeTheorem", .str "RiemannGaussian.GaussianFermiSharpZeroFree.exists_eventual_right_margin"),
      ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.GaussianFermiSharpZeroFree.exists_eventual_strip"),
      ("literalNonvanishingTheorem", .str "RiemannGaussian.GaussianFermiSharpZeroFree.exists_eventual_nonvanishing"),
      ("strictImprovementTheorem", .str "RiemannGaussian.GaussianFermiSharpZeroFree.exists_eventual_improved_region"),
      ("retainedIdentity", .str "For every b>0 and real x, G_b(-x)=exp(x^2/(4*b))*(sqrt(pi/b)/2+integral_(-x/(2*b))^0 exp(-b*u^2) du). The finite interval retains its exact value and orientation. For x>=0 it is at most x/(2*b)"),
      ("rationalEnclosures", .str "G_1(31/400)>=3389/4000 and G_1(-3/8)<=557/500, proved using the integrated tangent, exact shifted identity, rational pi bounds and exp(9/256)<=256/247"),
      ("allCoefficientSurplus", .str "For every 0<=a0<=37/200,a1>=79/250,M<=61/100 and 149/1000<=mu<=3/20, a0*G_1(-(5/2)*mu)+M/10+1/2000<=a1*G_1((5/2)*(9/50-mu)). The original exact phase row satisfies these same bounds"),
      ("actualParameters", .str "L=log(abs(t)),H=48*abs(t),m=m_F(H),B=4/(25*L^2),b=c=B/2. The first global Fermi margin still supplies its proved 3/20 formula and normalized interval. The scale is admissible whenever L*m<=2/5"),
      ("completeContradiction", .str "For d<=9/(50*L), the source is at least a0*G_B(-m)+M*L/4+L/800. The full pole and gamma cost is at most a0*G_B(-m)+M*L/4+8; the original uniform allowance eventually makes the weighted whole-divisor tail cost at most one. With actual multiplicity at least one, a zero would require L/800<=9, contradicting L>=100000"),
      ("unconditionalRegion", .str "There exists T>=1 such that every actual nontrivial zero at abs(Im(rho))>=T satisfies 9/(50*log(abs(Im(rho))))<Re(rho)<1-9/(50*log(abs(Im(rho)))). Literal zeta is nonzero on the corresponding closed right edge. The eventual width is 9/8 times the preceding 4/25 width"),
      ("limitations", .str "The finite threshold is existential and unevaluated; exp(100000) alone does not discharge the margin-transition and whole-divisor allowance conditions. Both edge widths tend to zero with height. The global margin and squarefree-radius transport still use their first 3/20 eventual formula. No bound for the original signed prime tail or the complex moment-filtered costs follows. The external 4.896 region and RH remain open; no historical novelty or best-published-region claim")
    ]),
    ("fermiCurvatureZeroFree", Json.mkObj [
      ("role", .str "Unconditional actual zero exclusion with coefficient 3/16 from Gaussian endpoint curvature and feedback through the complete height divisor"),
      ("pointwiseCurvatureTheorem", .str "RiemannGaussian.GaussianHalfLaplaceCurvature.window_one_le_quadratic"),
      ("integratedCurvatureTheorem", .str "RiemannGaussian.GaussianHalfLaplaceCurvature.integral_window_one_le"),
      ("curvaturePoleBoundTheorem", .str "RiemannGaussian.GaussianHalfLaplaceCurvature.halfGaussian_neg_curvature_upper"),
      ("generalLogRegionFeedbackTheorem", .str "RiemannGaussian.exists_eventual_common_log_margin"),
      ("actualInputBandTheorem", .str "RiemannGaussian.exists_eventual_sharp_common_margin"),
      ("sourceEnclosureTheorem", .str "RiemannGaussian.GaussianFermiCurvatureProfile.halfGaussian_unit_nineteen_thousandths_lower"),
      ("poleEnclosureTheorem", .str "RiemannGaussian.GaussianFermiCurvatureProfile.halfGaussian_unit_neg_nine_twentieths_upper"),
      ("allCoefficientSurplusTheorem", .str "RiemannGaussian.GaussianFermiCurvatureProfile.profile_surplus"),
      ("allCoefficientScaledSurplusTheorem", .str "RiemannGaussian.GaussianFermiCurvatureProfile.scaled_profile_surplus"),
      ("actualPhaseSurplusTheorem", .str "RiemannGaussian.GaussianFermiCurvatureProfile.exact_scaled_profile_surplus"),
      ("normalizedMarginTheorem", .str "RiemannGaussian.GaussianFermiCurvatureProfile.normalized_margin_bounds"),
      ("finiteHeightContradictionTheorem", .str "RiemannGaussian.GaussianFermiCurvatureZeroFree.margin_lt_one_sub_re_of_allowance_lt_one"),
      ("unconditionalRightEdgeTheorem", .str "RiemannGaussian.GaussianFermiCurvatureZeroFree.exists_eventual_right_margin"),
      ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.GaussianFermiCurvatureZeroFree.exists_eventual_strip"),
      ("commonBandTheorem", .str "RiemannGaussian.GaussianFermiCurvatureZeroFree.exists_eventual_common_margin"),
      ("literalNonvanishingTheorem", .str "RiemannGaussian.GaussianFermiCurvatureZeroFree.exists_eventual_nonvanishing"),
      ("retainedCurvature", .str "For u^2<=h^2, exp(-u^2)<=1-u^2/(1+h^2). For h>=0 the full shifted interval integral is at most h-h^3/(3*(1+h^2)). Completing the square retains this cubic improvement in the negative-damping pole estimate. The exact shifted-interval identity remains available upstream"),
      ("generalFeedback", .str "Any positive coefficient a with a proved eventual logarithmic zero strip yields a common margin a/log(H) for every actual zero of abs(Im(rho))<=H at all sufficiently large H. The bounded-height zeros are controlled by the existing positive global margin. The actual 9/50 region supplies the input to this comparison, and the new 3/16 region is fed through the same construction for later budgets"),
      ("uniformProfile", .str "G_1(19/1000)>=1753/2000 and G_1(-9/20)<=1167/1000. For every 0<=a0<=37/200,a1>=79/250,M<=61/100 and 1799/10000<=mu<=9/50, a0*G_1(-(5/2)*mu)+M/10+1/20000<=a1*G_1((5/2)*(3/16-mu)). The existing exact phase row satisfies this entire coarse class; no new coefficients are fitted"),
      ("actualContradiction", .str "With L=log(abs(t)),H=48*abs(t),m=9/(50*log(H)),B=4/(25*L^2), a proposed zero at distance d<=3/(16*L) gives source at least a0*G_B(-m)+M*L/4+L/8000. The full pole and gamma cost is at most a0*G_B(-m)+M*L/4+8. The original complete divisor allowance eventually pays its weighted tail by one, so the actual multiplicity-aware budget would require L/8000<=9, contradicting L>=100000"),
      ("unconditionalRegion", .str "There exists finite T>=1 such that every actual nontrivial zero with abs(Im(rho))>=T satisfies 3/(16*log(abs(Im(rho))))<Re(rho)<1-3/(16*log(abs(Im(rho)))). Literal zeta is nonzero on the corresponding closed right edge. A further proved finite threshold supplies this same coefficient as a common margin for the entire bounded-height divisor"),
      ("limitations", .str "The height threshold is existential and unevaluated; exp(100000) alone does not discharge the common-band, older global-margin and complete divisor-tail conditions. The newer Fisher tail bound is not needed for this leading coefficient gain. The original global zetaFermiZeroMargin and older squarefree-radius transport keep their 3/20 eventual formula. The independent signed ordinary-prime estimate, external 4.896 region and RH remain open. No repeated-feedback convergence, historical novelty or best-published-region claim is made")
    ]),
    ("fermiCosineModulation", Json.mkObj [
      ("role", .str "Positive cosine modulation of the actual Fermi source, prime series and complete zero budget; the downstream exact comparison now proves the 24/125 eventual zero-free region"),
      ("factorBoundsTheorem", .str "RiemannGaussian.FermiCosineModulation.factor_bounds"),
      ("nonnegativeWindowTheorem", .str "RiemannGaussian.FermiCosineModulation.modulate_nonneg"),
      ("endpointNormalizationTheorem", .str "RiemannGaussian.FermiCosineModulation.modulate_zero"),
      ("windowContinuityTheorem", .str "RiemannGaussian.FermiCosineModulation.continuous_modulate"),
      ("allExponentialMomentsTheorem", .str "RiemannGaussian.FermiCosineModulation.integrable_modulate_exp"),
      ("exactExponentialIdentityTheorem", .str "RiemannGaussian.FermiCosineModulation.factor_mul_exp"),
      ("exactThreeFrequencyTransformTheorem", .str "RiemannGaussian.FermiCosineModulation.transform_modulate"),
      ("exactReflectedPairTheorem", .str "RiemannGaussian.FermiCosineModulation.reflected_pair_modulate"),
      ("generalPairPositivityTheorem", .str "RiemannGaussian.FermiCosineModulation.reflected_pair_nonneg"),
      ("actualGaussianPositivityTheorem", .str "RiemannGaussian.FermiCosineModulation.gaussian_reflected_pair_nonneg"),
      ("realIntegralTheorem", .str "RiemannGaussian.FermiCosineModulation.transform_real_re"),
      ("realMonotonicityTheorem", .str "RiemannGaussian.FermiCosineModulation.transform_real_antitone"),
      ("exactWindowPartitionTheorem", .str "RiemannGaussian.FermiCosineModulation.real_partition"),
      ("retainedSignedSourceReserveTheorem", .str "RiemannGaussian.FermiCosineModulation.real_pair_eq_halfLaplace_add_reserve"),
      ("generalSourceComparisonTheorem", .str "RiemannGaussian.FermiCosineModulation.halfLaplace_le_real_pair"),
      ("generalPoleComparisonTheorem", .str "RiemannGaussian.FermiCosineModulation.real_pole_pair_le_halfLaplace"),
      ("finiteSumRetentionTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.average_sum"),
      ("coupledCosineIdentityTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.average_cos"),
      ("actualPrimeHasSumTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.hasSum_prime_modulated"),
      ("allPhasePrimeHasSumTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.hasSum_prime_phase"),
      ("actualPrimeSignTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.prime_phase_nonneg"),
      ("fullSignedBudgetTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.selected_zero_phase_budget_with_prime"),
      ("primeSignBudgetTheorem", .str "RiemannGaussian.GaussianFermiModulatedBudget.selected_zero_phase_budget"),
      ("actualFrequencyTransformTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.average_transform"),
      ("fullContributionTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.average_contribution_eq"),
      ("resonantContributionTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.average_contribution_at_ordinate"),
      ("multiplicitySourceTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.halfLaplace_le_contribution"),
      ("fullPartnerSourceTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.halfLaplace_le_partner_pair"),
      ("coupledConstantPoleTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.average_pole_zero_eq"),
      ("retainedPoleBoundTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.average_pole_zero_le"),
      ("allFamilyActualSourceTheorem", .str "RiemannGaussian.GaussianFermiModulatedSource.resonant_pair_phase_bound"),
      ("window", .str "g_(B,delta)(u)=exp(-B*u^2)*(1+cos(delta*u))/2. For every real delta and B>0 it is nonnegative, normalized at zero, and has all exponential moments. The exact Fermi transform is the positive combination with weights 1/2,1/4,1/4 at z,z+i*delta,z-i*delta. Reflection keeps the same three coupled shifts"),
      ("actualArithmetic", .str "Every original von Mangoldt prime-power summand is multiplied by (1+cos(delta*log(n)))/2. A genuine HasSum identity proves this equals the three original prime evaluations. Every finite original phase family with a nonnegative full cosine kernel retains nonnegative whole prime work; individual oscillatory prime terms are not assigned a sign"),
      ("sourceAndPole", .str "Both distinct horizontal partners retain m_rho*H_g(sigma-beta). The actual averaged constant pole is bounded above by H_g(sigma-1), for the same modulated time window g. The exact signed Fermi source reserve stays upstream. The terminal actual all-family source budget retains the complete averaged pole/gamma costs and all analytic multiplicities"),
      ("outsideCost", .str "The complete original outside allowance is unchanged: the three positive averaging weights have total mass one. Every base frequency must satisfy 2*(abs(omega_j*t)+abs(delta))<=H, and the original common-band, comparison-margin and Gaussian-scale hypotheses remain explicit"),
      ("nextObligation", .str "The downstream fermiModulatedZeroFree object closes the exact scalar enclosures, dilation, shifted pole/gamma costs and all eventual thresholds at B=1/(9*log(t)^2),delta=1/(2*log(t)). Further progress must control the independent signed prime estimate or prove a stronger region with all costs retained"),
      ("limitations", .str "These general identities do not alone bound the separate factorial-moment prime heat. The downstream full comparison proves the larger eventual 24/125 edge region with an existential unevaluated threshold. No historical novelty claim; RH remains open")
    ]),
    ("fermiModulatedZeroFree", Json.mkObj [
      ("role", .str "Unconditional actual 24/125 logarithmic zero exclusion from positive cosine modulation, exact signed moments and complete costs"),
      ("unconditionalBothEdgesTheorem", .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_strip"),
      ("literalNonvanishingTheorem", .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_nonvanishing"),
      ("latestCommonBandTheorem", .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_common_margin"),
      ("allCoefficientSurplusTheorem", .str "RiemannGaussian.GaussianFermiModulatedProfile.profile_surplus"),
      ("actualSourceEnclosureTheorem", .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfModulated_source_lower"),
      ("actualPoleEnclosureTheorem", .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfModulated_pole_upper"),
      ("completeHeightCostTheorem", .str "RiemannGaussian.GaussianFermiModulatedHeight.exact_average_phase_cost_le"),
      ("signedMoments", .str "For every n and real damping x, M_n(x)=integral_(0,infinity) u^n*exp(-u^2-x*u)du is absolutely integrable. The exact endpoint recurrence is 2*M_1+x*M_0=1; all higher orders satisfy 2*M_(n+2)+x*M_(n+1)=(n+1)*M_n. No alternating coefficient is replaced by its absolute value before integration"),
      ("exactEnclosures", .str "For H_(B,delta)(x)=integral_(0,infinity) exp(-B*u^2)*(1+cos(delta*u))/2*exp(-x*u)du, H_(1,3/2)(69/5000)>=6911/10000 and H_(1,3/2)(-9/16)<=2263/2500. The source uses exact Fourier mass and first moment <=83/256. The pole uses a global degree-twelve cosine majorant and exact moment recurrence. No quadrature or numerical oracle"),
      ("uniformProfile", .str "For every 0<=a0<=37/200,a1>=79/250,M<=61/100 and 937/5000<=mu<=3/16, a0*H_(1,3/2)(-3*mu)+M/12+1/20000<=a1*H_(1,3/2)(3*(24/125-mu)). The original exact phase row satisfies this entire coefficient class; no new base phase coefficients are fitted"),
      ("actualParameters", .str "L=log(abs(t)),H=50*abs(t),m=3/(16*log(H)),B=1/(9*L^2),delta=1/(2*L),b=c=B/2. The proved 3/16 common-band theorem supplies every input zero location. At L>=100000 the normalized margin lies in the stated interval and every shifted ordinate stays in the complete band"),
      ("completeContradiction", .str "A zero at distance d<=24/(125*L) gives source at least a0*H_(B,delta)(-m)+M*L/4+3*L/20000. Full shifted pole and gamma costs are at most a0*H_(B,delta)(-m)+M*L/4+9. The unchanged complete outside allowance eventually pays its weighted cost by one. Full analytic multiplicity is at least one, so the actual budget would require 3*L/20000<=10, contradicting L>=100000"),
      ("unconditionalRegion", .str "There exists finite T>=1 such that every actual nontrivial zero above T satisfies 24/(125*log(abs(Im(rho))))<Re(rho)<1-24/(125*log(abs(Im(rho)))). Literal zeta is nonzero on the closed right edge. The same coefficient supplies a common margin for every actual zero below H at every sufficiently large H"),
      ("limitations", .str "The height threshold is existential and unevaluated; exp(100000) alone does not discharge the common-band, older margin and whole-divisor-tail thresholds. The edges still shrink as 1/log(height). The original global zetaFermiZeroMargin and older squarefree-radius transport retain their definitions. No independent signed factorial-moment prime bound, global RH bound, finite zero-count improvement, best-published-region or historical novelty claim follows. RH remains open"),
      ("documentation", .str "docs/gaussian-fermi-modulated-zero-free.md"),
      ("publicTheorems", .arr #[
        .str "RiemannGaussian.CosineTaylorEnclosure.abs_sub_taylor_le",
        .str "RiemannGaussian.CosineTaylorEnclosure.cos_le_quartic",
        .str "RiemannGaussian.CosineTaylorEnclosure.cos_le_degree_twelve",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.integrable_atom",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.tendsto_atom",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.moment_zero",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.moment_one",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.moment_recurrence",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.moment_one_eq",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.moment_succ_succ",
        .str "RiemannGaussian.GaussianHalfLaplaceMoments.integral_sum_atoms",
        .str "RiemannGaussian.GaussianModulatedLaplace.integrable_halfModulated",
        .str "RiemannGaussian.GaussianModulatedLaplace.halfModulated_nonneg",
        .str "RiemannGaussian.GaussianModulatedLaplace.halfModulated_antitone",
        .str "RiemannGaussian.GaussianModulatedLaplace.halfModulated_scale",
        .str "RiemannGaussian.GaussianModulatedLaplace.halfModulated_zero",
        .str "RiemannGaussian.GaussianModulatedLaplace.integrable_atom_factor",
        .str "RiemannGaussian.GaussianModulatedLaplace.halfModulated_tangent_lower",
        .str "RiemannGaussian.GaussianModulatedLaplace.first_moment_le",
        .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfModulated_zero_lower",
        .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.first_moment_upper",
        .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfModulated_source_lower",
        .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfGaussian_pole_upper",
        .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfModulated_le_moment_polynomial",
        .str "RiemannGaussian.GaussianModulatedLaplaceEnclosure.halfModulated_pole_upper",
        .str "RiemannGaussian.GaussianFermiModulatedProfile.profile_surplus",
        .str "RiemannGaussian.GaussianFermiModulatedProfile.scaled_profile_surplus",
        .str "RiemannGaussian.GaussianFermiModulatedProfile.exact_scaled_profile_surplus",
        .str "RiemannGaussian.GaussianFermiModulatedProfile.normalized_margin_bounds",
        .str "RiemannGaussian.GaussianFermiModulatedProfile.scale_admissible",
        .str "RiemannGaussian.GaussianFermiModulatedHeight.gammaUpper_le_shifted",
        .str "RiemannGaussian.GaussianFermiModulatedHeight.frequency_shift_bounds",
        .str "RiemannGaussian.GaussianFermiModulatedHeight.polePair_le_one",
        .str "RiemannGaussian.GaussianFermiModulatedHeight.digamma_cost_le",
        .str "RiemannGaussian.GaussianFermiModulatedHeight.exact_average_phase_cost_le",
        .str "RiemannGaussian.GaussianFermiModulatedZeroFree.margin_lt_one_sub_re_of_allowance_lt_one",
        .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_right_margin",
        .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_strip",
        .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_common_margin",
        .str "RiemannGaussian.GaussianFermiModulatedZeroFree.exists_eventual_nonvanishing"
      ])
    ]),
    ("fullRadiusZeroFreeToolkit", fullRadiusZeroFreeToolkit),
    ("caratheodoryZeroFreeToolkit", caratheodoryZeroFreeToolkit),
    ("zetaLogLogZeroFreeToolkit", zetaLogLogZeroFreeToolkit),
    ("zetaArbitraryLogZeroFreeToolkit", zetaArbitraryLogZeroFreeToolkit),
    ("zetaGaussianLocalJensenToolkit", zetaGaussianLocalJensenToolkit),
    ("zetaSechLogarithmicToolkit", zetaSechLogarithmicToolkit),
    ("zetaNearOneLineToolkit", zetaNearOneLineToolkit),
    ("zetaDyadicPowerToolkit", zetaDyadicPowerToolkit),
    ("uniformDerivativePowerToolkit", uniformDerivativePowerToolkit),
    ("higherDerivativeRecursionToolkit", Json.mkObj [
      ("role", .str "Classical finite derivative induction at every order and for every adaptive cutoff rule; all derivative hypotheses are discharged for the original logarithmic phase and the full damped complex Dirichlet terms"),
      ("exactConjugationTheorem", .str "RiemannGaussian.PhaseConjugation.weighted_sum_conj"),
      ("allOrientationNormTheorem", .str "RiemannGaussian.PhaseConjugation.norm_sum_neg_one_pow"),
      ("exactNaturalOverlapTheorem", .str "RiemannGaussian.NatPhaseDifferencing.overlap_eq"),
      ("naturalDifferencingTheorem", .str "RiemannGaussian.NatPhaseDifferencing.bound"),
      ("originalDomainTheorem", .str "RiemannGaussian.ShiftedDerivativeFamily.overlap_subset"),
      ("allDerivativeTransportTheorem", .str "RiemannGaussian.ShiftedDerivativeFamily.derivative_family"),
      ("actualLagScaleTheorem", .str "RiemannGaussian.ShiftedDerivativeFamily.top_bounds"),
      ("nonnegativeBudgetTheorem", .str "RiemannGaussian.DerivativeRecursionBudget.nonneg"),
      ("trivialFallbackTheorem", .str "RiemannGaussian.DerivativeRecursionBudget.le_length"),
      ("allPositiveBaseScalesTheorem", .str "RiemannGaussian.DerivativeRecursionBudget.base_le"),
      ("allOrderInductionTheorem", .str "RiemannGaussian.HigherDerivativeTest.bound"),
      ("actualAllDerivativeTheorem", .str "RiemannGaussian.LogarithmicDerivativeFamily.hasDerivAt_jet"),
      ("actualOrientedTopTheorem", .str "RiemannGaussian.LogarithmicDerivativeFamily.oriented_top"),
      ("actualAllDyadicBoundsTheorem", .str "RiemannGaussian.LogarithmicDerivativeFamily.dyadic_bounds"),
      ("actualLogarithmicBoundTheorem", .str "RiemannGaussian.HigherLogarithmicDerivativeBound.bound"),
      ("completeDampingTheorem", .str "RiemannGaussian.DirichletHigherDerivativeBound.damped_bound"),
      ("originalDirichletBoundTheorem", .str "RiemannGaussian.DirichletHigherDerivativeBound.feature_bound"),
      ("parameterFamily", .str "The arbitrary natural-valued rule kappa(k,L,ell,A) selects the positive shift count H=kappa(k,L,ell,A)+1. It can depend on order, common length cap, scaled derivative size and ratio. No coefficients are fitted and no cancellation premise is assumed"),
      ("baseBudget", .str "For 0<ell<=1, D_0=min(L,(3+2*pi)*(A*L*sqrt(ell)/(2*pi)+2/sqrt(ell))); otherwise D_0=L. For every ell>0 and A>=1 the same square-root envelope bounds the fallback, so analytic base estimates have no omitted large-curvature case"),
      ("recursiveBudget", .str "D_(k+1)=min(L,sqrt((L+H-1)/H^2*(H*L+2*sum_(0<=j<H)(H-j-1)*D_k(L,(j+1)*ell,A)))). Every lag keeps its own scaled derivative size. The expression is finite and defined without reference to an unknown phase sum"),
      ("genericScope", .str "A genuine real derivative family F_r through order k+2 on [a,a+N], with ell<=F_(k+2)<=A*ell, ell>0, A>=0 and N<=L, satisfies norm(sum exp(i*F_0(a+n)))<=D_k. Monotonicity of the top derivative is not assumed. The same cap works for every partial block"),
      ("retainedInformation", .str "The original h-lag overlap has exactly N-h terms and is empty if h>N. Both shifted endpoints and their mean-value interval stay inside [a,a+N]. Differencing preserves the derivative ratio and scales its lower bound by exactly h. The common-cap envelope can overpay overlap lengths and empty lags; the exact original identities remain available upstream"),
      ("actualDerivativeFamily", .str "For x>0, F_0=-t*log(x) and F_(r+1)=(-1)^(r+1)*t*r!/x^(r+1), with every HasDerivAt relation proved. One consistent orientation makes the chosen top derivative positive; exact conjugation restores the original phase norm"),
      ("actualDirichletScope", .str "For s=sigma+i*t, sigma>=0, t>0, X>0, natural a>=X and a+N<=2*X, set ell_k=t*(k+1)!/(2*X)^(k+2), A_k=2^(k+2). For every k and kappa, norm(sum_(n<N) zetaPrimeFeature(s,a+n))<=zetaPrimeExpWeight(sigma,a)*D_k(N,ell_k,A_k). No resonance avoidance or upper-height restriction is assumed"),
      ("literature", .str "Yang, Explicit bounds on zeta(s) in the critical strip and a zero-free region, JMAA 2024, Section 2, https://arxiv.org/html/2301.03165v2#S2. Classical mathematics; the paper's optimized constants are not claimed"),
      ("limitations", .str "The recursion and its closed uniform power bound are proved; see uniformDerivativePowerToolkit for the analytic cutoff, complete lag sums and uniform constants. The full finite zeta bound and small-block range are now proved in zetaDyadicPowerToolkit. The complete near-one line estimate is now proved in zetaNearOneLineToolkit. The complete local zero detector now proves every fixed logarithmic coefficient eventually in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit. Extra prime, sieve and moment weights require independent variation or correlation control. These upstream estimates are used by the stronger region in zetaArbitraryLogZeroFreeToolkit; the fixed-ordinate signed prime lower bound and RH remain open"),
      ("documentation", .str "docs/all-order-dirichlet-recursion.md"),
      ("publicTheorems", .arr #[
        .str "RiemannGaussian.PhaseConjugation.rotation_neg",
        .str "RiemannGaussian.PhaseConjugation.weighted_sum_conj",
        .str "RiemannGaussian.PhaseConjugation.norm_sum_neg",
        .str "RiemannGaussian.PhaseConjugation.norm_sum_neg_one_pow",
        .str "RiemannGaussian.PhaseConjugation.neg_one_pow_mul_self",
        .str "RiemannGaussian.NatPhaseDifferencing.sum_Ico_zero",
        .str "RiemannGaussian.NatPhaseDifferencing.overlap_eq",
        .str "RiemannGaussian.NatPhaseDifferencing.trivial_bound",
        .str "RiemannGaussian.NatPhaseDifferencing.bound",
        .str "RiemannGaussian.ShiftedDerivativeFamily.hasDerivAt_difference",
        .str "RiemannGaussian.ShiftedDerivativeFamily.overlap_subset",
        .str "RiemannGaussian.ShiftedDerivativeFamily.derivative_family",
        .str "RiemannGaussian.ShiftedDerivativeFamily.top_bounds",
        .str "RiemannGaussian.DerivativeRecursionBudget.shiftCount_pos",
        .str "RiemannGaussian.DerivativeRecursionBudget.nonneg",
        .str "RiemannGaussian.DerivativeRecursionBudget.le_length",
        .str "RiemannGaussian.DerivativeRecursionBudget.base_le",
        .str "RiemannGaussian.HigherDerivativeTest.bound",
        .str "RiemannGaussian.LogarithmicDerivativeFamily.hasDerivAt_jet",
        .str "RiemannGaussian.LogarithmicDerivativeFamily.hasDerivAt_oriented",
        .str "RiemannGaussian.LogarithmicDerivativeFamily.oriented_top",
        .str "RiemannGaussian.LogarithmicDerivativeFamily.lowerScale_pos",
        .str "RiemannGaussian.LogarithmicDerivativeFamily.ratio_pos",
        .str "RiemannGaussian.LogarithmicDerivativeFamily.dyadic_bounds",
        .str "RiemannGaussian.HigherLogarithmicDerivativeBound.bound",
        .str "RiemannGaussian.DirichletHigherDerivativeBound.damped_bound",
        .str "RiemannGaussian.DirichletHigherDerivativeBound.feature_bound"
      ])
    ]),
    ("secondDerivativeCancellationToolkit", Json.mkObj [
      ("role", .str "Classical second-derivative cancellation with exact integer twists, a complete finite resonance partition and genuine two-sided curvature bounds; every analytic hypothesis is discharged for literal damped Dirichlet terms on the stated dyadic blocks"),
      ("exactTwistTheorem", .str "RiemannGaussian.FiniteKuzminLandauPeriodic.rotation_twist"),
      ("completeNonresonantBlockTheorem", .str "RiemannGaussian.FiniteKuzminLandauPeriodic.bound_Ico"),
      ("actualBandCardinalityTheorem", .str "RiemannGaussian.MonotonePhaseBlocks.band_card_le"),
      ("exactComplexPartitionTheorem", .str "RiemannGaussian.FiniteResonancePartition.sum_eq_bands"),
      ("resonantBandBoundTheorem", .str "RiemannGaussian.DiscreteSecondDerivativeTest.resonant_band_bound"),
      ("completeCellCountTheorem", .str "RiemannGaussian.DiscreteSecondDerivativeTest.cells_card_le_of_separation"),
      ("fullIncrementSeparationTheorem", .str "RiemannGaussian.SecondDerivativeIncrements.increment_gap_bounds"),
      ("generalSecondDerivativeTheorem", .str "RiemannGaussian.SecondDerivativeTest.bound"),
      ("squareRootScaleTheorem", .str "RiemannGaussian.SecondDerivativeTest.square_root_bound"),
      ("actualLogarithmicBoundTheorem", .str "RiemannGaussian.LogarithmicSecondDerivativeTest.square_root_bound"),
      ("fullDampingTheorem", .str "RiemannGaussian.DirichletSecondDerivativeBound.damped_bound"),
      ("originalDirichletBoundTheorem", .str "RiemannGaussian.DirichletSecondDerivativeBound.feature_bound"),
      ("retainedInformation", .str "The translated floor assigns every original index to an exact half-open cell. Each cell splits into a near-resonant band and a complete nonresonant band. The partition holds for arbitrary complex summands before taking norms. Integer twists preserve each rotation exactly; both endpoint cells and all cutoff indices are retained"),
      ("discreteEstimate", .str "For ell>0, U>=0, 0<eta<=pi, and ell*(j-i)<=delta_j-delta_i<=U*(j-i) for i<=j<N, norm(sum exp(i*phi_n)) <= (U*N/(2*pi)+2)*(2*eta/ell+1+2*pi/eta). No phase winding or resonance-avoidance hypothesis is imposed"),
      ("continuousEstimate", .str "HasDerivAt f f' and HasDerivAt f' f'' on [a,a+N], ell<=f''<=A*ell, 0<ell<=1 and A>=0 imply norm(sum exp(i*f(a+n))) <= (3+2*pi)*(A*N*sqrt(ell)/(2*pi)+2/sqrt(ell)). The proof uses the real unit increment and retains the full index separation"),
      ("actualParameterRange", .str "s=sigma+i*t, sigma>=0, t>0, X>0, positive natural a>=X, a+N<=2*X, t<=4*X^2. With ell=t/(4*X^2), norm(sum_(n<N) zetaPrimeFeature(s,a+n)) <= zetaPrimeExpWeight(sigma,a)*(3+2*pi)*(4*N*sqrt(ell)/(2*pi)+2/sqrt(ell)). The logarithmic curvature t/x^2 and all positive-domain conditions are proved"),
      ("literature", .str "Yang, Explicit bounds on zeta(s) in the critical strip and a zero-free region, JMAA 2024, https://arxiv.org/html/2301.03165v2. Classical mathematics with coarse proved constants; no historical novelty claim"),
      ("limitations", .str "The generic curvature theorem currently treats positive curvature. The actual Dirichlet theorem concerns coefficients equal to one with their full real damping. Extra prime, sieve and moment weights require separate variation or correlation control. The all-order finite recurrence is now proved in higherDerivativeRecursionToolkit. The closed uniform power bound is now proved in uniformDerivativePowerToolkit. The full finite zeta bound and small-block range are now proved in zetaDyadicPowerToolkit. The complete near-one line estimate is now proved in zetaNearOneLineToolkit. The complete local zero detector now proves every fixed logarithmic coefficient eventually in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit. These upstream estimates are used by the stronger region in zetaArbitraryLogZeroFreeToolkit; the fixed-ordinate signed prime bound and RH remain open"),
      ("documentation", .str "docs/second-derivative-dirichlet-bound.md"),
      ("publicTheorems", .arr #[
        .str "RiemannGaussian.FiniteKuzminLandauPeriodic.rotation_int_period",
        .str "RiemannGaussian.FiniteKuzminLandauPeriodic.rotation_twist",
        .str "RiemannGaussian.FiniteKuzminLandauPeriodic.increment_twist",
        .str "RiemannGaussian.FiniteKuzminLandauPeriodic.bound_period",
        .str "RiemannGaussian.FiniteKuzminLandauPeriodic.bound_Ico",
        .str "RiemannGaussian.MonotonePhaseBlocks.mem_band",
        .str "RiemannGaussian.MonotonePhaseBlocks.band_eq_Ico",
        .str "RiemannGaussian.MonotonePhaseBlocks.band_card_le",
        .str "RiemannGaussian.MonotonePhaseBlocks.nonresonant_band_bound",
        .str "RiemannGaussian.FiniteResonancePartition.cellIndex_mono",
        .str "RiemannGaussian.FiniteResonancePartition.cellIndex_eq_iff",
        .str "RiemannGaussian.FiniteResonancePartition.cellIndex_mem_cells",
        .str "RiemannGaussian.FiniteResonancePartition.cell_eq_filter",
        .str "RiemannGaussian.FiniteResonancePartition.band_sum_split",
        .str "RiemannGaussian.FiniteResonancePartition.sum_eq_bands",
        .str "RiemannGaussian.FiniteResonancePartition.cells_card_le",
        .str "RiemannGaussian.DiscreteSecondDerivativeTest.monotone_of_separation",
        .str "RiemannGaussian.DiscreteSecondDerivativeTest.resonant_band_bound",
        .str "RiemannGaussian.DiscreteSecondDerivativeTest.cells_card_le_of_separation",
        .str "RiemannGaussian.DiscreteSecondDerivativeTest.bound",
        .str "RiemannGaussian.SecondDerivativeIncrements.difference_bounds",
        .str "RiemannGaussian.SecondDerivativeIncrements.hasDerivAt_unitIncrement",
        .str "RiemannGaussian.SecondDerivativeIncrements.unitIncrement_eq",
        .str "RiemannGaussian.SecondDerivativeIncrements.increment_gap_bounds",
        .str "RiemannGaussian.SecondDerivativeTest.bound",
        .str "RiemannGaussian.SecondDerivativeTest.square_root_bound",
        .str "RiemannGaussian.LogarithmicSecondDerivativeTest.hasDerivAt_first",
        .str "RiemannGaussian.LogarithmicSecondDerivativeTest.curvature_bounds",
        .str "RiemannGaussian.LogarithmicSecondDerivativeTest.bound",
        .str "RiemannGaussian.LogarithmicSecondDerivativeTest.square_root_bound",
        .str "RiemannGaussian.DirichletSecondDerivativeBound.damping_antitoneOn",
        .str "RiemannGaussian.DirichletSecondDerivativeBound.damped_bound",
        .str "RiemannGaussian.DirichletSecondDerivativeBound.feature_bound"
      ])
    ]),
    ("firstDerivativeCancellationToolkit", Json.mkObj [
      ("role", .str "Classical first-derivative cancellation with exact inverse-increment and Abel identities; every hypothesis is discharged for complete damped Dirichlet overlap correlations in the stated admissible regime"),
      ("exactInverseTheorem", .str "RiemannGaussian.PhaseIncrementInverse.inverseStep_eq"),
      ("inverseOrderingTheorem", .str "RiemannGaussian.PhaseIncrementInverse.inverseStep_im_monotoneOn"),
      ("exactSignedIdentityTheorem", .str "RiemannGaussian.FiniteKuzminLandau.phase_sum_identity"),
      ("discreteCancellationTheorem", .str "RiemannGaussian.FiniteKuzminLandau.bound"),
      ("actualMeanValueWitnessTheorem", .str "RiemannGaussian.FirstDerivativeTest.increment_witness"),
      ("firstDerivativeTestTheorem", .str "RiemannGaussian.FirstDerivativeTest.bound"),
      ("actualLogarithmicCancellationTheorem", .str "RiemannGaussian.LogarithmicShiftCancellation.log_ratio_bound"),
      ("exactWeightedIdentityTheorem", .str "RiemannGaussian.FiniteAbelVariation.weighted_sum_eq"),
      ("allComplexWeightBudgetTheorem", .str "RiemannGaussian.FiniteAbelVariation.weighted_bound"),
      ("exactDecreasingWeightBudgetTheorem", .str "RiemannGaussian.FiniteAbelVariation.decreasing_budget"),
      ("actualDampingTheorem", .str "RiemannGaussian.DirichletOverlapCancellation.feature_pair"),
      ("actualDampedCorrelationTheorem", .str "RiemannGaussian.DirichletOverlapCancellation.correlation_bound"),
      ("actualCompleteDirichletBlockBoundTheorem", .str "RiemannGaussian.DirichletOverlapCancellation.vanDerCorput_bound"),
      ("retainedInformation", .str "The literal inverse of exp(i*delta)-1 has constant real part -1/2 and ordered imaginary part -cot(delta/2)/2 between neighbouring resonances. Complete signed summation by parts retains both endpoints and every variation term. Norms are taken after the variation telescopes. All reciprocal uses have genuine zero avoidance"),
      ("firstDerivativeScope", .str "Angles in radians. A monotone or antitone derivative in [eta,2*pi-eta] throughout the actual closed interval [a,a+N], eta>0, gives norm(sum_(0<=n<N) exp(i*f(a+n)))<=2*pi/eta. Each increment has a mean-value witness in its original unit interval. This is the coarse Kuzmin constant, not the optimal Landau constant"),
      ("actualParameterRange", .str "t,h,X>0, h<=X, X<=a, a+N<=2X, t*h<=pi*X^2. The shifted phase -t*log(1+h/x) has decreasing derivative between t*h/(6X^2) and t*h/X^2<=pi. All first-derivative hypotheses are discharged, giving the explicit upper bound 12*pi*X^2/(t*h)"),
      ("weightedTransport", .str "All complex weights retain the explicit cost norm(w_last)+sum norm(w_n-w_(n+1)). For nonnegative decreasing real weights the cost is exactly w_0. The actual overlap damping D_sigma,h(x)=exp(-sigma*(log(x+h)+log(x))) is positive and decreasing for sigma>=0"),
      ("actualCorrelationBound", .str "For s=sigma+i*t with sigma>=0 and t>0, the complete original positive-shift correlation C_s(h) of a finite zetaPrimeFeature block has norm <= (12*pi*X^2/(t*h))*D_sigma,h(a) in the actual parameter range. Integer-to-natural conversion is justified on the positive block; all overlaps and empty shifts are exact"),
      ("actualWholeBlockBound", .str "If 0<H<=X and t*H<=pi*X^2, all positive lags in the original finite van der Corput inequality receive the proved correlation estimate. The exact N+H-1 factor, original diagonal energy, triangular shift weights and initial damping remain explicit. No hypothetical-zero premise or assumed arithmetic cancellation is used"),
      ("literature", .str "Arias de Reyna, On Kuzmin-Landau Lemma, https://arxiv.org/abs/2002.05982; Yang, Explicit bounds on zeta(s) in the critical strip and a zero-free region, JMAA 2024, https://arxiv.org/html/2301.03165v2. Classical mathematics, no historical novelty claim"),
      ("limitations", .str "The complete Dirichlet estimate concerns coefficients equal to one with their actual real damping. Extra prime, sieve and polynomial weights require independent control of their variation or arithmetic correlations. The complete second-derivative test and actual damped Dirichlet bound are now proved in secondDerivativeCancellationToolkit. The all-order finite recurrence and actual Dirichlet bound are now proved in higherDerivativeRecursionToolkit. The closed uniform power bound is now proved in uniformDerivativePowerToolkit. The full finite zeta bound and small-block range are now proved in zetaDyadicPowerToolkit. The complete near-one line estimate is now proved in zetaNearOneLineToolkit. The complete local zero detector now proves every fixed logarithmic coefficient eventually in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit. This finite estimate alone does not prove zero exclusion. The downstream arbitrary-coefficient region is proved; the fixed-ordinate signed infinite-prime lower bound and RH remain open"),
      ("documentation", .str "docs/first-derivative-dirichlet-cancellation.md"),
      ("publicTheorems", .arr #[
        .str "RiemannGaussian.PhaseIncrementInverse.norm_rotation",
        .str "RiemannGaussian.PhaseIncrementInverse.rotation_add",
        .str "RiemannGaussian.PhaseIncrementInverse.norm_rotation_sub_one",
        .str "RiemannGaussian.PhaseIncrementInverse.rotation_sub_one_ne_zero",
        .str "RiemannGaussian.PhaseIncrementInverse.inverseStep_eq",
        .str "RiemannGaussian.PhaseIncrementInverse.inverseStep_re",
        .str "RiemannGaussian.PhaseIncrementInverse.inverseStep_im",
        .str "RiemannGaussian.PhaseIncrementInverse.cot_antitoneOn",
        .str "RiemannGaussian.PhaseIncrementInverse.inverseStep_im_monotoneOn",
        .str "RiemannGaussian.PhaseIncrementInverse.sin_half_lower",
        .str "RiemannGaussian.PhaseIncrementInverse.norm_inverseStep_le",
        .str "RiemannGaussian.FiniteKuzminLandau.summation_by_parts",
        .str "RiemannGaussian.FiniteKuzminLandau.variation_le",
        .str "RiemannGaussian.FiniteKuzminLandau.inverseStep_mul_difference",
        .str "RiemannGaussian.FiniteKuzminLandau.phase_sum_identity",
        .str "RiemannGaussian.FiniteKuzminLandau.bound",
        .str "RiemannGaussian.FirstDerivativeTest.increment_witness",
        .str "RiemannGaussian.FirstDerivativeTest.bound_succ",
        .str "RiemannGaussian.FirstDerivativeTest.bound",
        .str "RiemannGaussian.LogarithmicShiftCancellation.bound",
        .str "RiemannGaussian.LogarithmicShiftCancellation.log_ratio_bound",
        .str "RiemannGaussian.LogarithmicShiftCancellation.integer_block_sum",
        .str "RiemannGaussian.LogarithmicShiftCancellation.unit_feature_pair",
        .str "RiemannGaussian.LogarithmicShiftCancellation.dirichlet_correlation_bound",
        .str "RiemannGaussian.FiniteAbelVariation.weighted_sum_eq",
        .str "RiemannGaussian.FiniteAbelVariation.weighted_bound",
        .str "RiemannGaussian.FiniteAbelVariation.decreasing_budget",
        .str "RiemannGaussian.FiniteAbelVariation.decreasing_bound",
        .str "RiemannGaussian.DirichletOverlapCancellation.damping_pos",
        .str "RiemannGaussian.DirichletOverlapCancellation.damping_antitoneOn",
        .str "RiemannGaussian.DirichletOverlapCancellation.feature_pair",
        .str "RiemannGaussian.DirichletOverlapCancellation.damped_block_bound",
        .str "RiemannGaussian.DirichletOverlapCancellation.correlation_bound",
        .str "RiemannGaussian.DirichletOverlapCancellation.vanDerCorput_bound"
      ])
    ]),
    ("finiteDifferencingToolkit", Json.mkObj [
      ("role", .str "Classical weighted van der Corput differencing with exact finite overlaps, applied to the original weighted Dirichlet features; logarithmic phase calculus supplies the genuine derivative scales used by the proved cancellation tests downstream"),
      ("exactComplexCorrelationTheorem", .str "RiemannGaussian.FiniteShiftCorrelation.mixed_shift_eq"),
      ("exactEnergyTheorem", .str "RiemannGaussian.FiniteShiftCorrelation.shiftedSum_energy"),
      ("signedDifferencingTheorem", .str "RiemannGaussian.FiniteVanDerCorput.signed_bound"),
      ("absoluteDifferencingTheorem", .str "RiemannGaussian.FiniteVanDerCorput.absolute_bound"),
      ("exactOverlapTheorem", .str "RiemannGaussian.FiniteVanDerCorputPhase.correlation_windowed"),
      ("retainedPhaseChannelsTheorem", .str "RiemannGaussian.FiniteVanDerCorputPhase.phaseTerm_pair_re"),
      ("classicalUnweightedTheorem", .str "RiemannGaussian.FiniteVanDerCorputPhase.unit_phase_bound"),
      ("multiplicativePhaseBridgeTheorem", .str "RiemannGaussian.ZetaFiniteDifferencing.phase_eq_multiplicative"),
      ("actualDirichletCorrelationTheorem", .str "RiemannGaussian.ZetaFiniteDifferencing.feature_shift_pair_log"),
      ("actualDirichletSignedBoundTheorem", .str "RiemannGaussian.ZetaFiniteDifferencing.signed_bound"),
      ("actualDirichletAbsoluteBoundTheorem", .str "RiemannGaussian.ZetaFiniteDifferencing.absolute_bound"),
      ("actualDerivativeTheorem", .str "RiemannGaussian.LogarithmicShiftPhase.hasDerivAt_shift"),
      ("actualSecondDerivativeTheorem", .str "RiemannGaussian.LogarithmicShiftPhase.hasDerivAt_slope"),
      ("actualDyadicScaleTheorem", .str "RiemannGaussian.LogarithmicShiftPhase.slope_dyadic_bounds"),
      ("finiteScope", .str "For f supported on N consecutive integers and H>0, H^2*norm(sum f)^2 <= (N+H-1)*(H*sum norm(f)^2+2*sum_(1<=h<H)(H-h)*Re(C(h))). Complete complex correlations C(h)=sum f(n+h)*conj(f(n)) remain available. No periodic wrap, omitted endpoint or assumption H<=N; correlations beyond the block are empty"),
      ("actualArithmetic", .str "For the literal feature w(n)*exp(-s*log(n)) on every positive integer block, the overlap is a_s(n+h)*conj(a_s(n))*exp(-i*Im(s)*log(1+h/n)), where a_s retains w and the exact real damping. All complex arithmetic weights and both sine/cosine channels are preserved"),
      ("phaseCalculus", .str "For x>0 and h>=0, g_h=-t*log(1+h/x), g_h'=t*h/(x*(x+h)), g_h''=-t*h*(2*x+h)/(x^2*(x+h)^2). The first derivative is positive for t,h>0 and decreasing for t,h>=0. If X<=x<=2X, 0<=h<=X, X>0 and t>=0, t*h/(6X^2)<=g_h'<=t*h/X^2"),
      ("literature", .str "Yang, Explicit bounds on zeta(s) in the critical strip and a zero-free region, JMAA 2024, Lemma 2.3, https://arxiv.org/html/2301.03165v2. Classical infrastructure; no historical novelty claim or external axiom"),
      ("limitations", .str "The first-derivative test and complete damped Dirichlet overlap bounds are now proved in firstDerivativeCancellationToolkit. The second-derivative test now pays for every resonance in secondDerivativeCancellationToolkit. The all-order finite recurrence is now proved in higherDerivativeRecursionToolkit. The closed uniform power bound is now proved in uniformDerivativePowerToolkit. The full finite zeta bound and small-block range are now proved in zetaDyadicPowerToolkit. The complete near-one line estimate is now proved in zetaNearOneLineToolkit. The complete local zero detector now proves every fixed logarithmic coefficient eventually in zetaArbitraryLogZeroFreeToolkit. The joint order-height costs and specified log-log width are now proved in zetaLogLogZeroFreeToolkit. Phase smoothness alone does not bound arbitrary arithmetic weights. These finite high-height tools do not supply the fixed-ordinate signed prime-tail lower bound. No larger zero-free region or RH proof is claimed"),
      ("documentation", .str "docs/weighted-van-der-corput.md"),
      ("publicTheorems", .arr #[
        .str "RiemannGaussian.FiniteShiftCorrelation.summable_correlation",
        .str "RiemannGaussian.FiniteShiftCorrelation.correlation_re",
        .str "RiemannGaussian.FiniteShiftCorrelation.correlation_zero",
        .str "RiemannGaussian.FiniteShiftCorrelation.mixed_shift_eq",
        .str "RiemannGaussian.FiniteShiftCorrelation.correlation_neg",
        .str "RiemannGaussian.FiniteShiftCorrelation.correlation_neg_re",
        .str "RiemannGaussian.FiniteShiftCorrelation.finite_shiftedSum",
        .str "RiemannGaussian.FiniteShiftCorrelation.shiftedSum_mass",
        .str "RiemannGaussian.FiniteShiftCorrelation.norm_sq_shiftedSum_eq",
        .str "RiemannGaussian.FiniteShiftCorrelation.shiftedSum_energy",
        .str "RiemannGaussian.FiniteShiftCorrelation.shiftedSum_eq_zero_outside",
        .str "RiemannGaussian.FiniteShiftCorrelation.norm_sum_sq_le_correlation_matrix",
        .str "RiemannGaussian.FiniteVanDerCorput.toeplitz_sum_eq",
        .str "RiemannGaussian.FiniteVanDerCorput.shifted_energy_eq",
        .str "RiemannGaussian.FiniteVanDerCorput.triangular_form_nonneg",
        .str "RiemannGaussian.FiniteVanDerCorput.signed_bound",
        .str "RiemannGaussian.FiniteVanDerCorput.absolute_bound",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.finite_windowed",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.windowed_on",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.windowed_outside",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.sum_windowed",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.energy_windowed",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.correlation_windowed",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.signed_window_bound",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.absolute_window_bound",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.norm_phaseTerm",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.phaseTerm_pair",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.phaseTerm_pair_re",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.real_phaseTerm_pair_re",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.signed_phase_bound",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.absolute_phase_bound",
        .str "RiemannGaussian.FiniteVanDerCorputPhase.unit_phase_bound",
        .str "RiemannGaussian.LogarithmicShiftPhase.shift_eq_log_ratio",
        .str "RiemannGaussian.LogarithmicShiftPhase.shift_eq_log_one_add",
        .str "RiemannGaussian.LogarithmicShiftPhase.hasDerivAt_phase",
        .str "RiemannGaussian.LogarithmicShiftPhase.hasDerivAt_shift",
        .str "RiemannGaussian.LogarithmicShiftPhase.hasDerivAt_slope",
        .str "RiemannGaussian.LogarithmicShiftPhase.slope_pos",
        .str "RiemannGaussian.LogarithmicShiftPhase.slope_antitoneOn",
        .str "RiemannGaussian.LogarithmicShiftPhase.slope_dyadic_bounds",
        .str "RiemannGaussian.ZetaFiniteDifferencing.phase_eq_multiplicative",
        .str "RiemannGaussian.ZetaFiniteDifferencing.feature_polar",
        .str "RiemannGaussian.ZetaFiniteDifferencing.weighted_feature_eq",
        .str "RiemannGaussian.ZetaFiniteDifferencing.norm_weighted_feature",
        .str "RiemannGaussian.ZetaFiniteDifferencing.norm_amplitude",
        .str "RiemannGaussian.ZetaFiniteDifferencing.feature_shift_pair",
        .str "RiemannGaussian.ZetaFiniteDifferencing.feature_shift_pair_log",
        .str "RiemannGaussian.ZetaFiniteDifferencing.overlap_eq",
        .str "RiemannGaussian.ZetaFiniteDifferencing.signed_bound",
        .str "RiemannGaussian.ZetaFiniteDifferencing.absolute_bound"
      ])
    ]),
    ("zeroFreeRegionArithmeticTransport", Json.mkObj [
      ("role", .str "General decreasing zero-free widths reach complete divisor bands and the literal squarefree arithmetic Cauchy bounds. The proved log-log region now supplies actual larger eventual discs and stronger fixed-mark decay for every coefficient in its stated open range"),
      ("generalCompleteBandTheorem", .str "RiemannGaussian.exists_eventual_common_margin_of_antitone"),
      ("openBoundaryBandTheorem", .str "RiemannGaussian.exists_eventual_common_weak_margin_of_antitone"),
      ("combinedWidthTheorem", .str "RiemannGaussian.nontrivialZetaZero_common_margin_max"),
      ("generalActualArithmeticTheorem", .str "RiemannGaussian.SquarefreeEulerBand.exists_eventual_response_bound_of_region"),
      ("openBoundaryDiscTheorem", .str "RiemannGaussian.SquarefreeEulerBand.exists_eventual_analytic_discs_of_weak_region"),
      ("actualLargerRadiusTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_radius_spec"),
      ("actualLargerArithmeticBoundTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_response_bound"),
      ("actualStrongerDecayTheorem", .str "RiemannGaussian.SquarefreeLogLog.exists_eventual_coefficient_scaled_decay"),
      ("generalWidth", .str "Every w positive and antitone beyond T, tending to zero, with a proved eventual zero-location theorem, gives the same width w(H) for every zero below H at sufficiently large H. The old positive global margin pays for every zero below T. No a/log(t) shape restriction. Two proved common margins combine by max"),
      ("boundaryConvention", .str "Strict zero-location bounds yield analyticity on the full closed Cauchy disc. Non-strict zero-location bounds from an open zero-free region yield every strictly smaller closed disc. The endpoint is not silently included, and there is no fixed fractional loss in width"),
      ("actualRadius", .str "For H=2*abs(y)+3 and complete margin 0<m<1/4, R(y,m)=1+min((abs(y)-1)/2,m/2). The actual quotient zeta(s)/zeta(2*s) is analytic on the entire closed disc about 3/2+i*y, with both poles and every doubled-denominator zero excluded. Every fixed 0<A<1/(140*log(2)) now gives R_A=1+A*log(log(H))/(2*log(H)) at sufficiently large abs(y), with a threshold depending on A"),
      ("retainedArithmeticCost", .str "A single C(y)>0 bounds every valid response by C(y)*A(S,c,r)*r^(-N)*sum norm(p_k)*r^(-k), all 0<r<=R_new, all finite excluded prime sets S, squarefree marks P, complex polynomials p and orders N. A is the actual maximum of exp(-Re(Phi_2)) on that radius, retaining the first and doubled prime harmonics. No uniform bound on A for growing S is asserted"),
      ("concreteDecayGain", .str "For every fixed 0<=A<B<1/(140*log(2)) and every fixed valid S,P,p, sufficiently large abs(y) gives the genuine log-log radii R_A(y)<R_B(y), and the actual complex response times R_A(y)^N tends to zero. Thresholds depend on the coefficients. Constants and the full phase maximum may increase with radius, so not every finite-order upper bound is claimed improved"),
      ("externalTargets", .str "A specified Littlewood log-log shape is now proved in zetaLogLogZeroFreeToolkit, with coarse coefficient range and existential thresholds. Published optimized Littlewood constants, finite starting heights, stronger Vinogradov--Korobov shapes and finite-height interval-arithmetic verification await their own checked formal counterparts. None is imported as an axiom. The growing-order estimates and complete actual prime budget are proved; the separate signed ordinary-prime bound remains open. See docs/zero-free-region-transport.md for literature scopes"),
      ("limitations", .str "Every eligible coefficient has an existential unevaluated height threshold. Old global margins and radii keep their definitions and theorems. The complete squarefree response is not the separate ordinary-prime source; its stronger decay does not supply the independent signed lower bound. No optimized published coefficient, numerical threshold, RH proof or historical novelty claim"),
      ("documentation", .str "docs/zero-free-region-transport.md"),
      ("publicTheorems", .arr #[
        .str "RiemannGaussian.exists_eventual_common_margin_of_antitone",
        .str "RiemannGaussian.exists_eventual_common_weak_margin_of_antitone",
        .str "RiemannGaussian.nontrivialZetaZero_common_margin_max",
        .str "RiemannGaussian.riemannZeta_ne_zero_of_common_margin",
        .str "RiemannGaussian.riemannZeta_ne_zero_of_common_weak_margin",
        .str "RiemannGaussian.SquarefreeEulerBand.radius_bounds",
        .str "RiemannGaussian.SquarefreeEulerBand.radius_mono",
        .str "RiemannGaussian.SquarefreeEulerBand.radius_eq",
        .str "RiemannGaussian.SquarefreeEulerBand.disc_safe",
        .str "RiemannGaussian.SquarefreeEulerBand.analyticOnNhd_response",
        .str "RiemannGaussian.SquarefreeEulerBand.disc_safe_of_weak_band",
        .str "RiemannGaussian.SquarefreeEulerBand.analyticOnNhd_response_of_weak_band",
        .str "RiemannGaussian.SquarefreeEulerBand.exists_eventual_analytic_discs_of_weak_region",
        .str "RiemannGaussian.SquarefreeEulerBand.exists_response_bound",
        .str "RiemannGaussian.SquarefreeEulerBand.exists_eventual_response_bound_of_region",
        .str "RiemannGaussian.SquarefreeEulerBand.tendsto_scaled_response",
        .str "RiemannGaussian.SquarefreeEulerModulated.fermi_radius_le",
        .str "RiemannGaussian.SquarefreeEulerModulated.exists_eventual_radius_spec",
        .str "RiemannGaussian.SquarefreeEulerModulated.exists_eventual_response_bound",
        .str "RiemannGaussian.SquarefreeEulerModulated.exists_eventual_fermi_scaled_decay"
      ])
    ]),
    ("squarefreeEulerRetainedPhase", Json.mkObj [
      ("role", .str "Exact finite prime-harmonic decomposition and uniformly bounded higher-order remainder, transported to the original marked squarefree response; no new signed prime-source bound"),
      ("exactProductTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.inverse_product_eq_exp"),
      ("exactMarkedMultiplierTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.multiplier_eq"),
      ("finiteRemainderTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.norm_remainder_le"),
      ("allPrimeSetRemainderTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.exists_uniform_remainder_bound"),
      ("twoSidedCompensatedProductTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.exists_compensated_product_bounds"),
      ("allMarkMultiplierTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.exists_uniform_mark_bound"),
      ("exactTwoHarmonicsTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.phase_two"),
      ("actualConvergentSeriesTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.hasSum_marked"),
      ("harmonicContinuityTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.continuous_phase"),
      ("signedTrigonometricIdentityTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.phase_two_re"),
      ("actualCompactMaximumTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.le_envelope"),
      ("positiveMaximumTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.envelope_pos"),
      ("generalAnalyticDiscTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.exists_response_bound_of_analytic"),
      ("actualArithmeticBoundTheorem", .str "RiemannGaussian.SquarefreeEulerPhase.exists_response_bound"),
      ("exactDecomposition", .str "Phi_J(S,s)=sum_(p in S) sum_(1<=k<=J) (-1)^(k+1)*p^(-k*s)/k; E_J=Phi_J-sum log(1+p^(-s)); the reciprocal finite Euler product equals exp(-Phi_J+E_J). The marked multiplier equals its exact empty-sieve mark factor times this exponential. No logarithm of the whole product or branch-cut identity is assumed"),
      ("uniformRemainder", .str "For every sigma>0 and natural J with (J+1)*sigma>1, one C>0 bounds norm(E_J(S,s)) for every finite prime set S and every s with Re(s)>=sigma. The exact finite norm allowance is sum norm(p^(-s))^(J+1)/((J+1)*(1-norm(p^(-s)))); a summable integer majorant pays the entire higher-harmonic remainder. The compensated product norm lies between exp(-C) and exp(C)"),
      ("twoHarmonicStructure", .str "At sigma=3/8, J=2 suffices: Phi_2=sum p^(-s)-(1/2)*sum p^(-2*s). Its real part retains the actual cos(t*log(p)) and cos(2*t*log(p)) with their respective damping and opposite signs. All valid squarefree marks have one common bounded cost. No special weight family or coefficient search is used"),
      ("actualCauchyBound", .str "For every fixed ordinate abs(y)>1, a common C>0 bounds every valid marked arithmetic response by C*A(S,c,r)*r^(-N)*sum norm(p_k)*r^(-k), where c=3/2+i*y, 0<r<=the existing Fermi radius, and A is the actual compact maximum of exp(-Re(Phi_2)) over the closed disc. The generic interface accepts any proved analytic quotient disc of radius at most 9/8. The constant is independent of r,S,P,p,N"),
      ("limitations", .str "The first and doubled prime phases remain uncontrolled for growing sets. The compact maximum is not a signed lower bound for the separate ordinary-prime source, and the complete squarefree response already has an independent decay theorem. Original series convergence is asserted only for Re(s)>1; the finite multiplier identities hold for Re(s)>0. No new zero exclusion, optimality or historical novelty claim; the independent signed prime bound and RH remain open")
    ]),
    ("polynomialPrimeHeatTransport", Json.mkObj [
      ("role", .str "Exact all-polynomial Gaussian operator and complete ordinary-prime-series transport; no new zero exclusion or arithmetic sign estimate"),
      ("polynomialIntegrabilityTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.integrable_weighted"),
      ("exactDerivativeTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.hasDerivAt_weighted"),
      ("steinIdentityTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.weighted_X_mul"),
      ("allPowerEvaluationTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.weighted_X_pow"),
      ("allPolynomialEvaluationTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.weighted_eq_transport"),
      ("linearFactorTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.transport_factor"),
      ("doubleFactorTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.transport_double_factor"),
      ("squaredFactorTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.transport_linear_square"),
      ("doubleRootCorrectionTheorem", .str "RiemannGaussian.GaussianPolynomialTransport.transport_double_root"),
      ("exactPrimeTermTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.polynomialHeatTerm_eq"),
      ("primeIntegralNormTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_norm_polynomialHeatTerm"),
      ("completeNormSummabilityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.summable_integral_norm_polynomialHeatTerm"),
      ("wholePrimeAverageIntegrabilityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integrable_polynomialHeatPrimeResponse"),
      ("wholePrimeTransportTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_polynomialHeatPrimeResponse"),
      ("correctedPrimeSeriesSummabilityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.summable_polynomialHeatPrimeResponse"),
      ("allCofactorPrimeCorrectionTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.polynomialHeatPrimeResponse_double_factor"),
      ("actualSquaredFactorIntegralTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_squaredFactor_primeHeat"),
      ("actualDerivativeTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.primeLogResponse_one_eq_signedTaylorMoment"),
      ("fullClearedLeibnizTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedPrimeMoment_eq_leibniz"),
      ("fullClearedHeatIntegrabilityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integrable_clearedPrimeMoment_heat"),
      ("fullClearedHeatTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_clearedPrimeMoment_heat"),
      ("normalization", .str "For B>0, H_B[q](s,x)=integral_y q(s-i*y)*exp(-y^2/(4*B))*exp(i*y*x). The exact unnormalized mass is M_B=sqrt(pi/(1/(4*B)))=sqrt(4*pi*B)"),
      ("operatorIdentity", .str "H_B[X*q](s,x)=(s+2*B*x)*H_B[q](s,x)-2*B*H_B[q'](s,x). The full derivative and polynomial Gaussian integrability are proved before integration by parts"),
      ("finiteEvaluation", .str "W_0(B,z)=1,W_1(B,z)=z,W_(n+2)=z*W_(n+1)-2*B*(n+1)*W_n, and T_B(q)(z)=sum_k q_k*W_k(B,z). For every complex polynomial q: H_B[q](s,x)=M_B*exp(-B*x^2)*T_B(q)(s+2*B*x)"),
      ("retainedCorrections", .str "T_B((X-r)*q)(z)=(z-r)*T_B(q)(z)-2*B*T_B(q')(z). For a double factor the exact result is ((z-r)^2-2*B)*T_B(q)(z)-4*B*(z-r)*T_B(q')(z)+4*B^2*T_B(q'')(z). In particular T_B((X-r)^2)(r)=-2*B; a double polynomial root is not preserved by Gaussian transport"),
      ("actualArithmeticIdentity", .str "For Re(s)>1,B>0,all complex q,p, every N,D and finite prime sieve S: integral_y q(s-i*y)*exp(-y^2/(4*B))*primeLogResponse(p,D,S,N,s-i*y)=M_B*sum_n primeCorrectionCoefficient(D,S,n)*K_(p,N)(s,n)*exp(-B*log(n)^2)*T_B(q)(s+2*B*log(n)). The original factorial filter p and the separate spectral multiplier q are retained as distinct polynomials. For D>=1 the support is precisely ordinary primes n>D outside S"),
      ("interchange", .str "Each integral norm equals the original arithmetic term norm times integral_y norm(q(s-i*y))*exp(-y^2/(4*B)). This finite polynomial Gaussian mass pays the complete norm summability. The whole average is integrable and the corrected arithmetic series is absolutely summable"),
      ("higherMomentScope", .str "For the actual fixed-support prime L-series F, clearedPrimeMoment(q,D,S,N,s)=M_N(q*F)(s)=sum_(k=0)^N q_k(s)*primeLogResponse(1,D,S,N-k,s), where q_k=(-1)^k*q^(k)/k!. Its complete Gaussian average is M_B times the sum over k of the polynomial heat response with q_k and moment N-k. Every derivative and Hermite correction is present. A multiplier on an already differentiated moment need not clear its higher-order poles; q remains distinct from the original factorial filter p"),
      ("limitations", .str "The positive Gaussian does not make the original complex moment or the finite Hermite multiplier positive. The existing source theorems remain intact. The subsequent quadraticClearedHeatSource proves the full fixed-cutoff heat source survives with vanishing residual. The independent cofinal fixed-gap lower bound above -1 for the original normalized prime moment and RH remain open. No new zero-free region or historical novelty claim for the Stein/Weyl identity or Hermite recursion")
    ]),
    ("clearedPrimeDivisorSource", Json.mkObj [
      ("role", .str "Actual finite divisor polynomial and preserved negative-multiplicity source for every fixed prime cutoff and finite prime sieve, connected to the full Leibniz/Hermite heat formula; no independent signed arithmetic bound"),
      ("actualPolynomialTheorem", .str "RiemannGaussian.meromorphicPairClearingPolynomial_eval"),
      ("selectedPolynomialNonvanishingTheorem", .str "RiemannGaussian.meromorphicPairClearingPolynomial_eval_ne_zero"),
      ("wholeDomainRegularityTheorem", .str "RiemannGaussian.analyticOnNhd_meromorphicPairSimpleRegular"),
      ("exactSelectedResidueTheorem", .str "RiemannGaussian.meromorphicPairSimpleRegular_apply"),
      ("exactSimplePoleMomentTheorem", .str "RiemannGaussian.signedTaylorMoment_div_sub"),
      ("genericGeometricErrorTheorem", .str "RiemannGaussian.exists_meromorphicClearingPolynomial_source"),
      ("actualCoefficientIdentityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.primeCorrectionCoefficient_eq_full_sub_head"),
      ("actualSeriesContinuationTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.LSeriesHasSum_primeTailContinuation"),
      ("actualPoleOrderTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.meromorphicOrderAt_primeTailContinuation"),
      ("actualNegativeResidueTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.meromorphicTrailingCoeffAt_primeTailContinuation"),
      ("actualMomentContinuationTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedPrimeMoment_eq_continuation"),
      ("selectedNormalizationTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedPrimeTailClearingPolynomial_eval"),
      ("actualGeometricSourceErrorTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_normalizedClearedPrimeMoment_source_error"),
      ("actualSourceLimitTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_normalizedClearedPrimeMoment"),
      ("polynomial", .str "The actual finite product over the support of e(z), where e(rho)=0 and e(z)=max(0,-divisor(f,K,z),-divisor(g,K,z)) elsewhere. All exponents are nonnegative integers, evaluation equals the existing whole clearing weight, and the selected value is nonzero. No pole locations or multiplicities are dropped"),
      ("actualContinuation", .str "For each fixed D>=1 and finite prime sieve S: F_(D,S)(s)=-zeta'(s)/zeta(s)-E(s)-sum_(p prime,p<=D or p in S) log(p)*p^(-s), where E is the actual proper-prime-power L-series analytic on Re(s)>1/2. Equality with the original prime tail is proved on Re(s)>1; each selected right-half-zero residue is exactly -m_rho"),
      ("sourceEstimate", .str "Use s_rho=3/2+i*Im(rho), R=5/4-Re(rho)/2 and u=3/2-Re(rho). The actual clearing polynomial Q for F_(D,S) on closedBall(s_rho,R), excluding rho, is normalized to q=Q/Q(rho). There exists C>0 such that every N satisfies norm(u^(N+1)*clearedPrimeMoment(q,D,S,N,s_rho)+m_rho)<=C*(u/R)^N, with 0<u/R<1. Hence the normalized complex moment converges to -m_rho"),
      ("heatConnection", .str "The same polynomial q is an admissible argument of the full cleared-prime heat identity: clearing precedes differentiation and the Gaussian acts on every signed derivative polynomial q_k with its exact finite Hermite correction. Integrability and all Euler-domain convergence hypotheses are proved"),
      ("limitations", .str "This source error is before Gaussian smoothing, with D and S fixed as N grows. Its polynomial and constant may depend on those fixed data. The subsequent quadraticClearedHeatSource gives vanishing complete residual at fixed positive quadratic relative widths. No uniform moving-cutoff estimate is proved. This bounds the error around the hypothetical negative source, not the signed prime sum independently. The original fixed-gap lower bound, any new zero exclusion and RH remain open")
    ]),
    ("quadraticClearedHeatSource", Json.mkObj [
      ("role", .str "Complete actual residual decay at every fixed positive quadratic relative width, combining central geometric decay and global Euler-line bounds with Gaussian localization. The full corrected prime heat retains its negative source; the independent signed arithmetic lower bound remains open"),
      ("complexLaplaceTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.integral_laplace"),
      ("actualPoleIntegrabilityTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.integrable_poleMoment"),
      ("exactGammaAverageTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.poleHeat_eq_attenuation"),
      ("gammaMassTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.integral_gammaWeight"),
      ("gammaSecondMomentTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.integral_gammaWeight_mul_sq"),
      ("centeredTangentLowerTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.exp_neg_secondMoment_le_attenuation"),
      ("exactImaginaryCancellationTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.poleHeat_im"),
      ("allWidthBoundsTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.poleHeat_re_bounds"),
      ("allWidthComplexErrorTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.norm_poleHeat_sub_one_le"),
      ("quadraticSourceTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.poleHeat_quadraticWidth_bounds"),
      ("quadraticComplexErrorTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.norm_poleHeat_quadraticWidth_sub_one_le"),
      ("allVanishingRelativeWidthsTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.tendsto_poleHeat_quadraticWidth"),
      ("actualResidualMomentTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.signedTaylorMoment_clearedPrimeRemainder"),
      ("actualResidualIntegrabilityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integrable_clearedPrimeRemainder_heat"),
      ("completeActualHeatIdentityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedClearedPrimeHeat_eq_source_add_remainder"),
      ("actualSignedHeatBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedClearedPrimeHeat_re_le"),
      ("wholeDiscResidualRegularityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_clearedPrimeRemainder_analyticRepresentative"),
      ("uniformCentralGeometryTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedPrimeCentralGeometry"),
      ("actualUniformCentralResidualBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_clearedPrimeRemainder_central_bound"),
      ("actualUniformEulerHalfPlaneTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_primeTailContinuation_euler_bound"),
      ("allPolynomialQuarterDiscTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_polynomial_quarterDisc_bound"),
      ("actualResidualQuarterDiscTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_clearedPrimeRemainder_quarterDisc_bound"),
      ("actualGlobalResidualMomentTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_clearedPrimeRemainder_global_bound"),
      ("generalGaussianLocalizationTheorem", .str "RiemannGaussian.GaussianCentralTailBound.norm_average_le"),
      ("quantitativeQuadraticTailTheorem", .str "RiemannGaussian.GaussianCentralTailBound.tailAllowance_quadraticWidth_le"),
      ("everyExponentialTailDecayTheorem", .str "RiemannGaussian.GaussianCentralTailBound.tendsto_pow_mul_tailAllowance_quadraticWidth"),
      ("actualNormalizedAverageTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedClearedPrimeRemainderHeat_eq_average"),
      ("completeResidualBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_normalizedClearedPrimeRemainderHeat_bound"),
      ("completeResidualDecayTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_normalizedClearedPrimeRemainderHeat_quadraticWidth"),
      ("fullPrimeSourceWithArbitraryErrorTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.eventually_normalizedClearedPrimeHeat_re_le"),
      ("fullPrimeNegativeSourceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.eventually_normalizedClearedPrimeHeat_re_le_negative"),
      ("exactPoleIntegral", .str "For every N>=0,u>0,B>0, the complex poleHeat A_N=u^(N+1)/sqrt(4*pi*B)*integral_y exp(-y^2/(4*B))*(u-i*y)^(-N-1) equals integral_(t>0) g_(N,u)(t)*exp(-B*t^2), where g=u^(N+1)*t^N/N!*exp(-u*t). Full complex Laplace convergence, endpoint limits and product integrability precede the interchange. The complete average is real"),
      ("exactSourceBounds", .str "Integral(g)=1 and integral(t^2*g)=V_N=(N+1)*(N+2)/u^2. The exponential tangent gives 1-B*V_N<=A_N<=1 and norm(A_N-1)<=B*V_N. Centering the tangent at V_N strengthens the lower bound to exp(-B*V_N)<=A_N"),
      ("explicitWidthFamily", .str "For every c>0, B_N=c*u^2/((N+1)*(N+2)) is positive and has B_N*V_N=c exactly. At every N, exp(-c)<=A_N<=1 and norm(A_N-1)<=c. Every positive relative-width sequence c_N->0 recovers the full unit pole source jointly with growing order, without an unevaluated diagonal choice"),
      ("completePrimeIdentity", .str "For the actual fixed cutoff and prime sieve, normalized divisor polynomial q, selected multiplicity m and original continuation F, define the literal residual R=q*F+m/(s-rho). Its signed factorial moment and Gaussian average are genuinely defined and integrable on the original Euler line. The complete corrected prime arithmetic heat equals -m*A_N+E_N, where E_N is that residual integral with the identical geometric and Gaussian mass normalization. All Leibniz orders and Hermite corrections remain present"),
      ("actualCentralResidualBound", .str "For each fixed D,S and right-half zero, the actual residual has a filled analytic representative on the whole original clearing disc, agreeing with the Euler germs. With R0=5/4-Re(rho)/2,u=3/2-Re(rho), r0=(u+R0)/2 and delta=(R0-u)/4, there exists C>0 such that all N and all abs(y)<=delta satisfy norm(u^(N+1)*M_N(R)(s_rho-i*y))<=C*(u/r0)^N. The neighborhood, radius and constant are independent of N and B, with 0<u/r0<1"),
      ("actualGlobalResidualBound", .str "There exists A>0 such that all N and real y satisfy norm(u^(N+1)*M_N(R)(s_rho-i*y))<=A*(4*u)^N*(1+y^2)^d, where d is the actual normalized clearing polynomial's natural degree. Absolute Euler convergence controls F on Re(s)>=5/4, the polynomial has a common vertical envelope on all quarter-discs, and the selected denominator is separated by at least 1/4. Cauchy estimates retain the same A and d at every order and frequency"),
      ("completeResidualError", .str "For 0<B<=1, norm(E_N(B))<=C*(u/r0)^N+A*(4*u)^N*T(delta,d,B), where J_d=integral (1+y^2)^d*exp(-y^2/8) is genuinely finite and T=J_d/mass(B)*exp(-delta^2/(8*B)). At B_N=c*u^2/((N+1)*(N+2)), T<=J_d/mass(c*u^2)*(N+2)*exp(-delta^2/(8*c*u^2)*(N+1)^2). This absorbs every fixed exponential growth rate. The original complete residual E_N(B_N) tends to zero for every fixed c>0"),
      ("retainedWholePrimeSource", .str "The exact full prime heat -m*A_N+E_N consequently has Re(P_N)<=-m*exp(-c)+epsilon eventually, for every epsilon>0, and Re(P_N)<=-m*exp(-c)/2 eventually. These conclusions concern the actual complete corrected prime series, including all Leibniz orders and Hermite corrections; the central and outer residuals have both been bounded"),
      ("limitations", .str "Cutoff, sieve, selected zero and positive relative width c are fixed. The constants may depend on them; no uniform moving-cutoff or arbitrary varying-relative-width residual theorem is claimed. The full negative source is conditional on a hypothetical right-half zero. Its stability supplies no independent conflicting lower bound for the signed prime heat. That arithmetic bound and RH remain open, with no new zero-free region or historical novelty claim for the Gaussian localization or gamma/Jensen identities")
    ]),
    ("clearedHeatPolynomialOperator", Json.mkObj [
      ("role", .str "Exact all-polynomial factorial/Gaussian operator inside the original convergent prime sum, including the displaced square's signed correction. This exposes the independent arithmetic frontier but proves no new lower bound or zero exclusion"),
      ("finiteBinomialOperatorTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.shift_eq_binomial"),
      ("derivativeCommutationTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.derivative_shift"),
      ("allCofactorAdjacentOrderTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.shift_factor_mul_succ"),
      ("factorialDisplacementTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.shift_factor"),
      ("factorialQuadraticCorrectionTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.shift_factor_sq"),
      ("fullBinomialHermiteTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.heat_eq_binomial"),
      ("allCofactorHeatRecurrenceTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.heat_factor_mul_succ"),
      ("combinedQuadraticCorrectionTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.heat_factor_sq"),
      ("exactFactorialNormalizationTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.factorialHeat_eq_leibniz"),
      ("actualPrimeSummandTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedHeatPrimeTerm_eq_operator"),
      ("actualFullSeriesConvergenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.hasSum_clearedHeatPrime_operator"),
      ("actualFullPrimeOperatorTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedHeatPrimeResponse_eq_operator"),
      ("actualCofactorPrimeRecurrenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedHeatPrimeResponse_factor"),
      ("actualQuadraticPrimeMultiplierTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedHeatPrimeResponse_factor_sq"),
      ("strictNegativeMultiplierTestTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedHeatSquareMultiplier_displaced_root_neg"),
      ("unchangedNormalizedSourceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedClearedPrimeHeat_eq_operator"),
      ("exactOperator", .str "For x=log(p)>0, S_(N,x)=(1-x^-1*D)^N acts on every complex clearing polynomial q as a genuine linear-endomorphism power. Its full binomial sum retains choose(N,k)*(-1/x)^k*q^(k). H_(B,N,x)=T_B o S_(N,x), with T_B the exact finite Hermite transform, and x^N/N!*H(q)=sum_(k<=N) x^(N-k)/(N-k)!*T_B((-1)^k/k!*q^(k))"),
      ("actualPrimeIdentity", .str "For Re(s)>1, B>0, cutoff D>=1 and every finite prime sieve S, the whole original corrected heat equals sum_(p prime,p>D,p notin S) log(p)*p^(-s)*(log(p))^N/N!*exp(-B*log(p)^2)*H_(B,N,log(p))(q)(s+2*B*log(p)). Every Leibniz row is absolutely summable before interchange. Zero natural indices have zero actual coefficient. The genuine divisor polynomial and original source normalization are explicitly included"),
      ("retainedSignedCorrection", .str "H_(B,N,x)((X-r)^2)(z)=(z-r-N/x)^2-(2*B+N/x^2). For real x and B>0 its real part is strictly negative at z=r+N/x. This tests the exact multiplier and does not infer a sign for the whole prime sum. The term N/x^2 is present before Gaussian smoothing"),
      ("allCofactorRecurrence", .str "For every complex q,r,z and B>0: H_(N+1)((X-r)*q)(z)=(z-r)*H_(N+1)(q)(z)-2*B*H_(N+1)(q')(z)-(N+1)/x*H_N(q)(z). All three channels are also retained in the same original prime series. No prime phase, derivative correction or adjacent-order coupling is discarded"),
      ("limitations", .str "These are exact identities and a multiplier sign test, not an independent signed prime lower bound. The actual clearing polynomial is not asserted to be a single square. Neither nonnegativity nor source-scale cancellation of the full prime sum follows. The prior fixed-cutoff quadratic-width residual decay is unchanged. RH and the conflicting arithmetic bound remain open; no new zero-free region or historical novelty claim is made")
    ]),
    ("clearedHeatThreeOrderControl", Json.mkObj [
      ("role", .str "Exact all-polynomial three-order recurrence for the actual convergent prime heat and a proved inverse-order bound for its whole upper-neighbour contribution at the same quadratic width. No new independent signed lower bound or zero exclusion"),
      ("factorialHeatStepTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.heat_succ"),
      ("displacementCancellationTheorem", .str "RiemannGaussian.FactorialPolynomialTransport.heat_factor_closed"),
      ("actualPrimeRecurrenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedHeatPrimeResponse_three_order"),
      ("actualNormalizedRecurrenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedClearedPrimeHeat_three_order"),
      ("exactQuadraticCoefficientTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.normalizedClearedPrimeHeat_three_order_quadraticWidth"),
      ("fixedOffsetResidualDecayTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_clearedPrimeRemainderHeat_sharedWidth"),
      ("completeHeatNormTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.norm_normalizedClearedPrimeHeat_le_multiplicity_add_residual"),
      ("sharedWidthNeighbourBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.eventually_norm_clearedPrimeHeat_sharedWidth_le"),
      ("quantitativeWholeUpperTermTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.eventually_norm_clearedPrimeHeat_upper_coupling_le"),
      ("completeUpperTermDecayTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_clearedPrimeHeat_upper_coupling"),
      ("actualSignedDifferenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_clearedPrimeHeat_extraFactor_sub_difference"),
      ("exactPrimeIdentity", .str "For every complex q,r, B>0, Re(s)>1, D>=1 and finite prime S, the complete prime heat satisfies A_(N+1)[(X-r)*q]=(s-r)*A_(N+1)[q]-A_N[q]+2*B*(N+2)*A_(N+2)[q]. The derivative channel cancels exactly against the Gaussian displacement after retaining the next order. All three orders have the same B,s,D,S and keep the original prime phases"),
      ("normalizedQuadraticIdentity", .str "For the actual divisor polynomial q, u=3/2-Re(rho), P_k(B)=u^(k+1)*A_k[q](B,s_rho) and B_N=c*u^2/((N+1)*(N+2)), the extra-factor heat u^(N+1)*A_(N+1)[(X-rho)*q](B_N,s_rho) equals P_(N+1)(B_N)-P_N(B_N)+2*c/(N+1)*P_(N+2)(B_N). Every term uses B_N, not its own order's quadratic width"),
      ("wholeUpperTermBound", .str "Under the hypothetical right-half zero, E_(N+j)(B_N)->0 for every fixed j,c>0,D,S. The exact source identity and 0<=attenuation<=1 give norm(P_k(B))<=m+norm(E_k(B)). Thus norm(2*c/(N+1)*P_(N+2)(B_N))<=2*c*(m+1)/(N+1) eventually, and the whole upper term tends to zero. Its full residual and multiplicity source are included"),
      ("limitations", .str "The remaining signed adjacent-order difference is not independently bounded here. Multiplication by X-rho removes the selected pole, so decay of that altered expression would not contradict the original negative source. Reconstruction of the original heat must retain its boundary value and justify any changes of width. Cutoff, sieve, positive c and offset j are fixed. The independent arithmetic bound, RH and the zero-free region are unchanged; no historical novelty claim is made")
    ]),
    ("clearedHeatBandControl", Json.mkObj [
      ("role", .str "Actual growing-order residual decay, exact recurrence reconstruction and a proved nonvanishing source in the complete correction band. This rejects discarding individually small upper corrections during iteration; it supplies no independent signed prime lower bound or new zero exclusion"),
      ("weightNonnegativityTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.quadraticBandWeight_nonneg"),
      ("exactWeightSumTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.sum_quadraticBandWeight"),
      ("weightSumLimitTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.tendsto_sum_quadraticBandWeight"),
      ("weightSumBoundsTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.sum_quadraticBandWeight_bounds"),
      ("sharedWidthSecondMomentTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.quadraticWidth_mul_secondMoment_band_le"),
      ("uniformBandPoleFloorTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.exp_neg_four_mul_le_attenuation_band"),
      ("weightedBandPoleFloorTheorem", .str "RiemannGaussian.GaussianSimplePoleHeat.weighted_attenuation_band_lower"),
      ("actualGrowingOrderUniformityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.eventually_norm_clearedPrimeRemainderHeat_band_le"),
      ("wholeResidualBandDecayTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_clearedPrimeRemainderHeatBand"),
      ("actualBandSourceIdentityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedPrimeHeatBand_eq_source_add_remainder"),
      ("actualBandSourceBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedPrimeHeatBand_re_le"),
      ("actualBandNegativeSourceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.eventually_clearedPrimeHeatBand_re_le_negative"),
      ("exactBandReconstructionTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.clearedPrimeHeat_extraFactor_band"),
      ("sharedWidthBand", .str "For B_N=c*u^2/((N+1)*(N+2)), w_(N,j)=2*c*(N+j+2)/((N+1)*(N+2)) and W_N=sum_(j<N) w_(N,j)*P_(N+j+2)(B_N). Every term has the same B_N,D,S,rho and the original prime phases. The weights sum exactly to 3*c*N/(N+2), tend to 3*c, and lie between c and 3*c in every nonempty band"),
      ("uniformResidualEstimate", .str "For every epsilon>0, eventually all orders N<=k<=2*N+2 have norm(E_k(B_N))<=epsilon. The central term is at most C*theta^N with theta<1, and the outer term at most A*G^(2*N+2)*T(B_N), still absorbed by the proved quadratic Gaussian tail. The entire weighted residual band tends to zero because its weight sum is bounded by 3*c"),
      ("nonvanishingBandSource", .str "For each j<N the exact gamma pole attenuation at order N+j+2 and width B_N is at least exp(-4*c). Hence its weighted sum is at least c*exp(-4*c). The complete actual W_N equals minus m times that positive sum plus the entire residual band, so Re(W_N)<=-m*c*exp(-4*c)/2 eventually under the hypothetical right-half zero"),
      ("exactEndpoints", .str "Summing the actual three-order recurrence gives sum_(j<N) u^(N+j+1)*A_(N+j+1)[(X-rho)*q](B_N,s_rho)=P_(2*N)(B_N)-P_N(B_N)+W_N. The growing correction band and both endpoints remain explicit. All orders use B_N; no moving-width telescoping is asserted"),
      ("limitations", .str "This is a source-side theorem under a hypothetical right-half zero. It gives no independent conflicting arithmetic estimate. The extra factor on the left removes the selected pole, and the accumulated upper corrections cannot be discarded despite the proved decay of a single neighbour. Cutoff, sieve, zero and positive relative width are fixed. RH and the zero-free region are unchanged, and no historical novelty claim is made")
    ]),
    ("fermiCurvatureDivisorBound", Json.mkObj [
      ("role", .str "Unconditional analytic improvement for the entire actual outside divisor and all admissible finite signed phase budgets; no new zero exclusion"),
      ("logisticMassTheorem", .str "RiemannGaussian.GaussianFermiFisherBound.integral_logisticSlope"),
      ("signedSecondDerivativeTheorem", .str "RiemannGaussian.GaussianFermiFisherBound.dampedTwo_eq_score_curvature"),
      ("closedStripBalanceTheorem", .str "RiemannGaussian.GaussianFermiFisherBound.integral_score_eq_curvature"),
      ("closedStripDerivativeBoundTheorem", .str "RiemannGaussian.GaussianFermiFisherBound.integral_abs_dampedTwo_le_curvature"),
      ("enlargedStripBalanceTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.integral_score_eq_curvature_enlarged"),
      ("enlargedStripDerivativeBoundTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.integral_abs_dampedTwo_le_enlarged"),
      ("complexReflectionBoundTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.im_sq_mul_norm_pair_le_enlarged"),
      ("physicalReflectionBoundTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.abs_physical_pair_re_le_enlarged"),
      ("completeOutsideDivisorTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.abs_tsum_outside_le_uniform"),
      ("uniformHeightRateTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.exists_uniform_outside_sqrt_bound"),
      ("allParameterLimitTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.eventually_all_outside_lt"),
      ("generalSignedBudgetTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.selected_zero_phase_budget_with_uniform_tail"),
      ("actualSignedBudgetTheorem", .str "RiemannGaussian.GaussianFermiFisherTail.fermi_selected_zero_phase_budget_with_uniform_tail"),
      ("exactIdentity", .str "For q(v)=1/(1+exp(-a*v)) and f(v)=exp(-B*v^2-x*v)*q(v), score=-2*B*v-x+a*(1-q), curvature=2*B+a*q'. The original derivative is f''=score^2*f-curvature*f, and the full squared-score and curvature integrals agree. Integrability, both integrations by parts and integral(q')=1 are proved before estimating"),
      ("closedStripCost", .str "For a,B>0 and 0<=x<=a: integral(abs(f''))<=4*B*sqrt(pi/B)+2*a. Thus for a,B<=1 the complex analytic reflected pair has squared-frequency norm bound 4*sqrt(pi)+2. The physical same-phase pair inherits only the real-part bound through the exact conjugation identity"),
      ("enlargedStripCost", .str "For a,B>0,delta>=0,delta^2<=B and -delta<=x<=a+delta: integral(abs(f''))<=exp(1/2)*(4*B*sqrt(pi/(B/2))+2*a). For a,B<=1 this is at most C_F=exp(1/2)*(8*sqrt(pi)+2), with no inverse-width factor"),
      ("actualDivisorBound", .str "For H>=1,0<B<=1,1/2<sigma<=1,(1-sigma)^2<=B and 2*abs(t)<=H, abs(sum_(abs(Im(rho))>H) contribution(B,sigma,t,rho))<=E_F(H)=4*C_F*divisorTail(H)<=K/sqrt(H). Every actual zero and analytic multiplicity is included. K>0 is existential and independent of B,sigma,t,H; no outside-zero location assumption is made"),
      ("generalBudget", .str "For any 0<=m<=1/4 enclosing every actual zero through H, positive split B=b+c<=1 with m^2<=B, every finite family w_j>=0 and 2*abs(omega_j*t)<=H, and every selected finite actual zero set S in the band: selectedZeroSource+sum_j w_j*primeSum(1-2*m,B,omega_j*t)<=exactPoleGammaCost+(sum_j w_j)*E_F(H). No nonnegative-cosine-test assumption or comparison to an older margin is required. The proved global Fermi margin discharges the actual band conditions"),
      ("limitations", .str "This removes the logarithmic loss from the previous uniform K_old*log(H+2)/sqrt(H) outside allowance. It does not prove a favorable lower bound for the retained signed prime expression or the complex moment-filtered costs. The latest eventual zero-free family has width A*log(log(abs(t)))/log(abs(t)) for 0<A<1/(140*log(2)), with coefficient-dependent unevaluated thresholds; RH remains open. No historical novelty claim for the Fisher-information identity")
    ]),
    ("fermiConstantModeCancellation", Json.mkObj [
      ("role", .str "Uniform control of the actual constant-frequency prime/pole residual while retaining the remaining signed arithmetic combination; no new zero exclusion"),
      ("insideDivisorBoundTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.abs_tsum_inside_zero_le"),
      ("entireZeroSideTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.abs_zero_side_zero_le"),
      ("exactPrimeResidualTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.abs_constant_prime_residual_le"),
      ("actualPrimeResidualTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.abs_fermi_constant_prime_residual_le"),
      ("allSplitToleranceTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.eventually_constant_prime_residual_lt"),
      ("generalBudgetTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.selected_budget_without_constant_pole"),
      ("actualBudgetTheorem", .str "RiemannGaussian.GaussianFermiConstantMode.fermi_selected_budget_without_constant_pole"),
      ("residual", .str "For any valid common band margin 0<=m<=1/4, H>=1, b,c>0 and m^2<=B=b+c<=1: abs(polePair(B,1-m,0)-log(pi)/4+digammaAverage(1-2*m,b,c,0)-primeSum(1-2*m,B,0))<=K0+E_F(H), where K0=(4*sqrt(pi)+2)*sum_rho multiplicity(rho)/(1+Im(rho)^2) is finite and E_F is the improved outside allowance. The actual global Fermi margin discharges the zero-location premises"),
      ("retainedPhaseBudget", .str "For a finite nonnegative coefficient family with j0 in J and omega(j0)=0, keep every selected zero channel and remove only the constant-frequency prime and analytic terms: selectedZeroSource+sum_(j in J.erase j0) w_j*primeSum_j<=sum_(j in J.erase j0) w_j*exactPoleGamma_j+w_j0*K0+(sum_(j in J) w_j+w_j0)*E_F(H). The remaining prime expression is signed and is not discarded"),
      ("limitations", .str "Nonnegativity of the full cosine test does not imply nonnegativity after its constant term is removed. If the constant-frequency zero channel is also dropped, the signed phase budget can already be applied directly to the reduced family. The bounded residual does not by itself give a stronger resonant source bound, a new region, the original prime-moment fixed-gap lower bound, or RH")
    ]),
    ("gaussianPhaseProfileAudit", Json.mkObj [
      ("role", .str "All-family method constraint; not a zero-exclusion milestone"),
      ("fullSignedHeatIdentityTheorem", .str "RiemannGaussian.GaussianPhaseHeatConstraint.heat_deficit_eq_integral"),
      ("finiteScaleConstraintTheorem", .str "RiemannGaussian.GaussianPhaseHeatConstraint.heat_deficit_nonneg"),
      ("countableInterchangeTheorem", .str "RiemannGaussian.GaussianPhaseHeatConstraint.summable_integral_norm_probe"),
      ("exactFrequencyLimitTheorem", .str "RiemannGaussian.GaussianPhaseHeatConstraint.tendsto_heatMass"),
      ("constantMassConstraintTheorem", .str "RiemannGaussian.GaussianPhaseHeatConstraint.opposite_frequencyMass_le"),
      ("nonconstantMassConstraintTheorem", .str "RiemannGaussian.GaussianPhaseHeatConstraint.opposite_frequencyMass_le_nonconstantMass"),
      ("gaussianReciprocalBoundTheorem", .str "RiemannGaussian.GaussianPhaseProfileCeiling.halfGaussian_unit_le_recip"),
      ("generalCoefficientCeilingTheorem", .str "RiemannGaussian.GaussianPhaseProfileCeiling.strict_profile_surplus_bounds"),
      ("allFamilyCeilingTheorem", .str "RiemannGaussian.GaussianPhaseProfileCeiling.family_profile_ceiling"),
      ("exactScaleTransportTheorem", .str "RiemannGaussian.GaussianPhaseProfileCeiling.scaled_family_profile_ceiling"),
      ("familyScope", .str "Every a:Nat->Real with a_n>=0 and sum_n a_n finite, arbitrary real frequencies omega_n, and full kernel P(y)=sum_n a_n*cos(omega_n*y)>=0 for every real y. Frequencies may repeat, accumulate or have infinite support. These are phase-test design conditions, not additional assertions about zeta"),
      ("retainedHeatIdentity", .str "For every c>0 and real xi, the sum of a_n*(q_c(omega_n)-(q_c(omega_n+xi)+q_c(omega_n-xi))/2) equals the integral of density(1,c,y)*P(y)*(1-cos(xi*y)), hence is nonnegative. Here q_c(x)=2*signal(1,c,x)=exp(-c*x^2)*q_0(x); the fixed Fermi factor is retained. The envelope 2*a_n pays every integral norm before interchange"),
      ("exactMassConstraint", .str "H_c(xi)=sum_n a_n*q_c(omega_n-xi) converges to A(xi)=sum_(omega_n=xi) a_n. Summable domination pays for accumulating frequencies. Therefore A(xi)+A(-xi)<=2*A(0); for xi!=0 this pair is also bounded by M=sum_(omega_n!=0) a_n"),
      ("specifiedProfile", .str "G(x) is the actual half-line Gaussian Laplace integral at unit scale. With a0=A(0),a1=A(1)+A(-1),ell>0 and nu>=mu, the tested strict surplus is a0*G(-ell*mu)+M/(4*ell)<a1*G(ell*(nu-mu)). This is the coarse unit-multiplicity source, constant pole envelope and leading gamma cost; it is not an equality with the full explicit formula"),
      ("ceiling", .str "Every such strict surplus forces mu<pi/4 and nu<mu+4<pi/4+4, uniformly over the family and positive scale. The constants are a proved coarse ceiling, not an exact optimizer"),
      ("actualScaleTransport", .str "For arbitrary L>0,ell>0,B=1/(ell^2*L^2),d>=m, the strict unnormalized comparison a0*G_B(-m)+M*L/4<a1*G_B(d-m) forces L*m<pi/4 and L*d<L*m+4<pi/4+4. At L=log(t), this particular sufficient comparison cannot reach a fixed positive edge distance at all large heights"),
      ("limitations", .str "No new zero exclusion, RH consequence or historical novelty claim. The full signed prime combination, Fermi reserves, additional zeros with their actual multiplicities and frequency-dependent gamma cost remain available upstream. Stronger estimates using them, including for frequencies moving with height, are not ruled out. The actual eventual region is now 3/(16*log(abs(t))) with an existential threshold; the original independent signed ordinary-prime-tail lower bound and RH remain open")
    ]),
    ("fermiPrimeMomentComparison", Json.mkObj [
      ("role", .str "Exact complex prime-moment spectral transport, fixed-order regulator limits and independent bounds for weighting corrections; no new zero exclusion"),
      ("gaussianSummandIdentityTheorem", .str "RiemannGaussian.GaussianFermiPrimeComparison.ordinarySummand_eq_prime_add_correction"),
      ("uniformGaussianCorrectionTheorem", .str "RiemannGaussian.GaussianFermiPrimeComparison.norm_correctionSum_le"),
      ("fullGaussianPrimeIdentityTheorem", .str "RiemannGaussian.GaussianFermiPrimeComparison.ordinarySum_eq_primeSum_add_correction"),
      ("actualZeroFormulaTheorem", .str "RiemannGaussian.GaussianFermiPrimeComparison.zero_side_eq_poles_digamma_sub_ordinary_add_correction"),
      ("exactMomentDifferenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.primeLogResponse_sub_fermi_eq"),
      ("completeMomentBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.norm_primeLogResponse_sub_fermi_le"),
      ("uniformGeometricBoundTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_normalized_primeFermi_bound"),
      ("movingFamilyDecayTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_normalized_prime_sub_fermi"),
      ("actualTailComparisonTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_actual_prime_sub_fermi"),
      ("actualMarginParameterTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_actual_prime_sub_margin_fermi"),
      ("retainedSourceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_normalizedFermiPrimeLogResponse"),
      ("integralNormIdentityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_norm_density_primeLogTerm"),
      ("wholeMomentIntegrabilityTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integrable_density_primeLogResponse"),
      ("exactSpectralTransportTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_density_primeLogResponse"),
      ("actualMarginSpectralTransportTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.integral_margin_density_primeLogResponse"),
      ("fixedOrderRegulatorLimitTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_gaussianFermiPrimeLogResponse"),
      ("fixedOrderIntegralLimitTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_integral_density_primeLogResponse"),
      ("gaussianComparison", .str "For sigma>=sigma0>2/3 and B>0, the ordinary sum G=sum_n Lambda(n)*exp(-sigma*log(n)-B*log(n)^2)*cos(t*log(n)) equals primeSum(2*sigma-1,B,t)+R. The exact correction has damping 3*sigma-1 and the same Gaussian, Fermi factor and cosine. Its norm is at most Re(-zeta'/zeta(3*sigma0-1)), uniformly for B>=0 and every real t. The correction also converges at B=0; no convergence of the main unsmoothed strip series is asserted"),
      ("zeroFormula", .str "The full actual multiplicity-aware zero side equals polePair-log(pi)/4+digammaAverage-G+R. All signs and multiplicities remain. The existing evaluation line sigma=1-m_F(H)>3/4 allows the fixed correction bound Re(-zeta'/zeta(5/4))"),
      ("momentComparison", .str "For D>=1 and a finite prime sieve S, the original primeLogResponse retains precisely ordinary primes r>D outside S. Its Fermi version multiplies each original log(r)*zetaPrimeFilterKernel(p,N,s,r) by fermi(-a*log(r)). Their exact difference multiplies that same summand by fermi(a*log(r)); no prime-power terms are added to either response"),
      ("momentBound", .str "For Re(s)>1,q>0,Re(s)+a-q>1, the norm of the complete difference is at most q^(-N)*sum_k norm(p_k)*q^(-k)*Re(-zeta'/zeta(Re(s)+a-q)). This follows from the positive exponential envelope on the correction, not a cancellation assumption on the main prime tail"),
      ("exactHeatTransport", .str "For a>0,B>0,Re(s)>1, integral_y density(a,B,y)*P(p,D,S,N,s-i*y)=2*F_B(a,p,D,S,N,s+a/2), where F_B retains the original Fermi moment with multiplier exp(-B*log(n)^2). The full complex polynomial, factorial orders and original prime exclusions stay inside the average. Every integrated term norm equals its original norm, paying the complete sum-integral interchange and whole-average integrability"),
      ("actualHeatLine", .str "At a=1-2*m_F(H), the exact input line is 1+m_F(H)+i*t and the output is the original 3/2+i*t. The positive margin discharges Euler convergence. The density is nonnegative with unit mass; the complex moment being averaged is not asserted nonnegative"),
      ("regulatorLimit", .str "For every fixed moment order, polynomial, cutoff and sieve, nonnegative Gaussian width tending to zero recovers the original Fermi moment by summable domination. The corresponding full spectral averages tend to twice that moment. No interchange with the separate growing-order source limit or uniform growing-order signed bound is asserted"),
      ("uniformRate", .str "For any 0<u<1 and fixed complex p, set q=(1+u)/2 and C=u*sum_k norm(p_k)*q^(-k)*Re(-zeta'/zeta(2-q)). For every N,D>=1,finite prime S and a>=1/2, the norm of u^(N+1)*(P-F) at 3/2+i*y is at most C*(2*u/(1+u))^N. The ratio is strictly below one. The constant is independent of a,D,S and y"),
      ("actualSourceTransport", .str "Use the unchanged u=3/2-Re(rho), zero-isolating polynomial, actual quadratic prime sieve and sampling ordinate. The comparison tends to zero for every moving cutoff eventually at least one, with no upper cutoff restriction, and every moving Fermi parameter eventually at least 1/2. In particular a_N=1-2*m_F(H_N) works for every height schedule. On the original squared cutoff schedule, the Fermi-weighted normalized tail therefore has the same hypothetical limit -multiplicity(rho) as the original prime tail"),
      ("limitations", .str "Only the weighting corrections are bounded. The Gaussian sum includes prime powers; the original moment remains an ordinary-prime sum. Gaussian positivity is not transported through the complex polynomial, factorial orders or moving prime support by these estimates. The surviving moment still needs an independent cofinal fixed-gap lower bound above -1. The unweighted original carrier is retained. No new zero exclusion, RH theorem or historical novelty claim; the eventual zero-free family now has width A*log(log(abs(t)))/log(abs(t)) for 0<A<1/(140*log(2)), with coefficient-dependent unevaluated thresholds")
    ]),
    ("primeAdmissibleHeatSource", Json.mkObj [
      ("role", .str "Independent comparison with admissible moving Gaussian families and transport of the original hypothetical source; no new zero exclusion"),
      ("marginLimitTheorem", .str "RiemannGaussian.tendsto_zetaFermiZeroMargin"),
      ("widthAdmissibilityTheorem", .str "RiemannGaussian.fermi_margin_square_admissible"),
      ("wholeZeroAllowanceLimitTheorem", .str "RiemannGaussian.tendsto_allowance_fermi_margin_square"),
      ("jointParameterLimitTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_gaussianFermiPrimeLogResponse_joint"),
      ("heightFloorExistenceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_primeMomentHeatHeight"),
      ("allLaterHeightsTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.primeMomentHeatHeight_tail_spec"),
      ("movingFamilyComparisonTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_actual_prime_sub_marginHeat"),
      ("explicitNormalizedErrorTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.exists_actual_prime_marginHeat_bound"),
      ("movingFamilySourceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_marginHeatPrimeResponse_of_height"),
      ("canonicalSourceTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.tendsto_admissibleHeatPrimeResponse"),
      ("exactSpectralAverageTheorem", .str "RiemannGaussian.SquarefreeEulerQuadratic.admissibleHeatPrimeResponse_eq_integral"),
      ("heightFloor", .str "For every original order N and cutoff D, a proved floor T(N,D)>=max(N,1,2*abs(Im(rho))) makes norm(G_N(H)-F_N(1))<1/(N+1) and the existing scalar whole-zero allowance(m_F(H)^2,H)<1/(N+1) for every H>=T(N,D). The floor is chosen from proved fixed-order joint limits; its growth is not estimated"),
      ("retainedArithmetic", .str "G_N(H) is the unchanged original source-normalized ordinary-prime sum at 3/2+i*Im(rho), with its original complex polynomial, factorial orders and quadratic prime sieve, multiplied by exp(-m_F(H)^2*log(n)^2)*fermi(-(1-2*m_F(H))*log(n)). No limiting value is used in its definition"),
      ("uniformComparison", .str "For u=3/2-Re(rho) in (1/2,1), one C>=0 gives norm(P_N-G_N(H_N))<=C*(2*u/(1+u))^N+1/(N+1), for every cutoff family D and height family H whenever D_N>=1 and H_N>=T(N,D_N). This error is independently proved, with no upper cutoff bound or use of the hypothetical source limit"),
      ("source", .str "Every moving height family eventually above the proved floors has P_N-G_N(H_N)->0 and vanishing standard whole-zero allowance. On the original squared cutoff schedule, the existing hypothetical source P_N->-multiplicity(rho) therefore implies G_N(H_N)->-multiplicity(rho)"),
      ("spectralAverage", .str "The canonical response equals u^(N+1)/2 times the full integral of the actual positive unit-mass density at (1-2*m,m^2) against the original complex prime moment at 1+m+i*Im(rho)-i*y. The full sum-integral interchange remains proved"),
      ("limitations", .str "No independent signed lower bound for the surviving prime response, no upper growth estimate on the height floors, and no estimate for pole, gamma or whole-zero costs after applying the complex moment filter. Positivity of the averaging density does not make the averaged complex moment nonnegative. The actual eventual zero-free family now has width A*log(log(abs(t)))/log(abs(t)) for 0<A<1/(140*log(2)), with coefficient-dependent unevaluated thresholds; the published 4.896 region is not formalized here, and RH remains open")
    ]),
    ("roughDivisorIncidence", Json.mkObj [
      ("massTheorem", .str "RiemannGaussian.RoughDivisorIncidence.sum_lcmSqrtFactorMass_le"),
      ("intersectionTheorem", .str "RiemannGaussian.RoughDivisorIncidence.prod_correctedWeight_le_lcmSqrtFactorMass"),
      ("exactSeriesTheorem", .str "RiemannGaussian.RoughDivisorIncidence.hasSum_fibre"),
      ("generalBoundTheorem", .str "RiemannGaussian.RoughDivisorIncidence.exists_sum_norm_fibre_bound"),
      ("actualBoundTheorem", .str "RiemannGaussian.RoughDivisorIncidence.exists_actual_sum_norm_bound"),
      ("allFamilyArithmeticTheorem", .str "RiemannGaussian.RoughDivisorIncidence.tendsto_actual_incidence"),
      ("massBound", .str "sum_(1<=P<=X) lcmSqrtFactorMass(P) <= 2*sqrt(X)*sum_d exp(-(3/2)*log(d)); the complete divisor correction is summed before any worst-case factor estimate"),
      ("familyScope", .str "All moving finite families of nontrivial squarefree factors P<=D_N^4 with primes outside the original quadratic sieve, and all moving complex weights of norm at most one. No restriction on the number of prime factors"),
      ("bound", .str "The sum of norms of the full source-normalized marked arithmetic responses is <=C(rho)*(1+N)*eta^N -> 0, with eta=2*u^(1/8)/(1+u^(1/8))<1"),
      ("informationRetained", .str "Original rough squarefree coefficients, divisor cutoff, polynomial filter, ordinate, every prime intersection, full lcm divisor mass and the exact ordinary-prime correction"),
      ("limitations", .str "Complete convergent arithmetic series. The bound does not make arbitrary physical restrictions or unweighted union deletion free, and does not prove the remaining full signed inequality")
    ]),
    ("roughMoebiusIncidenceSource", Json.mkObj [
      ("maskIdentityTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.mask_eq_one_add_weight"),
      ("coefficientIdentityTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.coefficient_eq_add_fibres"),
      ("smallProductCancellationTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.coefficient_eq_zero_of_le"),
      ("cofactorCancellationTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.coefficient_large_prime_small_cofactor_zero"),
      ("squareIdentityTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.coefficient_eq_square_add_mixed"),
      ("squareSignTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.mask_square_re_nonneg"),
      ("exactSourceComparisonTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.response_eq_source_add_fibres"),
      ("independentErrorTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.exists_response_error_bound"),
      ("allCutoffSourceTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.tendsto_response"),
      ("fourthCutoffSourceTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.tendsto_fourth_cutoff_response"),
      ("conditionalContradictionTheorem", .str "RiemannGaussian.RoughMoebiusIncidence.false_of_cofinal_response_bound"),
      ("coefficient", .str "M_Y(n)*A_D,S(n), with M_Y(n)=sum_(d|n,d<=Y) mu(d). All higher prime intersections fitting the cutoff are present, with exact signs"),
      ("source", .str "For every moving 1<=Y_N<=D_N^4, the complete source-normalized compensated response tends to -m_rho; its norm error from the old full rough response is <=C(rho)*(1+N)*eta^N at every order"),
      ("exactSupport", .str "Every n<=Y vanishes. Every p*m with p prime, p>Y and 1<m<=Y also vanishes. These cancellations change the remaining coefficient by the stated mask; they are not deletion with unchanged weights"),
      ("squareAndMixed", .str "On rough squarefree composites and at Y=D, M_D*A_D=-M_D^2*log(n)+M_D*L_D, where L_D=sum_(d|n,d<=D) mu(d)*log(d). M_D is real, hence M_D^2 is nonnegative. The subsequent mixed-decay module independently controls M_D*L_D and retains the oscillatory square source"),
      ("limitations", .str "No independent bound for the whole signed square-plus-mixed response is proved. The earlier 1-k_N balanced source is a separate checked representation; its support and error estimates are not silently transferred to this mask. No additional zero exclusion or proof of RH")
    ]),
    ("roughMoebiusMixedDecay", Json.mkObj [
      ("exactLogRemovalTheorem", .str "RiemannGaussian.RoughSquarefreeBare.log_mul_kernel"),
      ("envelopeTheorem", .str "RiemannGaussian.RoughSquarefreeBare.dividedPolynomial_envelope_le"),
      ("uniformMarkedBoundTheorem", .str "RiemannGaussian.RoughSquarefreeBare.exists_response_bound"),
      ("exactLcmExpansionTheorem", .str "RiemannGaussian.RoughMoebiusMixed.coefficient_eq_lcm_sum"),
      ("convergentMixedSeriesTheorem", .str "RiemannGaussian.RoughMoebiusMixed.hasSum_response"),
      ("generalMixedBoundTheorem", .str "RiemannGaussian.RoughMoebiusMixed.exists_response_bound"),
      ("actualMixedBoundTheorem", .str "RiemannGaussian.RoughMoebiusMixed.exists_actual_bound"),
      ("actualMixedDecayTheorem", .str "RiemannGaussian.RoughMoebiusMixed.tendsto_actualResponse"),
      ("primeCancellationTheorem", .str "RiemannGaussian.RoughMoebiusMixed.mask_mul_logMask_prime"),
      ("completeCoefficientIdentityTheorem", .str "RiemannGaussian.RoughMoebiusMixed.compensatedCoefficient_eq_neg_square_add_mixed"),
      ("squareSignTheorem", .str "RiemannGaussian.RoughMoebiusMixed.squareCoefficient_re_nonneg"),
      ("completeSourceErrorTheorem", .str "RiemannGaussian.RoughMoebiusMixed.exists_actualSquare_source_error_bound"),
      ("squareSourceTheorem", .str "RiemannGaussian.RoughMoebiusMixed.tendsto_actualSquareResponse"),
      ("conditionalContradictionTheorem", .str "RiemannGaussian.RoughMoebiusMixed.false_of_cofinal_square_bound"),
      ("mixedBound", .str "The complete normalized rough squarefree M_D*L_D response has norm <=C(rho)*(1+N)*eta^N -> 0 for N>=1, eta=2*u^(1/8)/(1+u^(1/8))<1. The estimate does not use source convergence"),
      ("mechanism", .str "Divide each polynomial coefficient by N+k+1 to remove one logarithm exactly; the envelope does not increase. Uniform marked bare squarefree bounds then control every ordered pair mu(d)*mu(e)*log(e) with exact mark lcm(d,e), at total cost D^2*log(D)"),
      ("primeStructure", .str "All small-prime exclusions, squarefree intersections and shared-prime lcm coincidences are retained. M_D(p)*L_D(p)=0 for every ordinary prime, so mixed completion has no prime leakage"),
      ("squareSource", .str "Q_N=u^(N+1)*sum_(rough squarefree composites n) M_D(n)^2*log(n)*K_N(n) tends to m_rho. Both errors relative to the negative original full rough response have one independently vanishing geometric allowance"),
      ("remainingObligation", .str "An independent Re(Q_N)<=1-epsilon on a cofinal subsequence for every hypothetical right-half zero. Nonnegative coefficients do not control the oscillatory complex kernel. This premise and RH remain open"),
      ("limitations", .str "Complete arithmetic series, with no free physical localization or transfer of the earlier 1-k_N support restrictions. No new zero exclusion or mathematical-priority claim")
    ]),
    ("roughDivisorCorrelation", Json.mkObj [
      ("linearLcmMassTheorem", .str "RiemannGaussian.sum_pair_lcmSqrtFactorMass_le_linear"),
      ("exactPrimeMultiplicityTheorem", .str "RiemannGaussian.sum_pair_prime_lcm_eq"),
      ("linearArithmeticBoundTheorem", .str "RiemannGaussian.RoughDivisorLinear.exists_bounded_remainder_bound"),
      ("enlargedCutoffErrorTheorem", .str "RiemannGaussian.RoughDivisorLinear.exists_cubic_cutoff_error_bound"),
      ("enlargedCutoffDecayTheorem", .str "RiemannGaussian.RoughDivisorLinear.tendsto_cubic_cutoff_error"),
      ("enlargedCutoffSourceTheorem", .str "RiemannGaussian.RoughDivisorLinear.tendsto_cubic_cutoff_source"),
      ("linearBound", .str "For every pair of pointwise bounded complex families through D, the complete nonunit remainder is bounded by C(y,r)*D*exp(4*sqrt(R))*r^(-N)*B_p(r). This improves the preceding D^3*(1+log(D^2)) bound for this class and includes the complete prime correction"),
      ("linearMechanism", .str "Group the full lcm divisor mass by gcd(d,e), retain both exact divided cutoffs, and sum the remaining weight F(g)/g using a convergent g^(-5/4) majorant. Each prime lcm occurs only in (1,p), (p,1), (p,p); its full kernel contribution also has linear total cost"),
      ("enlargedCutoffScope", .str "All moving divisor cutoffs 1<=Y_N<=D_N^3 and all pointwise bounded complex families satisfy norm(C_N(Y_N,w_N,v_N)-w_N(1)*conj(v_N(1))*U_N)<=C(rho)*eta^N. The actual sieve, polynomial and ordinate are unchanged. The unit source remains. Physical localization and n-dependent cutoffs are not free; the separate prime-log lcm theorem proves small-prime-log decay through D_N^2"),
      ("exactMatrixTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.coefficient_eq_pairs"),
      ("convergentSeriesTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.hasSum_response"),
      ("exactUnitSplitTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.response_eq_unit_add_remainder"),
      ("independentEntryTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.exists_entry_bound"),
      ("independentFamilyTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.exists_remainder_bound"),
      ("actualUniformErrorTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.exists_actual_error_bound"),
      ("allMovingFamiliesTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.tendsto_actual_error"),
      ("sourceClassificationTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.tendsto_actualResponse"),
      ("exactDiagonalTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.coefficient_self_eq"),
      ("boundedFamilyEligibilityTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.mass_budget_of_norm_le_one"),
      ("actualMobiusSquareTheorem", .str "RiemannGaussian.RoughDivisorCorrelation.actualResponse_moebius"),
      ("scope", .str "All pairs of moving complex divisor-weight families through D_N with L1(w)*L1(v)<=D_N^2. This includes all pointwise bounded weights and some larger sparse families; weights need not be real, multiplicative or equal"),
      ("exactCarrier", .str "C_N(w,v)=u^(N+1)*sum_n W_w(n)*conj(W_v(n))*b_S(n)*K_N(n), with W_w(n)=sum_(d<=D_N,d|n) w(d) and b_S the original rough squarefree composite logarithmic weight"),
      ("independentBound", .str "norm(C_N(w,v)-w(1)*conj(v(1))*U_N)<=C(rho)*(1+N)*eta^N, uniformly at every order, eta=2*u^(1/8)/(1+u^(1/8))<1. U_N is the original unweighted composite logarithmic response"),
      ("generalCost", .str "The exact nonunit remainder costs C(y,r)*L1(w)*L1(v)*D*(1+log(D^2))*exp(4*sqrt(R))*r^(-N)*B_p(r), including every lcm cross term and complete ordinary-prime correction"),
      ("limitingSource", .str "If w_N(1)*conj(v_N(1)) tends to c, then C_N tends to c*m_rho. All nonunit entries are independently negligible; the original full kernel and unit-source phase remain"),
      ("interpretation", .str "Within this mass and support budget, changing the nonunit coefficients does not change the leading source. It can still change a useful representation for proving an independent upper bound; this theorem is not an impossibility result for such proofs"),
      ("remainingObligation", .str "The independent strict signed upper bound below the retained unit source on a cofinal subsequence remains open. No free physical localization, unrestricted mass claim, new zero exclusion or proof of RH")
    ]),
    ("roughMoebiusHyperbola", Json.mkObj [
      ("endpointTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.divisor_reflected_cutoff"),
      ("weightedReflectionTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.weighted_tail_reflection"),
      ("completeCoefficientTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.compensatedCoefficient_reflection"),
      ("complementarySquareTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.squareCoefficient_eq_complementary_mixed"),
      ("convergentSeriesTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.hasSum_response"),
      ("independentCoefficientBoundTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.norm_reflected_coefficient_le"),
      ("uniformSubsetBoundTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.norm_normalized_reflected_head_le"),
      ("actualHeadBoundTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.norm_actualHead_le"),
      ("reflectedCutoffSizeTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.reflected_cutoff_large"),
      ("convergentTailTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.summable_tailResponse"),
      ("exactSourcePartitionTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.actualTail_eq"),
      ("retainedSourceTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.tendsto_actualTail"),
      ("halfCutoffCoefficientTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.coefficient_half_cutoff"),
      ("cutoffOneResponseTheorem", .str "RiemannGaussian.RoughMoebiusHyperbola.response_one"),
      ("identity", .str "For E=floor(n/(D+1)), the complete supported coefficient M_D*A_D equals -B_E, where B_E is the rough squarefree M_E*L_E coefficient. Also M_D^2*b_S=B_D+B_E. All sieve, prime, unit and zero cases are proved"),
      ("independentBound", .str "Every selected finite subset T of n<=D_N^3 has normalized reflected response norm <=C(p)*(9/10)^N. The bound covers all complex polynomials, real ordinates and finite prime sieves, and uses no source limit"),
      ("mechanism", .str "Exact reflection bounds the adaptive coefficient by D_N times the original divisor-log majorant. Divide by D_N, apply the cubic small-product estimate, and pay D_N*(3/4)^N<=(9/10)^N"),
      ("remainingSupport", .str "The literal convergent tail n>D_N^3 retains source m_rho. Its reflected cutoff satisfies D_N^2<E+D_N, including every integer endpoint"),
      ("remainingObligation", .str "An independent strict signed upper bound for the retained tail below its unit source cofinally. Fixed-cutoff mixed decay does not control a cutoff that changes with each summation integer. No new zero bound, RH proof or mathematical-priority claim")
    ]),
    ("roughPrimeLogSource", Json.mkObj [
      ("lcmBareBoundTheorem", .str "RiemannGaussian.RoughSquarefreeBare.exists_response_lcm_bound"),
      ("primeInsertionMassTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.sum_prime_log_lcm_mass_le"),
      ("completeTripleMassTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.exists_triple_mass_bound"),
      ("improvedFullBoundTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.exists_smallResponse_bound"),
      ("enlargedCutoffBoundTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.exists_square_cutoff_bound"),
      ("enlargedCutoffDecayTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.tendsto_square_cutoff"),
      ("enlargedCutoffSourceTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.tendsto_large_square_cutoff"),
      ("exactFourthTailTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.normalizedLargeResponse_eq_fourth_tail"),
      ("fourthTailSourceTheorem", .str "RiemannGaussian.RoughPrimeLogLcm.tendsto_doubled_log_cutoff_source"),
      ("improvedFullBound", .str "The complete small-prime logarithmic response costs C(y,r)*D*sqrt(D)*log(D)*exp(4*sqrt(R))*r^(-N)*B_p(r), retaining the full bare lcm mass, shared-prime cases and every ordered pair"),
      ("enlargedCutoff", .str "Every moving 1<=Y_N<=D_N^2 has independently vanishing normalized complete small-prime response, bounded by C(rho)*(1+N)*eta^N. The actual large-prime response at that same cutoff tends to m_rho"),
      ("fourthTailSupport", .str "At Y_N=D_N^2, every nonzero coefficient has a prime and cofactor both greater than D_N^2, so the entire convergent source is exactly the tail n>D_N^4. The original sieve, polynomial, complex phase and normalization are unchanged"),
      ("completeIntersectionTheorem", .str "RiemannGaussian.RoughPrimeLog.smallCoefficient_eq_lcm_sum"),
      ("independentFullBoundTheorem", .str "RiemannGaussian.RoughPrimeLog.exists_smallResponse_bound"),
      ("actualDecayTheorem", .str "RiemannGaussian.RoughPrimeLog.exists_actualSmall_bound"),
      ("exactSourceSplitTheorem", .str "RiemannGaussian.RoughPrimeLog.coefficient_eq_square_sub_small"),
      ("smoothSupportCancellationTheorem", .str "RiemannGaussian.RoughPrimeLog.coefficient_eq_zero_of_smooth"),
      ("primeCofactorSupportTheorem", .str "RiemannGaussian.RoughPrimeLog.exists_prime_cofactor_of_coefficient_ne_zero"),
      ("exactPrimeFibresTheorem", .str "RiemannGaussian.RoughPrimeLog.coefficient_eq_large_prime_fibres"),
      ("generalQuadraticHeadTheorem", .str "RiemannGaussian.norm_normalized_sum_zetaArithmetic_quadratic_cubic_le"),
      ("actualHeadTheorem", .str "RiemannGaussian.RoughPrimeLog.norm_actualHead_le"),
      ("convergentTailTheorem", .str "RiemannGaussian.RoughPrimeLog.summable_tailResponse"),
      ("completeErrorTheorem", .str "RiemannGaussian.RoughPrimeLog.exists_actualTail_error_bound"),
      ("independentErrorDecayTheorem", .str "RiemannGaussian.RoughPrimeLog.tendsto_actualTail_sub_square"),
      ("retainedSourceTheorem", .str "RiemannGaussian.RoughPrimeLog.tendsto_actualTail"),
      ("conditionalContradictionTheorem", .str "RiemannGaussian.RoughPrimeLog.false_of_cofinal_tail_bound"),
      ("weightedPrimeInsertionTheorem", .str "RiemannGaussian.RoughMoebiusPrimeRecurrence.weighted_prefix_prime"),
      ("adaptiveLogRecurrenceTheorem", .str "RiemannGaussian.RoughMoebiusPrimeRecurrence.reflected_logMask_prime"),
      ("carrier", .str "M_D(n)^2*sum_(p|n,p>D) log(p) on the original rough squarefree composites. The literal retained series is further restricted to n>D_N^3, with the original complex kernel and normalization"),
      ("independentBounds", .str "The preceding bound cost C(y,r)*D^3*log(D)*exp(4*sqrt(R))*r^(-N)*B_p(r) at order N+1; the separate lcm bound improves this to D*sqrt(D)*log(D). Every selected cubic-head subset with full D_N^2 majorant cost also has bound C(p)*(1/(2u))^N, retaining u>1/2"),
      ("scope", .str "Both complete errors independently vanish. The new weight is zero when all prime factors are <=D_N, and every nonzero coefficient has a prime and cofactor both >D_N. This does not estimate a separately restricted part of the old correction or assert an independent bound on the surviving prime-cofactor sum"),
      ("remainingObligation", .str "For every hypothetical right-half zero, a cofinal real-part upper bound strictly below one for the retained normalized tail. That premise remains open. No new zero exclusion or proof of RH")
    ]),
    ("multiplicativePhase", Json.mkObj [
      ("kernelTransportTheorem", .str "RiemannGaussian.MultiplicativePhase.kernel_shift"),
      ("fullMatrixTransportTheorem", .str "RiemannGaussian.MultiplicativePhase.bilinear_shift"),
      ("uniformBoundEquivalenceTheorem", .str "RiemannGaussian.MultiplicativePhase.uniform_bound_iff_zero_height"),
      ("scope", .str "Arbitrary finite matrices on positive factor indices, with the full complex polynomial amplitude and every arithmetic restriction held fixed. The factorized height phase is exactly absorbed by unit row and column modulations"),
      ("interpretation", .str "Bounds uniform over all complex coefficients with fixed magnitude budgets are equivalent to those at zero height. The actual fixed Mobius coefficients have additional structure, which this equivalence does not discard or control"),
      ("remainingObligation", .str "An independent strict signed bound on the actual source remains open. These transport identities provide no new arithmetic bound or zero exclusion")
    ]),
    ("roughPrimeIncidenceSource", Json.mkObj [
      ("coefficientIdentityTheorem", .str "RiemannGaussian.RoughPrimeIncidence.compensatedCoefficient_eq_sub"),
      ("semiprimeCancellationTheorem", .str "RiemannGaussian.RoughPrimeIncidence.compensatedCoefficient_unbalanced_semiprime_zero"),
      ("balancedSupportTheorem", .str "RiemannGaussian.RoughPrimeIncidence.compensatedCoefficient_balanced"),
      ("smallProductBoundTheorem", .str "RiemannGaussian.RoughPrimeIncidence.norm_smallPart_le"),
      ("exactSourceIdentityTheorem", .str "RiemannGaussian.RoughPrimeIncidence.balancedPart_eq_source_sub_corrections"),
      ("fullErrorBoundTheorem", .str "RiemannGaussian.RoughPrimeIncidence.exists_balanced_error_bound"),
      ("sourceTheorem", .str "RiemannGaussian.RoughPrimeIncidence.tendsto_balanced_source"),
      ("conditionalContradictionTheorem", .str "RiemannGaussian.RoughPrimeIncidence.false_of_cofinal_balanced_bound"),
      ("coefficient", .str "(1-k_N(n))*A_N(n), where k_N(n) counts primes at most D_N which divide n and are outside the original quadratic sieve; every multiple incidence retains its exact sign"),
      ("remainingSupport", .str "n>D_N^3 with a factorization n=a*b, a>D_N, b>D_N. The old unbalanced semiprime arm vanishes coefficientwise after incidence subtraction; no separate decay for that old arm is claimed"),
      ("source", .str "The complete normalized compensated balanced series tends to -m_rho, with full complex kernel, analytic multiplicity, roughness, squarefreeness and original divisor cutoff retained"),
      ("subtractionError", .str "At every N its norm difference from the original full rough carrier is at most C(rho)*(1+N)*eta^N + 2*C(P)*(9/10)^N, tending to zero; eta=2*u^(1/8)/(1+u^(1/8))<1"),
      ("limitations", .str "A complete infinite arithmetic series, without an additional physical-window restriction. The independent bound Re(balancedPart_N)>=-1+epsilon for some epsilon>0 on a cofinal subsequence remains open; no additional zero exclusion or proof of RH")
    ]),
    ("roughPrimeIncidence", Json.mkObj [
      ("coefficientTheorem", .str "RiemannGaussian.RoughPrimeIncidence.fibreCoefficient_eq"),
      ("exactSeriesTheorem", .str "RiemannGaussian.RoughPrimeIncidence.hasSum_fibre"),
      ("incidenceIdentityTheorem", .str "RiemannGaussian.RoughPrimeIncidence.hasSum_weight"),
      ("generalVariationBoundTheorem", .str "RiemannGaussian.RoughPrimeIncidence.exists_sum_norm_fibre_bound"),
      ("actualVariationBoundTheorem", .str "RiemannGaussian.RoughPrimeIncidence.exists_actual_sum_norm_bound"),
      ("variationDecayTheorem", .str "RiemannGaussian.RoughPrimeIncidence.tendsto_actual_sum_norm"),
      ("allFamilyArithmeticDecayTheorem", .str "RiemannGaussian.RoughPrimeIncidence.tendsto_actual_incidence"),
      ("primeRange", .str "Every selected prime outside the original quadratic sieve and at most D_N^4, where D_N=floor(q^N) and q=u^(-1/4)"),
      ("bound", .str "Sum over all selected primes of the norm of each complete source-normalized marked response <=C(rho)*(1+N)*eta^N; eta=2*u^(1/8)/(1+u^(1/8))<1"),
      ("familyScope", .str "Every moving finite prime family in the enlarged range and every moving complex weight family of norm at most one; the constant is independent of both families"),
      ("informationRetained", .str "The exact original rough squarefree coefficient, divisor cutoff, pole-isolating polynomial, ordinate and prime overlaps. Each marked completion includes all signed squarefree intersections and the explicit single ordinary-prime correction"),
      ("limitations", .str "The estimate is for complete arithmetic series and linear prime incidences. It does not control their union or arbitrary physical restrictions. The source companion uses an exact subtraction to cancel unbalanced semiprimes while retaining weight 1-k_N(n) on the balanced arm; its independent signed bound remains open")
    ]),
    ("roughCoprimeFactorFamilies", Json.mkObj [
      ("complexityTheorem", .str "RiemannGaussian.RoughCoprimeFactor.actual_complexity_le"),
      ("uniformSubexponentialTheorem", .str "RiemannGaussian.RoughCoprimeFactor.eventually_actual_complexity_le"),
      ("familyBoundTheorem", .str "RiemannGaussian.RoughCoprimeFactor.exists_actual_factor_family_budget_bound"),
      ("arithmeticDecayTheorem", .str "RiemannGaussian.RoughCoprimeFactor.tendsto_actual_factor_family_arithmetic"),
      ("exactCoverageTheorem", .str "RiemannGaussian.RoughCoprimeFactor.hasSum_coverage"),
      ("coverageDecayTheorem", .str "RiemannGaussian.RoughCoprimeFactor.tendsto_actual_coverage"),
      ("semiprimeCoverageTheorem", .str "RiemannGaussian.RoughCoprimeFactor.coverage_semiprime"),
      ("semiprimeMassTheorem", .str "RiemannGaussian.RoughCoprimeFactor.card_semiprimes_le_mass_of_coverage_one"),
      ("complexity", .str "For every divisor P of actual rough physical support, tau(P)^2*(1+2*log(P)) <= (1+16*N)*exp(16*log(2)*N/log(R_N)); for every b>1 this is eventually <=(1+16*N)*b^N uniformly in P"),
      ("familyBound", .str "Complete coprime-factor response families with sum of coefficient norms <=D_N^2 have source-normalized norm <=C(rho)*(1+16*N)*(u^(1/8))^N, tending to zero. This includes both original finite prefixes and all Euler terms"),
      ("factorScope", .str "Factors divide nonzero actual rough-window coefficients; they may move throughout the entire physical divisor range. The old P^2<=D_N restriction is absent. Genuine arithmetic identification requires mixed-prime factors"),
      ("exactCoverage", .str "The weighted response is exactly the original c_D(n)*K_N(n) series multiplied by sum_P w(P)*1_(P divides n and gcd(P,n/P)=1), retaining all overlaps and extra multiples"),
      ("semiprimeRigidity", .str "For every mixed-prime factor family, coverage at p*q is its own weight w(p*q) if that factor is selected, and zero otherwise. Exact coverage of a finite semiprime set T costs at least card(T) in coefficient mass. No asymptotic count or impossibility of a controlled signed approximation is claimed"),
      ("limitations", .str "The full rough squarefree survivor is not yet represented by such coverage within the proved mass budget and controlled restriction error. Each bounded sector includes all coprime multiples, not just the physical rough window. The independent full signed inequality remains open; no additional zero is excluded")
    ]),
    ("roughCoprimeEulerChannels", Json.mkObj [
      ("exactProductTheorem", .str "RiemannGaussian.CoprimeEulerPhase.coprimeEuler_eq_product"),
      ("primePhaseTheorem", .str "RiemannGaussian.CoprimeEulerPhase.norm_coprimeEuler_le_with_phase"),
      ("jointPrimeGainTheorem", .str "RiemannGaussian.CoprimeEulerPhase.exists_uniform_coprimeEuler_gain"),
      ("actualFactorMassTheorem", .str "RiemannGaussian.CoprimeEulerPhase.actual_factor_feature_mass_le"),
      ("budgetDecayTheorem", .str "RiemannGaussian.CoprimeEulerPhase.tendsto_roughEulerBudget"),
      ("jointChannelBoundTheorem", .str "RiemannGaussian.CoprimeEulerPhase.actual_cauchy_factor_Euler_channels_le"),
      ("jointChannelDecayTheorem", .str "RiemannGaussian.CoprimeEulerPhase.tendsto_roughEulerChannelAllowance"),
      ("allFamilyBoundTheorem", .str "RiemannGaussian.CoprimeEulerPhase.norm_weighted_actual_Euler_channels_le"),
      ("vanishingPhaseGainTheorem", .str "RiemannGaussian.CoprimeEulerPhase.eventually_actual_factor_phaseGain_lt"),
      ("scope", .str "Every divisor P of every nonzero actual rough-window coefficient n, with the original quadratic prime cutoff and log(n)<=8*N, throughout the full closed disc of fixed radius r<1 about 3/2+i*Im(rho)"),
      ("budget", .str "b(rho,sigma,N)=(8*N/log(2))*exp(-sigma*log(R_N)) tends to zero for every fixed sigma>1/2, including the exact floor in R_N"),
      ("jointBound", .str "norm(E_P(s)-1)+norm(L_P(s)) <= (1+2/(1-r))*(exp(b(rho,1-r/2,N))-1), tending to zero. L_P=-deriv(E_P) is the original logarithmic channel"),
      ("informationRetained", .str "All prime-product intersections and exact cosine gains precede the bound. Distinct primes force a positive joint gain on compact regions; the total gain on moving actual rough factors is nevertheless at most 2*b and tends uniformly to zero"),
      ("familyCost", .str "For arbitrary finite complex families the two weighted channel-error norms together are at most the allowance times the full sum of coefficient norms. This mass is not assumed bounded for the remaining arithmetic response"),
      ("limitations", .str "No bound for the full coupled arithmetic response or the separate Euler product over all selected small primes. The later roughCoprimeFactorFamilies result controls full prefixes for its stated family class; representation of the actual survivor within the mass and restriction budget remains open. No additional zero is excluded; RH remains open")
    ]),
    ("roughSquarefreeFactorSource", Json.mkObj [
      ("generalSmallProductBoundTheorem", .str "RiemannGaussian.norm_normalized_sum_zetaArithmetic_cubic_product_le"),
      ("actualSmallProductBoundTheorem", .str "RiemannGaussian.norm_zetaRightHalfRoughSquarefreeSmallProduct_le"),
      ("pointwiseCancellationTheorem", .str "RiemannGaussian.zetaRoughSquarefreeCoefficient_large_prime_composite_zero"),
      ("finiteDeletionTheorem", .str "RiemannGaussian.sum_zetaRoughSquarefreeCoefficient_remove_small_composite"),
      ("factorizationTheorem", .str "RiemannGaussian.zetaRoughSquarefreeCoefficient_balanced_or_semiprime"),
      ("actualSemiprimeSupportTheorem", .str "RiemannGaussian.zetaRightHalfRoughSquarefreeUnbalancedProduct_support"),
      ("exactPartitionTheorem", .str "RiemannGaussian.zetaRightHalfRoughSquarefreeProduct_partition"),
      ("coupledSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfRoughSquarefreeFactorSource"),
      ("finiteSignedComparisonTheorem", .str "RiemannGaussian.abs_zetaRightHalfRoughSquarefreeFactorSource_sub_reflection_le"),
      ("conditionalContradictionTheorem", .str "RiemannGaussian.false_of_cofinal_zetaRightHalfRoughSquarefreeFactor_bound"),
      ("independentBound", .str "For any coefficients dominated by zetaMoebiusLogMajorant, any polynomial P and ordinate y, and every finite subset of n<=D_N^3, the original u^(N+1)-normalized sum has norm at most C(P)*(3/4)^N, where 1/2<u<1 and D_N=floor(u^(-N/4))"),
      ("pointwiseGeometry", .str "For p prime and 1<m<=D<p, the original tail coefficient at p*m is -vonMangoldt(m). On the actual squarefree composite support, composite m vanishes exactly and prime m leaves -log(m). All selected-prime overlaps remain excluded"),
      ("survivingGeometry", .str "Above D_N^3, nonzero actual coefficients either factor as n=a*b with both factors greater than D_N, or have n=p*q with q<=D_N<p, both primes above the quadratic prime cutoff, and coefficient -log(q). Both factors greater than D_N does not mean comparable factors"),
      ("fullSource", .str "The already normalized coupled sum B_N+U_N tends to -m_rho. The exact complex partition retains both sectors, the original filter, phase and physical window"),
      ("completeComparison", .str "abs(-Re(B_N+U_N)/2-u^(N+1)*W_N) <= (C(P)*(3/4)^N+zetaLogWindowError+zetaAveragedWindowError)/2; every error tends to zero"),
      ("remainingObligation", .str "Prove an independent one-sided bound for the coupled large-product sum; for example Re(B_N+U_N)>=-1+epsilon with epsilon>0 on a cofinal subsequence. This arithmetic premise remains unproved; no additional zero is excluded and RH remains open")
    ]),
    ("roughSquarefreeSignedSource", Json.mkObj [
      ("infiniteSquareLimitTheorem", .str "RiemannGaussian.tendsto_zetaSquarefreeDivisibilityPrefixFilter"),
      ("squarefreeIntersectionBoundTheorem", .str "RiemannGaussian.exists_zetaSquarefreeDivisibilityPrefixFilter_bound"),
      ("primeAvoidanceTheorem", .str "RiemannGaussian.primeAvoidance_eq_signed_subsets"),
      ("exactOnePrimePatternTheorem", .str "RiemannGaussian.primeCountOneTransform_indicator"),
      ("completePatternSeriesTheorem", .str "RiemannGaussian.hasSum_primeCountOneTransform"),
      ("completeOverlapTheorem", .str "RiemannGaussian.norm_primeCountOneTransform_le"),
      ("primeCorrectionTheorem", .str "RiemannGaussian.zetaOnePrimeSquarefreeCoefficient_eq_prefix_add_primes"),
      ("actualPrefixSeriesTheorem", .str "RiemannGaussian.hasSum_zetaOnePrimeSquarefreePrefixFilter"),
      ("actualPrefixBoundTheorem", .str "RiemannGaussian.exists_zetaOnePrimeSquarefreePrefixFilter_bound"),
      ("literalSurvivorRestrictionTheorem", .str "RiemannGaussian.zetaOnePrimeSquarefreeCoefficient_eq_sieved"),
      ("fullArithmeticSeriesTheorem", .str "RiemannGaussian.hasSum_zetaOnePrimeSquarefreeFilter"),
      ("primeCorrectionBoundTheorem", .str "RiemannGaussian.norm_selectedPrimeFilter_le"),
      ("wholeArithmeticBoundTheorem", .str "RiemannGaussian.exists_zetaOnePrimeSquarefreeFilter_bound"),
      ("exactSeriesSplitTheorem", .str "RiemannGaussian.zetaSquarefreeFilter_eq_onePrime_add_rough"),
      ("actualCutoffBudgetTheorem", .str "RiemannGaussian.zetaRightHalfPrimePatternCutoff_sq_le"),
      ("normalizedDeletionBoundTheorem", .str "RiemannGaussian.exists_zetaRightHalfOnePrimeSquarefree_error_bound"),
      ("normalizedDeletionDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfOnePrimeSquarefreeFilter"),
      ("fullSurvivingSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfRoughSquarefreeFilter"),
      ("arithmeticErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfRoughSquarefreeFilter_error_bound"),
      ("unchangedSurvivorCoefficientTheorem", .str "RiemannGaussian.zetaRightHalfRoughSquarefreeWindowCoefficient_eq"),
      ("survivorSupportTheorem", .str "RiemannGaussian.zetaRightHalfRoughSquarefreeWindowCoefficient_support"),
      ("complexSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfRoughSquarefreeWindowFourierCarrier"),
      ("signedSourceTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfRoughSquarefreeWindowReflectionWork"),
      ("reflectionIdentityTheorem", .str "RiemannGaussian.zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection"),
      ("finiteErrorTheorem", .str "RiemannGaussian.exists_zetaRightHalfRoughSquarefreeWindowReflection_error_bound"),
      ("totalErrorDecayTheorem", .str "RiemannGaussian.tendsto_zetaRightHalfRoughSquarefreeWindowTotalError"),
      ("familyScope", .str "Every finite selected-prime family through R, every positive divisor cutoff, polynomial filter and moment order, and each fixed ordinate with abs(y)>1. Squarefree restriction includes every prime square by genuine dominated convergence of the full series"),
      ("intersectionBound", .str "The actual squarefree prefix on a prime intersection W has norm at most C(y,r)*D*r^(-N)*sum_k(norm(p_k)*r^(-k))*prod_{a in W}b_tau(a), where tau=1-r/2>1/2 and b_tau=w_tau*(1+w_tau); all shared-prime corrections are retained"),
      ("exactPattern", .str "Exactly one selected prime is full minus the exact zero-prime and at-least-two-prime patterns. Every signed subset and shared intersection is present before the companion norm bound"),
      ("wholeOverlapCost", .str "For every nonnegative prime weight w and every response with norm(F(W))<=A*prod_W w, the entire one-prime transform has norm at most 3*A*prod_S(1+2*w). The actual corrected weights give a fixed constant times exp(4*sqrt(R))"),
      ("finitePrimeCorrection", .str "The literal one-prime squarefree distinct-prime coefficient equals its full negative divisor prefix plus exactly 1_{n in S}*log(n). The complete complex correction has bound R^2*r^(-N)*sum_k(norm(p_k)*r^(-k))"),
      ("actualWholeBound", .str "The entire one-prime squarefree series is bounded by C(y,r)*(1+R^2)*D*exp(4*sqrt(R))*r^(-N)*sum_k(norm(p_k)*r^(-k)), with no remaining overlap or cancellation premise"),
      ("actualCutoffAndRate", .str "u=3/2-Re(rho), q=u^(-1/4), D_N=floor(q^N), R_N=floor(N*log(q)/8)^2, r=(1+sqrt(u))/2 and lambda=2*sqrt(u)/(1+sqrt(u)) in (0,1). The full normalized last-prime contribution is at most C(rho)*(1+N^4)*lambda^N tending to zero"),
      ("survivor", .str "Exactly the preceding squarefree coefficients on integers avoiding every selected prime. Each nonzero window index has 2*N/5<=log(n)<=8*N, n>D_N^2, Squarefree n, at least two distinct prime divisors, and every prime divisor strictly greater than R_N"),
      ("fullSource", .str "Re(C_N)=-2*W_N exactly; u^(N+1)*C_N tends to -m_rho and u^(N+1)*W_N tends to m_rho/2. Complete physical phases and centered Fourier products remain in the (6/7)^N region"),
      ("completeAllowance", .str "(C1*(1+N^4)*(sqrt(u))^N+C2*(1+N^4)*lambda^N+zetaAveragedWindowError(p,N,y))/2 tends to zero. Original head, prime powers, all quadratic-prime overlaps, every prime square, the last selected prime and its finite correction, both physical shells and all complementary Fourier interactions are included"),
      ("remainingObligation", .str "One independent strict upper bound below m_rho/2 for the entire normalized rough squarefree signed correlation at arbitrarily late orders for every hypothetical right-half zero"),
      ("status", .str "The entire final selected-prime contribution is independently controlled. The full source remains on its rough squarefree complement, whose strict arithmetic bound is still open. No additional zero exclusion is proved; the all-height edge strip is unchanged and RH remains open")
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
      ("status", .str "Stronger unconditional arithmetic floor and necessary zero inequality. Strict violation of the explicit finite energy budget proves literal zeta nonvanishing, but that test is not proved throughout the right half-strip. The fixed-degree reserve has a uniform mass-normalized ceiling; this is not an upper bound on the complete prime work. A separate signed-pole argument now widens the uniform edge region; RH remains open")
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
