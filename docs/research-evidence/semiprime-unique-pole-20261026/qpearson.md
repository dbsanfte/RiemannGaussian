# Finite q-Pearson and little-q-Jacobi execution for the unique pole

26 October 2026. Scratch paper investigation; no repository edits or numerical campaign. **Result:** the finite Lambert functional is a concrete terminating little-q-Jacobi functional. Its short recurrence and both endpoint conventions are initialized with certified units. The natural polynomial Pearson closure of a row modification is redundant; a genuinely rational Pearson closure gives a first-order adjacent q-connection, retaining shifted pole data. Neither executed route yet supplies the one selected singular value in soft K. The completed cost remains soft K^(5/4), not a general lower bound.

## 1. Native input and exact finite Pearson equation

Use the selected whole-bin singleton family from [unique-cover.md](../semiprime-unique-weighted-20261026/unique-cover.md), J<=K/3 and h=O(K^(3/2)). At the correct nonsplit field exactly ONE row-clock leaf vanishes. Let x_i=rho^i and

 c_i=(-1)^i*rho^(i(i+1)/2)*[h-1 choose i]_rho,
 Lambda(f)=sum_(i=0)^(h-1)c_i*f(x_i), kappa=(rho;rho)_(h-1).

The c_i are implicit unit formulas. Only kappa and O(J) ordinary moments are acquired; no h-entry coefficient array is emitted. Their ratio gives

 (1-rho*x_i)c_(i+1)=(rho^h-rho*x_i)c_i.

The missing lower and upper boundary contributions vanish because 1-x_0=0 and rho^h-rho*x_(h-1)=0. Therefore, for every polynomial or admissible rational f,

 Lambda((1-X)f(X))=Lambda((rho^h-rho*X)f(rho*X)).      (1)

This is a finite algebraic identity after clearing denominators; no infinite-series or positive-measure assumption enters. It gives exactly

 (1-rho^(m+1))*mu_(m+1)=(1-rho^(h+m))*mu_m,
 mu_0=kappa.

All O(J) short starts cost soft(J+sqrt h), with the native h+O(J)<16H guard. Numerators at larger exponents need no inverse; actual denominators are screened.

## 2. Execute the natural polynomial Pearson closure: it adds no condition

Use the actual short row denominator D_delta(X)=prod_j(1+delta-T_j X), and let A_delta(X) be either cofactor numerator from unique-lambert.md (unmarked or tag-marked). Define the rationally modified functional

 Gamma(p)=Lambda(A_delta(X)*p(X)/D_delta(X)).

Its natural cleared Pearson pair is

 sigma(X)=(1-X)*D_delta(X)*A_delta(X/rho),
 tau(X)=(rho^h-rho*X)*D_delta(X)*A_delta(rho*X),
 Gamma(sigma*f)=Gamma(tau*f(rho*X)).                  (2)

The sigma/tau degrees are O(J); their coefficients to fixed delta precision and all initial source moments are acquired in soft J. No row root separation is needed. The cofactor-over-denominator sources remain sums of simple inverse row factors, so their componentwise poles are at most simple even when other components have several hits.

Here is the exact redundancy calculation, not just an arbitrary-moment objection. If Gamma already satisfies Gamma(D_delta*p)=Lambda(A_delta*p), the left side of (2) is

 Lambda((1-X)*A_delta(X)*A_delta(X/rho)*f(X)),

and its right side is

 Lambda((rho^h-rho*X)*A_delta(X)*A_delta(rho*X)*f(rho*X)).

They agree by (1) with test function A_delta(X)*A_delta(X/rho)*f(X). Thus (2) is an algebraic CONSEQUENCE of the already acquired multiplication/source equation, for ALL polynomial test functions. Adding this particular Pearson closure does not impose the missing clock support.

Both sigma and tau vanish at any root theta(delta)=(1+delta)/T_j of D_delta. Hence the extraneous row-root Dirac functionals in unique-lambert.md remain homogeneous solutions, even with the rank-one/simple-pole promise. This is a scoped failure of THIS polynomial Pearson closure. It proves nothing against other rational support conditions or direct selected-pole algorithms.

## 3. Constant barycentric numerator: a real rational connection, not unsafe cancellation

Suppose the additional paid separation gate supplies unit row differences. With alpha_j=T_j^(J-1)/D_row'(T_j), the exact barycentric identity is

 sum_j alpha_j/(A-T_j X)=A^(J-1)/prod_j(A-T_j X), A=1+delta.

Thus the unmarked source can have constant numerator. This does not allow cancellation of the common D_delta factor INSIDE (2): that would discard the Dirac terms one is trying to select.

Instead apply (1) to the rational test p(X)/D_delta(X), BEFORE singular specialization. For Gamma_D(p)=Lambda(p/D_delta), this gives the honest minimal rational equation

 Gamma_D((1-X)*p(X))
   =Gamma_(D_delta(rho X))((rho^h-rho*X)*p(rho*X)).    (3)

The shifted denominator is a real new functional input. Its poles can lie at the predecessor clock node; they cannot be declared regular simply because the original row has only one hit. This retains the actual finite boundary and every shifted atom.

For a single row define F_T(A)=Lambda(1/(A-TX)). Polynomial division in (3) cancels the KNOWN mu_0/T contacts and executes it as

 (A-rho^h*T)*F_(rho T)(A)=(A-T)*F_T(A).               (4)

Every coefficient is acquired in soft J for all supplied T_j. At A=1, original endpoint factors can be norm/coordinate-screened in soft J; only an actual labelled leaf gets the two-coordinate decoder. When both endpoints are units, (4) transports an interior singular residue by a nonzero acquired multiplier. It does not remove that residue.

The fixed regular start is F_0(A)=kappa/A. The exact solution is

 F_T(A)=kappa*A^(h-1)/prod_(i<h)(A-T*rho^i).          (5)

Equation (4), its regular start and known terminal exponent h are a fully initialized first-order rational q-connection. Evaluating (5) at the J selected arguments by the shared engine costs soft(J+sqrt(Jh)). No h coefficient list is needed, but neither (4) nor the constant numerator supplies a shorter connection from T=0 to the one singular supplied T. In particular multiplicative q-transports never reach nonzero T from zero in finitely many steps. This is an execution/cost statement, not a bound against alternative connection algorithms.

For barycentric weights the unmarked sum is a linear combination of these F_T values; its tag-marked partner has the same known row weights times u_j. Unit alpha_j makes the good amplitude admissible under whole-bin uniqueness, but does not evaluate those unknown F_T values. No field-only Geronimus inversion is taken at delta=0.

## 4. Explicit finite little-q-Jacobi continued fraction

Primary source inspected: Aldenhoven–Koelink–de los Rios, *Matrix-Valued Little q-Jacobi Polynomials*, arXiv:1308.2540v2, 5 September 2014, §2.2 equations (2.4)–(2.7), https://arxiv.org/html/1308.2540v2 ; published J. Approx. Theory 193 (2015), 164–183. It records the scalar polynomial, weight and three-term recurrence. Its real positive-weight setting is NOT imposed on our modular functional.

A finite algebraic specialization of the scalar weights uses a=rho^(h-1), b=rho^-h. Indeed

 (a*rho)^i*(b*rho;rho)_i/(rho;rho)_i=c_i,

and the sequence terminates at i=h. After cancellation of the removable n=0 parameter factors, the recurrence coefficients specialize to

 A_0=(1-rho^h)/(1-rho), C_0=0,
 A_n=rho^n*(1-rho^(h+n))/[(1+rho^n)*(1-rho^(2n+1))],
 C_n=-rho^(2n-1)*(1-rho^(h-n))/[(1-rho^(2n-1))*(1+rho^n)], n>=1. (6)

A_0 is exceptional: substituting n=0 into the simplified n>=1 expression would give an incorrect factor 1/2. At n=h, C_h=0 is the exact finite terminal condition. For 1<=n<h, A_n,C_n and beta_n=A_(n-1)*C_n are units. All denominators reduce to screened differences with exponents <=2h+1<16H; 1+rho^n is a unit because (1-rho^(2n))/(1-rho^n) is a quotient of certified units. Native h<=8K^(3/2)+9 and K>=54 give the displayed range uniformly.

Let b_n=A_n+C_n. The monic continuants satisfy

 P_0=1, P_1=z-b_0,
 P_(n+1)=(z-b_n)*P_n-beta_n*P_(n-1).

Their numerator companions have Q_0=0,Q_1=kappa and the same recurrence. At length h the exact finite Cauchy transform is

 Q_h(z)/P_h(z)=Lambda(1/(z-X))
             =kappa*z^(h-1)/prod_(i<h)(z-rho^i).      (7)

This follows directly from the finite Lambert partial fractions; the terminal polynomial is the normalized finite q-binomial polynomial. It is not a new norm representation counted as acquisition.

There is a genuine paid short-prefix algorithm: acquire the first s=O(J) coefficients (6), multiply the degree-one 2-by-2 transfer matrices by a balanced polynomial product tree, and evaluate the resulting fixed-size polynomial matrix at all (1+delta)/T_j by monic MPE/fixed jets. This costs soft J, with NO Hankel-pivot or row-separation hypothesis. One can acquire a suffix of O(J) coefficients adjacent to n=h just as cheaply from (6). The nonterminal transfer determinant factors beta_n, 1<=n<h, are certified units, so homogeneous projective coordinates avoid all future chart inversions. The terminal beta_h is ZERO, not a unit: initialize g_(h-1) by the homogeneous pair [1,z-b_(h-1)] and never invert the final zero-determinant map.

The exact missing connection is now explicit. If h>2s, the known prefix and suffix are separated by an initialized continued-fraction tail of length h-2s. The scalar tails obey

 g_n=1/(z-b_n-beta_(n+1)*g_(n+1)), g_h=0,
 Lambda(1/(z-X))=kappa*g_0.

Interpret this in homogeneous coordinates at poles. All coefficients and the actual finite terminal state are supplied implicitly, but acquiring the correlated tail condition at the J selected spectral points remains unperformed below the old query cost. A prefix transfer has unit determinant, so it cannot simply erase its unknown projective input. This does not say a selected-pole method must construct the full tail. If h<=2s, the whole transfer is already a degree-O(J) product and is paid in soft J, consistent with the old short-clock bound.

## 5. Outcome and precise scope

The polynomial q-Pearson attempt was executed and proved redundant, not merely rejected by an input-size analogy. The constant-numerator rational equation was also executed; its shifted poles and endpoint multipliers are retained. The little-q-Jacobi identification supplies explicit guarded coefficients, genuine short prefix/suffix starts and the exact finite terminal condition without emitting h coefficients.

What is still needed is a selected singular connection across that initialized finite tail, or an alternative rational Pearson saturation that acquires the same coefficient without deleting atoms. Whole-bin uniqueness makes either a constant-weight one-moment or a two-scalar unit-amplitude readout sufficient. None of the equations above acquires it in soft K. The retained complete query remains soft K^(5/4); these scoped failures do not preclude another q-Pearson, continued-fraction or nonlinear scalar algorithm.
