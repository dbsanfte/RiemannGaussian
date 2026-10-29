# Independent scope and semantic review of counter algebra

26 October 2026. **PASS for the stated finite algebraic theorems and their mathematical correspondence to the current counter.** Reviewed final stable `SemiprimeBooleanDiagonal.lean`, `SemiprimeCounterFiltration.lean`, and `SemiprimeHermiteRecovery.lean` against frozen `semiprime-shared-counter-20261026/shared_counter.py` and paper Section 3.4, Lemma 3.3 / Proposition 3.4. No owned source was edited. This review does not assert a compiled end-to-end execution or running-time theorem.

## BooleanDiagonal

`mobius` has the implementation's exact coefficient `(-1)^(|E|-|U|)`. All uses of natural subtraction in the sign have U subset E, so the exponent is the intended integer cardinality difference. `sum_mobius` proves full Boolean inversion before introducing a degree condition. The polynomial cutoff is then proved from support: a monomial cannot depend on a variable outside its support, and support cardinality is bounded by total degree. There is no assumption of a supplied diagonal identity or of multilinear inputs; arbitrary powers are allowed and Boolean evaluation handles them correctly.

`boolean_diagonal` permits a genuinely different polynomial p_x for every original assignment x. This is important: the scalar base of the counter's corrected polynomial depends on x. The outer ambient set S and x subset S accurately represent original Boolean assignments as their sets of one bits. Its right side forces x_i=1 for every i in E, precisely matching `forced=E` in `separated_fibre_sum`; it does not force x to equal U.

`retained_taylor_diagonal` uses the **same** menu |E|<=J-1 for every coefficient j<J. This is valid because its coefficient degree bound is <=j<=J-1. The code sets J=q+1 and loops |E|<=min(q,n), so the formal common menu and the implementation menu agree. No j-specific menus or missing highest coefficient are present. J=0 has no retained j and is not illicitly used; production J is positive.

## CounterFiltration

The low-degree coefficient condition is proved for concrete ports, not reintroduced as an unproved frontend premise. `inputPort` has an independent rational scalar constant plus a finite sum of z^(d+1) times **linear** polynomials in the independent Boolean indeterminates. Its positive-degree indexing is essential and matches `delta[0]=0` in the code. The row coefficients may be arbitrary rationals and may have either sign; zero rows and absent high coefficients are allowed.

Closure under sums and products proves that the coefficient of z^j has X-totalDegree<=j. `filtered_evaluate` applies this to the actual recursive multilinear tensor evaluator, including both `(1-port)*left` and `port*right`. The already established evaluator sum formula identifies this recursive value with the Boolean-assignment/product stream used by Python; the module does not run the Boolean predicate directly on non-Boolean inputs.

`correctedProduct_taylor_diagonal` therefore supplies the needed hG internally from `filtered_correctedProduct`. Its `base x` may depend arbitrarily on the original assignment x, while the positive-z row coefficients are independent of x. This is exactly paper (3.7)–(3.9): base=P(t) dot x and corrections=(P(t+z)-P(t)) dot X. The unrestricted finite D here is the number of positive z coefficient slots, not the shared-layout measurement bound D; those are distinct parameters despite the reused letter. Actual finite row degrees can be instantiated by padding missing coefficient slots with zero.

The code evaluates and sums in the truncated z-jet ring after substituting X=1_U. The formal module proves the corresponding polynomial coefficient identities before truncation. For j<J this is the same mathematical operation. It does not yet identify the Python arrays or an executable jet machine with these formal polynomial objects; that remains an execution-refinement obligation, explicitly outside the claims.

## HermiteRecovery

Distinct field-valued nodes and J coefficients at each node yield divisibility by the product of `(X-t)^J`, including multiplicity. The degree requirement is **strictly** `<QJ`. `counter_precision_sufficient` proves dR<Q*(floor(dR/Q)+1) for Q>0, exactly the code's precision. The module's rational sample points are 1,...,Q, with proved cardinal Q, so there is no finite-characteristic collision or implicit inversion of an unknown modular nonunit.

The explicit normalized cardinal factor is

`L_t(T)=prod_(s!=t) ((T-s)/(t-s))^J`.

It has L_t(t)=1. The code's local packet is the truncation of `L_t(t+z)=prod_(s!=t)(1+z/(t-s))^J`; its factor coefficients are `comb(J,k)/(t-s)^k`, exactly as in the loop. Omitting k>=J is correct modulo z^J. The outside scalar is `L_t(0)=prod_(s!=t)(-s/(t-s))^J`, again matching `at_zero` with the correct signs and powers.

`inverseJet L J=sum_(i<J)(1-L)^i` is a constructed finite inverse modulo z^J when L(0)=1, not an assumed oracle. The code instead computes its coefficients by the usual unit-series recurrence. Both give the same inverse jet: multiplying by L gives 1 modulo z^J, and its nonzero constant coefficient makes this jet inverse unique. `localQuotient` truncates H times this constructed inverse, and its local congruence and degree<J are proved.

`hermiteTerm` multiplies L_t(T) by the local quotient translated with **taylor(-t)**, i.e. z=T-t. At T=0 the quotient is therefore evaluated at **-t**, matching `sum(coefficient*(-t)^j)` in the loop. `explicit_hermite_at_zero` proves exactly the scalar sum with these local inverses and normalizers. The proof constructs matching local packets and proves the global degree bound; it does not assume the desired recovery equality as an interface.

The numerator packet may be truncated before forming the quotient (`localQuotient_truncate`). One precise remaining execution bridge is that the code inverts the **truncated denominator packet** by a recurrence, while the formal definition uses the full known cardinal factor in a finite geometric sum before reducing modulo X^J. Their equality follows from the same unit-jet uniqueness and dependence only on coefficients <J; the current module does not separately export this denominator-truncation / recurrence-correspondence theorem. This is a missing explicit array-refinement lemma, not a wrong scalar formula or a new unproved mathematical interpolation assumption.

## Boundary and disposition

These modules prove concrete finite algebra needed by the algorithm: the signed forced-coordinate identity, the actual positive-z filtration, and constructed exact Hermite recovery. They do not formalize the layout-to-counter separation connection, all array/loop implementations, all integer bit heights, measurement enumeration, primitive-machine execution, or factor-prefix recovery. No conclusion here removes the still-open exact binomial-tail schedule acceptance or full runtime theorem. The already reviewed ordinary-bit resource argument and exact tests are evidence at their stated levels, not substitutes for those formal interfaces.

No substantive sign, normalization, cutoff, hidden-filtration, or field-guard error was found. Final source SHA-256 values for exactly the three reviewed modules are in `algebra-counter-source-hashes.json`; these identify reviewed source bytes and are not themselves proof certificates.
