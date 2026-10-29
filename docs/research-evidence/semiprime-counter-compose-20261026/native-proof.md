# Native replacement-row counting bridge

Sole new source: `RiemannGaussian/SemiprimeCounterNative.lean`. No existing source, frozen evidence or external build was changed.

## Constructed objects and zero recovery

Replacement data are actual scalar polynomials `rows[e,i,v] : Polynomial ℚ`, a finite variable type V, finite tensor vertices E with dependent arities, and local Boolean tensor tables `T_e` valued in ℚ.

`rowPort rows x = sum_v rows[v] * C(indicator_x(v))`.
`rowProduct` is the product of the actual recursive streamed multilinear tensor evaluations at these ports. `globalPolynomial` is its finite sum over ALL one-coordinate subsets x of V. `globalPolynomial_eq_powerset` identifies this with the diagonal theorem's exact ambient `univ.powerset` sum, with no assignment multiplicity change.

`globalPolynomial_at_zero` proves `H(0)=originalContraction` under literal Kronecker row restoration at zero: `rows[e,i,v](0)=1` when v is the supplied original port coordinate and zero otherwise. It uses actual Boolean recovery of the streaming evaluator. No original-contraction-value hypothesis is supplied.

`globalPolynomial_degree` proves `natDegree H <= (sum_e arity_e)*R` from degree bounds on the replacement rows. It uses the already proved direct total-incidence bound, without maximum-arity times vertex-count inflation.

## Actual Taylor corrections and specialization

`evaluate_map` is public naturality of the recursive evaluator for arbitrary commutative-ring homomorphisms.

`inputPort_map` explicitly gives each corrected port after any fixed independent Boolean substitution U. `correctedProduct_map` gives the exact product of mapped streaming tensor evaluations. `correctedProduct_coeff_eval` exposes its coefficient handoff. These are the interfaces for grouping factors by shared measurements; no measurement-separation premise or precomputed group value is used in this module.

`shiftedBase` is the actual rational base `sum_v rows[e,i,v](t)*indicator_x(v)`.
`shiftedRows[e,i,d,v]` is the actual coefficient `[z^(d+1)] rows[e,i,v](t+z)`.

`taylor_row_expansion` proves the exact finite row expansion, given degree<=R. `shifted_inputPort` proves that evaluating the concrete corrected port at X=x yields the entire shifted original row port, not merely matching low coefficients.

`correctedProduct_shift` proves the exact polynomial equality

`map_(eval_X=x) correctedProduct(base_x, shiftedRows) = taylor_t rowProduct(x)`.

`globalPolynomial_taylor_coeff` then gives the literal sum-of-corrected-coefficients identity required by the counter. Its only row premise is the actual degree bound; the correction identity itself is proved.

Finally **`native_taylor_diagonal`** composes this bridge with the actual corrected-product filtration and Boolean Möbius theorem. For every j<J it proves

`[z^j] H(t+z) = sum_(A subset V, |A|<=J-1) sum_(U subset A) (-1)^(|A|-|U|) sum_(x superset A) eval_X=U ([z^j] actualCorrectedProduct_x)`.

Thus root can now replace the remaining fixed-U sums by its native grouped measurement contraction and then supply Hermite packets. No Taylor-identity or filtration premise is supplied to this final theorem.

## Validation and scope

Strict absolute-lake module compilation PASS (`autoImplicit=false`, `warningAsError=true`), repository `.olean` and identical isolated scratch output. Seven requested axiom reports contain only standard axioms. Module log: `native-build.log`.

The module is algebraic frontend correctness. It does not construct the replacement row design, measurement spans or finite measurement ranges; does not prove exact rational array execution; and does not assert primitive-machine time/space or an end-to-end factoring runtime. Those interfaces remain genuine composition work, while H(0), degree, actual corrected Taylor substitution and Möbius packet identity are now proved from concrete row data.

Final root-import gate PASS: `CheckNative.lean` imports existing `RiemannGaussian` plus this new leaf module, runs all 15 namespace linters (zero errors), and audits EVERY declaration emitted by the module, rejecting project axioms or any transitive axiom beyond `propext, Classical.choice, Quot.sound`. It checked 33 declarations, including 27 theorem declarations and generated artifacts. Log `native-audit.log`. No broad project build was launched.
