# Boolean Möbius diagonal: formalized general identity

Authorized sole new module: `/home/dbsanfte/riemann/formal/RiemannGaussian/SemiprimeBooleanDiagonal.lean`. Existing evaluator modules, frozen evidence, external checkout and closure build were not edited.

The target is paper Lemma 3.3, printed page 24, equation (3.10), with its coefficientwise application (3.13) on printed page 25; local paper text lines 1343 onward. Frozen `semiprime-shared-counter-20261026/shared_counter.py` lines 310 onward enumerate exactly the same `E,U` pairs and force the coordinates in E to one.

## Verified declarations

* `mobius`: actual finite coefficient `sum_(U subset E) (-1)^(|E|-|U|) f(U)`.
* `mobius_insert`: exact finite-difference recursion with original signs.
* `sum_mobius`: full Boolean inversion for an ARBITRARY table f, proved by induction on the ambient finite set.
* `mobius_eq_zero_of_independent`: one unused variable kills a coefficient.
* `mobius_monomial_eq_zero`: Möbius coefficient of a monomial vanishes unless E lies in its exponent support.
* `mobius_eval_eq_zero_of_totalDegree_lt`: genuine polynomial total degree implies coefficient zero when |E| exceeds it. Proof expands the actual polynomial into its supported monomials, uses support-cardinality <= sum of positive exponents <= total degree, and unused-variable cancellation. This does not assume multilinearity or a supplied diagonal identity.
* `eval_indicator_eq_sum_mobius` and `eval_indicator_eq_sum_ambient`: pointwise Boolean reconstruction with real degree cutoff and forced-coordinate indicator.
* **`boolean_diagonal`**: complete Lemma 3.3 for arbitrary row-dependent polynomials `p_x` over any commutative ring, any finite ambient S, and actual hypothesis `(p_x).totalDegree <= q`. The equality is

  `sum_x eval(1_x,p_x) = sum_(E subset S, |E|<=q) sum_(U subset E) (-1)^(|E|-|U|) sum_(x subset S, E subset x) eval(1_U,p_x)`.

Boolean assignments are represented by their subsets of one coordinates, so `E subset x` is exactly the paper's `x_i=1 for i in E`. Variables outside S are set to zero on both sides. Taking S to be the full finite index set is the paper's original formulation. This representation does not impose any relation between different p_x.

* **`retained_taylor_diagonal`**: given a polynomial family `G_x(z)` with coefficients in multivariate polynomials, and degree filtration `deg_X coeff_j G_x <= j`, every j<J uses the SAME retained pairs `|E|<=J-1`. The scalar coefficient identity has the exact signs and restrictions above.

## Compilation and remaining integration

Strict module compilation PASS with absolute `/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true`. Outputs: repository `.lake/build/lib/lean/RiemannGaussian/SemiprimeBooleanDiagonal.olean` and identical isolated scratch copy. `diagonal-build.log` records the six explicit axiom reports; each contains only `propext, Classical.choice, Quot.sound`. No sorry, new axioms, or native decision procedure.

The entire general diagonal lemma is now proved. The retained-Taylor theorem assumes ONLY the filtration (paper equation (3.9)); proving that filtration for the counter's concrete product of affine corrections, and proving its coefficient-extraction operations match the implementation, are still next integration obligations. This module does not assume the diagonal conclusion, does not replace it with examples, and does not assert a machine time/space or factoring theorem.

Root-import scoped lint also PASS: `diagonal-root-audit.lean` imports existing `RiemannGaussian` and the new module, runs silent `#lint- in RiemannGaussian.SemiprimeBooleanDiagonal`, and audits both final theorem axioms. Strict exit status 0; log `diagonal-root-audit.log`. No broad rebuild was launched.
