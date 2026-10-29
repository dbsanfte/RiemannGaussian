# Concrete Taylor filtration and Boolean diagonal frontend

New sole-owned module: `/home/dbsanfte/riemann/formal/RiemannGaussian/SemiprimeCounterFiltration.lean`. Existing evaluator, diagonal, frozen packets, and external build were not edited by this task.

`Filtered p` means `totalDegree(coeff_j p)<=j` for every j, with p a polynomial in z having multivariate rational polynomial coefficients. This is exactly paper equation (3.9).

Proved closure theorems `filtered_scalar`, `filtered_add`, `filtered_sub`, `filtered_mul`, `filtered_sum`, `filtered_prod`. Multiplication is proved from the actual coefficient convolution and total-degree subadditivity. It is not assumed as a property of a supplied operation.

`linearForm row = sum_v C(row_v)*X_v` has total degree at most one. The actual input port is

`inputPort base D rows = C(C(base)) + sum_(d<D) monomial(d+1, linearForm(rows_d))`.

Its constant scalar is independent of X and every correction has positive z degree. `filtered_inputPort` proves its filtration for arbitrary rational coefficients, without a supplied degree assumption. This represents all finite correction polynomials (the index d corresponds to original positive degree d+1).

`filtered_evaluate` proves the ORIGINAL `SemiprimeStreamingTensor.evaluate` preserves the filtration when supplied these ports and constant-polynomial tensor table entries. The proof follows the exact two Boolean branches, including `1-port` and both recursive tensor restrictions. It applies to arbitrary rational table entries, so Boolean 0/1 tensors are included.

`correctedProduct` is the actual product of these streamed multilinear tensor evaluations over the finite factor family, with arbitrary dependent arities. `filtered_correctedProduct` proves paper (3.9) for this concrete polynomial.

**`correctedProduct_taylor_diagonal`** applies the previously proved full Boolean Möbius identity to this concrete family, with scalar base allowed to depend arbitrarily on assignment x and correction rows fixed. For every j<J it obtains exactly the paper's common menu `|E|<=J-1`, all U subsets of E, sign `(-1)^(|E|-|U|)`, and forced assignments E subset x. There is NO filtration premise in this final frontend theorem. The degree premise was discharged from the concrete construction.

Strict build PASS using absolute `/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true`. Output written both to repository `.lake/build/lib/lean/RiemannGaussian/SemiprimeCounterFiltration.olean` and identical scratch copy. Four printed axiom reports contain only `propext, Classical.choice, Quot.sound`. No custom axiom, sorry, native decision tactic, or backend counter hypothesis.

This closes the polynomial filtration and finite Boolean-diagonal correctness step. It does not assert the source-row compiler, construction of separating layouts, group/fibre enumeration, Hermite recovery machine, or primitive-machine resource theorem. Assignments are represented by their one-coordinate subsets, matching the existing diagonal theorem and implementation's forced-coordinate semantics. The ambient S can be univ for the paper's complete Boolean cube.

Root-import scoped audit also PASS: `filtration-root-audit.lean` imports existing `RiemannGaussian` and the new module, runs silent `#lint- in RiemannGaussian.SemiprimeCounterFiltration`, and audits the final two theorem axioms. Strict exit status 0; logs `filtration-build.log` and `filtration-root-audit.log`. No broad build was launched.
