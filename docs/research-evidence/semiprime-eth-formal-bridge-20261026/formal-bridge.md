# Generic Lean bridge for bounded-incidence Boolean tensor networks

Source audited: pinned `openai-math` commit `7ef5c0c`, source directory `/tmp/semiprime-d1-audit-20261026/openai-math/lean`. This is a SOURCE-interface audit, not a claim that the complete closure or the new extension has compiled. Root is independently strictly compiling the existing closure. `docs/378.md` explicitly claims the older fixed-k CNF rate `2^{O(n(log log n)^2/sqrt(log n))}`, not Appendix D.1.

## Positive reusable interfaces

All paths below are relative to the source directory, under `OAI/Algorithms/SubexponentialSAT/`.

* `Factor.lean:20–39`: `Pattern`, `Pattern.Bounded`, and `System` already describe arbitrary finite scopes and arbitrary Boolean-valued local tables. Maximum arity and variable incidence are separate numeric parameters. The semantic objects do not require constant arity.
* `TableInterpolation.lean` (`eval_mvInterpolate`, `degreeOf_mvInterpolate_le`) and `GlobalPolynomial.lean:359–405` (`interpolatedTable`, `eval_interpolatedTable`, `eval_zero_interpolatedGlobalPolynomial`) supply the genuine multilinear extension and exact sum-product counting identity over a commutative ring. For Boolean input the interpolation denominator is 1.
* `GlobalPolynomial.lean:30` gives `natDegree_compose_le` over **CommSemiring**, and `:101` proves the product degree bound by summing these bounds. Its final published bound replaces every scope size by maximum arity; that replacement is unnecessary. The exact total-incidence strengthening is provided separately in scratch `TotalIncidence.lean`.
* `Separation.lean:337–416` (`coset_weighted_separation`, `coset_row_group_separation`, `coset_full_weighted_separation`) are generic finite sum/product identities, not SAT-specific endpoint statements.
* `SqrtLog/LayoutExactBuckets.lean:96–112` (`integer_kernel_of_rational_span`, `killsIntegerKernel_of_rational_span`) supplies the rational-span to exact integer-summary-fibre implication. `LayoutRowSelection.lean` supplies actual-row basis selection, retaining integer coefficient bounds rather than silently rescaling a rational basis.
* `SubexpKernelCorrectness.lean:163,198`: `canonical_rawMomentValue_eq_separatedMoment` and `executeJet_buildBlocks_eq_separatedJet` accept generic local denotations, fibre enumerations, invariant group values and factored weights. They establish an actual executed finite-kernel equality once those inputs are supplied.
* `SqrtLog/LeafParametersProgram.lean:10–19,40–56,98–105` already separates `occurrence`, `arity`, and `incidences`. The tail cutoff `R` depends on occurrence, not arity. The exact guard contains `4*(occurrence+arity)*N^2*epsilonDen^2 <= incidences`, with `N=r^(2Q)`. `SqrtLog/LayoutProducedHeadsQuery.lean:29` proves the selected-head bound from precisely that guard. Thus the layout interface does not itself force arity to be constant.

These are substantive generic interfaces; a final theorem restricted to fixed-k CNF alone would not establish the proposed extension.

## Concrete extension and its degree budget

For a Boolean tensor network with n edge variables and two endpoint incidences per edge, take a factor for each vertex. Then b=2, total incidence `sum_e |scope_e|=2n`, and maximum scope w=O(n^(3/4)). The local polynomial is

`f_e(X) = sum_{a in {0,1}^{scope_e}} T_e(a) product_i (if a_i=1 then X_i else 1-X_i)`.

Each variable has degree at most 1, and the total table degree is at most the scope size. For paths of degree at most R the *actual* global counting polynomial therefore has degree at most `2nR`, rather than `(#vertices)*w*R`. This uses no tensor rank assumption and holds in the prime-power coefficient ring.

For the proposed beta=1 schedule, if the existing asymptotics provide `N^2 <= n^(1/64)` and `epsilonDen=polylog(n)`, then the finite guard's left side is `O(n^(49/64) polylog(n))=o(n)`. This paragraph is an asymptotic instantiation obligation, not a claim that the current SAT endpoint already proves it. The selected-summary tail uses b=2, so it does not incur w in its exponent.

A tensor entry oracle running in polynomial time on its local Boolean assignment permits multilinear evaluation by streaming all `2^w` assignments. Maintain one assignment, local product and accumulator; no truth-table list is required. Fixed precision jets admit the same streaming construction. The extra time `2^{O(w)} poly(n)` is absorbed by `2^{O(n(log log n)^2/sqrt(log n))}`. Space is polynomial provided coefficient representations, common-denominator bounds and local entry workspace are explicitly controlled. In particular, merely naming a multilinear polynomial is not yet this evaluator.

## Precisely missing formal obligations

1. **Total-incidence degree theorem.** Scratch `TotalIncidence.lean` proves the proposed statement directly using the existing compose bound and `natDegree_prod_le`, then `Finset.sum_mul`. It imports the pinned module and ends with `#print axioms`. At writing, `GlobalPolynomial.olean` was not yet present in the independent strict build; this new file is therefore not claimed compiled. No source checkout was changed.
2. **Use the sharper budget throughout the counting/reconstruction frontend.** The existing `natDegree_interpolatedGlobalPolynomial_le`, old `LayoutSpec.Constants.degree_budget`, and the existing Taylor-precision parameter formula use maximum-arity/factor-count estimates. Supplying a large arity to their existing SAT wrapper is not enough. The new frontend must use `sum scopes=2n` when selecting interpolation precision and Taylor order.
3. **High-arity streaming implementation.** `SubexpSourceFactors.lean` proves semantic evaluation for actual prepared source rows, but the existing factor representation includes materialized row/cache lists. A network compiler must instead supply and verify a streaming local-extension evaluator with the stated bit/space bounds, or formally refine the list execution to a streaming implementation. Generic semantic finite sums alone do not prove polynomial-space evaluation.
4. **Instantiate the finite layout guard and costs.** Prove its eventual validity for b=2, w<=C n^(3/4), total incidence 2n, with constants and finite fallback. Reuse `query_max_bound_rat`, rather than postulating a summary bound. Check representation heights and coefficient precision for the new evaluator and all shared-summary calls.
5. **Export a generic network machine theorem.** Compose the generic kernel equality, streamed evaluator, refined degree budget, reconstruction and machine-resource accounting. Then compose the separately audited O(L)-wire macro-FFT network. Neither D.1 nor its disputed precision claims are needed for this route, but these frontend/resource lemmas are real new work.

If these obligations are discharged, the resulting conditional-on-this-extension factoring implication is `2^{O(L(log log L)^2/sqrt(log L))}` time and polynomial space, since network edge count is O(L) and local scope O(L^(3/4)). This is asymptotically below N^(1/6), but **is not yet a formalized factoring theorem or an implemented algorithm**. The present positive contribution is identifying an already generic core and isolating a concrete small degree lemma, rather than treating the SAT endpoint as a black-box high-arity tensor theorem.

## Implemented streaming algebra bridge

`StreamingTensor.lean` now strictly compiles against Mathlib (Lean 4.34.1, `autoImplicit=false`, `warningAsError=true`). It proves finite tensor-product interpolation and exact Boolean recovery. The same-branch instrumented definition `evaluateTracked` has a proved full triple `(evaluate w T x,2^w,w)`, attaching table-leaf count and recursion depth directly to execution recursion. No custom axioms or sorry are used. This discharges a concrete algebra/recursion sub-obligation in item 3; a compiler, oracle runtime, coefficient bit bounds and machine-space accounting remain unproved by this file. See `streaming-tensor-build.md` for replay and axiom output.
