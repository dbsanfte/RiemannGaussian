# Composed counter and remaining executable boundary

The root-owned modules are `SemiprimeCounterSeparation` and
`SemiprimeCounterCompose`. The all-input finite identity is now compiled as
`RiemannGaussian.SemiprimeCounterCompose.counterValue_eq_original`.

This is a composition of the actual formula, not a theorem with the counter's
correctness as a hypothesis. It accepts original finite coordinates, original
factor arities and rational Boolean-entry tables, polynomial replacement rows,
literal restoration at zero, row-degree bounds, and certificates only at the
positive sample nodes 1,...,Q. Precision is exactly
`J = floor((sum arities)*R/Q)+1`.

## Local design interface

`NodeCertificate` contains an actual coordinate-partition equivalence, assigned
factor groups, measurement rows and finite summary values, exact measurement
readouts, off-group row-span witnesses, and representatives valid on nonempty
fibres. It contains no aggregate count, packet equality, assumed separation
identity, or promised original contraction.

The representative need not satisfy forced coordinates. It is consulted only
when the corresponding fibre is nonempty; each local summation assignment
satisfies the forced-coordinate constraints. Empty fibres contribute zero.

These certificates are an exact-algebra interface. They do not bound summary
dimension, measurement range, representation sizes, or acquisition time. The
actual layout constructor must still be proved to produce them with the
quantitative bounds needed by the algorithm. Existence of a large arbitrary
certificate would not establish the scaling goal.

## Composition actually checked

1. `splitAssignment` is a bijection between original subsets of one bits and
   grouped Boolean assignments. `forced_splitAssignment` identifies the exact
   original forced-set predicate under this bijection.
2. `rowValue_eq_of_measurements` and `basePort_invariant` derive equality of
   native scalar bases from finite row-span witnesses. Consequently the actual
   streamed tensor products satisfy the shared-summary invariance.
3. `fibrePacket_eq` applies that derived invariance to the explicit measurement
   and fibre sums; no invariance premise remains in this theorem.
4. `fibrePacket_native` identifies its fixed-U correction with the positive
   coefficients of the shifted native polynomial rows.
5. `rawPacket_coeff` composes the native Taylor/Möbius theorem with separation.
   It uses the common menu |S|<=J-1, U subset S, sign (-1)^(|S|-|U|), and forces S.
6. `nodePacket_eq` proves equality of retained packets modulo X^J.
7. `counterValue_eq_original` applies the constructed Hermite quotient and
   cardinal factors to these packets, proves degree<QJ from the original total
   incidence, and restores the original contraction at zero.

`SemiprimeCounterSearch` then supplies the counting premise formerly required
by the generic recovery module. Its prefix policy checks every existing
occurrence of a fixed bit, preserving all scopes, arities and variable counts.
Coordinate coverage proves equivalence to restricting the original witness.
The actual rational counter equals the natural accepted count; natural floor
therefore recovers that count exactly. Its search soundness/emptiness/call-count
theorems no longer require a supplied count-correctness oracle.

## Why this still is not the full factoring theorem

These expressions and certificates are finite mathematical objects. Most are
marked `noncomputable` because their Lean presentation uses general finite types
and classical equality. The Python implementation has explicit scans and exact
rational arrays; those executions have not yet all been related to this
presentation, with costs on the same executions.

`SemiprimeJetRecurrence` now supplies the algebra of retained addition,
convolution, and the actual inverse coefficient recurrence, including the
previous denominator-first-truncation gap. The recursive definition can
recompute smaller inverse coefficients; its algebraic correctness is not a
proof of the cached Python loop's quadratic operation count.

The newly proved tail guard gives eventual acceptance of the mathematical
parameter tests for occurrence two and arity O(n^(3/4)). It does not by itself
certify the constructed layout, the graph's actual sizes, or any machine's time.

For the factoring endpoint, the direct finite bit relation counts nontrivial
bounded integer factor pairs. Macro-stage unique-extension and signal-size
results must be integrated into the actual complete graph, including consumer
wiring, canonical ports, OR flags, target digits and padding. A signal-family
cardinality alone does not prove that this graph has those incidences.

The remaining complete bridge is therefore: actual layout constructor and
finite measurement scans; exact full macro bit graph and binary-size bounds;
array/enumeration execution refinement; then primitive bit-time, all-prefix
space, and the analytic rate substitution for the same factoring execution.
The native long-query soft-K^(5/4) result is unchanged; this is the alternative
shared-summary factoring route.

## Root review of the exact tail

The root read the entire finite MGF/concentration/schedule calculation and the
frozen `shared_parameters.py`. The finite mean uses Q trials, probability
(r-1)/(2r), and the literal centered interval. Natural subtraction is justified
by the proved nonnegative interval numerator. The loose deviation R/4 and
Chernoff constant 32 imply exponent at least64*nu under the actual schedule.
The budget then yields exactly numerator*(2*r^2*lambda)<=(2*r)^Q, matching
tau_denominator=r*lambda and occurrence=2. No missing sign, Q-1 substitution or
probability approximation was found. The streamed binomial-term recurrence's
execution refinement remains distinct from this closed-form integer theorem.

The independent composition review is in `compose-separation-review.md`.
Root strict compilation, scoped ordinary-root lint and all-generated-declaration
standard-axiom audits are recorded in the combined audit artifacts. No finite
factor examples were used to infer coverage or asymptotic complexity.
