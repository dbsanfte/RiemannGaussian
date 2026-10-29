# Actual original-network prefix counter and search

Sole new source: `RiemannGaussian/SemiprimeCounterSearch.lean`. Existing source and frozen evidence were not edited.

## Exact policy preserving incidence

The implementation chooses the explicitly permitted **every local occurrence** policy. A fixed original bit is checked at every port whose original coordinate equals that bit. `prefixTable` has precisely the original dependent domain `Fin(arity e) → Bool`; it conjoins the original table acceptance with these equality checks. No new factor, unary tensor, variable, port, arity or scope is introduced. It therefore preserves the original degree/incidence layout certificates. It differs from the Python designated-owner policy only in redundant equality checks, which have exactly the same global acceptance semantics under coordinate coverage.

`prefix_accept_iff` proves all prefix-modified local tables accept iff the original global local-acceptance predicate and the original bit prefix both hold. It requires only every original searched variable has an existing port occurrence. No uniqueness of occurrence or factor-specific ownership assumption is needed.

`Problem` bundles actual Boolean tables, original port coordinates and coverage, replacement rows, positive Q, degree R, literal row restoration, and the SAME local node certificates used by `CounterCompose`. These certificates depend on rows and scopes, not on local table contents, so they are reused for all prefixes.

## No count-correctness oracle premise

`prefixCounter` is the actual finite rational `counterValue` expression applied to zero/one rational embeddings of the prefix-modified local tables. The precision J remains `(sum arities)*R/Q+1`.

`prefixCounter_eq_accepted` derives, using the composed counter theorem and local prefix semantics,

`prefixCounter(fixed) = (acceptedCount(restricted originalPredicate fixed) : ℚ)`.

No desired counter-value equality is a structure field or theorem premise. The natural `prefixCount` is explicitly `Nat.floor(prefixCounter fixed)`. Its equality to the true accepted count follows from the exact rational natural-number cast, including empty/contradictory prefixes. Nonnegativity/integrality are consequences, not rounding assumptions.

`counterSearch` directly calls the existing zero-first `CountRecovery.search` with `prefixCount`. Final theorems instantiate the old proof using the just-proved exact equality:

* `counterSearch_queries_le`: at most requested-list length+1 actual prefix counter calls.
* `counterSearch_none_iff`: none iff there is no original accepting assignment.
* `counterSearch_some_sound`: returned indices are exactly the requested indices, and all returned bits belong to a single original accepting assignment.

These statements do not require an arbitrary-predicate counting oracle. The original global predicate is fixed; only its original bit prefixes are changed through the existing local tables.

## Validation and boundary

Strict compilation PASS using absolute lake, `autoImplicit=false`, `warningAsError=true`. Repository `.olean` and identical isolated scratch output saved. Five explicit theorem axiom reports use only `propext, Classical.choice, Quot.sound`. Log `search-build.log`.

The counter is an explicit finite algebraic expression, still noncomputable as a Lean definition. This module supplies exact search correctness and call count, not a primitive execution/refinement theorem or a cheap count oracle. Local table prefix-check runtime is not silently free. Selecting all factor bits, linking accepted assignments to the actual Boolean multiplication graph, nontrivial factor guarantees, and proving total bit-time/space remain separate composition obligations. The incidence b=2 property is preserved by construction but is not asserted unless supplied by the actual graph.

Final root-import audit PASS: `CheckSearch.lean` imports existing root and this leaf, all 15 scoped linters report zero errors, and all 51 emitted declarations (25 theorem declarations) pass the project-axiom/transitive-axiom allowlist. Log `search-audit.log`. No broad build was launched.
