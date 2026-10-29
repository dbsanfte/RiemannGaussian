# Actual setup budget — completed

NEW `RiemannGaussian.SemiprimeFullSetupBudget` proves the literal `FullSetupCounter.count` setup ledger from its original inputs. Frozen prior modules were not edited.

## Interfaces

- `setupWork arity coordinate eps R B` duplicates exactly the actual enumeration/source/raw/Array.ofFn physical-design work plus `10*Q+20`, with no native work.
- `setupBudget n F M r Q R B D A` is an explicit fixed polynomial in the listed independent integer dimensions. It uses `P=M*D+M` candidate rows, head bound `n`, reader budget `2*(Q+r+P+n)+14`, and `bits=B+2+2*R*(Q+3)`. It never uses the measurement magnitude as a polynomial input dimension.
- `setup_work_bound` assumes `2≤r`, original owner multiplicity ≤B, `1≤Q` and original interval-start≤Q. It proves `setupWork ≤ setupBudget n F (sum arity) r Q R B (r^(2Q)) (r^Q)`. No terminal/label/rank/coefficient/output-cost advice appears.
- `nativeWork` is the ACTUAL materialized native count work using the ACTUAL physical designs and acquired source arrays. `count_work_eq_setup_add_native` gives exact additive separation, not equality to an old counter's work.

## Proof and finite costs

Acquired enumeration lengths are substituted by the existing exact incidence, universal-alphabet, score-menu and original-index cardinality theorems. The actual word tail is bounded by the complete word alphabet. The source coefficient subset expansion is charged through `rowBudget_polynomial`, using `2^(2Q)≤r^(2Q)` from `r≥2`. Source and raw interval starts are enlarged to Q in positive scalar polynomials. Both repeated source searches remain charged.

The physical builder's actual integer callbacks are its retained snapshot reader. Its original entry bound is transferred through the proved measurement bit envelope, and every callback report is bounded from the actual snapshot count. Candidate count is at most MD+M; each head size is at most n only inside a fixed polynomial setup budget. One full selector per head and all Q design reports are summed. No selected-rank or balanced-head claim is inferred for the exponential native algorithm. Whole Q-design-sum transport through the paid enumerator equality is explicit, avoiding hidden comparison of old/new work.

## Scope and verification

This closes the setup ledger in the frozen scalar/list/flat-cell/physical-rational-word model. It does not yet bound the native counter, source integer primitive bit execution, tape addressing, public graph/schedule acquisition, or the complete controller. Those require separate composition. Numeric polynomial bounds are attached to the actual executed setup report, not an independent free tally.

Strict compile PASS; ordinary-root fifteen-linter and all-generated standard-three-axiom audit PASS: 18 declarations, 12 theorem constants. Final isolated object is byte-identical to canonical. Pins: setup-verification.json.
