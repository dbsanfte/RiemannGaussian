# Computed original-row selection and exact span tests

Owned NEW sources: `RiemannGaussian/SemiprimeRowSelectionExecution.lean` and `RiemannGaussian/SemiprimeRowSelectionTracked.lean`. No frozen module was edited.

## Executed algorithm and full certificate

The selector has an explicit first-nonzero scan of rational residual coordinates. Accepted rows are normalized and back-eliminated; finite residual/matrix arrays are materialized via Vector.ofFn. It processes a supplied finite original-index list from its tail and records only original indices. The output measurement rows themselves remain the ORIGINAL integer rows, never rational scratch rows.

The source proves the Kronecker active-pivot invariant, exact computed span update, zero-residual rejection law, full input span, selected-original span equality, selected-index injection, selected cardinal=true rowRank, and selected original-row linear independence. Empty/zero matrices and rank-deficient inputs are included. No desired span/rank certificate or noncomputable membership test is supplied to the program.

The public adapter is:

`selectedRows (C : Fin m -> Fin n -> Z) : LayoutSelection.SelectedRows C`

and, for actual head-column orders,

`selectedRowsWithColumns (C : Fin m -> V -> Z) (columns : Fin n ≃ V) : SelectedRows C`.

The latter takes only the actual explicit column order and proves its rank transport. Rows of the source layout are already Fin(rowCount). The separate constructive `MixedRadix.filtered` helper provides the actual head-column enumeration from the supplied original variable enumeration; ExecutedNodeDesign uses this API rather than the old choice-based selectedRows. The proof does not claim the chosen list equals the old Classical.choice list—any computed original-row basis with the proved certificate suffices.

The additional `inSpan` computes exact rational span membership by a residual/pivot scan. `inSpan_correct` is proved from the executed residual linear map and its kernel on the actual RREF basis. In particular actual rational replacement rows can be tested without a membership oracle.

## Actual arithmetic and test counts

The tracked companion executes every rational add/subtract/multiply/divide through ScalarRun constructors, builds actual cached finite rows/matrices, and tracks the real finite zero scan. `runTracked_value` proves the returned complete state is exactly the proved selector state. It pays BOTH residual computations of the pure insertion (one for pivot detection and one for normalization), not an assumed CSE optimization.

For an input index list of length m, the formal bounds are at most `8*m*(n+1)^2` rational arithmetic calls and `m*n` rational pivot-zero tests. These are actual data-path counts, not an independent timeout annotation. Boolean active-column tests, flat index/array reads, integer-to-rational input conversion, allocation and bit costs are separate control/representation work. The generic matrix function must be supplied as the actual explicit input table, not an arbitrarily expensive callback hidden behind a unit-cost oracle.

`row-height-cost.md` supplies the rigorous current-RREF minor/partial-scratch argument and a constructive polynomial bit/space consequence using the existing canonical rational backend. The minor/flat-machine bound remains PAPER-LEVEL, not a formal primitive-bit theorem inferred from rational-operation counts. In particular retained functional active histories are allowed to keep polynomially many older states; no free constant-time lookup or garbage-collection assumption is used.

## Controls

Six focused implementation outputs are captured in row-controls.lean/log: a dependent 3x3 matrix selects original IDs [0,2]; the all-zero matrix selects none; the tracked run executes 81 rational arithmetic operations and 6 pivot tests; an actual span vector accepts; an independent vector rejects. These are local controls, not a factoring or performance campaign. The all-input correctness proofs carry the actual mathematical claim.

## Scope

This closes the computed original-row selection/span/rank interface and its exact arithmetic-call ledger. Native executed-node binding is a separate coordinated adapter. It does not implement the different binomial-system exact_solve routine, prove the complete layout constructor machine cost, or complete the whole counter's primitive runtime theorem.

## Final gates

Both individual strict builds PASS with autoImplicit=false/warningAsError=true. Root import plus all 15 scoped linters PASS for both modules. All generated/transitive-axiom audit PASS: 308 declarations, 152 theorems, only standard propext/Classical.choice/Quot.sound. Source/log/checker/report hashes are recorded in row-hashes.json.
