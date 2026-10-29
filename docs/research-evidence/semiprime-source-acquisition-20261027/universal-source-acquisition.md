# Acquired universal source coefficient arrays

Six new modules construct the universal integer entries, finite mismatch interpolation, and actual coefficient arrays. The runtime supplier has no `Polynomial` index or requested-coefficient oracle. It computes its parity data using the new integer solver. The connection to the original source `Layout.Data` is proved, including its proof-only finite constraint reindexing. Original coefficient-array block/owner pullback, caching and the whole-source controller are separate root work; the concrete original-constraint join is included below.

## Exact interfaces

`SemiprimeUniversalNumeratorExecution.entry c i t a y : Z` executes the source sum over j<R and j-element active subsets, using literal register swaps/differences. `integerDifference_perm` proves that swapping the order of commuting differences changes no value. Consequently a computable `Finset.sort` list can replace the semantic `Finset.toList`; the latter is not used by the runtime entry. `entry_eq` proves equality to `LayoutNumerator.entry` whenever c is the computed parity vector. `extended` and `extended_eq` implement and identify both zero-extension membership branches.

`SemiprimeSourceCodeArrays.compile J p : InverseReport` interprets the source's finite rational `PolynomialCode` syntax tree into width-J arrays. This is a finite arithmetic AST, not mathlib's noncomputable polynomial representation. Both child arrays are bound once before addition/multiplication. `compile_coefficient` proves every low coefficient; `compile_size` proves the actual width. Formal ledgers are:

* arithmetic <= nodes(p) * (J*(J+1)+J);
* coefficient reads <= nodes(p) * (J*(J+1)+2*J).

These do not charge construction of rational constants, the syntax tree, indices, or physical rational bits.

`SemiprimeSourceInterpolationExecution` constructs positive rational nodes i+1, node/difference units, and the power-of-two denominator explicitly. `prescription c a i y t` uses the computed zero-extended integer numerator with the exact negative inverse-denominator sign. `code` builds the source's finite mismatchRowCode and `row c a i y` compiles it at width R+1. The proofs `prescription_eq`, `code_denote`, `row_coefficient` identify the actual source formula, including empty constraints and the unchanged initial selector. `universal_coefficient` identifies LayoutUniversal.data's single-slot rows. No noncomputable section or supplied polynomial is used in these runtime definitions.

`SemiprimeUniversalSourceExecution.universalRow A R a y : InverseReport` computes c=`BinomialExecution.parity A R` internally and acquires the actual arrays. `universalRow_coefficient` identifies the source for arbitrary interval A; `source_universal_coefficient` specializes to the exact centered `SourceLayout.universalLayout`. Both node units and denominator match the source's units. Its integer `numerator` likewise computes c internally. The padded full-universal `constraint A R t g a y` returns d*delta(a,y)-N(a,y) inside the joint fibre and zero otherwise. `constraint_eq` identifies the exact zero-extended cleared defect; `constraint_source` identifies the actual source's joint-row/head-column matrix. `constraint_not_head` and `constraint_not_joint_row` prove the literal zero cases.

The generic entry/row(c) functions permit the root controller to bind a single computed parity closure outside its matrix loops. The convenience universalRow wrapper acquires parity once per requested row-column array; the convenience constraint wrapper acquires it per call. This is polynomial repetition, not a claim of global preprocessing once. The new tracked supplier `BinomialExecutionTracked.acquiredParity` can instead be cached once and passed through its equality theorem; its own report charges kernel/target/solve generation.

`SemiprimeUniversalConstraintPadding` is deliberately proof-only. `sourceJoint`/`jointIndex` expose the original source's Fintype.equivFin reindexing. `source_rows_in_padding` proves that every original finite source row is a literal padded row, and `padding_rows_from_source` proves that each padded row is zero or a literal source row. The actual centered corollaries have prefix `actual_`. Thus a runtime enumeration over all universal words does not have to execute the source's noncomputable finite inverse or obtain the desired row as a witness. The proof changes no integer row values or row spans.

## Actual execution diagnostic

`SourceArraySmoke.lean` calls the actual universalRow/numerator/constraint functions with r=2,Q=2,R=1,A=0. The row word has head00 and slot11; the other word swaps register position1. Lean executes the full integer parity solve, swaps, subset difference sum, rational interpolation expression and coefficient-array compiler. Output:

```
#[1, 0]
#[0, -1]
1
-1
```

The first two results are the identity-selector and nontrivially corrected row arrays; the final two are the integer numerator and padded constraint. This is a structural executability check, not a semiprime fixture, factoring campaign, or performance theorem. In particular it catches a polynomial-index/noncomputable runtime leak rather than merely checking that a definition can be written.

Replay from the repository:

```
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-source-acquisition-20261027/SourceArraySmoke.lean
python3 /tmp/semiprime-source-acquisition-20261027/strict_recheck_universal.py
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-source-acquisition-20261027/CombinedUniversalSourceAudit.lean
```

## Explicit constructor cost and remaining proofs

Let U=r^(2Q) be the actual universal single-slot alphabet size. Its words/indices must really be constructed or scanned; U is not treated as a fixed constant. For one integer numerator, the source sums over j<R and j-element subsets of Q-1 positions. A j-difference has 2^j delta leaves, so the total leaves are bounded by sum_j binom(Q-1,j)*2^j <=3^(Q-1). Sorting, subset generation, word equality and nested swap lookups add polynomial factors in Q and the register width. The outer loop also has R iterations, including empty j-layers. No universal operator entry is a free oracle.

Under the actual scheduled guards r>=2 and R<=Q, 2^Q and 3^(Q-1) are <=U. Thus even explicit subset construction/differences and repeated full universal scans have polynomial overhead in the actual alphabet dimensions. This is not uniform polynomial time in log(U), nor polynomial in arbitrary unscheduled r,Q measured only by their binary encodings. Source alphabets r^Q and U are polynomial in the network size only after the previously proved parameter schedule is instantiated.

The displayed source interpolation syntax has at most 6Q^2+8Q+3 AST nodes: a normalized divisor has <=5 nodes; basis <=6Q+5; correction <=6Q^2+8Q+1; adding the selector gives the bound. This node-count calculation is paper-level here, while the array interpreter's bound in its ACTUAL node count is proved. The imported mismatchRowCode also tests membership in the finite correctionColumns set, which may materialize/scan U words; charge that construction, or optimize to the equivalent mismatch-count predicate in a later implementation. This introduces polynomial alphabet overhead, not an uncharged exponential scan over original Boolean assignments.

For height, if parity entries have maximum bit height B, each partial difference is bounded by 2^j and each weighted subset term by 2^(R-1)*max|c|. Summing all subset layers gives the coarse intermediate bound 2^(Q+R)*(max|c|+1), up to harmless loop counters. Rational interpolation uses only public nonzero integer nodes/differences and a power of two. The existing source-row height theorems bound the resulting polynomials; their attachment to EVERY operation in this new interpreter, and all exact scalar/finite-index primitive bit/storage costs, remains to be composed. No free rational arithmetic assumption or full factoring bit theorem is claimed.

## Source provenance and scope

Imported formulas: pinned OpenAI source 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, vendored import-prefix-only closure under `vendor/openai-semiprime`. Exact source modules are SubexpRowInterpolation, Subexp/MatrixSupport, SqrtLog/LayoutNumerator, LayoutNumeratorBridge, LayoutScaledMatrices, LayoutUniversal and LayoutIndexed. The new sorted-difference implementation and coefficient-array compiler refine those formulas; source identities are not newly credited mathematics. Source/licence provenance remains the previously recorded Apache vendor provenance. All new repository files use the standard local copyright/licence header.

This slice closes an actual universal coefficient acquisition interface. It does not by itself acquire original packed/pulled-back layout arrays or instantiate an original-integer factorer. The earlier native long-residue acquisition rate remains unchanged. Root block/pullback/controller composition and the full bit-cost theorem are still separately required.

## Concrete original-variable constraint acquisition (sixth owned module)

`SemiprimeSourceConstraintAcquisition` now composes the actual searched packing, padded universal constraints, complete-block/leftover copy rows and original owner pullback. Runtime inputs are owner/factor maps, explicit SourceLayout.Enumerations and public rational/natural parameters. `packing`, `head`, `rowIndices` and `matrix` are ordinary compiled definitions, before the separate noncomputable proof section. They take no Layout.Data, Polynomial or requested matrix entry. The matrix truncates columns outside its actual computed original head to literal zero.

`rowIndices` enumerates `(Fin blockCount × UniversalType r Q 1) ⊕ I` using the supplied lists. Root's PaddedBlockCoverage.indices_length_le proves this length <=2*incidenceCount, even when the universal alphabet is larger than the input. Invalid universal rows, covered incidences, and wrong-head leftovers are zero padding; real leftovers are literal singleton constraints.

`source_rows_in_matrix` proves that EVERY finite row of the exact searched `SourceLayout.builtLayout` is an acquired matrix row on its original head. `matrix_rows_from_source` proves the converse: every acquired row is zero or a literal original source row on that head. This uses the universal padding comparison, root's complete-block cover and `sourceRow_spec` for the owner pullback; it is not an assumed row-span or locality premise. No runtime finite-type inverse is introduced. These two covers let the runtime design builder derive the actual locality, source-row height and selected-rank bound from the source interface.

The matrix fields remain function suppliers: accessing a field can recompute packing/word data if the caller does not materialize/cache it. The finite source dimensions make this polynomial overhead under the schedule, but it is not included for free in a constant-time matrix read. Root's concrete design acquisition/cache must retain or charge the supplier calls.

`SourceConstraintSmoke.lean` executes this entire constraint path on a two-variable one-factor two-port indexed diagnostic, including actual word search and packing. It reports:

```
2
[0, 1]
[[1, 0], [0, 0]]
```

These are the padded row count, computed original heads, and the acquired head-0 matrix. This is an executability/structural test, not a factoring fixture or asymptotic evidence.

Final owned gate: SIX modules strict PASS, ordinary-root scoped15lint PASS, every-generated standard3-only audit PASS: 95 declarations /66 theorem constants. `strict_recheck_universal.py` now covers all six with source-stability checks and byte-identical isolated/root objects. Root's separate source-array/block/descriptor/controller and AcquiredSourceCounter modules are not included in these six counts.
