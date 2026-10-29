# Actual pinned-source layout executable

The new `source_layout.py` implements the complete-bucket layout and imports the unchanged frozen counter. `source_factor_solver.count` checks the stronger guards before auxiliary allocation; a failed guard takes an explicitly labelled exhaustive finite-input fallback. An optional auxiliary-dimension cap returns a resource-limit result **without** silently calling the fast route or claiming a count. This is an executable algebraic construction aligned with the proved source, not a Lean-certified implementation or a new factoring-rate theorem.

## Exact source mapping

All paths below are relative to `vendor/openai-semiprime/OpenAISemiprime/Algorithms/SubexponentialSAT/` at the pin in `ATTRIBUTION.md`.

| Python | Pinned source | Exact convention |
|---|---|---|
| `conditional_score`, `computed_words` | `SqrtLog/PackingAlgorithm.lean`, `Subexp/LocalExpectation.lean` | Joint unnormalized score, variable labels then factor labels; exact conditional mean, lexicographic first minimizer. No random search or eigenbasis. |
| `Parameters.A0` | `Subexp/TailInterval.lean`, `mean`, `centeredStart`, `intervalStart` | Natural floor of `(Q−1)(r−1)/(2r)−R/2`, clipped at zero. |
| `parity_coefficients` | `BinomialInterpolation.lean` | Integer vector satisfying `sum c_j choose(A+d,j)=(-1)^(A+d)` for `0<=d<R`. |
| `numerator_operator_row` | `SqrtLog/LayoutNumerator.lean`, `integerDifference`, `entry` | Active positions exclude the current node; all projector denominators cleared by `2^(R−1)`. |
| `Universal.rows` | `SubexpAnnihilation.lean`, `SubexpRowInterpolation.lean` | Negative zero-extended matrix prescriptions at mismatch nodes; restoration correction `z/t product_(s!=t)(z−s)/(t−s)`. |
| Buckets and `block_count` | `Subexp/ConstructivePacking.lean` | Minimum bucket size over **all** universal types. Complete copies only. Every unused incidence is an identity leftover. |
| `raw_constraints` | `SqrtLog/LayoutBlocks.lean`, `LayoutHeadPullback.lean` | Cleared defect on each copy, singleton constraints for leftover incidences, then literal sum over original-owner fibres. |
| `select_actual_rows` | `SqrtLog/LayoutRowSelection.lean` | Exact rational rank test selects an actual subset of original integer rows. Temporary pivots are normalized; returned measurement rows never are. |

`check_stats` checks `4(B+w)D² <= epsilon² M`, `16Qr²<=n`, `R>=4`, `4R<=Q`, plus the centered spectral sufficient guard `32(Q−1)ceil(log2(ceil(2/epsilon)))<=R²`. This rational/integer test implies the source natural-log guard. It additionally checks `epsilon M<=n/2` for the frozen counter's `tau` API. The numerical schedule is `lambda=ceil(log2 n)`, `nu=ceil(log2 lambda)`, `r=floor(sqrt(lambda))/nu²`, `Q=floor(lambda/(128nu))`, `R=4ceil(sqrt(lambda))`, `epsilon=1/(r lambda)`; invalid small schedules fail before exponentiation/allocation. No numerical spectral approximation is used.

The frozen interface calls its **measurement L1 radius** `D`; the source calls its **universal dimension** `D`. These are kept distinct: `universal_dimension=r^(2Q)`, while `layout.D=n B 2(8Q)^(2R)`. `tau=epsilon M/n`. Selected row counts are checked against `2epsilon M` per node, head sizes against `3n/(2r)`, and complete-copy coverage against `(1−epsilon)M` on the guarded route.

Supplying explicit word labels and disabling guards is a diagnostic-only interface used to exercise small complete copies. Such fixtures do not satisfy the asymptotic schedule. The production adapter never supplies labels or disables guards.

## Executed structural checks

Replay:

```
python3 /tmp/semiprime-executable-counter-20261027/test_source_layout.py --output /tmp/semiprime-executable-counter-20261027/source-tests.json
```

The standard-library checker verifies universal numerator entries against an independent dense projector/elementary-symmetric matrix recurrence (Q=2 and Q=3), conditional means against exhaustive label completions, original-row selection, and the frozen counter's exact restoration/degree/kernel checks. It compares exact tensor contractions with exhaustive truth-table counts for a complete copy, a complete copy with one identity leftover, an all-leftover network with repeated owners, and an empty-factor network. It verifies invalid guards precede word/matrix construction and separately tests a valid enormous **numeric guard only**, without allocating a network. JSON contains operation counters and observed rational bit sizes. These are structural tests, not semiprime fixtures or factoring benchmarks.

## Charged implementation and remaining gap

Write F for number of factors, M for incidences, n for original bits, B for maximum incidence multiplicity, w for maximum arity, and D=r^(2Q). Computed labels try `(n+F)r^Q` candidates. Each candidate recomputes O(M²+Qn²) exact score terms, with word comparisons costing O(Q); this is deliberately simple polynomial setup. It does not enumerate all completions. Empty factors can be dropped (or their scalar callbacks multiplied separately) if F is not otherwise polynomially bounded.

The numerator builder emits the literal subset/difference sum: per universal input and node, at most `sum_(j<R) choose(Q−1,j)2^j <=3^(Q−1)` terms. Since r>=2, this is bounded polynomially in D. Dense universal interpolation considers D² ordered pairs, constructs degree-at-most-R rows, and caches mismatch interpolation bases. Complete bucket packing is linear in M after the label lookup. Sparse owner pullback merges repeated fibres exactly; it does not split original bits or add scopes.

At any node, the number of raw constraints is at most M. Each has at most n integer coordinates of magnitude at most `W=B*2(8Q)^(2R)`. Rank selection costs at most O(Q M n²) rational elimination operations with naive row updates. Intermediate fractions are tracked diagnostically; mathematically they are ratios of minors of the original integer matrix, with O(n(log n+log W)) bits by determinant bounds. Selected rows retain literal integer entries, so measurement enumeration depends on W, not on Gaussian pivot denominators. Polynomial interpolation denominators are explicit rational products from nodes 1..Q and the cleared power of two; all are polynomial-bit under the schedule. This implementation records maxima at key stages, not every primitive arithmetic operation.

The unchanged counter streams Boolean local assignments and explicit integer summary boxes. Thus local table callbacks remain evaluated on Boolean entries; no complete high-arity truth table is stored. The source row-range bound gives `log(nW)=O(log n+log B+R log Q)`, and summary rank is at most `2epsilon M`. For M=2n, the schedule gives the intended subexponential summary exponent. This report does not replace the existing finite quantitative inequalities or prove a Python/Turing-machine resource theorem. Dense exact arithmetic, interpreter overhead, callback bit complexity and the finite-fallback cutoff remain separately charged implementation obligations; executable alignment is supported by exact checks, not a compiler refinement certificate.

No frozen Python, Lean source, journal, AGENTS, or external build was modified.

Final replay: **10 tests PASS**. The four exact contraction values are respectively 11, 5, 2, 2; independent dense matrix comparisons cover 64+1536 entries. All four Python files pass `py_compile`. The preservation check rehashed 1553 protected repository files against `preservation-before.json`: zero changes (`preservation-after.json`).
