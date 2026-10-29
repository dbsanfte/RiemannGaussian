# Executable counter, public factor coverage, and arithmetic heights

This checkpoint makes substantive progress toward the guaranteed 1/6-or-better
factoring goal. It closes the public graph's factor-count semantics and size
obligations, supplies the actual source-layout Python constructor, and proves
streamed enumeration, cached arithmetic and several missing input-height bounds.
The complete uniform primitive bit-time theorem remains open.

## Whole-family reduction

For every positive integer N, the literal subdivided graph's local 0/1 tensor
contraction equals the number of ordered integer pairs P,Q>=2 with PQ=N.
Every such pair has a constructed, unique accepted graph extension. Public
padding, top-bit caps and target digits are derived from N. This theorem includes
squares and both orientations when distinct; it is not restricted to a finite
test family or to prime factors.

The actual Boolean edge count E satisfies `L<=E<=6400L`, with L=N's bit length.
Maximum local scope is at most `512L^(3/4)`. The actual occurrence-two graph is
connected to the source-layout rank, summary-size and eventual guard theorems.
The exact integer logarithm test used by the executable guard is included.

See [the graph proof](graph-semantics-proof.md),
[the independent graph review](review-public-factor-count.md),
[public parameters](parameters-proof.md), and
[the scheduled counter](scheduled-proof.md).

## Executed loops and arithmetic

The new Python constructor uses the pinned source's complete buckets, universal
rows, identity leftovers, original-owner pullback and selection of actual integer
measurement rows. The factor entry point reuses one layout across at most L+1
original-scope prefix queries. Guard failure invokes explicitly labelled trial
division; an optional resource cap returns no result. The frozen older constructor
and counter are preserved. See [implementation status](source-layout-report.md),
[factor adapter](factor-search-report.md), and
[independent implementation review](review-source-python.md).

The new Lean array implementation computes each inverse coefficient once.
Its quotient has at most `3J^2+J+1` rational arithmetic operations. The streamed
ternary traversal equals the required subset-pair sum, with exactly
`Cq=sum_(j<=q) 2^j choose(E,j)` callbacks, at most `(E+1)Cq` traversal nodes and
depth E. Its finite entropy bound retains the actual strict jet width J=q+1.
See [cached arithmetic](jet-array-proof.md),
[enumeration](counter-enumeration-report.md), and
[the independent cached-array review](review-jet-array.md).

The actual rational rows have one common denominator
`delta=2^(R-1)*(Q!)^(Q+1)` and constructor-derived polynomial-bit integer
numerators. Integer Taylor shifts preserve delta. The actual normalized Hermite
cardinal factors have denominator `(Q!)^(QJ)` and rational coefficient magnitude
at most `2^(QJ)`. Cached inverse coefficients and all inverse recurrence partial
sums have proved denominator/numerator bounds; actual quotient output bounds are
also proved. See [native row heights](row-proof.md),
[the row/Taylor review](review-source-taylor-height.md),
[cardinal input bounds](cardinal-proof.md), and
[their independent review](review-cardinal-height.md). These are not claims that
all global intermediate loops are already
attached to a primitive execution model.

## Rate interpretation

The concrete operation ledger includes support pairs, summary boxes, head scans,
local table expansion, construction, Hermite arrays and prefix recovery. It yields
the rational-operation envelope

`poly(E) * 2^(O(E*(loglog E)^2/sqrt(log E)) + w)`.

With E=Theta(L) and w=O(L^(3/4)), its exponent is o(L). This is a promising
solution route, not a claimed completed factoring bit-complexity proof. The
[operation ledger](rational-operation-composition.md) specifies which finite
bounds are formal and which remaining composition is on paper. The
[next proof obligations](research-frontier.md) identify the concrete work still
needed: all intermediate height attachments, primitive execution/refinement,
and the single uniform fallback-plus-search bit-time theorem.

The native long-residue query remains at its prior soft-K^(5/4) bound. This
checkpoint advances the alternative factoring route; it does not claim soft-K
acquisition of the original residue scalar.

## Published Lean proof

The [prior external audit](../semiprime-layout-assembly-20261026/external-final-audit.md)
already checked the original pinned fixed-k SAT endpoint: 2,569 source modules,
90,034 declarations and 63,007 theorem constants, all standard axioms only. The
exact expected theorem signature typechecked. Its formalized rate is the older
`n(loglog n)^2/sqrt(log n)` rate, with a primitive bit-tape machine and polynomial
visited space. The configured Main wrapper's extra 522 dependencies were not
built. That fixed-k theorem alone does not certify generic growing-arity tensor
counting or the factoring extension here.

## Verification and preservation

Each new module is strictly compiled with `autoImplicit=false` and
`warningAsError=true`, independently recompiled to an isolated object, and checked
against its ordinary build object hash. The combined audit imports the existing
repository root, runs all 15 scoped linters and audits every emitted declaration's
transitive axioms. The only permitted axioms are propext, Classical.choice and
Quot.sound. Semantic reviews are independent of their module authors; the
[schedule/enumeration review](review-public-schedule-enumeration.md) checks their
public-size and exact-cutoff interfaces.

Root independently replayed 10 constructor/algebra checks and 4 adapter checks;
their results match the authors' outputs. The cases are structural diagnostics,
not a performance campaign or empirical justification of coverage. Frozen files,
concurrent work and append-only document prefixes are checked by hash. The packet
manifest and verification record give the precise completed scope. No commit or
push is performed in this checkpoint.
