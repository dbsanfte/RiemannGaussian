# Conditional recovery and arbitrary-group measurement sums

Two new repository modules are implemented and strictly compiled with the pinned
Lean 4.34.1 toolchain and warnings as errors. Their theorem axiom reports contain
only the permitted standard axioms. The combined root-import audit checks every
generated declaration, not only the named endpoints.

## Prefix-only recovery

`SemiprimeCountRecovery.select` receives a counter whose input is a finite list
of bit restrictions on the **original** witness space. It does not ask for a
fast counter on arbitrary global predicates or remove internal wire variables.
The semantic contract is

`count fixed = acceptedCount (originalPredicate AND all fixed bits)`.

`select_sound` proves that all selected bits belong to a single original
accepted witness. If the zero-child count is positive, that branch is retained;
if it is zero, any parent witness must belong to the one child. Repeated requested
indices are allowed, with consistency forced by the same invariant.

`select_queries` counts one actual zero-child query on every recursive branch.
`search` adds one empty-prefix existence query; `search_queries_le` proves the
complete bound `length(indices)+1`. `search_none_iff` proves failure exactly when
the original acceptance set is empty, and `search_some_sound` proves that a
returned list has the requested indices and one common accepted witness.

These are statements about the executed recursive selector and its attached
query counter. They do not give a free-cost counting oracle. The actual tensor
counter must still satisfy this prefix-only semantic contract, and the Boolean
network/compiler must relate an accepted witness to a proper factor. The Python
wrapper's final integer reconstruction/division check and its primitive bit
costs remain separate refinements.

## Shared-summary separation

`SemiprimeSharedSummary.fibre_factorization` proves the finite distributive
identity for any number of groups, dependent finite local assignment types,
measurement functions, and local forced-bit conditions. The group-value
functions may take values in any commutative semiring, including truncated jets.

Its invariance premise says a group's value is unchanged when its own assignment
is held fixed and every other group's measurement is held fixed. Representatives
need only have the requested measurement when that fibre exists. They do not
need to obey forced bits. The proof replaces other-group assignments by those
representatives and then distributes the finite product of sums.

`shared_summary_contraction` sums all measurement tuples and recovers the whole
original forced-bit contraction. Empty measurement fibres contribute zero;
empty groups and arbitrary representative choices are included. One may use
arbitrary default Boolean representatives for fibres the executable scan skips.

This matches the actual streamed counter's two scans and reset-to-representative
behavior. It does not assume a precomputed contraction, rank bound, or fibre
cardinality. The row-span/kernel condition still must be connected to the
concrete factor products to discharge the pointwise invariance premise. The
finite sum expression still must be refined to the actual enumeration loops
with their bit costs; that execution theorem is not supplied by distributivity.
