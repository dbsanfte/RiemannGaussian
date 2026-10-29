# Pure raw-integer runtime design acquisition

SemiprimeRuntimeDesignAcquisition strict/root15/all-generated PASS:38 declarations/12 theorems, standard axioms only. Frozen sources unchanged. RuntimeRawSmoke.lean executes actual build and count without Layout.Data or polynomial runtime indices: duplicate constraints select one row, stdout `(1, [(1, 1)])`, then counts `1`, `2`, `0`. These are execution controls, not complexity or factoring evidence.

## API and correctness

RawDesign n F has precisely r, head, assigned, count, rows and W. rows are literal global-coordinate integers. columns uses a deterministic filtered Fin list; matrix restricts raw rows to that explicit head. selection is the executed rational pivoting algorithm retaining original integer row IDs. uncache makes a RuntimeDesign; cache materializes its selected measurement entries with nested Array.ofFn, and build composes them.

selected_count proves build.m equals the actual rational row rank of the raw constraints on the head. build_bounded keeps the original integer entry bound, with no rational scaling in output. certify attaches native rational row validity using RAW integer-kernel annihilation, transfers it through the proved selected-row span, and obtains native rational span through integer-kernel locality. It does not assume selected native span or a count answer. certify_runtime identifies proof erasure with the pure build result.

## Cost and caching scope

Only the selected integer entries are materialized by cache. Filtering/shape fields and the uncache selector functions can be recomputed. During construction of the cached table, reading each selected original ID can itself run the polynomial pivot algorithm again. Consequently this module does NOT claim elimination is executed exactly once per group or give a tight preprocessing count. It gives a computable supplier with polynomial overhead in candidate-row count, group size, explicit row-lookup cost and integer bit length. For example, multiplying a standard polynomial elimination cost by the number of output table entries is still polynomial under the source schedule. Repeated filtered-column inverse lookup is also polynomial. Subsequent C reads access the retained nested arrays and do not rerun elimination.

A tighter frontend can cache selected IDs and columns once per group. That optimization is not needed for the subexponential rate but would require a further concrete record/array refinement before claiming its exact improved operation count. Raw input evaluation must itself be supplied/paid by the actual block/leftover source builder. No arbitrary function-read oracle is automatically constant-time.

## Remaining source join

The input proof hlocal is a genuine raw-source locality obligation, not yet derived here from the new padded block/leftover constructor. Likewise selected_count is raw rank, not an assertion that padding has the old source rank; exact span/rank transport remains the root source join. These distinctions prevent treating this intermediate builder as a complete proved source acquisition algorithm. Primitive rational pivoting bit-cost attachment and finite indexing/control overhead remain separate from semantic selection correctness.
