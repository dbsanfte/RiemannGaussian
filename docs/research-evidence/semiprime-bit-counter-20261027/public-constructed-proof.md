# Public constructed count

`SemiprimePublicConstructedCount.lean` joins the actual scheduled source-layout
counter to the existing public ordinary-factor cardinality theorem. The public
input supplies only N>0 and the stated source-layout guard. The row construction,
local tables, coordinates, and occurrence/coverage certificates are constructed.

`assignmentEquiv` reindexes the counter's finite-set witnesses as Boolean wire
assignments. `accepted_eq_tensor` identifies its local conjunction count with
the literal zero/one tensor contraction. `constructed_empty_count` attaches this
to the source-constructed counter. `public_coverage` derives every searched
wire's occurrence from the actual graph's occurrence-two theorem.

`public_constructed_factor_count` therefore proves that the actual public count
equals `Fintype.card (OrdinaryFactors N)`. These are ordered nontrivial integer
factor pairs, including squares; primality is not a premise. The positivity
theorem detects precisely the existence of such a pair. Prefix counts retain
their original restricted-assignment semantics, and search needs no more than
one initial count plus one count per requested wire.

The guard remains explicit; its eventual acceptance is the earlier separate
public-schedule theorem. This module does not introduce a runtime theorem,
make `defaultEnumerations` executable, prove that Python identifiers are a
compiled copy of the Lean graph, or complete original-input decoding from the
search output. It closes the mathematical count composition, with those
execution and recovery obligations still stated separately.
