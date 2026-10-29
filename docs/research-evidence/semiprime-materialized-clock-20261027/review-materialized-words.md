# Independent semantic/scope review: SemiprimeMaterializedWords

PASS for the stated scalar/list-control trace and its equality to the existing
local-expectation search. Read-only review; no source changes.

`expectation` executes every local completion. Its base case executes `f omega`
and retains that producer's work B, rather than assigning it cost one. Recursive
`sumRun` accounts for every child, and the division and list traversal have
explicit selected charges. The envelope `(A+1)^(s+1)*(B+10)` is a conservative
polynomial for fixed support size s; it does not treat growing support as free.

`activeRun` actually scans membership lists and computes the active indices;
`localTerm_work` uses remaining.Nodup to bound their count by support.length,
so duplicate entries in a supplied support list cannot invalidate the bound.
`evaluate` includes every term and the offset operation. `choose` recomputes
both score producers at each comparison, and its bound charges both: there is
no hidden memoization assumption. `assign` retains each chosen-score search and
the recursive remainder. The reachable-length condition in `assign_work`
correctly includes the trial symbol appended to the fixed list. `sequential`
uses the same range/decode conventions as the underlying source algorithm.

Important retained boundaries:

- `search_value` identifies the COMPUTED search with `localAssign`; by itself it
  is not a theorem that the selected word satisfies the desired source bad-event
  bound. Actual terminal dependence on the supplied support, original source
  objective, and the conditional-expectation invariant must still be connected.
  Parent is adding that bridge; the present module does not assume its result.
- Arbitrary terminal computation is paid only through the explicit hypothesis
  `(f j omega).work <= B`. This must be instantiated with the actual terminal
  producer and appropriate word-access environment, not an arbitrary function
  silently packaged with work1.
- A supplied `support : J -> List Nat` is not automatically cached/acquired by
  these definitions. If its producer recomputes source data, that acquisition
  must be charged or the list must be materialized separately. The same applies
  to construction of the alphabet/terms lists and the scalar offset.
- Function.update/decode accesses, rational comparison/division bit arithmetic,
  physical word/list addressing, allocation, and output materialization are not
  a complete primitive bit clock merely because scalar/control events are
  recorded. The module's docstring explicitly preserves this distinction.
- Empty alphabets can produce a defined rational average by division by zero;
  the intended `search a tail` alphabet is nonempty. No empty-alphabet
  conditional-expectation correctness should be inferred from generic value
  identities.

No mathematical or selected-ledger error found. The support4 specialization is
appropriate after the actual support and terminal budget are supplied; the
module does not itself establish that application-specific support bound.
