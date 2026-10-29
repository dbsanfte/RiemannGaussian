# Computed-source and N-only materialized execution join

Three NEW modules join the materialized cached-head algorithm to the actual
source constructor and public factoring graph. Frozen sources remain unchanged.

## Runtime path

`SemiprimeMaterializedAcquiredCounter.count` acquires the same original source
coefficient arrays with `SourceArrayAcquisition.acquire`, obtains their actual
indexed reads, and materializes each selected runtime integer design with
`Array.ofFn (build (AcquiredSourceCounter.raw ...))`. It then invokes the NEW
`MaterializedFibreNative.count`. No source/design/coefficient/group/fibre/count
answer is supplied by a caller.

`SemiprimeMaterializedPublicExecution.prefixCount` uses the actual indexed
public arity/coordinate maps, the paid `indexedEntry` arithmetic/equality
checker, and the existing every-occurrence prefix gate. Its source owner bound
is the proved actual B=2. The same `CountRecovery.search` is run using these NEW
prefix counts, and the same physical little-endian input-bit decoder returns
the integer factor. No change of graph, restrictions, scopes, or decoder is
smuggled through the equivalence proof.

`SemiprimeMaterializedScheduledExecution.run` takes ONLY N. It computes the
previous actual group/node/degree/precision/tolerance schedule, tests its literal
decidable guard, and invokes the new materialized public search on the accepted
branch. Zero is explicitly rejected. The complementary branch uses the same
complete finite `trialFactor`; there are no user-selected parameters or
promised semiprime assumptions at this API.

## Formal semantics

- `MaterializedAcquiredCounter.count_correct` proves the actual original
  contraction from the already proved sourceDesign, acquired coefficient
  theorem, original row-degree/origin properties, and the new materialized
  count correctness. Numerical owner/node/interval/precision premises are
  explicit at this generic layer.
- `count_value_eq_old` compares scalar VALUE only, not operation traces.
- Public `prefixCount_eq_old`, `search_eq_old`, `factor_eq_old` prove exact
  outputs for every restricted count and selected physical bit list under the
  numerical premises. `factor_sound` and `factor_none_iff` follow.
- N-only `run_eq_old` proves equality on EVERY natural input, using the actual
  runtime guard to discharge those numerical premises. `run_sound` and
  `run_none_iff` therefore cover zero/one/primes/squares and arbitrary composites.
- `eventually_run_materialized` proves that the actual new source-counter
  branch, not merely some hypothetical good parameter branch, is taken
  eventually. It reuses the already proved actual-schedule eventual guard.

## Clock scope

This completes the whole N-to-factor SEMANTIC join for the new materialized
counter. It does not assert a new complete primitive-bit clock theorem.
The existing interpreter work, actual preprocessing loops, finite index/word
accesses, source selection, integer/rational heights, and their bit-machine
simulation retain the separately stated resource-attachment obligations. In
particular equality of outputs to the old algorithm is NOT used as a transfer
of its runtime or work report. Qhol's pending tracked source supplier can match
the identical acquire/read/build inputs without changing this semantic endpoint.

## Narrow executable control

`MaterializedPublicSmoke.lean` evaluates run0 and run4, primarily to force Lean
compilation of the ENTIRE new runtime dependency closure and detect any hidden
noncomputable polynomial index. Expected output is `none`, `some 2`. This is
not an asymptotic performance control or a factoring campaign. All substantive
coverage/correctness statements above are proved for all inputs.
