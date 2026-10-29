# Independent acquired-source counter review

Disposition: PASS for the source-to-original-contraction execution/correctness interface. Read-only proof/API review; no source edits or extra compilation/testing by this reviewer. Final source pins are recorded separately after the author gate/freeze.

## Runtime data path

`AcquiredSourceCounter.count` takes original indexed scopes/coordinates, public scalar parameters, and actual local EntryReports. It constructs the explicit source enumerations and owner map, materially acquires the original incidence/variable coefficient ARRAY family, materially builds an Array of runtime designs at the Q nodes, and calls the executed NodeArray counter. Neither Layout.Data nor a Polynomial nor certified Data is a runtime argument. Mathematical layout/sourceDesign objects occur only in proof definitions/theorems.

The source supplier `SourceArrayAcquisition.acquire` uses actual universalRow generation (integer parity solve, swaps, finite differences, finite rational interpolation and coefficient compiler), complete-block/leftover lookup, and owner-fibre array sums. Its cached array is indexed by the explicit incidence enumeration. `acquire_read` and `acquire_coefficient` identify the cache entries with the actual searched builtLayout coefficients; they do not assume a requested coefficient. Array getD defaults are total implementation branches whose non-use for acquired legal indices is proved by acquire_read.

The runtime raw constraint supplier calls the concrete SourceConstraintAcquisition.matrix. Its head and factor ownership come from the same computed word search as the source layout. All raw source row indices are the explicit padded list, and columns outside the named original head are zero. `raw_covers` and `raw_from_source` prove BOTH source→actual and actual→zero/source, not merely the favourable containment. Hence padded rows cannot impose extra measurements or conceal missing native locality. The source bounded-owner/positive-node/interval guards yield raw_bounded on all original coordinates, including zero outside-head columns.

`build raw` computes original row selection; its finite coordinate order, literal selected integer rows and summary radii are data, not witnesses from the desired answer. `sourceDesign` is a proof-only native certificate; sourceDesign_runtime identifies its erased runtime fields with that exact computed build. The native locality is derived from old-row coverage and the actual source locality, not assumed. `selected_count_source` uses both covers and coordinate reindexing to obtain the exact original source rank; zero padding does not inflate it.

## Actual correctness endpoint

`count_correct` concludes the executed scalar is `CounterNative.originalContraction` for the ORIGINAL table values and supplied original coordinates. Its assumptions are an actual owner-fibre bound, Q>=1, intervalStart<=Q, J>0 and totalIncidence*R<Q*J. It does NOT take coefficients, raw constraints, desired Taylor packets, group/fibre values, native row spans, a count-correctness oracle, or a source restoration premise as an input. The proof obtains coefficient correctness from acquire_coefficient and restoration/degree from builtLayout, then invokes the earlier executed NodeArray theorem through the computed runtime design.

The theorem allows arbitrary integer EntryReport values, so the result is a weighted rational tensor contraction in general. A nonnegative Boolean accepted-assignment count requires the original public 0/1 local-entry instantiation. No factor-count or prefix-recovery machine endpoint is asserted by this theorem alone. Isolated original variables are not silently omitted: originalContraction includes them and the group scans count them.

The validity guards are correctness theorem hypotheses, not runtime validation built into count. The spectral/packing schedule is needed to bound rank/summary sizes and running time, not to manufacture count correctness by assertion. Its actual instantiation and guard/fallback controller remain separate.

## Cost, caching and remaining boundary

The top-level source coefficient family and the array of node designs are materially acquired before the Node counter call, which closes the former supplied-H/source-answer gap. Source matrix/word/packing fields are still function suppliers before materialization; internal repeated calls can recompute polynomial preprocessing. The source cache's original incidence inverse lookup is an explicit finite idxOf-style scan, not a constant-time inverse assumed for free.

IMPORTANT: the returned count.work is the Node/Hermite operation report. It does not include generating source coefficient arrays, repeated source packing/interpolation constants, raw matrix generation, or build's row selection/materialization. Thus it is not yet a complete ARITHMETIC work bound for the entire new count function, much less a primitive bit clock. These acquisition loops are executable and their polynomial scheduled-alphabet cost is constructively analyzable, but must be attached rather than hidden in “reads.” Likewise finite index/tuple/set operations, physical rational arithmetic, every new interpreter prefix height, and allocation/control/storage need composition.

The coefficient family has polynomial public dimensions M*n*(R+1); node design materialization is polynomial in its actual row/group dimensions. The source universal alphabets and subset loops are exponential in Q but polynomial in the network size only under the actual parameter schedule. No uniform polynomial-in-binary-Q claim is warranted.

No substantive algebra/interface correction requested. A stable actual Lean #eval through this precise top-level count is a useful independent execution diagnostic; its output is not asymptotic factoring evidence. The open full factoring bit-time conclusion remains distinct from this proved finite original-input counting identity.

## Final execution/gate confirmation

The author reports final strict/root15/all-generated PASS (21 declarations,16 theorem constants) for AcquiredSourceCounter. Read-only inspection of `AcquiredSourceCounterSmoke.lean` confirms that its runtime calls supply only the original one-variable/one-factor scopes, coordinates, scalar parameters and three actual local table callbacks. There are no source arrays, row measurements, Layout or Polynomial arguments. The recorded actual Lean outputs are `1`, `2`, `0` for the bit, constant-one and constant-zero controls. This is a deliberately tiny source-to-count executability test (R=0,r=Q=1), not a spectral-schedule test, prepared factoring case or rate demonstration. Final reviewed source and diagnostic pins are in review-acquired-source-counter-hashes.json. No further corrections requested.
