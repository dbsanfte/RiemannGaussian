# Report-preserving prefix/factor controller

NEW sources only: `SemiprimePaidPrefixController`, `SemiprimePaidFactorDecoder`,
`SemiprimePaidPublicController`, `SemiprimePaidScheduledController`.
Earlier sources and sealed packets are unchanged.

## Actual execution and formal endpoints

The generic selector caches each acquired initial/zero-child report ONCE and
adds its entire work on the same executed branch. It performs one initial and
at most one conditional count per requested wire. `select_result/search_result`
identify the literal selected bits AND query counts with the original selector.
The uniform work premise concerns only reachable prefix lengths, not arbitrary
witness predicates. `finIndices` actually acquires the ascending finite wire/
digit lists; map/cons/length work is retained with a polynomial bound.

The concrete public `counter` is the actual `CachedSourceCounter.count` on the
original indexed graph and original paid arithmetic/equality checker with the
existing every-occurrence restriction. `prefixRun` executes that counter ONCE,
then the actual rational floor, retaining `counter.work + fixed.length + 3`.
It does not project a scalar count and discard its source/native report.
`entry_work_le` derives the explicit uniform terminal callback budget

    1048576*(64*bitLength N+2)^10
      + wireCount N*(3*scopeBound(bitLength N)+2) + 1.

The decoder executes actual original edge-index `idxOf` scans, selected-label
list reads (including their explicit natural-index copies), little-endian
binary accumulation, radix powers, and digit sums. Its edge enumeration is
cached once before repeated scans. `decode_value` equals the exact original
physical `decodeOperand`; no semantic integer normalizer is substituted.
Successful selected lists have exactly wireCount entries, which supplies the
uniform decoder budget. No fresh counter is called by decoding.

The N-only `run` accepts ONLY N and retains the actual source/native prefix
reports, selector work, decoder work, or executed finite trial fallback work.
Its source schedule and literal guard are unchanged. `run_value` proves exact
output equivalence for EVERY natural input to the previous complete factorer;
`run_sound/run_none_iff` give proper divisors and all-input completeness.
No user count callback, source/design/table answer, or promised factor input
occurs at this public runtime API.

## Exact proved aggregate envelope

For B bounding the ACTUAL `counter.work` for every prefix of length at most
W=wireCount N, `factor_work` proves

    factor.work <= (W+1)*(B+W+3*(W+1)^2+decoderBudget(N,W)+16).

On the actual accepted fast branch, `run_fast_work` adds the three selected
outer branch events, giving the same bound with constant19. The initial finite
index list is acquired once; each actual acquired count is invoked once per
query; no extra source-counter call is made for report extraction.
`decoderBudget` is the explicit polynomial

    d*((length+1)*(2*W+6*v+9)+2*d+8)
      +2*radixBits+3*(d+1)^2+3,

where d=digitCount and length=firstAxis*secondAxis. The fallback actually
constructs its ascending interval and scans tested candidates;
`trial_work <= 8*N+3` counts this selected scalar/list execution.

B is a PROOF-SIDE uniform resource bound, not a runtime count/terminal answer.
This slice does not yet derive B from the source numerical guard: that requires
joining the forthcoming paid full-setup counter. The explicit entry budget is
available for that native-counter work theorem.

## Concrete setup/refinement still excluded

These reports are selected scalar/list/array/control ledgers, not complete
primitive-bit clocks. In particular:

1. The currently instantiated CachedSourceCounter report includes the new
   original-source acquisition report and native/Hermite report, but still
   excludes its initial `FiniteEnumerations.indexed` construction and its old
   `Array.ofFn(build(raw ...))` design/setup computations. Parent owns their
   paid replacements. Our wrapper retains all reports that THIS counter
   actually returns; it does not declare those old omissions paid.
2. Public `edgeEnumeration`/`vertexEnumeration` generation and public graph
   parameter/port-map acquisition remain unreported setup. The NEW decoder
   caches its edge enumeration and pays EVERY subsequent index scan, but does
   NOT claim that constructing the cached macro edge list was free or paid.
   Qhol's indexed-source finite enumeration adapter is not a theorem about this
   separate public macro graph enumeration.
3. The original N bit-length/macro schedule computation, repeated parameter
   references, integer/rational arithmetic inside the literal guard, and source
   callback index/coordinate metadata acquisition are not a complete primitive
   setup clock here. `run` records outer branch events, not a false constant
   bound for the entire guard computation.
4. Rational floor, natural multiplication/remainder, equality of encoded
   vertices/wires, finite-index constructor/closure evaluation, report/natural
   arithmetic, physical list/array addressing/allocation and control encoding
   still need their bit/word simulation. The floor is an actual operation
   retaining the input count report; it is not asserted to cost one primitive
   bit step. The already proved count correctness bounds its finite output,
   but that fact alone is not a clock implementation.
5. The old prefix `entry` report has its stated selected checker/restriction
   scope. In particular physical public-coordinate lookups and source metadata
   refinements are not silently absorbed by calling its field `clock`.

No full N^o(1) bit-time theorem is inferred from these conditional report
bounds or the equality of output values. The actual paper result remains as in
the sealed authoritative packet; this slice closes the report-retention seam.

## Exact narrow execution controls

`PaidControllerSmoke.lean` prints:

- a three-query positive selector retains work54 (not just querycount3);
- an empty initial count retains its work7 plus control3;
- N-only run0 and run4 compile the entire new runtime closure and return
  `(none,0,1)` and `(some2,0,31)`;
- one literal physical input bit decodes2, agrees with old decodeOperand2,
  and retains work922.

These are small exact interpreter controls, not a semiprime/factoring campaign
or asymptotic performance evidence. All semantic claims above are proved for
all inputs.
