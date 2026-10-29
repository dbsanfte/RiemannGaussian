# Source-layout factoring entrypoint

`source_factor_search.py` is a new entrypoint. It imports the frozen `factor_network.py`, designated-host `Network.restrict`, trial division, and `recover_from_counter` without changing them. The only layout constructor on its production counter branch is the new pinned-source `construct_layout`, created once and reused for every prefix count.

```
python3 /tmp/semiprime-executable-counter-20261027/source_factor_search.py 91
python3 /tmp/semiprime-executable-counter-20261027/test_source_factor_search.py --output /tmp/semiprime-executable-counter-20261027/factor-search-tests.json
```

The first command exercises the **explicit finite invalid-guard trial-division branch**, not the fast counter. A production guard cannot be bypassed by CLI options. `--max-universal-dimension D` only limits the accepted-guard branch; if exceeded, the result explicitly says `resource_limit_no_result`, with no counter, fallback factor search, or claimed divisor.

The wrapper compiles N, checks actual scope statistics M=2n/B=2 and every input bit's original host, then checks the exact stronger schedule. The accepted branch constructs one layout, passes each same-scope restricted network to the frozen counter, verifies nonnegative integer counts, and uses at most L+1 queries from the frozen prefix recovery. Recovered divisors receive a final exact multiplication/divisibility check. Restriction is imposed at the compiler's designated existing endpoint, preserving every local scope and incidence multiplicity; equality wires propagate it to the other endpoint. No new unary tensor or Boolean variable is added.

Four adapter/control tests PASS. They check the actual compiler's public input edges and same-scope restrictions using one publicly supplied witness, rejection before layout allocation, actual frozen-counter prefix recovery on a clearly labelled tiny diagnostic source layout (four queries), and a synthetic accepted-guard control proving resource exits return no result. The diagnostic fixture does not claim a small instance satisfies the production guard. This is not a factor-performance campaign.

The ordinary bit cost includes the new exact conditional-score construction, complete-copy matrices, literal integer selection, rational polynomial coefficients, and counter execution described in `source-layout-report.md`; it is not the earlier manual-denominator/eigenbasis constructor. Prefix counts reuse setup but still execute full local counter algebra per query. Strong-guard finite fallback is ordinary trial division, and no practical crossover or extracted Lean runtime theorem is asserted.

## Cached Lean jet semantic check

Read-only review of `SemiprimeJetArray.lean`: `buildInverse` makes one recursive prefix call, reads earlier stored coefficients in `dotPrefix`, and pushes each inverse coefficient once. The recurrence matches the frozen Python inverse loop. `inverse_work` charges a reciprocal, rational arithmetic, and coefficient accesses; `multiply_work` charges the actual convolution loop. These field-operation/access counts are **not bit costs**, allocation/copy costs, or a Turing-machine space/time theorem. Inverse-as-inverse requires the separately proved nonzero/unit-constant hypotheses; the total recurrence's value at zero constant alone provides no such semantics. No issue found within those stated scopes.
