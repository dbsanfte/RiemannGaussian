# Closed public counter resource envelopes

NEW `SemiprimePublicCounterResources.lean` compares the ACTUAL closed `PublicCounterBudget` resources with `MaterializedRate` envelopes.

- `closed_summary_le`: sourceSignatureBase(n) raised to the literal floor(4n/(r*lambda)) is bounded by summaryEnvelope(n), for nu>=64. It uses the independently proved parameter-only summary_envelope_log, not a statement about a default layout.
- `summaryBound_le`: instantiates that exact expression at public wireCount/groups/points/degree/lambda; no supplied summary bound or rank remains.
- `ceil_head_le`: ceil(3n/(2r)) <= 2n/r after real embedding if r>0 and n>=2r.
- `fast_headroom`: the ACTUAL fastGuard head-load clause 16*Q*r^2<=n, with r,Q>=2, implies n>=2r.
- `headBound_le`: the literal 2^headBound is bounded by the existing headEnvelope on the fast branch. The ceiling is paid explicitly; it is not silently dropped.
- `scopeBound_le`: 2^scopeBound(bitLength N) is bounded by exp(512*wireCount(N)^(3/4)*log 2), for N>0, using the actual wireCount equality and macro scope bound.
- `supportCount_eq`: weightedCount(wireCount N,precision(N)-1) is EXACTLY weightedCount(wireCount N,cutoff(wireCount N)); no fresh support cutoff is assumed.

The use of known real rate envelopes is a resource comparison only. The module does not assume an unproved default/indexed layout equality, a complete counter work bound, or a primitive bit/address clock. Parent's actual PublicCounterBudget supplies the counter/report theorem; the subsequent fixed-polynomial rate composition is separate.

Final status: canonical strict compilation with autoImplicit=false/warningAsError=true PASS; ordinary root15 lint and all-generated-declaration standard-axiom audit PASS17 declarations/17 theorems. Source/object frozen; hashes in public-counter-resources-hashes.json. No frozen module, journal or archive was edited.
