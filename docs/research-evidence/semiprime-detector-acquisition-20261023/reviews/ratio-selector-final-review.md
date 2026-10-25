# Final review: labeled descriptors and separate ratio menus

23 October 2026. PASS for the precise universal-selector model below; no assertion that no soft-r factorizer exists.

Each descriptor v is charged for ONE AP residue s=1+rt. The actual catalog has a a unit modulo r, so its coefficient pair determines one such s. Reuse at several residue labels is charged as several labeled descriptors. Assume 0<|C_v|<=V. Its explicit ratio menu R_v may depend arbitrarily on N and on the descriptor.

Let Pi count primes c in (r/2,r), and b_V=floor(log V/log(r/2)). For prime c, the exact true-witness denominator c/gcd(c,C_v) is either 1 or c. Consequently a descriptor can cover at most b_V+|R_v| such prime multipliers: at most b_V divide its nonzero C_v; every other covered prime must occur as a reduced denominator in its own menu. Overcounting duplicates only strengthens this upper bound. Summing capacities over descriptors and requiring all r*Pi labeled pairs (s,c) gives

    b_V*J + sum_v |R_v| >= r*Pi.

For V<=r^2(log r)^K, b_V<=2 once (r/2)^3>V, whereas Pi=Theta(r/log r). Hence both explicit labeled-descriptor volume and explicit menu/root-test volume cannot be soft O(r) in this stronger residue-wise universal representation. N-dependent menu choices do not avoid the count if they must cover every residue label. An N-dependent selector covering only an actual divisor, implicit simultaneous root algorithms, or a different source representation is not excluded.

The continuation now states this extension and explicitly restricts the a/label convention, avoiding uncharged multi-residue polynomials with nonunit a.

One exact replay was retained and run successfully:

- `replay_ratio_counterexample.py`
- `ratio-counterexample-replay.json`, status PASS.

For r=43, N=59447*59747=3551779909, P0=59168, A=1, the recomputed true ratios are 48/41 and 3/7. Both factors and the two local orders 29723 and 29873 passed complete trial division. The replay certifies beta=4 has those exact odd, coprime local orders, both >16H=29584; its exact global order is 887915179>256r^4=875213056, and H/M powering preserves both local orders. Thus this instance satisfies the strong hard-branch preparation. All root, derivative, and source congruence residuals are zero. Both reduced denominators match c/gcd(c,C)>1, so legal B shifts cannot make either ratio integral. This checks one prepared-instance counterexample to integer forcing in the original representative box, not a general algorithmic hardness claim.

Reviewed current SHA256 after the exact replay:

- `ratio-selector-continuation.md`: `09be7f838ae336b16a09f56620550b7c4fe8e39c595ed46ecb674c7f2ea3f173`
- `replay_ratio_counterexample.py`: `17c4dab7b2d3e24647e9f7ac921d5b3ca2139c8db89d4823a1de73ca19a0cf4e`
- `ratio-counterexample-replay.json`: `8e414e24c823c0b30ba88d5c4749f00c4df0dbebbe2cfedbd6842dbdbe57ee92`

The continuation's minor index/box qualification, b_V=0 case, and “can produce” exponential-scaling wording are retained. No repository files were changed.
