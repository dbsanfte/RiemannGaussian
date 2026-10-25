# Independent integration review

23 October 2026. Reviewed `README.md`, `root-review.md`, `unbalanced-geometry.md`, `trace-index.md`, and the finalized `frobenius-traces.md`. No repository or frozen-file edits. This reviews the paper-level composition; it does not certify executable/Lean integration or reprove every inherited analytic consumer.

**Verdict.** The whole-input Gauss geometry, common-curvature trace normalization, separate coefficient-one AP continuation, and per-window count target are integrated correctly. No new full query, collision detector, or factoring exponent is established or claimed. The final files were checked after root applied all requested precisions: the common base is explicitly purified, support equivalence names the Gauss leaves for that purified base, h<=r is stated for the denominator-safe formal prefix, the finite Frobenius diagnostic is labeled coefficient-one AP, and the geometry input explicitly has P<Q with prime squares handled by the inherited prefix. No integration fix remains outstanding.

The independent geometry check confirms

    d^2+X^2 b^2+X^4 a^2
      <=X^2 F(u,a)/D+D/4
      <=(2N/H+H^2/2)X^2 <=(5/2)H^2 X^2.

The exact X=2P0/r>=32r gives |a|<=sqrt(5/2)r/32<r/20. The true h<X and Cauchy--Schwarz give |sigma|<=sqrt(30)r<6r without a balance assumption or an h>=X/2 assumption. The exact shortest-vector condition is used correctly when a=0 to obtain u=+N or -N; this implies b is a unit modulo H and C=+H or -H. For a!=0, a is an r-adic unit. Both branches therefore give the claimed public-zero screen c=s modulo H, hence only s=c=1 within the catalog, once per window. C cannot be zero, and the true K=(P-1)(CQ-ac^2) is nonzero because the prime Q cannot divide a product of nonzero integers whose individual magnitudes are below r. These checks validate the controlled linear branch and the zero cleanup.

The purification and root step is legitimate with its charged data. E0 contains r and all nonzero |a| with multiplicity; K0=E0^ceil(log_2 N) has soft-r explicit bits. Purification removes all those prime factors from the surviving local orders. On global collapse the known small-factor product tree, rather than a polylog-bit-annihilator theorem misapplied to K0, supplies the factor branch. Its descent preserves a base nontrivial in both fields and a known annihilating node product; a leaf <=r cannot contain two nontrivial coprime local orders without the paid first-nonunit detector separating them. The product-tree exponent work is soft r.

On the retained branch beta=gamma^E0 and rho_v=gamma^(E0/a_v) satisfy rho_v^a_v=beta with equal large odd local orders. Signed a_v use actual signed exponents. The outside powers are acquired collectively by the inherited product tree; powering separately with each long outside exponent would not be the claimed ledger. Including r ensures rho_v^(r^4) retains its local order. The normalized node is exactly rho_v^K, and its vanishing is equivalent to beta^K for the purified common beta. It need not have the pre-purification beta_in query's exact zero set. Coverage is valid for each supplied unit base directly, so this distinction does not weaken the all-input source.

The fixed-k trace uses one polynomial with coefficients beta^(kc^2) for every quadratic row/window and a second polynomial with coefficient 1 for the linear rows. Descriptor-dependent rho_v points, weights and signed geometric seed sums are paid in soft-r total work. This permits different short row intervals. No multiplier-label table of size r^2 is acquired or needed by the MPE. The O(log N) descriptor/window factor is absorbed by soft notation, rather than treated as a constant. The repeated-k bound remains soft O(rh); the proved formal exponentiation statement is for h<=r, ensuring every denominator is a unit.

The coefficient-one AP row algebra is a separate family. Its linear W coordinate, dense carried interpolant V, rank-r endomorphism exclusion, and adjacent-window boundary ratio are not transferred to the varying-a Gauss family. The endomorphism exclusion only rules out the specified reuse of the quadratic-product doubling law. The boundary ratio is a formal identity whose common collision factors cancel; it cannot serve as a nonunit locator at z=1. The Frobenius identities apply to both families because their scalar nodes lie in F_P and F_Q; the retained numerical diagnostic tests only the coefficient-one AP family.

For one Gauss size window, every (row,c) has at most one local hit since the seed order exceeds 16r^2 and the maximum difference between searched sigma values is 12r. Thus

    0<=mu_P,mu_Q<=r(r-1)<P,Q.

A hypothetical residue U encoding these two counts has gcd(U,N)=N exactly when both counts are zero; a proper gcd gives a factor; gcd 1 means both counts are positive. Under binary restrictions, a positive parent count splits into nonnegative child counts without characteristic wrap. One either obtains a one-sided child and factors, or keeps a child positive in both fields until a global clean leaf is reached. The Gauss source guarantees a hit in the true smaller-factor window; it does not need to guarantee a larger-factor hit in every window. If that window has only one-sided hits, the count query already returns a proper gcd. Testing all O(log N) windows separately therefore suffices conditionally. The combined all-window count has no proved <P bound and is correctly excluded from this inference.

The count interface and character-deficit predecessor remain inherited sufficient reductions. The local bound above sharpens their application; it does not acquire a count algorithm. The final outcome/frontier claims correctly leave both multiplicative and count detection unpaid, followed by executable and Lean bit-complexity integration.

AKS and Grantham primary PDFs were accessed through web extraction only; no new local PDFs or hashes were produced. Exact primary URLs and relevant sections are recorded in `frobenius-traces.md`. The single Frobenius diagnostic's script and JSON output are replayable and are not a coverage/runtime campaign.
