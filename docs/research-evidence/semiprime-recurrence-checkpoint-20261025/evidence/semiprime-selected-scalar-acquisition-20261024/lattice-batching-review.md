# Independent review: product-fused residue lattices

24 October 2026. **PASS** after the author clarified the scheduled-budget scope. No mathematical correction was required.

Final exact source: /tmp/semiprime-selected-scalar-acquisition-20261024/lattice-batching.md SHA256 `e7e9582f310c0d1dad8b59bf15d52b485a4cc92926e234b206bd1d6899f0a293`.

Primary independently checked: Alexander May, *New RSA Vulnerabilities Using Lattice Reduction Methods* (2003), Section3.2 Theorem6 and its all-roots validation discussion. Cached /tmp/semiprime-partial-tag-20261024/sources/may-2003.pdf SHA256 `a6f8075b93c32a6a687ae83dde2698a98739b069a54c2cb644b75418ffc54332`; https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235 . The theorem's actual bound is one-half N^(beta^2/delta-epsilon), with polynomial runtime in log N, delta and 1/epsilon.

## Cover, input and root radius

The dyadic bins cover every possible smaller prime. The public common interval [floor(B/m)-1,floor(U/m)], clipped at zero, contains every s=(P-c)/m with canonical c in[0,m) and P in the bin. Its length is O(1+B/m). Partitioning it into actual blocks with offsets S supplies Z0=s-S in the claimed nonnegative radius.

Each group polynomial prod_c(Z+S+[m^-1 c]_N) is monic of actual degree delta<=g. Coefficients are genuinely acquired by product trees and canonical integer lifting; no hidden factor or root is input. At the correct c, its corresponding factor vanishes modulo P, so the product meets May's unknown-divisor promise with P>=B>=N^(b/n).

For epsilon=1/n, N^(-epsilon)>=1/2. The exact-root definition X_g=max(1,floor(N^(b^2/(n^2*g))/16)) is therefore safely below the theorem's radius for every delta<=g whenever X_g>=2. Integer powers and roots have polynomial-logarithmic sizes when g is polylogarithmic; no floating-point bound is assumed. The X_g=1 branch explicitly enumerates and validates actual candidates. All roots produced by lattice extraction are checked against every residue in the group, and only verified proper gcds are accepted. False groups have bounded execution and cannot cause a false factor.

## Group cost and scope

The displayed call count O(ceil(m/g)*(1+B/(mX_g))) follows from the acquired group count and common block interval. All degree-g coefficient arrays, lattice dimensions, root extraction and g residue validations remain payable. May's polynomial(delta,1/epsilon) cost is soft-one only for g bounded by a fixed power of log N; there is no uncharged single-LLL claim for polynomial-sized groups.

In a balanced dyadic bin beta=1/2+O(1/log N), X_g is within a constant factor of N^(1/(4g)) whenever the nontrivial radius branch applies. The displayed scheduled full-search expression (m/g)+N^(1/2-1/(4g))/g is therefore the correct exponent/rounding ledger up to the explicitly suppressed polynomial logarithms. For g=1 it reproduces the all-residue budget soft(m+N^(1/4)); fixed g>=2 worsens its second exponent. Polylogarithmic grouping does not reverse this comparison, and larger g also loses the soft-one lattice-call budget.

The author explicitly amended the final source to compare the SCHEDULED full-catalog/full-block search before early exit. It does not assert an Omega runtime for actual semiprimes: an encountered verified factor can terminate sooner. Nor is it a lower bound on different shared-lattice constructions or a statement that the restricted native catalog has full density.

## Native square and translation

The local relation c_local=t^2/a mod r^2 has no acquired c_local. Keeping it as a free residue gives no restriction on t in the tested construction; knowing its bounded lift is not equated with knowing that residue. This is correctly scoped to insertion into this explicit product-batched search.

For cross-class reuse, the source tracks the actual integer translation representative of m^-1(c-c') modulo N and the block-start change. Modular equality alone does not bound that translation by the small-root radius. A norm certificate after translation must cover the enlarged interval or be reproved with an acquired new basis; neither is supplied by the class anchors/q carries. The report makes no general impossibility claim about future lattice sharing.

The complete residue-assisted decoder remains valid, but this fused search does not acquire the coarse native residue or improve the whole query. Existing fifth-rate fallback and original restriction/verification scopes are preserved. No source/shared edits or numerical experiments were performed by this reviewer.
