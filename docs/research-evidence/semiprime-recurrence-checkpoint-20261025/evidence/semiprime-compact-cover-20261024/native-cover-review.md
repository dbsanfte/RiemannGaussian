# Independent native inverse-cover combination review

24 October 2026. Reviewed exact bytes of /tmp/semiprime-compact-cover-20261024/native-cover-combination.md.

SHA-256: `72a8f581367f249bb764032fe9e249c3e7ae5ecc7021a2955ac11514a134fefe`.

Verdict: **PASS. No required fixes.** Read-only scope, arithmetic, gcd/exception and fallback audit; no source changes, examples or backend work.

## Native phase and exceptions

The input retains the original actual centered rows and prepared beta orders. The identity beta^N=beta^(P+Q-1) follows from Euler's exponent phi(N); the factor-sum bound makes the indicated representative small relative to the global order, but does not acquire its logarithm. The report distinguishes these correctly.

For A=1, the tag satisfies j²=N modulo m, so j*=j, B=1, rho=0 and the exact phase kappa is zero. At most two tags satisfy this condition. Their fused zero would be an integer tautology, so the original single-row queries are essential and correctly paid. The separate j=1 query costs one more soft-m call. If all these original row queries are unit, the actual own tag cannot have been among them by the original bounded-index coverage.

On every regular retained row, 1<=rho<=m-2<P,Q, so gcd(rho,N)=1 is certified; a proper computed gcd may safely terminate, and saturation is impossible there. The exceptions are routed rather than deleted. The retained own tag has A!=1,j!=1 and the actual nonzero kappa residue, as used.

The full-target ratio correctly includes beta^[(N-1)(B-1)] in addition to beta^(m kappa). No variable-power common scale is silently left unchanged.

## Exact fusion and its weighted-Fermat collapse

Both integer indices are legitimate at their own tags, but only the smaller factor's I is assigned the short native range. Computing H*(B I-I*) gives

    (AB-1)P+B ell_j-ell_j*.

The phase identity gives B ell_j-ell_j*=m*(kappa-rho), so after dividing by m,

    m*(B I-I*)=rho*(P-1)+kappa.

This checks the m/H factors in equation (1). Multiplying it by m and applying Fermat at P proves equation (2), without assuming that the complementary row is a P-local own row or that I* is short.

The public csharp is integral by kappa=rho*(1-j) modulo m. Substituting P=j+mh into the integer relation yields B I-I*=rho*h+csharp. Thus all targets/bases in equation (3) are actually acquired from public metadata, and the own-tag equality is valid.

Finally m*kappa-H*csharp=-m*rho*(j-1) exactly, so a transformed leaf differs by a known unit/sign from

    beta^[m*rho*(j+mh-1)]-1.

This verifies the decisive cancellation: the relation is a weighted ordinary candidate-factor/Fermat ray. It does not recover a new short seed or a two-list common-base cover. The report correctly stops at this exact identity rather than deriving a generic impossibility claim from it.

## Changed leaf recovery and grouping costs

Restricting x=j+mh to 16H<x<=W=floor(sqrt N) excludes x=1 and gives positive nonzero K=m*rho*(x-1). With rho<m and W<=m³, K<m⁵ and its bit length is O(log N). Proper gcds factor. A saturated leaf is a SHORT original-beta annihilator, so the pinned unconditional 31/192 consumer applies to the prepared beta. The changed exponent is not automatically an original bounded-sum leaf, and the report explicitly avoids that wrong decoder.

The candidate h interval has common lower bound 16m and upper bound taking at most two adjacent values across j. Therefore grouping by the actual rho and h length/origin is lawful after ordinary known starting-power scaling. Per group the actual acquired target polynomial degree is J_rho and its horizon is <=m²; fixed-base monic blocking costs soft(J_rho+sqrt(J_rho L_rho)). Summing over at most O(m) different bases gives the stated soft-m² upper bound. Even one common-base implementation would retain the old soft-m^(3/2) interaction. These are charges of the displayed implementation, with no claim about a lower bound on the number of distinct rho or on other algorithms.

No group value inverse is required at an actual collision, and repeat targets are allowed by monic MPE. The short exception queries and all transformed leaf branches are included.

## Complete fallback: actual coverage, hulls and saturation

Let Dcap=W-1, b=ceil sqrt(Dcap), and K=ceil(Dcap/b). The differences between exponents k*b (1<=k<=K) and i (0<=i<b) cover every integer 1,...,K*b, in contiguous blocks. Since ord_P(beta)<=P-1<=W-1, this includes at least one complete local order. Hull separation makes every cross difference strictly positive.

Both lists and the monic product/remainder computation are acquired in soft b, with actual volume Theta(b), not the number of implicit pairs. Their selected differences are at most K*b<W+b. On the stated hard branch W+b<256m⁴<ord_N(beta), so no selected GLOBAL equality can occur. A saturated row product may still occur from different local leaves; retained tree descent then finds a proper leaf gcd. It is correct not to call the saturated aggregate itself a factor. No wide-annihilator or unknown-order input is needed for this fallback.

The full bound is soft sqrt W=soft N^(1/4), at most the soft m^(3/2) worst scale, including all list powers, labels, gcds and monic arithmetic. This is a genuinely complete covered algorithm at the OLD volume; it is not soft m and is not asserted to improve the separate stronger factoring benchmark.

## Final scope

The report proves a covered transformed family and its fully acquired metadata, but its exact arithmetic simplification leaves the old candidate-factor coordinate and varying bases. It preserves exception coverage and valid bounded-bit witness recovery, and gives a complete honest-volume fallback. No O(m)-volume GAP cover, generic lower bound, or all-semiprime sixth-rate theorem is inferred. The exact reviewed bytes pass.
