# Independent review: order cleaning and shared coindex roots

2026-10-22. Reviewed `rough-order-cleaning.md`, `shared-coindex-roots.md`, and `strong-order-route.md` against the existing `semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md`. Verdict: the three factor-or-prepared-family constructions are valid, conditional on exactly the existing paid setup/detector/extractor theorems stated below. They do not close the retained factoring branch. No examples or finite certificates are used in this review.

## 1. Exact prerequisites and branch closure

The required starting data are a public unit beta with odd local orders r_P,r_Q> B=16m^2, gcd(r_P,r_Q)=1, and N=PQ<=m^6 with m=Theta(N^(1/6)). The existing setup supplies these or a factor; its separate q-order promise is restored after each cleaning rather than presumed invariant under powering. The exact first-nonunit detector must have its stated three-way contract, including an EXACT COMMON local order on its saturated outcome, and soft-O(m) BIT cost through B. A generic small-order or global-order detector would not suffice.

The short A-cleaning additionally depends on the existing unbalanced short-annihilator extractor for a supplied nonzero polylog-bit annihilator of the ORIGINAL pre-cleaning beta, whose local orders are odd and>B. It does not invoke that extractor on a cleaned base of possibly tiny order. Its exponent K=|A|^ceil(log2 N) has polylog bitlength for a polylog-bit A; its saturated outcome beta^K=1 is a verified global annihilator. Thus this call fits the source theorem exactly. No Burgess extractor is needed for the long smooth-cleaning exponent M.

On every powered base, local orders divide the original respective orders and remain coprime. Thus the detector's common-order case is necessarily order 1. After retaining both orders>B, a common order of b^(m^2) would again be 1 and would force each order of b to divide m^2, an impossibility. The restored base therefore has the full original q-interface, and the canonical native coverage and bounded-leaf recovery apply to that newly acquired base. This relies on their arbitrary-prepared-base statement, not preservation of old target values.

## 2. Smooth cleaning and saturated quotient tree

For each prime ell<=H take f_ell=ell^e with f_ell>=N, and M=product f_ell. Since each original order is<N, M contains its complete ell-primary part. The order after raising to M is exactly its >H-rough part.

At a product-tree node with subtree product A, maintain v=beta^(M/A). If A=A_left A_right, powering v by A_right and A_left produces the two correct child states. The root state is beta, not beta^M. Leaves give beta^(M/f_ell).

If beta^M=1, both local orders divide M. Choose any ell|r_P; by coprimality ell does not divide r_Q. Therefore r_Q|M/f_ell whereas r_P does not divide M/f_ell. The corresponding gcd is exactly Q. Scanning all public leaves acquires it without knowing ell, and repeated factors in r_P do not affect this proof. This is a valid closure of saturation; no factorization of a hidden order is used.

Let S=bitlength(M) and n be the number of leaves. At every depth, the sum of sibling-exponent bitlengths is O(S+n); binary modular exponentiation therefore costs O((S+n) M_int(log N)) up to logarithmic factors per depth. All O(log n) depths, gcds, explicit product-tree storage, and sieve/power construction are soft-O(m) bits because S=O(H(log N+log H)), H=O(m polylog N). Modular powering is never treated as constant time. This ledger also applies to the factorial variant after its prime-power factors are acquired.

The smaller-prime order has at most two prime factors counted with multiplicity: r<P<=m^3 while each retained prime is>H>=m. On the larger side Q<N/(16m^2)<=m^4/16 permits at most three. The small coindex inequality is strict: (P-1)/r<m/16. None of these numerical hidden quantities is output.

## 3. Simultaneous factorial roots and uniqueness

Put L=m!, T=ceil(log2 N), M=L^T and w=beta_0^(L^(T-1)). With public leaves 1,...,m, the complement tree rooted at w outputs b_t=w^(L/t)=beta_0^(M/t), so b_t^t=b exactly. The initial w power costs soft-O(m) bits, since its exponent has O(m log m log N) bits. The tree itself has per-depth exponent-bit sum O(log L+m), O(log m) depths, and m residue outputs. Thus the WHOLE family, including its input exponent/tree and outputs, has soft-O(m) bit cost.

For every ell<=m, v_ell(M/t)>= (T-1)v_ell(L)>=T-1. Both hidden primes exceed16m^2, so every original local order is<N/(16m^2). In particular its ell-adic valuation is<log2 N-4<T-1. Hence division by t does not leave any small-primary part behind. For ell>m, neither M nor t has an ell factor. Each b_t therefore has exactly the same m-rough local order r' as b, and belongs to the same local cyclic subgroup (the field multiplicative group is cyclic and has a unique subgroup of each order). Since gcd(t,r')=1, its t-th power map is an automorphism: b_t is genuinely the unique root inside this subgroup. This is not uniqueness in the full field.

A useful proof clarification, recommended in the source note: derive pairwise separation by writing b_t=b^(t^{-1} mod r') inside this subgroup. Then b_s=b_t iff s^{-1}=t^{-1} mod r', equivalently r'|(s-t). This avoids informal cancellation of the fractional-looking exponent M(s-t)/(st) against the original, partly smooth order. The stated conclusion is correct. Likewise b_t=b^k iff r'|(kt-1). Since r'>16m^2, distinct s,t<=m never collide, and k,t<=m allow only kt=1. These are simultaneous statements at both local primes, so the differences are units modulo N.

The assertion that X^t_P=b has exactly t_P full-field roots at the true integer coindex t_P=(P-1)/r'_P is also correct: t_P divides P-1 and the constructed b_t_P supplies one root, so its root set is a torsor for the kernel of size gcd(t_P,P-1)=t_P. The constructor acquires just the unique rough-subgroup root, not the other torsion branches. It does not select t_P.

## 4. Combined cleaning and scope

For A=N-1, eliminating all shared prime-primary parts gives gcd(r'_P,N-1)=1. As r'_P|P-1, reduction of N-1 modulo r'_P gives Q-1; hence gcd(r'_P,Q-1)=1. Subsequent smooth cleaning only divides r'_P and preserves this property. The symmetric assertion holds at Q. All acquired exponents have the claimed bit budgets, and only a constant number of soft-m detectors/extractors is used.

No correction to the algorithms is necessary. The sole recommended edit is the subgroup-inverse proof of pairwise root separation above. The constructions are usable unconditional factor-or-family reductions relative to the explicitly inherited paid theorems. They do not acquire a numerical rough order, identify the hidden coindex, supply other full-field torsion roots, or evaluate the original long collision query. No all-input sixth-rate conclusion follows yet.

## 5. Provenance correction: revalidation, not a new acquisition advance

The authoritative checkpoint `semiprime-acquisition-checkpoint-20261016/sources/constructive-frontier-index.json`, entry “Smooth projection and shared roots” (historical journal pin 4850), already records E=(m!)^A, A=O(log N), smooth-part projection, factor recovery on collapse, and outside-product roots for small j^2 as PAID. Its explicit missing input is a constructor covering large rough local orders. The current journal near line 4850 retains the factorial projection/roughness mechanism; near 5626 it documents staged collapse recovery using coprime local periods. The journal near 2506 already records `smaller_factor_group_budget` and `rough_order_prime_count_le_two` and the prime/semiprime rough-order reduction, without claiming to read the hidden order.

Accordingly the current smooth cleaning, complementary exponent tree, shared roots, and prime/semiprime surviving shape must be classified as revalidation/reassembly of inherited paid mechanisms. The proofs above certify correctness and their compatibility with the newer unbalanced prepared contract. They do NOT establish a fresh substantive acquisition advance. The direct high-power A=N-1 cleaning provides the stated additional normalization if not already separately pinned, but it too leaves the large rough-order acquisition problem unchanged. The uniqueness/separation discussion clarifies precisely why the reacquired roots alone do not furnish the missing relation. No novelty should be inferred from the earlier words “constructions are usable” or from the source reports’ descriptions of a “new optional” step.
