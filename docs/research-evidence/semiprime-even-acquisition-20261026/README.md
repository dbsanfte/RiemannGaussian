# Torus annihilator transfer and symmetric singleton residue blocks

26 October 2026. Continuation of the [symmetric-tag investigation](../semiprime-primitive-pair-20261026/README.md). Three investigations, three independent reviews and a primary-agent audit are retained.

**Two constructive results change the available interfaces.** First, an actual short annihilator of the supplied norm-one element can now be consumed in soft K without factoring that exponent. This closes the formerly unresolved N+1 projection branch and supplies coprime large torus orders across the primes. Second, the entire original weighted family can be partitioned into O(sqrt K) symmetric blocks with at most one good hit each. Finite Lambert weights are then admissible without expensive amplitude normalization.

Here K is of order N^(1/6). Neither result acquires the long collision query in soft K. The executed weighted query remains soft K^(5/4), and the full sixth-exponent theorem remains open.

## 1. A norm-one annihilator now leads to a factor

Retain the actual prepared scalar beta and norm-one W. Their local orders exceed 16H, H=K²; beta's orders are odd and coprime across primes. Both prime factors exceed 16H and N<=K^6. Suppose a nonzero short integer M is acquired with the actual global identity W^M=1.

At the split prime S, the norm-one group has order S-1. Thus t=ord_S(W)>16H divides both S-1 and M. Without computing S or t,

    ord_S(beta^M) divides (S-1)/gcd(S-1,M)
       <=(S-1)/t < N/(256H²) <=K²/256 <16H.

Compute beta^M and run the already paid scalar short-order detector through 16H. It must find a factor or an exact common local order. The latter is one, since powers preserve beta's cross-prime coprimality. Hence beta^M=1 globally. The existing scalar annihilator extractor then factors N at its proved soft N^(31/192) cost. It is applied to the original large-order beta, with the actual nonzero M, at most once on a terminating branch.

This is a complete soft-K consumer on the supplied preparation. No factorization of M, hidden order, index estimate or new analytic assumption is needed. The original extractor's asymptotic finite-input convention remains unchanged. A local W-annihilator can also be tested: its norm gives a proper factor or a genuine global identity, because norm-one identity detection is exact even at the split prime.

### The N+1 projection is completely resolved

Let R be nonsplit and S split. The identities

    gcd(R+1,N+1)=gcd(S-1,N+1)=gcd(R+1,S-1)

show that W_new=W^(N+1) has coprime local orders. Actually screen them through 16H. A proper factor terminates. If both projected orders are large, continue. If an exact common order is found, coprimality makes it one, yielding W^(N+1)=1; the new transfer factors this branch.

The surviving W_new has large, odd, K-rough, cross-prime coprime orders. Rebuild pi=beta*W_new, barpi=beta/W_new and q=pi^H, rerun the coupled unit screen, and reacquire the native roots. The total additional cost is soft K. The old numeric roots and screen are not inherited after changing W.

The transfer also closes the zero-scalar-label case for any actual short relation beta^u W^v=1 with (u,v) nonzero. If u is nonzero, take the norm and use the scalar extractor. Otherwise use the torus transfer. Equivalently, every nonliteral short global relation pi^A barpi^B=1 has a paid factor decoder. Additive zeros and unlocalized product zeros are not such certificates.

See [partial-order-supplier.md](partial-order-supplier.md) and the [original-source review](review-torus-transfer.md). Its partial-factor and cyclotomic discussions are secondary; they are not unresolved branches of the new native transfer.

## 2. Keep every row while preventing residue cancellation

Use the ORIGINAL bank with one deterministic Gauss row per unit colour j modulo K=2*3^e. Opposite colours share the same Gauss choice. Put

    n=3^ceil(e/2), L=K/(2n)=3^floor(e/2),
    block(j)=floor(min(j,K-j)/n).

There are L=O(sqrt K) blocks, each containing phi(n)/2 complete opposite-colour pairs. For any public unit square u modulo n, each block contains exactly one pair with j²=u: the two residue offsets r and n-r have opposite parity, so exactly one gives an odd representative in that block.

Every good-bin hit has j=R modulo n, including axes and nonprimitive rows. It therefore belongs to the block's unique pair with square tag R². Both signs cannot hit because 2R is a unit modulo n, and each row has at most one clock hit. Consequently every block has at most ONE good-field hit, and coverage guarantees that some block hits.

This partition is acquired by direct bucketing in soft K and preserves sign symmetry. It does not apply to an enlarged catalogue with several rows of the same colour.

## 3. Finite Lambert residues need no row normalization on these blocks

For the actual normalized row T_j, put rho=q^-1 and G(z)=(z;rho)_h. The exact finite identity is

    sum_(i<h) c_i/(1-z*rho^i)=(rho;rho)_(h-1)/G(z),
    c_i=(-1)^i*rho^(i(i+1)/2)*[h-1 choose i]_rho.

Every c_i is a certified unit. With the original additive regulator, substitute z=T_j/(1+delta) and divide by 1+delta. A hitting row then contributes the simple-pole residue c_I, while a nonhit contributes zero. This finite partial-fraction mechanism is proved directly, with [Gu–Prodinger](https://www.finanz.math.tugraz.at/~prodinger/Guo-Rice.pdf) providing primary q-series context; no infinite Lambert tail is discarded.

Sum these rational expressions over each symmetric block, both unweighted and marked by the canonical integer w_j=[j²]_n. Its residue pair is either (0,0) or (A,A*[R²]_n) at the good field, with A nonzero. The singleton proof prevents cancellation, so neither a long clock-cofactor normalizer nor a growing moment/Hasse search is needed.

After acquiring the block pairs, norm-test all denominators. A proper gcd factors; a saturated norm permits declining the block. Select the first unit denominator PER BIN, validate its ratio, and run the existing two-root/HH consumer once. In the correct bin a unit block must hit and a hitting block cannot be lost to a saturated-norm decline. Wrong-bin failures continue to later bins. The full recovery bill stays soft K.

All block rational inputs have degree O(sqrt K), total degree O(K), and are acquired in soft K by product trees. The first O(sqrt K) common functional moments are also paid. These short moments do not by themselves evaluate the singular rational functions. The h-entry clock-weight array is not materialized for free.

See [polar-reciprocity.md](polar-reciprocity.md), its [review](review-polar-reciprocity.md), [even-recurrence.md](even-recurrence.md) and its [review](review-even-recurrence.md).

## 4. What the executed recurrence still costs

An exact finite Askey-Wilson lowering identity was executed with the actual acquired square root rho^(1/2)=pi^(-H/2). Its two neighbouring values retain the desired long product as their common factor. The identity pays neither that factor nor its pole. This is a scoped calculation, not a lower bound on all recurrence algorithms.

The complete shared row-product engine, extended by constant-depth jets, does acquire the new block residues at soft K^(5/4). The first derivative of a globally zero row is a unit because each component has at most one clock hit. Evaluating blocks separately instead costs soft K^(3/2). Thus fewer outputs and simpler amplitudes have not yet lowered the acquisition exponent.

The next substantive operation is simultaneous finite-Lambert pole evaluation on these acquired small symmetric blocks, or a collision search exploiting the now-complete coprime torus preparation. Both must retain the full family and pay every changed-base operation. The new annihilator transfer supplies recovery from actual multiplicative certificates; it does not supply those certificates.

[Sources](sources.json), [review record](review.json) and [manifest](manifest.json) retain the audit. All 1010 prior protected files, both document prefixes and 23 concurrent files are preserved. Paper proofs and documentation only: no factoring implementation, numerical campaign, Lean changes, public assets, commit or push.
