# Symmetric supplier audit for a single-discriminant, all-factor-bin design

24 October 2026. **PASS for the supplier interface stated here.** The actual scalar, rough-cleaning, torus and coupled-seed proofs supply their guarantees at BOTH primes. None requires the nonsplit prime to be the smaller factor. Consequently an all-factor-bin construction that correctly covers whichever prime is nonsplit need not import the old QRH orientation palette. This audit does not establish that new row construction's lattice coverage, signed horizon or decoder; those are a separate proof obligation.

## Exact sources read

- Original scalar setup, `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md`: `4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`.
- Torus supplier, `/tmp/semiprime-quadratic-ideal-20261024/torus-order-supplier.md`: `1f3033cc85c1b6798a188daa7b7c32d702b87d2cb3401e3e1f1afe6cb3a4e9bc`.
- Rough torus extension, `/tmp/semiprime-large-order-recurrence-20261024/rough-torus-working.md`: `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda`.
- Actually performed scalar rough cleaning, first section of `/tmp/semiprime-rough-block-composition-20261024/rough-index-cancellation.md`: `283cb2dd6b39f1c84aa62e488703bc2f68a89e3fda2d6620aa14a59dc5236da0`.
- Single-D0 discovery is Sections1–2 of `/tmp/semiprime-unique-acquisition-20261024/orientation-palette.md`: `97db9cf0004dac3ec2c6c9cc341b27531fb90c51d5f6739e6b121c6bc4e20fbf`. The later QRH flip palette is NOT imported.
- The original coupled-seed norm proof is Section4 of `/tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md`: `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`; changed-W and changed-beta reruns are expressly required in the rough sources above.

## 1. Single negative discriminant and actual public scale

If N=3 mod4, D0=-4 has Jacobi(D0,N)=-1. If N=1 mod4, gcd/Jacobi scan through ceil(N^(5/32)) finds a unit Jacobi-minus a0 asymptotically; factor that PUBLIC small integer and choose one prime ell dividing it with Jacobi(ell,N)=-1. Use D0=-ell for ell=3 mod4, -4ell for ell=1 mod4, and -8 for ell=2. The result is negative fundamental, has known conductor c0<=4ceil(N^(5/32)), and has opposite Legendre signs at the two hidden primes.

This uses the unconditional composite-cubefree-modulus bound in Lau–Wu Theorem1, not the QRH least-prime-nonresidue import. Primary:
https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf
The already pinned PDF `/tmp/semiprime-unique-acquisition-20261024/sources/lau-wu-2007.pdf`, SHA256 `4cc9dba73064795de434d6b42baca0743347313b6a242f5439c9ed979ddd4368`, was reread at printed pp1–2. It bounds the least value outside{0,1} for every nonprincipal character modulo cubefree q by O_epsilon(q^(1/(4sqrt(e))+epsilon)); choose strict exponent slack below5/32. N=PQ is cubefree and its Jacobi character is nonprincipal. Scanning and public trial factorization cost soft N^(5/32) and soft N^(5/64), respectively, inside the sixth-rate budget.

Retain the sources' actual finite convention: the explicit scan cutoff and scale guards may fail on finitely many inputs; defined verified fallback handles them. No numerical Burgess constant or recognized effective threshold is asserted. This analytic input is unconditional; the finite-exception convention is not a new conditional hypothesis.

For K0=ceil(N^(1/6)), the fixed supplier k=2c0*3^e, least e>=3 with k>=K0, has k<3K0 under guard54c0<=K0. This guard eventually holds by exponent slack1/96. All factors of k are known, c0|k/2 and |D0|<=k/2. Before any supplier needs it, run the actual integer small-factor prefix through16k² (or the paid common16(3K0)² prefix). This costs soft k. Factor or certify BOTH primes>16H, H=k². N<=k^6 is automatic. No prefix through H² or recognition of the nonsplit side is required.

## 2. Both scalar orders and both torus orders are supplied

The original scalar setup explicitly removes balance. It returns a factor or beta with BOTH local orders odd, coprime and>16H. Its proof orders P<Q only for a factor-return branch using a known common order and the smaller prime's elementary upper bound; this does not impose an orientation condition on its successful output. Its N-1 projection, exact common-order-one branch and general unbalanced annihilator consumer also do not mention the discriminant's Legendre signs.

The actually executed smooth killing in rough-index-cancellation.md preserves coprimality and makes BOTH beta orders k-rough. If its short-order screen produces a common projected order, coprimality makes it1; the fully factored wide-exponent extraction then factors, because equal raw orders contradict the two old coprime large orders. No wide exponent is passed to a short-annihilator decoder.

The torus and rough extension are symmetric in the local signs epsilon_p. The local norm-one group has order p-epsilon_p for either prime. The Cayley denominators a²+|D0| are<16H, and pairwise differences are units at BOTH primes under the prefix. The2M+1 palette avoids the two M-kernels by counting, without choosing which is split. Norm(q_W^n-1)=0 tests WHOLE local identity even on a split side. Smooth killing, complementary exponent splitting, and common raw-order extraction handle both primes identically.

The AP escape's use of the smaller factor is also orientation independent: its acquired d divides BOTH p-epsilon_p, so the smaller factor lies in one of di+1 or di-1 regardless of its sign. The search through sqrt N has O(sqrt N/d+1) terms; d>=k and N<=k^6 give baby size O(k). If d<k, the common-kernel modulus grows by at least two. Thus both local rough W orders>16H are actually acquired in soft k, or a factor is returned. Large 3-adic valuation in the public k does not violate any of these proofs.

## 3. Coupled seed and the possibly LARGER nonsplit prime

Let p* be the unknown nonsplit prime, with no size ordering imposed. The scalar order r_beta divides p*-1; the norm-one torus order r_W divides p*+1. Both are odd, so gcd(r_beta,r_W)=1. Both exceed16H, hence

    ord_(p*)(pi)=r_beta*r_W>256H², pi=beta W.

Retaining the proved k-rough cleaning makes H powering injective on each generated local group; therefore ord_(p*)(pi^H) has the same large product. This reasoning works verbatim when p* is the LARGER prime. It never uses p*<=k³ or a smaller-nonsplit orientation.

RERUN the actual coupled q=(beta W)^H screen through16H after changing either base or k. At p* a zero norm is a field equality q^n=1, excluded by the beta norm bound (or the stronger product bound). Any split-side nonunit therefore returns a proper factor; otherwise the actual1-q^n are units globally for1<=n<=16H. Scalar/torus order certificates are not silently substituted for this coupled screen. Every call costs soft k with its explicit cap.

## Consequence and limits

One unconditional Jacobi-minus D0 thus supplies an unrecognized nonsplit prime, BOTH rough bases and the actual coupled unit interface at the target scale. If the new signed-weighted construction covers ALL factor-size bins16H<p<N/(16H), it will contain the bin for that nonsplit prime whether it is smaller or larger. QRH was used only to force the old smaller-prime orientation; that requirement is absent from this supplier interface. This conclusion is conditional on the NEW all-bin coverage/decoder proof, not a substitute for it.

No claim is made here that the old smaller-prime native row cover or factor-sum decoder automatically transfers to larger p. In particular the signed row horizon, bounds for every tested leaf, zero exponent handling, and a proper quadratic or general-annihilator consumer must be proved by the new construction. No source/shared file was edited; only this scratch audit was written.
