# Independent audit: torus annihilator to licensed scalar recovery

26 October 2026. Priority original-source and arithmetic review. No tests, code or repository edits. **PASS.** This resolves the previously explicit W^(N+1)=1 branch without factoring N+1 or its surviving cofactor. It is a preparation/decoder improvement, not a soft-K collision-query evaluator.

## 1. Original contracts actually checked

Read [uniform-setup-and-query-interface.md §§1–4](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md), SHA256 `4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`, and [unbalanced-extractor.md §§1–6](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md), SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.

The first supplies original scalar beta with both local orders odd, coprime across primes, and greater than 16H. Its actual monic first-nonunit detector through cap 16H costs soft K. Importantly, the extractor's §2 independently verifies that ONE local order at most the cap forces a hit; no upper bound on the other order is needed. Its first nonunit exponent yields a proper factor or an EXACT common order, not an arbitrary common multiple. Repeated nodes and zero divisors require no point-difference inversions.

The second accepts any nonzero polylog-bit GLOBAL annihilator of a specified scalar unit with both odd local orders greater than 16H. It requires no exponent factorization, balance, small coindex, numerical order or cross-prime coprimality. Cost is soft N^(31/192), below soft K. Its original unconditional analytic import and explicitly defined asymptotic finite-input fallback remain unchanged. The pure-K preparation report correctly retains these contracts for the actually supplied original beta.

## 2. Transfer theorem, including all inequalities

Assume native N=PQ<=K^6, H=K², P,Q>16H. Let W be the actually supplied norm-one point with both local orders greater than 16H. Let M be an ACTUAL supplied nonzero O(log N)-bit integer with W^M=1 globally in the quadratic algebra. Replace M by |M| if negative; the identity is unchanged because W is a unit. No factorization of M is required.

At the unique split prime S, its norm-one group is cyclic of order S-1. Put t=ord_S(W)>16H. Both t|(S-1) and t|M. Set b=beta^M. If u=ord_S(beta), then

    ord_S(b)=u/gcd(u,M)
      divides (S-1)/gcd(S-1,M)
      <= (S-1)/t
      < S/(16H)
      = N/(16H*(N/S))
      < N/(256H²)
      <= K²/256 <16H.                            (1)

The divisor assertion follows prime-by-prime from u|(S-1); it does not incorrectly assert that t divides u or gcd(u,M). The lower bound on the OTHER prime N/S is what gives the strict second inequality. This works with either ordering of the split/nonsplit primes.

Actually compute b and run the original scalar detector through 16H. By (1), NoHit is impossible. A proper gcd factors. Otherwise its first saturated exponent gives equal exact local orders of b. These orders divide the corresponding original beta orders and hence remain coprime across primes. Equality therefore forces both to be ONE. Thus b=1 globally, and the known nonzero integer M is now a valid global annihilator of the ORIGINAL beta.

Invoke the pinned unbalanced extractor on beta,M. All its premises concern beta, not the now-small-order b, so no large-order premise is lost. This call returns a factor, at most once on a terminating branch. Total cost is soft(K+N^(31/192))=soft K, including exponent reads, powering and the actual detector. The argument works for any fixed polylogarithmic bit bound allowed by that source, although the present supplied labels have O(log N) bits.

Norm-one identity detection may be done by coordinates directly. Its norm-zero criterion is also sound at a split prime: a norm-one pair is (w,w^{-1}), so Norm(W^M-1)=0 iff w=1, which forces the WHOLE pair to be one. A norm statement about an arbitrary non-norm-one torus expression would not have this equivalence. The theorem above assumes/validates an actual global point identity, not an unrelated additive zero.

## 3. N+1 projection is now completely paid

Let R be nonsplit and S split, and put A=R+1, B=S-1, g=gcd(A,B). The elementary congruences N+1=RS+1=-B modulo A and N+1=A modulo B give

    gcd(A,N+1)=gcd(B,N+1)=g.

For V=W^(N+1), its local orders divide A/g and B/g, respectively: the same divisor-quotient argument used in (1) justifies this even if W is not a generator. Those two group quotients are coprime. V remains odd and K-rough under powering.

Actually execute the native norm-one first-nonunit screen through 16H. Proper factors terminate. NoHit certifies both new local orders large, now also coprime. A first saturated identity gives equal exact projected orders, hence one. If the implementation screens V^H, roughness makes H-power injective and gives the same conclusion V=1. The exceptional branch is therefore the ACTUAL short torus annihilator W^(N+1)=1; §2 now factors it in soft K.

Consequently this projection returns a factor or a new norm-one point with odd, rough, coprime local orders greater than 16H. The old partial-factor classification of N+1 is no longer needed to close this branch. No factorization of N+1, numerical g or essential order prime is acquired or assumed. If the new point replaces W in a coupled input, rebuild pi/barpi/q and rerun the coupled q-unit screen: old mixed-base certificates are not automatically inherited merely because the new local order promises hold.

## 4. Corollary: every nontrivial short multiplicative two-coordinate relation is decodable

Suppose an ACTUAL global identity is supplied with short integer labels

    beta^u * W^v=1, (u,v)!=(0,0).

Taking the quadratic norm gives beta^(2u)=1. If u!=0, the original scalar extractor applies directly to the nonzero known exponent 2u, without factoring it. If u=0, then v!=0 and the actual identity W^v=1 is handled by the transfer theorem. Signed labels are replaced by absolute exponents only on their respective terminating annihilator branch.

Equivalently, for pi=beta W and barpi=beta/W, a global relation

    pi^A * barpi^B=1, (A,B)!=(0,0)

has u=A+B, v=A-B, which cannot both be zero over the integers unless A=B=0. Thus zero scalar-norm label A+B=0 is NO LONGER an undecoded exception when the other torus label is nonzero. Literal relations where both labels vanish remain excluded. This is exact multiplicative provenance: it does not license an additive observable's zero, an aggregate product zero without localization, or a local identity as a global annihilator.

All corollary branches cost soft K under the same supplied preparation, and at most one scalar extractor is used on a terminating branch. This strengthens the legal leaf decoder and preparation, not acquisition of the leaf or of the whole long query.

**Disposition:** accept the torus-annihilator transfer, the fully resolved N+1 gate and the two-coordinate short-label corollary. Original detector and extractor hypotheses are met exactly; no factorization or new analytic theorem is hidden.
