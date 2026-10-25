# Square-LCM smooth/rough certificate and the compact-list rough stage

24 October 2026. Scratch only; no repository edits, examples or backend work. Positive result: the SQUARE of lcm(1,...,m), followed by the already paid order detector, suffices to certify the exact full m-rough part of the smaller field order on the surviving branch. It is not necessary to acquire an exponent containing every possible small-prime power through m³ first. Factored kernel closure and complete short-witness recovery are paid below. The rough branch still has no O(m)-acquired covered exponent collision family, so there is no new whole-input exponent.

## Prior cover and smoothness work read first

Read the journal compact-GAP and product-cover consumers around the entry “compact exponent covers need no prefactored singleton,” the later distributed-order-factor/window attempts, and the preserved reports:

| Source | SHA-256 |
|---|---|
| semiprime-query-continuation-20261022/reports/rough-order-cleaning.md | 2c04b959d680ae3e04eed20c71e6ea3faf2b253b5d2c6b1aa940a28aac8142f9 |
| semiprime-acquisition-checkpoint-20261016/reports/paid-cover-transfer.md | 782c39a8e1eaa5a32b03cfcf2f6f61561aa3595d20c2dbd9cc7deb0ee856f644 |
| /tmp/semiprime-auxiliary-exponent-20261023/static-secret-construction.md | 59d800abcfbffcd003375d028da34b737c60bd0399c3f186a6fe92653a1f8ccc |

The first two paths are relative to /home/dbsanfte/riemann/formal/docs/research-evidence/. The original /tmp group-gap-criterion path is no longer present; its criterion was read in the preserved journal and paid-cover-transfer report rather than assumed from a missing file.

Smooth projection, fully factored exponent trees and prime/semiprime rough-order shape are OLD and credited. Compact GAP input must pay actual box volume, initial exponent bits and selected nonzero difference. Different integer factors covering different prime factors of an order do not imply an individual group collision. Overlapping-window exponent action is not an arbitrary unrelated-center multipoint theorem. The sharper square-LCM self-certificate below is the concrete refinement tested here, not a new discovery of those prerequisites.

## 1. Inputs: coprime preparation is essential

Use N=P Q, distinct odd primes, P<=Q, N<=m⁶ and the actual prepared branch P,Q>16m². The supplied working beta is a unit with odd COPRIME local orders d_P,d_Q>16m². If only odd large orders were initially supplied, first use the existing paid coprime-order preparation; coprimality is not inferred from oddness. This costs soft m or returns a factor.

The smaller order satisfies d_P|P-1<m³. The larger order need not be below m³ and will NOT be silently assigned the smaller-order rough shape. Set C=16m². All bit costs include O(log N)-bit modular multiplication and reductions.

## 2. Acquire and apply the square-LCM exponent once

Sieve primes p<=m and acquire b_p=floor(log_p m) by exact integer multiplication. Let

    K=lcm(1,...,m)=product_(p<=m) p^b_p,
    M=K²=product_(p<=m) p^(2b_p).

The complete prime-power factorization and balanced product tree are acquired. Even the elementary bound log K<=m log m is enough for soft-m bit length and construction; no uncharged prime-counting theorem is needed. Forming M and computing rho=beta^M cost soft(m log N) bits, customarily soft m. This is ONE M-bit exponentiation, not m exponentiations by M.

For comparison, a single K does not supply the smooth-removal certificate used below. The square has a useful self-certifying property that avoids assuming it contains all small-prime powers of d_P.

### Uniform square-LCM lemma

For each prime p<=m, write b=b_p>=1. Since m<p^(b+1)<=p^(2b),

    p^(2b)>m.                                      (1)

Let d be ANY positive integer <m³, and r=d/gcd(d,M). If a prime p<=m survives in r, then v_p(d)>2b, so gcd(d,M) contains p^(2b)>m. Therefore

    r< m².

Consequently

    r>16m²  ==>  r has NO prime factor <=m.         (2)

This is an elementary uniform dichotomy for the actual square-LCM projection. No hidden order value or factorization is computed by the proof, and no smoothness distribution is assumed.

## 3. Every kernel and residual-order branch is paid

First compute g=gcd(rho-1,N).

* Proper g returns a factor.
* If g=N, use the FACTORED exponent M, as follows; no wide-annihilator oracle is needed.
* If g=1, both local rho orders are nontrivial and still odd/coprime.

For g=N retain invariant u^A=1 modulo N, with both local orders of u nontrivial and coprime; initially (u,A)=(beta,M). Split the balanced prime-power leaf product A=A_left*A_right, with coprime children, and compute v=u^A_left. A proper gcd(v-1,N) factors. If gcd=N, retain (u,A_left). If gcd=1, retain (v,A_right). The first branch preserves the same nontrivial coprime orders; the second preserves nontriviality by its gcd test, coprimality by taking order divisors, and v^A_right=1. At a single prime-power leaf, two nontrivial coprime local orders cannot both divide that leaf. Thus a proper factor is reached before that impossible terminal state.

Only one path is followed. Each powering exponent is an acquired subtree product; the summed exponent-bit charge is soft(bit M), including depth and gcds. This is the old factored-kernel idea in a one-path form, not independently powering beta^(M/p^e) for every prime.

On the g=1 branch run the inherited EXACT first-nonunit order detector through C. It costs soft sqrt C=soft m. A proper factor stops. A common order <=C would have to be one by coprimality, contradicting g=1. Therefore the only nonfactor outcome is NoHit certifying BOTH rho orders>C. This closes all small-residual branches, including those in (2), without assuming large projected order.

Let r_P=ord_P(rho). By (2), r_P is m-rough. Also

    c_P=(P-1)/r_P < m/16.                          (3)

Every prime factor of c_P is <m, whereas every prime factor of r_P exceeds m. Hence

    r_P is EXACTLY the full m-rough part of P-1.    (4)

This is stronger than saying it is some unknown rough divisor. Its coindex is an integer, but neither c_P nor r_P is an algorithm input/output. Since r_P<m³, it is a prime or a product of TWO primes >m, counted with multiplicity. A surviving prime r_P is >16m². In the two-factor case each factor is <m²; a repeated factor is allowed. No balance or small-index promise has been imported: (3) was derived from the acquired detector certificate.

The larger rho order remains odd, coprime to r_P and >C, but may retain small-prime powers not completely removed by M, since its original bound can exceed m³. We do not call it m-rough or two-factor.

If the original canonical q interface is required, acquire q=rho^(m²) and run its detector through C. Since r_P is m-rough, powering by m² leaves its order unchanged>C. Thus this extra detector returns a proper factor or certifies BOTH q orders>C; a shared-order-one branch is impossible. Oddness/coprimality and global order>C² hold for rho. The original canonical source and bounded leaf decoder can now be reused with rho, under their proved hypotheses. This is another paid soft-m screen, not an inherited q-order assertion.

## 4. The actual compact O(m) lists and what they cover

Try the explicit short lists

    S={uN:1<=u<=m}, T={v:-m<=v<=m}.

Their group images rho^S,rho^T are acquired in soft m: compute rho^N once, traverse its m powers, and traverse rho powers for the 2m+1 small exponents, including the known inverse. Hulls are separated, so every selected difference uN-v is positive, nonzero and O(log N) bits. Monic product/remainder MPE consumes these lists in soft m and can detect a WHOLE-order collision. Proper gcds factor; a saturated group leaf supplies the nonzero polylog-bit annihilator uN-v for the CURRENT prepared rho, so the unconditional short-annihilator consumer costs soft N^(31/192)<=soft m. It is not applied to a long product or to an unguarded projected base.

What this does NOT prove is coverage. In the two-factor case r_P=lambda_1 lambda_2, each lambda_i<m². For each such prime lambda, the m+1 circular residues 0,N,...,mN modulo lambda have a gap <m; lambda>m and lambda<P<=Q imply N is a unit modulo lambda, so they are distinct. Their difference gives some displayed uN-v divisible by lambda. But the two prime factors may be covered on DIFFERENT pairs, and no displayed pair is proved divisible by the full r_P. For lambda² one pair may carry only one lambda-adic factor. Therefore this O(m)-acquired group-difference test is a valid adaptive branch, not a covered replacement query.

It is tempting to repair this with a small-order-of-ratio test: if one lambda divides uN-v, the P-order of rho^(uN-v) is <=m², so the C detector would factor or yield a short global original-rho annihilator. Such a witness exists in the two-factor branch. However there are Theta(m²) implicit ratios, and each ordinary detector costs soft m; no simultaneous detector on two compact lists has been acquired here. All list values being cheap does not pay this new order predicate.

The old distributed product makes the cost visible:

    K_box=product_(1<=u<=m,-m<=v<=m)(uN-v).

It removes both distinct rough factors or at least one copy of a repeated factor, so the P-order after that action is one or <=m². But K_box has Theta(m²) short leaves and bit length Theta(m² log N); explicitly constructing/applying it costs soft m². The windows around uN are unrelated/disjoint integer factor windows, so the old soft(e+T) overlapping-window action does not turn this into soft m.

All saturation branches of this overbudget action can still be defined without a too-long short-annihilator call: descend its short-leaf product tree. Keep a current large-order coprime base; after a unit gcd step changes that base, rerun the soft-m order detector, factoring if an order has fallen below C, otherwise restoring the invariant. A saturated branch keeps the old base and the corresponding subtree. At a single nonzero O(log N)-bit leaf the short-annihilator theorem applies. Product/exponent-bit work remains soft m², with soft-m detector/recovery overhead along a logarithmic path. This is an old charged distributed-factor route, not a new target-budget cover.

## 5. Concrete rough-prime continuation tested

For a surviving prime r=r_P>16m², (3) says P=c*r+1 with c<m/16 and c divides the known smooth exponent M. This is genuine information, but c and r are both unknown. It does not supply a residue modulus or a selected small coindex as input.

The direct candidate is to search the annihilator rho^r=1 using that form while scanning c. Ordinary group-order search up to m³ costs soft m^(3/2); enumerating c does not shorten that worst horizon because small c, including the fixed even coindices allowed by odd local order, remain possible. A public lower bound c>=C0 would reduce the sufficient horizon to m³/C0, but no such growing lower bound has been derived. The known divisibility c|M alone permits every small smooth c and supplies no missing lower bound.

The alternative known recurrence uses the actual secret S=P+Q. Since r|P-1, S=N+1 modulo r. Thus the old acquired Newton/Charlier families may evaluate integer polynomials at N+1 instead of S, but the exact small-degree fibre is still at N or N+1 modulo r, not a guaranteed public O(m)-label. Prime r and its small coindex do not convert an arbitrary remainder of N modulo r into a short supplied integer. The existing Charlier central cancellation therefore does not create a new covered list from (3).

A further tempting smoothness recursion would try to use N^M-1 to cover the unknown prime r through smoothness of r-1. Besides lacking a uniform smoothness theorem, that action is NOT paid by acquiring M: N^M has Theta(M log N) bits, with M an exponentially large integer in its bit length. Computing N^M modulo N is the wrong exponent ring. Repeated group exponentiation by N costs one step per iteration, not O(log M) iterations without a new recurrence. No such hidden-order fast action is assumed.

Thus the concrete remaining scalar/order predicate is a simultaneous small-order-of-ratio test for the two-factor branch, or a genuinely covered short group-order/exponent family for the rough-prime branch. The square-LCM certificate by itself supplies neither. This is an attempted continuation with an explicit missing operation, not a no-go theorem for N-dependent compact covers.

## 6. Many-base and selected-integer accounting

The projection beta->rho=beta^M is paid ONCE. A structured list of powers of this same beta can be projected cheaply by first projecting the common generator and traversing its actual GAP box, with all starts/step bit lengths charged. Arbitrary unrelated bases a_1,...,a_m cannot be projected for free from rho: independently computing a_i^M costs soft m² by the current powering implementation. No batch-power theorem removes this charge here.

For a general supplied GAP cover, pay its actual parameter-box volumes, not only distinct sumset size, and recover only the selected exponents from their short ordinal labels. If their difference has O(polylog N) bits, the CURRENT rho with its acquired odd large orders admits unconditional 31/192 short-annihilator recovery at a saturated leaf. If a proposed cover uses soft-m-bit offsets/steps and yields a soft-m-bit selected difference instead, that is outside the short decoder: the earlier QRH-dependent wide consumer is a separate conditional import. The factored M kernel needed neither decoder. Every zero integer difference must be excluded by a proved hull/label guard; the lists above have that guard.

## Ledger and exact result

| Operation | Paid work | Outcome |
|---|---:|---|
| Original coprime-order preparation, if needed | soft m | factor or actual prepared beta |
| Sieve K, factorization/tree, M=K² | soft m bits | explicit factored exponent |
| Apply M to ONE beta | soft m | acquired rho |
| Factored global-kernel closure | soft m | proper factor |
| Residual order detector and optional q detector | soft m | factor or certified surviving orders |
| Smaller-prime structural conclusion | proof from certificates | exact full m-rough(P-1), prime/two-factor, coindex<m/16 |
| Short S,T group lists and MPE | soft m | adaptive WHOLE-order collisions only |
| Distributed K_box action | soft m² | covered two-factor reduction, over budget |
| Ordinary remaining rough-prime order search | soft m^(3/2) | not a new compact cover |
| Selected polylog-bit global witness | soft N^(31/192) | unconditional factor for prepared current base |

The square-LCM projection gives a fully charged uniform certificate with all kernel and residual-order branches closed. It does not acquire a uniformly covered O(m)-size exponent family on the surviving prime/two-factor rough branch. The old compact-cover consumer remains conditional on ACTUAL acquired coverage, and the old whole-query scale is unchanged. No small-index, smoothness, prefactored singleton, long-exponent decoder or hidden-field assumption has been inserted.
