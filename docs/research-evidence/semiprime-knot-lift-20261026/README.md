# A target-scale Frobenius screen and native skein recovery

26 October 2026. **Positive result: a complete soft O(k) factor-or-interface prepass.** It handles a specified cross-prime order case on every valid prepared input; otherwise it strengthens the continuing native contract. The worst-case long collision query and guaranteed all-semiprime sixth-exponent factoring remain open.

## The constructive advance

Let N=P Q, P<Q, N<=k^6, and let the acquired native clock q have local orders r_P,r_Q>16k^2. Set

    A=16k^2+1, B=floor(N/A^2), w=q^N,
    Z=product_(j=1)^B (w^j-1) mod N.

The [Frobenius screen](frobenius-screen.md) proves exactly

    gcd(Z,N)=Q  if P divides r_Q,
    gcd(Z,N)=1  otherwise.

It never gives a saturated gcd on the supplied contract. The product is genuinely acquired using a degree-ceil(sqrt B) polynomial and monic multipoint tree; since B<k^2/256, its standard fast-arithmetic cost is soft O(k)=soft O(N^(1/6)). Proper-gcd recovery is immediate. A failed screen proves gcd(N,r_P*r_Q)=1 and the analogous fact for beta and eta. Thus N-th powering preserves each relevant local subgroup and its collision equalities. No inverse exponent or discrete logarithm is acquired.

This combines existing product-evaluation methods with an exact native arithmetic branch; no novelty or new general q-factorial algorithm is claimed. It is a conditional factoring result and uniform preparation theorem, not coverage of every remaining instance. The [first review](frobenius-screen-review.md) and [second review](frobenius-periodicity-review.md) check the arithmetic, ring legality, complete cost and continuing contract.

The executable [prototype](frobenius_screen.py) implements the actual blocked product and monic remainder tree. Its [six focused kernel tests](test_frobenius_screen.py) pass, including repeated points, composite zero divisors and incomplete blocks; see [implementation notes](implementation-notes.md) and [test output](kernel-validation.txt). It checks cheap public preconditions but does not certify semiprimality or hidden orders. These tests are not a numerical coverage campaign, a Lean proof, or an asymptotic timing guarantee for the installed library.

## What the knot investigations now supply

| Route | Acquired result | Remaining issue |
| --- | --- | --- |
| [Integer twist lifts](lift-collision.md) | Explicit affine multiplicative orbit and known row/orientation target equations; the new screen removes possible loss of subgroup under N-th powering. | Subgroup membership, lift selection, scalar-zero decoding and full physical-clock contraction. |
| [Fixed skein recovery](skein-recovery.md) ([review](skein-recovery-review.md)) | Three fixed states recover each original adjacent Alexander pair exactly with unit-safe coefficients. | Products introduce higher channels; retaining them gives the existing query cost. |
| [Fractional twist interpolation](fractional-twist.md) ([review](fractional-review.md)) | Forces each supplied native root without solving a logarithm; the entire acquired scalar factors into the target polynomial times an explicit extra divisor. | Extra zeros need control or decoding. Safe cancellation before evaluation restores the original hard query. |
| [Cyclic norms and powered tangles](powered-tangle.md) ([review](powered-tangle-review.md)) | Cyclic/Bloch norm is paid in soft O(L log m). | Its colors differ from the original geometric clock. [Actual native coverage](cyclic-native-coverage.md) requires a still-open factor-correlated divisibility lemma. |
| [Finite root-system identities](finite-root-system.md) | Exact ternary-lattice map for the catalogue and finite-theta endpoint identity. | Inspected Macdonald/Borcherds formulas do not supply the native cutoffs and certified unit completion. |
| [Periodicity](periodicity-scope.md) | Standard Murasugi congruence restricts ordinary periodic lifts of the actual low-span native polynomial. | It does not evaluate the long product; twisted/free actions require separate analysis. |

## Direction and integrity

The next useful work is a contraction or coverage theorem for the remaining N-coprime native groups. N-powering cannot simply shorten their clock after the new screen. The explicit extra-divisor and row-target equations provide concrete candidate inputs, but another local representation alone is insufficient. The full query remains soft O(L+sqrt(Lm)), with L=soft O(k), m=Theta(k^(3/2)); the target is soft O(L+sqrt m).

Review corrected two potential overclaims: N-th powering is not an additive Frobenius map over either component, and an unsupported normalization/degree comparison for the extra divisor was removed. Rowwise lift targets are known from v and v^-1 and do not first require locating the unknown collision index. Earlier frozen packets remain intact. [Sources](sources.json), [integration review](integration-review.md), [validation](review.json), and [manifest](manifest.json) record the evidence. No Lean, public assets, concurrent engineering, commit or push changes were made.
