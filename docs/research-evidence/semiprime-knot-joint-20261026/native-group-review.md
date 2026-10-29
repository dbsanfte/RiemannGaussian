# Independent native inversion / group-polynomial review

26 October 2026. Read both requested reports; scratch only, no numerical campaign or repository changes. Verdict: smaller-order strengthening and native integer-height estimates pass. The factor-return wording needs the short-label/localization qualification below.

## Smaller component: correct strengthening

Write P<=Q, H=k², N<=k⁶. After the already paid k-roughening, every prime divisor of r_P exceeds k and r_P divides P-1, so r_P<P<=sqrt(N)<=k³. If powering removes any nontrivial primary part, the quotient r_P/r'_P is an integer at least k+1. Therefore

    r'_P <= r_P/(k+1) < k³/(k+1) < k² < 16H.

This does supersede the weaker possibility of retaining a large prime order after smaller-side loss. On a continuing branch of the paid factor-or-roots cleaning routine, all supplied-label powerings must be automorphisms on that smaller component. It does not show primality, identify r_P, or establish larger-side invariance. The order has at most two prime factors counted with multiplicity, since three factors exceeding k would give order greater than k³.

Scope correction: group-polynomial §1 says “powering by any integer” followed by automatic first-drop factor return. The inequality is true for any integer, but an algorithmic factor-return claim must retain the initialized short supplied-label routine or explicitly pay localization among short original factors. An enormous aggregate exponent by itself is not a licensed O(log N)-bit annihilator. Section 5 already recognizes this issue. Prefer: “For each paid supplied-label cleaning step, a genuine smaller-side loss enters the established first-drop factor-return branch.”

## Labels, witness, and swap fusion: pass

The witness equations E-HI=(P-1)(bQ-a) and E_swap-HI=(Q-1)(aP-b) follow directly from HI=aP+bQ+lambda. Retained E being coprime to its local order and E=HI there implies both H and I are invertible there. Pruning survival is correctly a premise about the actual complete witness, not all rows.

Including ef as an auxiliary label is legitimate when e,f are retained nonzero short labels; its bitlength remains O(log N). Root uniqueness in the cleaned cyclic group proves rho_e=x^f and rho_f=x^e, including negative labels. The equivalence between (3) and (4) uses invertibility of e and f modulo the group order and is zero/nonunit equivalence, not a geometric-quotient unit assertion. The same-lambda swap convention gives the stated sums and differences. Decoding keeps the original short E-Hi gap rather than the enlarged provenance exponent.

Axis roughening is explicitly implemented using auxiliary retained cleaning labels k*s, 1<=s<k, independently of query-row pruning. Since k=2*3^e, these labels include every prime <=k through k itself and the smaller s. The endpoint H is not silently restored as a query row. No stronger roughness is proved.

The carry formula for scaled lambda and I is correct modulo H, subject to that scaled pair still being a valid catalogue row if used for coverage. It does not prove a useful factorization of I. The rectangle omission of large primes is correct.

## Group polynomial heights: pass under stated branch

For nonaxis rows with b!=0, |a|<=k, |b|<=k and 0<=lambda<H,

    |E| >= N-H-k,   |E| <= kN+k+H.

With d=ceil(sqrt(k)), N>256k⁴ and k>16, subtracting H*n, 1<=n<=d, yields the conservative bounds N/4<|E-H*n|<3kN. Thus none vanishes, and log|P_d(E)|=Theta(d log N). Absolute values multiply in the literal aggregate, irrespective of signs, giving Theta(J_nonaxis*d*log N) bits. This is an output-height statement for that explicit integer interface; it is correctly not claimed as a lower bound for every zero-only algorithm.

The coefficients of P_d have O(d log(Hd)) bits each and total soft O(d²)=soft O(k) size. Product-tree initialization and literal binary powering of all coefficient images fit that scale (polylogarithmic N factors suppressed). Point-product coefficients for degree-d blocks have O(d log N) bits each, giving the stated soft O(Jd) scalar-volume upper accounting for that transposed-module approach. It is not a proof that every group-valued MPE algorithm needs that cost; the report explicitly leaves more sophisticated methods open.

Multiplying group images adds their hidden exponents, so it cannot produce beta raised to the product A. A resultant that explicitly outputs A has its full integer height. Generic addition-chain/formal-exponent remarks are appropriately limited and do not establish an unconditional arithmetic lower bound.

## Query scope

The group-polynomial proposal still lacks both a cheaply acquired primary-incidence aggregate and coverage at n<=d. A genuine witness only gives E=HI modulo the relevant order with a potentially much longer signed I. No full-query gain follows, and no such gain is claimed. Short-factor localization must also retain the original actual signed label conditions before invoking the annihilator decoder; arbitrary new positive-index comparisons cannot inherit that decoder merely because the polynomial product is well-defined.
