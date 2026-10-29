# Independent character/string review — 26 October 2026

Reviewed character-norm.md, including its exact-support string specialization, native length bound, and unseparated derivative-deflation branches. Verdict: the conditional contraction and the factor branches are valid. Promote shift-zero screening to a mandatory first step before making the strong local-distinct-count/string-count conclusion. The current optional wording leaves that stronger conclusion unsupported; it does not invalidate the algebraic branch itself.

## Conditional principal-string contraction: pass

For an actually acquired string x_t=c q^t, 0<=t<ell, the original factors satisfy

    x_t-q^-i=q^-i(c q^(i+t)-1), 1<=i<=m.

The integer sums i+t fill every n in [1,m+ell-1]. Thus removing repeated copies preserves nonunit support over Z/NZ, and preserves exact zero support when N=PQ is squarefree. The replacement product is precisely the displayed single Pochhammer product, up to known unit factors and multiplicities. No inverse of a collision factor is required.

Recovery is explicit: for a selected n choose i=max(1,n-ell+1), t=n-i. Then 1<=i<=m and 0<=t<ell. Use the acquired original label E_t for that row, and exponent E_t+Hi for the leaf equality. Even if the string equality was acquired modulo N rather than as equality of integer exponents, the original label supplies the correct licensed relation. Its nonzero premise is the public original-row deletion rule for the searched signed interval.

For B=O(1) strings and sum ell=O(J), separate finite-product evaluation costs soft(J+sqrt(m)): each factor length is m+ell-1, and B is constant. A product across strings must be evaluated as one aggregate or otherwise combined through gcd/nonunit information; OR-ing individual zero-only answers would miss mixed-prime saturation. The report's scalar product/gcd algorithm is safe on this point.

For variable B the report's old batched interval cost is the appropriate bound. Merely giving a short description of many strings is not the constant-B contraction.

## Exact native integer strings: pass

Write E=bN+r with -k<=r<H+k. If two labels differ by H, the equation for their b-difference has right side of magnitude <2H+2k<N on the actual hard branch. Hence b is unchanged. For that fixed b, the r range has width H+2k<2H, so no three *distinct integer* labels E,E+H,E+2H exist. Pruning cannot create a longer chain.

The displayed primitive subfamily has Omega(k) distinct integer labels: bN gaps exceed the entire residual r range. This is an integer-label count. Transferring it to distinct local field points requires the mandatory shift-zero screen below.

## Mandatory shift zero: exact and separation-free

After deduplicating equal integer exponents, let D(T)=prod_j(T-x_j). Evaluate D'(x_j) at every acquired point by monic multipoint evaluation. The polynomial identity

    D'(x_j)=prod_(t!=j)(x_j-x_t)

holds over any commutative ring, including repeated modular roots; no root separation or division is involved.

A proper gcd with N factors. At a saturated derivative value, scan all t!=j. Product multiplicativity guarantees a nonunit factor. Its gcd is either proper or saturated; in the latter case beta^(E_j-E_t)=1 modulo N, with nonzero integer exponent because labels were integer-deduplicated. The licensed extractor applies to that O(log N)-bit relation. Only one complete final scan is needed before the branch finishes.

If the branch continues, every pairwise x_j-x_t is a unit, simultaneously at both primes. In particular there are exactly J distinct local points at each prime. This is the needed certificate for the strong lower bound on the number of local strings. It should precede shift one and should not be optional when that lower bound is claimed.

## Shift one with known-successor deflation: pass

For Q_j=q x_j, if no integer successor E_j+H is in the list, D(Q_j) is exactly the product of all tested differences. If it is present at label s, Q_j=x_s in R and

    D'(Q_j)=prod_(t!=s)(Q_j-x_t).

Thus derivative deflation omits exactly the one known integer-zero factor, retaining any additional hidden modular partners. Every nonunit value resolves by a proper gcd or the same one-scan argument, now with exponent E_j+H-E_t. Excluding s makes this exponent nonzero. No inverse of D, D', root differences, or a successor factor is used.

If both screens continue, the local q-neighbor graph is exactly the graph of integer successors. A three-point local q-string would force an integer chain E,E+H,E+2H, contradicting the preceding width proof. Since shift zero certifies J distinct local points, at least ceil(J/2) local q-strings are needed at each prime for a partition of the alphabet into complete positive strings. Together with the Omega(k) label subfamily, this blocks the particular constant-B principal-alphabet specialization on the continuing branch. It is not an obstruction to another zero-preserving alphabet transformation.

Nuance: shift one alone can already rule out a three-point local chain, because each outgoing target must have its unique known-successor label. It cannot certify that isolated local points have unique labels. For example, hidden coincident isolated labels may all pass a shift-one test when none has a q-neighbor. Thus the local *count* conclusion needs shift zero even if the local *length* conclusion is defensible without it.

## Cost, deletion and scope

Constructing D,D', both monic MPE batches, integer successor metadata, gcd screens, and the one final root scan costs soft(J), plus the already licensed extractor if invoked. The two screens terminate on a factor/extractor result; they do not silently remove bad values and continue. Repeated labels may be deduplicated for squarefree zero support, with all original labels retained for recovery and opposite-class bookkeeping.

The supersymmetric rectangle identity is polynomial and therefore safe at collisions; its use as an acquisition oracle would still be unpaid. This review does not establish a product-to-one-hook identity, nor a new complete query bound. The full-family worst-case prefix remains at the old bound after these selected-shift branches.

Post-review resolution: the author promoted shift-zero separation to a mandatory first step, followed by shift-one deflation. Root inspected the revised report before archiving; the strongest local distinct-count conclusion now explicitly depends on both screens. The review's requested correction is resolved.
