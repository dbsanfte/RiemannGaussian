# Independent proof review: prefix-only weak-selector consumer

Verdict: the proposed consumer is correct, conditional on the stated coverage guarantee after deletion/central processing, the exact Boolean prefix primitive, and the already licensed nonzero-exponent saturated-relation extractor. It needs neither shifted intervals nor full polynomial remainders. This is a specialization of the existing weak-selector/bisection mechanism.

## Setup and central processing

Let R=Z/NZ and beta be a unit. Write H for the exponent defining q=beta^H, and acquire the unit points x_j=beta^(E_j). Delete a point whenever E_j/H is an integer in [-M,M]; equivalently, E_j=Hs for some such integer s. This test is on known integers and requires no discrete logarithm.

For every retained point, compute gcd(x_j-1,N). A proper gcd factors N. If the gcd equals N, beta^(E_j)=1 modulo N. Here E_j is nonzero, since E_j=0 would have been deleted; pass that exponent to the licensed saturated-relation extractor. Central processing must resolve this branch under that extractor's guarantee before claiming that all continuing x_j-1 are units. A gcd of 1 permits continuation.

Deleting exact integer matches removes trivial exponent-zero certificates. It does not by itself prove that a collision remains: U(M)=true must be supplied by the old coverage theorem in its post-deletion form, as the proposal explicitly assumes. No new coverage theorem is established here.

## Exact normalized norm identity

Define

    G(Z)=prod_j (Z-x_j-x_j^-1),
    Delta(t)=G(t+t^-1)/G(2).

Every x_j is a unit, and

    2-x_j-x_j^-1=-(x_j-1)²/x_j.

Hence G(2) is a unit after central processing. All normalization divisions are justified over R, including with repeated points or repeated roots of G.

For each unit t the exact factor identity is

    (t+t^-1-x_j-x_j^-1)/(2-x_j-x_j^-1)
         =(x_j-t)(x_j-t^-1)/(x_j-1)².

Consequently

    Delta(t)=prod_j (x_j-t)(x_j-t^-1)/(x_j-1)².            (1)

There is no missing sign or t-power in (1). At t=1 it equals 1. It is an identity in R, rather than an identity merely up to an unspecified unit.

For 0<=m<=M set B_m=prod_{i=1}^m Delta(q^i), with B_0=1. Its denominator from (1) is a unit. Thus B_m is nonunit iff at least one x_j-q^i or x_j-q^-i is nonunit for some 1<=i<=m. This holds over a commutative ring because a product is a unit iff every factor is a unit. Over Z/NZ, nonunit is exactly gcd(value,N)>1; no squarefreeness is needed for this equivalence.

## Prefix Boolean search

Let U(m) be the exact Boolean assertion that B_m is nonunit. Then U(0)=false, and U(m) is monotone: B_(m+1)=B_m Delta(q^(m+1)), so a nonunit prefix cannot become a unit. Given U(M)=true, binary search with a false lower endpoint and true upper endpoint finds the smallest positive m with U(m)=true in O(log(M+1)) exact queries. All queries use the same acquired G. There is no need to evaluate an interval product.

At the resulting m, B_(m-1) is a unit and B_m is nonunit. Therefore Delta(q^m) is nonunit. By (1), at least one of the 2J values

    x_j-q^m,  x_j-q^-m

has gcd greater than 1 with N. Scanning them all therefore finds a proper gcd or a saturated equality. Computing q^m and its inverse uses unit powering, and scanning costs soft(J) ring/gcd work.

## Leaf signs, saturation and mixed CRT branches

If gcd(x_j-q^m,N)=N, then beta^(E_j-Hm)=1 modulo N; the exponent is K=E_j-Hm. If gcd(x_j-q^-m,N)=N, then beta^(E_j+Hm)=1 modulo N; the exponent is K=E_j+Hm. Neither K can be zero, by the exact-integer deletion rule and 1<=m<=M. These are precisely the signed relations the licensed extractor must accept. The consumer assumes that its allowed exponent range includes these |E_j|+HM bounds; a preexisting license with a smaller range would need separate checking.

A mixed CRT event, such as x_j=q^m modulo p but x_j=q^-m modulo r, is not missed: the two signed differences are scanned separately, yielding a proper gcd unless one of those differences already vanishes modulo all of N. A nonunit Delta can even be zero modulo N because different j or different signs cover different prime factors; its complete saturation does not force an uninformative saturated *individual* leaf. Individual scans distinguish these cases.

If both signs for a point are saturated, each resulting exponent is nonzero and either licensed relation suffices. If a proper gcd appears anywhere, no saturation extractor is needed. No central t=1 branch remains, because every continuing x_j-1 is a unit; repeated q powers or q^m=1 do not invalidate the proof and cannot create a new hit solely from that central value.

## Conditional cost and boundary cases

Assume each requested Boolean prefix U(m) costs soft(J+sqrt(m)), with a reusable acquisition of G, and integer powering/gcd/extractor costs are within the already licensed budget. Binary search then costs soft(J+sqrt(M)); logarithmic query overhead is absorbed. Acquisition, exact-exponent deletion, central screening and the final signed scan cost soft(J). With J=soft(k) and M=Theta(k^1.5), sqrt(M)=Theta(k^0.75), the total is soft(k).

This is a consumer bound conditional on the Boolean primitive. The review does not supply that primitive or replace an unproved Boolean cost by the cost of obtaining full remainders.

If M=0 or J=0 after preprocessing, U(M)=true cannot hold: B_0=1 and the empty G gives Delta=1. Those cases must be discharged by the earlier coverage/preprocessing logic rather than entering binary search. For M=1, endpoint knowledge already identifies m=1 and the signed scan applies directly. These are control-flow conditions, not new mathematical exceptions.

No numerical campaign was needed: the exact unit factorization (1) resolves the sign, saturation, and mixed-prime issues directly.

## Independently reviewed zero-only prefix variant

Verdict: correct, and strictly less informative than the nonunit Boolean oracle. Write A_m=B_m and request only

    Z(m) = [A_m=0 in R].

Given A_0=1 and A_M=0, Z is monotone because zero absorbs every subsequent multiplication. Binary search therefore finds the first i with A_i=0 using O(log(M+1)) same-G prefix queries. At this point A_(i-1) is nonzero; it need not be a unit. If Delta(q^i) were a unit, A_i=A_(i-1)Delta(q^i)=0 would force A_(i-1)=0 by multiplying its inverse, a contradiction. Hence Delta(q^i) is nonunit, and identity (1) guarantees a signed leaf with gcd>1. The existing signed scan and saturated-exponent consumer apply unchanged.

No gcd of a prefix is required; a false Z answer need not distinguish a unit from a nonzero zero divisor. The zero-only primitive must be exact. A routine that returns zero on some additional nonzero inputs would not support this argument. With query cost soft(J+sqrt(m)), the previous total soft(J+sqrt(M)) and conditional soft(k) bounds are unchanged.

### Check against the actual swap coverage and pruning

I read the actual archived proof in /tmp/semiprime-arithmetic-locator-20261024/swap-erratum.md, Sections 1–3, rather than inferring global zero from one local collision. It supplies distinct prime factors P,Q and retained swapped rows with exponents E=a+bN+lambda and E'=b+aN+lambda and a common signed integer I in (-M,M), such that

    beta^E=q^I mod P,    beta^E'=q^I mod Q.

Its equations (1),(2) prove both rows survive public exact-integer-zero deletion. Its Section 2 pays for the diagonal query before deleting diagonals: on the continuing branch the diagonal aggregate is a global unit, so the surviving coverage pair is nondegenerate. Section 3's complete-swap pruning is explicitly coverage-safe because both actual witness members survive. The pair-difference gcd screen either finishes or leaves unit pair differences; this screen does not remove a useful surviving pair. These are the precise pruning conditions used here; arbitrary additional pruning is not covered.

The central screen gives one more necessary observation. If I=0, the original row has x_j=1 mod P. Then gcd(x_j-1,N)>1 and central processing finishes via a proper factor or the licensed nonzero-exponent saturated branch. Thus on a genuinely continuing branch the surviving coverage witness has I!=0. Put r=|I|, so 1<=r<=M. At either prime, q^r+q^-r=q^I+q^-I. The two retained rows therefore show

    G(q^r+q^-r)=0 mod P and mod Q,

so it is zero modulo N=PQ. The already-unit normalization G(2) gives Delta(q^r)=0 modulo N and hence A_M=0. No inverse closure of the uncentered catalogue is used: changing I to |I| changes neither trace, and both signed differences are present in the leaf scan. This independently verifies the full-zero endpoint for the actual continuing, coverage-preserving pruned catalogue.

### Limit of weaker coverage assumptions

A guarantee of a hit at only one unspecified prime proves A_M nonunit, not A_M=0; a zero-only binary search is then unjustified. If both distinct prime factors are guaranteed hits somewhere in the prefix, even at different indices, their product A_M is already zero modulo PQ. Thus a common signed index is sufficient and stronger than necessary for the zero-only consumer; it supplies the especially clean individual-factor certificate Delta(q^r)=0 above. For a repeated-prime modulus, separate mod-p hits alone do not certify the valuation needed for zero modulo p². The actual reviewed swap proof uses N=PQ with distinct factors.

This variant is a natural specialization of the old known-zero binary-search consumer, not a new general selector theorem or an implementation of its prefix primitive.
