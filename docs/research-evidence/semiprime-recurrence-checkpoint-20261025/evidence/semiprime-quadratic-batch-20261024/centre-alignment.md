# The native antipodal centre never equals the finite-theta centre

24 October 2026. Root's exact follow-up to quadratic-product.md, frozen
SHA256 69d3bbc5a0813ba7a5a5cd40e315b250f51d209b82e7085073a9aed52b607eb1.
This is a uniform statement about that literal centre alignment, not
about other finite-theta algorithms or the difficulty of factorization.

Under that report's actual prepared hypotheses, EVERY native antipodal
centre C=beta^(2(N+a))*q^mu, 1<=a<2k, mu in{-8,...,0}, satisfies C*q != 1
as an element of B. Consequently z=1/C never equals q globally. The
acquired factor/unit/globalzero test on C*q-1 always returns either a
proper factor or a unit; the globalzero case is impossible.

Proof. Suppose C*q=1. Let r be the unique nonsplit prime side, used only
in the proof, and write q=(beta W)^H. There the alleged equality is

    beta^(2(N+a)+H(mu+1))*W^(H(mu+1))=1.

The local scalar beta order is odd and divides r-1. The norm-one W order
is odd and divides r+1. These two orders are coprime, since gcd(r-1,r+1)=2.
Thus both factors in the displayed equality are separately one. In
particular ord_r(W) divides H(mu+1). Its order is greater than16H while
|H(mu+1)|<=7H, so mu=-1. No analogous coprimality at the split prime,
and no cross-prime coprimality for W, is assumed.

The hypothesized GLOBAL equality now becomes beta^(2(N+a))=1 in B,
equivalently for the scalar beta modulo N. Its global order D_beta is
odd, so D_beta divides N+a. The two local beta orders are coprime and
both exceed16H, hence D_beta>256H^2. Their product also divides
lambda=(P-1)(Q-1). Subtraction gives

    D_beta divides (N+a)-lambda=P+Q+a-1.

But this positive integer is strictly less than H^2: use P<=k^3,
Q<H^2/16, a<2k and continuing k>16. It therefore cannot be a positive
multiple of D_beta>256H^2. This contradiction proves the assertion.

For an actual centre test, a proper norm gcd gives a factor and a unit
norm gives an inverse. A saturated norm forces both coordinates to zero
at the nonsplit side; their coordinate gcd gives a proper factor unless
the coefficient is globally zero. The latter is excluded by the proof.
Thus all O(k) centre tests are initialized in soft k and contain no
ambiguous global equality. They may find a factor, but there is no claim
that they must do so. On their continuing branch every actual centre
differs from q^-1 by a unit, and the special finite-theta alignment never
applies to any native pair.

This strengthens the previous centre-class count's at-most-O(1) matching
pairs to ZERO matching pairs under the same prepared hypotheses. The
general four-boundary paired recurrence and its fully charged query are
unchanged. A different evaluator of varying centres remains open.
