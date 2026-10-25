# Canonical lift masks: closed row recursion and the first unpaid contraction

23 October 2026. Original dyadic native rows only. Read the inherited native half-tag transport before deriving the identities below; its bounded odd shifts and four phase startups are inherited, not new. No repository edits, build, or semiprime coverage campaign. All 208 frozen entries are preserved.

**Result.** There is a closed constant-size arithmetic recursion for the canonical lift mask and an exact single-slope recursion for the original scalar targets. One previously unspecified vertical phase simplifies to a linear tag phase. All row descriptors, masks, target polynomials, and their bounded-degree moment data remain acquired in soft O(m) bits. This does NOT acquire the long original collision product. The first explicit loss when attempting to apply the paid sparse norm is identified in Section5: either accumulate moving phase directions, or absorb them into a spatial base multiplier which is inserted repeatedly and loses the tangent's single-insertion support bound. No total-soft-m query recurrence was obtained.

## 1. Lift mask and canonical b are the same row information

For any dyadic M>=4 and odd canonical j, define

    u=j^(-1) mod M^2,
    A=[N*u^2]_(M^2),
    a=[A]_M,
    h=(a−A)/M mod M,
    b=center_M(((a*j^2−N)/M)*j^(-1) mod M),
    E_M(j)=N+a+M*b−2*a*j.

Here center_M is the half-open interval [−M/2,M/2). The mask h is exactly the negative high M-adic digit of the acquired inverse-square lift. It obeys

    b=center_M(j*h mod M).                                      (1)

This follows by multiplying a−Nu^2=Mh modulo M^2 by j^2 and dividing by M before reduction. Thus carrying both b and h as independent arbitrary directions would overcount the source. Both can be acquired from one another within the same soft-linear row ledger.

## 2. Closed fixed-modulus update, including all smaller splits and wraps

Let the actual integer displacement be Delta, chosen so j'=j+Delta is the desired canonical representative. For a nominal shift d this means Delta=d−omega*M, with the actual wrap omega retained. Compute

    F=(1+Delta*u)^(-2) mod M^2,
    a'=[a*F]_M,
    C=(a*F−a')/M  (an exact integer).

Then

    u'=u*(1+Delta*u)^(-1) mod M^2,
    h'=F*h−C mod M,
    b'=center_M(j'*h' mod M).                                  (2)

The identity uses A'=A*F modulo M^2 and A=a−Mh. It is valid for every smaller dyadic tag split; it uses actual modular inversions on odd integers, not formal divisions by an unchecked ring element. All integers have O(logN) bits in the native scale.

For Delta=+/-M/2 and M>=8, Taylor truncation in the INTEGER auxiliary modulus gives

    a'=a,
    h'=h +/- a*u+(M/4)*a mod M.                               (3)

After (1) and canonical recentering, this reproduces the inherited odd half-tag target shift. It is a consistency check rather than a new half-tag theorem.

For the unwrapped quarter shift Delta=M/4, M>=16, put zeta=+1 if a<M/2 and zeta=−1 otherwise. Then

    a'=a+zeta*M/2,
    h'=h+(a*u+zeta)/2 −(M/2)*h*u −(3M/16)*a*u^2 mod M.         (4)

The displayed half is integral because a*u and zeta are odd. If this unwrapped j' exceeds M, canonical wrapping subtracts M; its additional exact correction is h' -> h'−2*a'*u' modulo M. Formula(2) handles that case directly and is the preferred implementation. Thus the smaller split introduces no unknown arithmetic carry: its coefficient digit and centering are fully determined.

## 3. New vertical phase simplification

Let M=2n>=8, write j=r+epsilon*n with odd canonical 1<=r<n and epsilon in {0,1}, and let a0,b0,E_n(r),h_n(r) denote the independently canonical lower rows. Set

    a=a0+eta*n, eta in {0,1}.

Because (r+n)^2=r^2 modulo2n, eta is the SAME for both upper tags. More precisely,

    eta = h_n(r) mod2.                                        (5)

Indeed N*r^(-2)=a0−n*h_n modulo n^2, and 2n divides n^2; its next coefficient bit is −h_n=h_n modulo2.

The defining b congruences yield

    2b−b0−2a*epsilon = eta*r mod n.

Define the actual integer

    kappa=(2b−b0−2a*epsilon−eta*r)/n.                           (6)

It is integral, and canonical centering gives the safe bound

    −7.5<kappa<2.5, hence kappa in {−7,...,2}.                 (7)

Exact subtraction now gives

    E_M(j)=E_n(r)+n*eta*(1−r)+n^2*kappa.                       (8)

The inherited report retained a more general bracket in this vertical comparison. Equation(8) shows that its phase modulo n^2 is an explicit LINEAR tag modulation, selected by the already acquired lower lift-mask parity. It is not an arbitrary per-row offset. This is the substantive refinement of the inherited phase description.

The arithmetic identity was independently checked on744 auxiliary row cases with arbitrary odd N and dyadic ranks8,...,128. These are modular-identity checks only; primality or semiprime coverage was not tested or used as evidence. The derivation above proves the identity.

## 4. One slope closes exactly; seed phases must still be carried

Define the slope state

    T_M(j;lambda)=E_M(j)+M*lambda*(1−j).

Then (8) gives the exact recursion

    lambda'=2lambda+eta,
    K=kappa−2lambda*epsilon,
    T_M(j;lambda)=T_n(r;lambda')+n^2*K.                        (9)

For an arbitrary common original seed subinterval, suppose the current seed exponent is M^2*(A*i+theta). Put q_n=beta^(n^2). Every ORIGINAL scalar factor transforms as

    beta^T_M − beta^(M^2*(A*i+theta))
      =q_n^K * [beta^T_n − q_n^(4A*i+4theta−K)].               (10)

Thus the seed state updates by

    A'=4A, theta'=4theta−kappa+2lambda*epsilon.                 (11)

All prefactors are known units; for an exact product they can be accumulated by row counts and the interval length without iterating over every seed. Original tag ancestry and the original i label remain attached, so a nonunit or saturated localized leaf is still an ORIGINAL scalar leaf, with its original nonzero-gap decoder.

Starting with lambda=0,A=1,theta=0, after t levels put p=2^t and n=m/p. Then

    0<=lambda<p,
    lambda=(a_original−a_n)/n,
    A=p^2,
    theta=O(p^2).

The p slope values times rank n have total size m. This count alone is compatible with a near-linear algorithm and is NOT a failure argument. The exact row-mask records also number at most m/2: each original tag has one current (r,lambda,theta) label. They can be propagated in soft O(m) total work per level. Theta modulo p^2 is the seed phase; its integer quotient additionally reorigins the same inherited original-i interval. It is not valid to replace these arithmetic progressions by fresh canonical lower-row seed intervals of length O(n^2).

## 5. What moment batching actually pays, and the first explicit state growth

There is a successful near-linear scalar batching step. Partition current target roots by their acquired masks and build their root polynomials. Multiplying roots in one mask by q_n^K is the coefficient dilation z->q_n^K*z in product(1−z*x). The total polynomial degrees over a partition sum to the original number of tags. All such coefficient dilations and product-tree combinations therefore cost soft O(m) per level, independent of the phase alphabet. Computing the corresponding bounded-degree power sums by logarithmic differentiation has the same bound. Here the TOTAL requested precision across the partition is O(m): each mask may be expanded through its own degree, or the combined target polynomial may be expanded through O(m). This does not pay O(m) moments separately for every mask. This re-acquires the native target polynomial, which was already paid; it is not the long-seed query.

For the proposed fixed-direction norm route, carry phase theta affects the kth moment by q_n^(theta*k). Even in the favorable situation where a fixed slope has a paid rational base R_lambda and supplied phase-mask directions U_(lambda,theta), the required sequence is

    S_k=sum_theta q_n^(theta*k) CT[U_(lambda,theta)*R_lambda^k]. (12)

At a SINGLE fold, the bounded kappa list permits constantly many fixed-direction calls followed by cheap scalar modulation. This fold does not have a quadratic cost. After recursion, however, packing phase masks as

    U_lambda=sum_theta q_n^theta*U_(lambda,theta)

computes q_n^theta instead of q_n^(theta*k), and is wrong for k!=1. Acquiring all phases separately introduces one fixed-direction sequence per nonempty cumulative phase. No bound making that sequence-acquisition cost soft O(m) has been derived. The total number of scalar mask records being O(m) does not charge an all-k sequence for each record.

One can instead absorb the phases into a base multiplier in a valid point-mask representation. If a supplied point-mask representation gives orthogonal e_theta and a common weight U_lambda with U_(lambda,theta)=U_lambda*e_theta, set

    A_lambda(X)=sum_theta q_n^theta*e_theta(X),
    R_lambda_new=R_lambda*A_lambda.

Then (12) becomes the ONE weighted power sequence CT[U_lambda*R_lambda_new^k]. This is an exact constructive alternative, provided the common-weight factorization, mask algebra and its scalar coefficient/extension costs are supplied; arbitrary coefficient-list masks do not automatically have this orthogonal form. The first explicit support growth appears here: the available interpolation supplies A_lambda with up to rank-n spatial degree D=n−1; no bounded-width formula for that polynomial has been proved from(1)–(11).

The paid constructor's near-linear tangent bound permits ONE insertion U: its spatial width grows as deg(U)/p at norm rank p. Here A_lambda is inserted in EVERY selected base factor. For

    F=g−z*X^s*f*A_lambda,  deg f,deg g<=2,

the coefficient of z^j before normalization has a spatial interval of width at most 2p+j*D. After taking rank-p invariants this is width at most 2+j*D/p. A full prefix j<=p therefore has O(p*(1+D)) candidate scalar slots, rather than O(p+D). With supplied D=O(n), a rank-n call has O(n^2) candidate support under this representation. Monomial shifts do not remove the width term jD. Treating the phase multiplier as a tangent would remove repeated insertions and compute a different sequence.

This identifies the precise first loss in TWO attempted implementations: separate cumulative phase sequences, or a dense phase multiplier repeatedly inserted into the denominator. It is not a lower bound; sparsity or a new shared mask transform could avoid both. In particular no claim is made that the phase interpolation actually has degree n−1 on every semiprime. The existing interface simply gives no smaller guaranteed width, nor a paid factorization that keeps its repeated-insertion support small.

The actual scalar targets beta^T_n must also be embedded into any proposed low-degree cyclic base; the slope congruence by itself is not that embedding. Interpolating the supplied scalar target values gives an O(n)-coefficient polynomial, whose dense degree does not meet the degree<=2 input contract. Replacing it by W or by a root-of-unity phase without a proved source bridge would change the original query.

## 6. Precise sufficient next contraction

A completion can now target an explicit operation instead of an unspecified carry:

    input: the recursively acquired h masks from(2),
           slope lambda and seed state(A,theta) from(9)–(11),
           ORIGINAL beta and common original-i subinterval;
    output: the original restricted collision product or a proper factor,
            with total soft O(m) work across all current masks.

A particularly useful missing lemma is a batching algorithm for(12), with total charged mask/sequence work soft O(m), whose base is proved to represent the ORIGINAL scalar query and which retains seed stride A=p^2. Equivalently it could supply phase multipliers A_lambda with bounded TOTAL repeated-insertion support, not merely bounded scalar storage. All slopes and masks are now fully public, exact, and recursively acquired. The long seed startup and this joint phase/moment contraction remain unacquired.

The established block product/MPE route still completes the original query in soft O(m^(3/2)) for J=O(m), L=O(m^2). The row recursion does not change that exponent. No factoring-rate theorem or new backend is claimed.
