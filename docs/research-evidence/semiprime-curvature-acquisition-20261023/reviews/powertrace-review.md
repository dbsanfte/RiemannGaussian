# Independent review: quadratic AP rows and power traces

23 October 2026. Reviewed the final scratch `ap-catalog.md`, `phase-contraction.md`, and the inherited strong-setup/query-interface and unbalanced-annihilator reports. This is a paper-level algebra/resource review, not certification of a complete executable or Lean factorizer. No repository files, builds, or frozen entries were changed. The requested precision clarification was added only to scratch `canonical-lift-recursion.md`, Section 5.

**Verdict.** The AP polynomial/root formulas, two carry transports, odd-prime cubic generator, four dyadic branches, specified-index trace evaluator, and public-zero cleanup are correct. One trace costs soft O(r), including the stated bit factors; an h-prefix costs soft O(rh). The complete query and its detector remain unacquired. The positive-C/centered-B row convention and the signed-C/centered-b AP convention are distinct, as the final phase report explicitly states. Both support the trace identity; a coefficient generator for one convention cannot silently be substituted into the other's literal product.

## 1. AP source and exact lifts

For H=r^2 and s_t=1+rt, the pair (t,c), 1<=c<r, is uniquely determined by any unit residue P modulo H through cP=s_t modulo H: first c=P^(-1) modulo r, then t. This establishes the elementary uniform cover without any factor oracle. It also shows that a restriction on the own native residue j=P modulo r becomes the common multiplier mask c=j^(-1) modulo r. This preserves the relevant own-witness labels for this new AP family; it does not identify its scalar factors with the inherited original dyadic-row product.

With signed C_t and centered b_t as in the AP report, H divides s_t^2-NC_t and H divides b_t s_t-(s_t^2-NC_t)/H. Hence d_t is integral and

    F_t(s_t+Hh)=H^2(h^2+b_t h+d_t),
    H^2 sigma=c^2P+B_t c+C_tQ,
    E_t,c-H^2 sigma=(P-1)(C_tQ-c^2).

The displayed balanced cap is valid:

    |sigma|<2r+r/2+2/r+r<4r  (r>=3).

Expanding the first centered coefficient gives exactly

    C_t=U+2ru t-H k_t,
    (s_t^2-NC_t)/H=t^2-2wt+a0+Nk_t.

Multiplication by s_t^(-1)=1-rt modulo H gives the second carry W_t-H ell_t. In particular E=E0-H^2 c ell_t. The shift of the sigma interval by c ell_t, and the unit prefactor in the AP report, have the correct signs. Removing either carry without its seed transport changes the query.

For the phase report's positive C and centered B convention, the same balanced estimates give the optional explicit cap |sigma|<9r/2, so |sigma|<=5r is safe. This does not replace the signed-C convention's sharper cap.

## 2. Cubic coefficient/root formulas

For odd prime r, X=CN-1 is divisible by r. The truncation

    B=-2-X+X^2/4-X^3/8 modulo r^4

satisfies B^2=4CN modulo r^4. The omitted error is divisible by X^4 and denominators are powers of 2, hence units. Since B=-2 modulo r, s=-B/2 modulo r^2 belongs to 1+r Z. Moreover

    G_s(s)=((2s+B)^2+4CN-B^2)/4

is divisible by r^4. Counting the distinct positive C=n0+ru gives all r AP rows. Reducing the cubic coefficients modulo r^4 and evaluating an integer cubic introduces exactly the reported carry B=P3-r^4 h. The associated sigma shift is h*c; polynomial exponent descriptions alone do not eliminate it.

For m=2^k, k>=2, the dyadic generator also passes review. X is divisible by 4m, and the displayed error

    R^2-(1+X)=5X^4/64-X^5/64+X^6/256

is divisible by m^4 (in fact by a larger power at the first term). The four B branches have the claimed matching s branches. The parity check is essential: for e=0, D=(B^2-4CN)/m^4 is 0 modulo 4 and b=(B+2s)/m^2 is even; for e=1, D is 1 modulo 4 and b is odd. Thus m^4(b^2-D)/4 is divisible by m^4. Centering B changes neither parity condition. These branches give four distinct s values for each C and cover exactly s=+1 or -1 modulo 2m. Merely checking B^2=4CN modulo m^4 would not by itself replace this 2-adic parity argument.

## 3. Exact trace and costs

For any Cartesian restrictions R, C, I and supplied positive index k,

    sum_(s,c,sigma) beta^(k(C_sN+c^2+B_sc-Msigma))
      = A_k(I) sum_s beta^(kC_sN) P_k(beta^(kB_s)),
    P_k(T)=sum_(c in C) beta^(kc^2) T^c.

This finite-sum factorization is exact over Z/NZ and includes actual integer endpoints. It requires only that beta be a unit. There is one degree-<r polynomial and O(r) evaluation points, so a monic product/remainder tree gives the claimed shared soft-r work without materializing r^2 pairs. Repeated points and nonunit differences cause no problem: no point differences or collision factors are inverted. Division-free geometric doubling computes A_k, including when a geometric denominator is a nonunit.

The final bit ledger is conservative and adequate. With b=ceil(log_2 N), k of O(b) bits, native O(r) endpoints, and polynomial-size coefficient lifts, exponent lengths are O(b). O(r) binary modular powers cost soft O(r b^2), and MPE costs soft O(rb). Workspace is soft O(rb) bits. Reading arbitrary row/multiplier masks costs at most O(r). A general interval whose endpoints had more than O(b) bits would require those bits to be charged; the final ledger explicitly restricts endpoint size, so this is not a gap in the native statement.

Computing h separate traces gives soft O(rh b^2) work and soft O((r+h)b) storage. Formal exponentiation recovers the product only modulo z^(h+1). It is valid when 1,...,h are units, in particular h<=r on the surviving setup branch. It cannot be applied at full degree without checking the larger integer denominators. The short trace evaluator has no acquired sharing across k.

Cartesian restrictions suffice for ordinary binary localization if a detector is eventually supplied: split a row subset, then a common multiplier subset, then a common seed interval, keeping one such rectangle at each step. Arbitrary unrelated leaf masks or row-dependent seed intervals are not included in the current formula. In particular the moving intervals introduced by dropping a cubic/centering carry cannot be silently replaced by a common I.

## 4. Public zero leaves and global recovery

Write y=c-s. Since

    K=y^2+H b_s y+H^2(d_s-sigma),

if v_r(y)<2, the first term has strictly smaller valuation than both other terms. Thus K=0 forces H|y. Canonical s and 1<=c<r then force c=s. Only the AP pair s=c=1 survives; checking its one integer sigma against I and the supplied masks gives h0 in {0,1}. For a general supplied O(r)-row list, one candidate per row gives the stated O(r) screen. Subtracting h0 from every trace exactly divides F by (1-z)^h0. The same valuation argument works at p=2.

The true covered leaf is retained: K=(P-1)(C_sQ-c^2) is nonzero because Q>16r^2, c^2<r^2, and C_s is a nonzero integer. Any remaining global leaf has a known nonzero O(log N)-bit K with beta^K=1. The inherited unbalanced short-annihilator report applies to beta's odd local orders >16r^2 and costs soft O(N^(31/192)). It does not require true-pair provenance, a factorization of K, or a new order promise for beta^M. This is an inherited paper-level recovery theorem, not newly acquired collision detection. Proper leaf gcds already factor N.

## 5. A useful stronger seed-order corollary, without a detector

The inherited setup additionally certifies local orders of beta^(r^2) greater than B=16r^2. For odd prime r, this already certifies the same bound for q=beta^(r^4).

Indeed both hidden primes exceed B, so N<=r^6 gives each hidden prime <r^4/16. Let d be its local beta-order. If r^2 divided d, then

    ord(beta^(r^2))=d/r^2<r^2/16<B,

contradicting the certificate. Hence v_r(d)<=1, and gcd(d,r^2)=gcd(d,r^4). The two powered bases have the same local order. For dyadic m this is even immediate from the beta-orders being odd.

It follows that seed differences in either finite balanced cap are units, and the AP report's optional local seed uniqueness needs no additional order purification. More particularly, if h<=r and the interval is nonempty with length 1<=ell<=10r+1, then k*ell<B for 1<=k<=h. Consequently 1-q^(-k), 1-q^(-k ell), and A_k(I) are units. Thus these short traces can safely be normalized to giant-only moments S_k/A_k. An empty interval instead has A_k=0 and collision product 1 and is handled separately. This is an optional consequence of the inherited setup, not a premise needed by the division-free evaluator.

Normalization does not acquire the giant root polynomial: it normally has r(r-1) roots, while only h<=r moments were paid here. No separation guarantee for giant-to-giant differences is inherited from the original native offset family. The corollary supplies neither a full product nor a nonunit detector.

## 6. Why the remaining detector claim is correctly left open

The complete F has Theta(r^3) labeled factors. A low formal prefix gives low symmetric functions, rather than F(1), and it can miss or cancel local zero information. Generic Newton identities provide no implication from such a prefix to a collision. For example, over a splitting field with suitable odd d>h, root sets of X^d-1 and X^d-a have the same first h power sums but differ on whether they contain 1. This illustrates the missing inference; it is not a counterexample theorem about this particular structured native family or its beta subgroup.

A new theorem could still exploit this family's coefficients to supply a detector or contract the k direction. Neither the trace identity, its safely normalized short prefix, nor the modular cubic generator presently does so. The reports correctly avoid claiming a sixth-rate algorithm, a full query, or a general lower bound.

## 7. Independent finite algebra checks

A separate pure-integer script checked 15 odd-prime cubic rows for (r,N)=(3,55),(5,77),(7,65), nine direct-versus-contracted trace identities with row/multiplier restrictions and signed sigma endpoints, and the exact public-zero screen. It also checked 112 dyadic branch rows for m=4,8,16 and N=1,3,17,77, including the D/b parity conditions and exact equality of the generated catalog sets. All passed. These checks test polynomial and finite-sum identities only; they are not a semiprime coverage campaign or asymptotic runtime evidence.
