# Independent algebra and scope review

23 October 2026. Reviewed `/tmp/semiprime-curvature-acquisition-20261023/canonical-lift-recursion.md` and the current repository `docs/research-evidence/semiprime-curvature-acquisition-20261023/README.md`, including its added dyadic-recursion, power-trace and zero-cleanup sections. The linked quadratic-transport and phase-contraction reports were read where needed to check the README's equations and conventions. This is an exact mathematical review; it is not an archive validation, backend audit or factoring coverage test. No repository files changed.

**Verdict.** I found no error in the lift recursion, quarter/wrap signs, vertical phase, slope/seed updates, repeated-insertion support upper bound, fixed-k trace, or public-zero cleanup. Their stated separation from full multiplicative acquisition is justified. I requested one precision qualifier in the bounded-moment batching claim, detailed in Section 6, and verified its repair in the source; it does not alter the algebra. A phase alphabet of p slopes at rank n=m/p has total size m, and neither the source nor this review treats that alphabet alone as too expensive.

## 1. Lift mask and fixed-modulus update

All congruences in this section are in the small integer auxiliary modulus; they are not inversions of arbitrary ring elements modulo N.

Let A=N u^2 modulo M^2, a=A modulo M, and h=(a-A)/M modulo M. Multiplying a-Nu^2=Mh modulo M^2 by j^2 gives

    (a j^2-N)/M = j^2 h modulo M.

Multiplication by j^(-1) proves b=center_M(jh). This also proves that the literal b and the inverse-square mask h carry the same row information.

For the actual integer displacement Delta taking j to the intended canonical odd representative j', u'=u/(1+Delta u) modulo M^2. Therefore A'=AF modulo M^2 with F=(1+Delta u)^(-2). Substituting A=a-Mh gives

    A'=aF-MFh modulo M^2.

Writing aF=a'+MC yields h'=Fh-C modulo M. This proves the source's fixed-modulus recursion, including its sign. The actual Delta must retain the canonical wrap, as the text requires. Since j,j' are odd and M is dyadic, 1+Delta u is odd and the integer modular inverse exists.

For the half shifts, the required residue is

    F=1 minus-or-plus M u + (3M^2/4)u^2 modulo M^2.

Its reduction modulo M is one, so a'=a. The mask correction is h'=h plus-or-minus a u -(3M/4)a u^2. Since u^2=1 modulo 4, the last term equals +(M/4)a modulo M. This verifies equation (3), including its sign and its endpoint M=8.

For the unwrapped quarter shift, M>=16,

    F=1-(M/2)u+(3M^2/16)u^2 modulo M^2.

The cubic Taylor term has coefficient -M^3 u^3/16 and is already divisible by M^2 at M=16; higher terms are also divisible. Thus the stated lower endpoint M=16 is valid, not only M>=64. Reducing modulo M gives a'=a+zeta M/2. The exact quotient contribution is

    C=-(a u+zeta)/2+(3M/16)a u^2 modulo M,

which yields the displayed quarter formula. The half-integer-looking expression is integral because a,u,zeta are odd.

If the unwrapped representative is then reduced by M, its inverse-square lift is multiplied by 1+2M u' modulo M^2. Thus a' remains unchanged and the additional correction is h' -> h'-2a'u' modulo M. The negative sign in the source is correct. Using the general fixed-modulus formula with the actual Delta is an equally valid way to implement the wrap.

## 2. Vertical bit, kappa and phase

Take M=2n>=8 and j=r+epsilon n. Because n is even, (r+n)^2=r^2 modulo 2n, so the upper coefficient a is the same for both upper tags. Write a=a0+eta n. The lower lift says

    N r^(-2)=a0-n h_n modulo n^2.

As 2n divides n^2, the next bit is eta=-h_n modulo 2, which equals h_n modulo 2. This proves the claimed bit and shows that it is acquired lower-row data.

Reducing the upper and lower b congruences modulo n^2 and dividing by nr gives

    2b-b0-2a epsilon=eta r modulo n.

Hence kappa=(2b-b0-2a epsilon-eta r)/n is an integer. The half-open centered ranges b in [-n,n), b0 in [-n/2,n/2), together with 0<a<2n and 0<r<n, give

    -7.5<kappa<2.5.

Since kappa is integral, {-7,...,2} is a safe fixed alphabet. No exact extremizer is required for this bound.

Directly subtracting the two literal exponents gives

    E_(2n)-E_n
      =n[eta+2b-b0-2a epsilon-2eta r]
      =n eta(1-r)+n^2 kappa.

This proves the vertical identity over the integers, not just modulo n^2. Its residual n eta(1-r) is linear in the tag within the acquired eta mask. It should not be interpreted as one unmasked linear phase independent of eta; the source retains that mask explicitly.

## 3. Slope and original seed ancestry

For T_M=E_M+M lambda(1-j), substitution of j=r+epsilon n into the vertical identity gives

    T_(2n)=T_n(r;2lambda+eta)+n^2(kappa-2lambda epsilon).

Thus lambda'=2lambda+eta and K=kappa-2lambda epsilon are correct. Factoring q_n^K from the original scalar difference gives exactly

    beta^T_(2n)-beta^((2n)^2(Ai+theta))
      =q_n^K[beta^T_n-q_n^(4Ai+4theta-K)].

Consequently A'=4A and theta'=4theta-kappa+2lambda epsilon. The sign of the kappa term in theta' is negative. The original i remains the same label, and the prefactor is a unit.

After t levels, p=2^t and n=m/p, canonical coefficient reduction gives

    lambda=(a_original-a_n)/n, 0<=lambda<p,
    A=p^2.

For completeness, the recurrence also gives the explicit safe bounds

    -(2/3)(p^2-1) <= theta <= (8p^2-3p-5)/3.

They follow by induction from kappa in [-7,2], 0<=lambda<=p-1 and epsilon in {0,1}; they substantiate theta=O(p^2). Thus the original-i progression retains stride p^2 at the lower rank. Replacing it by a new canonical interval of length O(n^2) would change the original query. The source correctly declines to do so.

There are at most p slopes times n lower tags, totaling m, and the actual ancestry records number at most the original m/2 odd tags. This is entirely compatible with soft-linear storage and propagation per level. It is not an obstruction argument. The text's stated missing operation is the joint long-sequence contraction, rather than this alphabet count.

## 4. Repeated insertion versus a tangent

The support envelope in Section 5 is correct as an upper bound. In a rank-p norm of

    g-z X^s f A, deg f,deg g<=2, deg A<=D,

the z^j coefficient selects j factors containing fA and p-j containing g. Before invariance, its spatial exponents lie in

    sj+[0,2p+jD].

After passing to X^p invariants and removing the known integer shear, the spatial interval has diameter at most 2+jD/p, up to the usual endpoint count of one. Summing the candidate integer slots over 0<=j<=p gives O(p(1+D)). This remains valid for signed monomial s; the shear affects location, not interval width.

For a single tangent insertion, the extra degree enters only once, giving the inherited O(p+D)-type bound. Replacing the repeated factor A by a tangent would indeed compute a different norm or sequence. The distinction is substantive.

This is an inspected-representation envelope, not a lower bound on the number of nonzero coefficients, not a proof of dense phase interpolation on every semiprime, and not a lower bound against a better algorithm. The source states each qualification. In particular it does not conclude that p slope values at rank n force more than soft m work.

Packing U_(lambda,theta) with a scalar q^theta reproduces that scalar only once; it does not reproduce q^(theta k) in a k-th power. The proposed orthogonal point-mask alternative is algebraically valid when its stipulated idempotents and common-weight factorization are supplied: A^k=sum_theta q^(theta k)e_theta. The source explicitly conditions this construction on those data and costs. It does not treat arbitrary coefficient-list masks as pointwise idempotents or claim an embedding of the original targets for free.

## 5. README transport, trace and cleanup additions

The earlier quadratic-to-native transport is consistent. The two initial numerator congruences make kappa and lambda integers; comparing G_s(cj) with C_s times the native quadratic at j proves nu integral. Substitution of P=j+ru then gives exactly r^2 sigma=C_s I+kappa u+nu. The legal coefficient-root representation preserves local zero support, not a claimed equality of ring products, as the linked report explains.

The fixed-k trace in the new README is an exact finite-sum factorization:

    sum_(s,c,sigma) beta^(k(C_sN+c^2+B_sc-r^4sigma))
      =[sum_sigma beta^(-kr^4sigma)]
       *sum_s beta^(k C_sN) [sum_c beta^(k c^2)(beta^(k B_s))^c].

Thus one degree-<r polynomial and O(r) points suffice. Monic multipoint evaluation remains legal with repeated points and zero divisors. The seed geometric sum is computed by division-free doubling, so it does not require an unsupported inverse of 1-beta^(-kr^4). With r=Theta(N^(1/6)) and k of O(log N) bits, all exponents have O(log N) bits and the conservative soft-O(r(log N)^2) bit bound is justified. This does not compute r moments for the price of one.

The formal prefix relation exp(-sum S_k z^k/k) is valid through degree h when 1,...,h are units. The prepared bound on both factors makes h<=r safe. The resulting soft-O(rh) bound and the explicit statement that F(1) remains unpaid are correct. The positive-C/centered-B convention of the trace source differs from the centered-C/centered-b convention of the AP report; the README now distinguishes these conventions and does not transfer the finite 4r cap without proof.

The public-zero proof is exact. For y=c-s,

    K=y^2+r^2 b_s y+r^4(d_s-sigma).

If v_r(y)<2, its first summand has strictly least valuation, so K cannot vanish. Canonical representatives force c=s<r; scanning those rows is linear, and the elementary AP catalog has only s=c=1. Each deleted K=0 node contributes beta^(kK)=1 for every k, so S_k(clean)=S_k-h0. This is a correction to the full trace, not a zero test based on the trace.

At the true covered leaf, K=(P-1)(C_sQ-c^2) is nonzero under Q>16r^2 and nonzero integer C_s. Every remaining global leaf therefore supplies a nonzero O(log N)-bit annihilator and is handled by the inherited unconditional 31/192 extractor. The README properly separates this already-paid recovery from the missing multiplicative acquisition. It does not reintroduce a bounded-exponent/global-order assumption for the quadratic query.


The optional true-row uniqueness refinement in the AP report was also clarified during review. It explicitly requires ord_P(beta^(r^4)) to exceed the sigma diameter. In the inherited prime-r prepared setting this is provable: both primes >16r^2 and N<=r^6 imply each prime <r^4/16. A local beta order d divisible by r^2 would give ord(beta^(r^2))=d/r^2<r^2/16, contradicting its certified value >16r^2. Hence v_r(d)<=1 and ord(beta^(r^4))=ord(beta^(r^2))>16r^2>8r. Outside these size/order hypotheses the diameter premise must remain explicit. Arbitrary nonzero global leaves still use the annihilator decoder, without this optional argument.

## 6. Requested wording repair and independent checks

The only requested change is to qualify the source's bounded-moment batching statement: soft-O(m) work follows when the **sum of requested moment precisions across the partition is O(m)**, for example each mask only through its own root-polynomial degree, or one combined target polynomial through degree O(m). It does not follow for O(m) moments requested separately for every mask. This is consistent with the later warning about the unpaid all-k sequence, but the earlier phrase should explicitly exclude the latter reading.

Repair status: **checked and repaired**. Section 5 now explicitly states that the TOTAL requested precision across the partition is O(m), gives the own-degree/combined-polynomial examples, and excludes O(m) separate moments per mask. I reread the amended source and verified that wording.

Independent finite algebra checks evaluated 10,668 literal rows at dyadic ranks 4,...,256, using arbitrary odd N. They included 31,752 fixed-displacement checks, 21,168 half-shift checks, 10,416 quarter/wrap checks, 10,584 vertical comparisons and 42,336 slope comparisons. The definitions of b and E in the check were the literal row definitions, rather than the identities being tested. All passed. These are boundary/sign sanity checks supporting the displayed derivations; they do not test semiprime coverage or algorithmic bit complexity. No additional validation campaign was run for the later README additions; those were checked by the direct algebra above, as requested.
