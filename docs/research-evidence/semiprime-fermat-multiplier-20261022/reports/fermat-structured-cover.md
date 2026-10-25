# Structured Fermat-quotient cover investigation

22 October 2026. Write ell for the auxiliary prime (called r in the parent work), H=ell^2, and N=PQ. The target regime has ell asymptotic to N^(1/6). This note does not establish a soft-N^(1/6) factoring algorithm. It derives an exact linear balanced consumer, an exact reciprocal-coset pairing, and concrete size constraints on several proposed structured multiplier replacements.

## 1. Exact cover and reciprocal pairing

Let q=q_ell:(Z/HZ)^* -> F_ell be the Fermat quotient homomorphism. Let C be the permitted multiplier set, Q_C=q(C), and choose A with A-Q_C=F_ell. Then

    S_A={s in (Z/HZ)^*: q(s) in A}

has |A|(ell-1) elements and covers cP modulo H for some c in C, for every unit P. The known full interval C=[1,ell) gives |Q_C| >= (1+o(1))ell/log^2 ell, hence a polylogarithmic-size A by greedy covering.

There is an exact simultaneous cover at no extra coset cost. If s=cP modulo H lies in S_A, put

    t=N/s modulo H.

Then t=c^(-1)Q modulo H, and

    q(t)=q(N)-q(s) in q(N)-A.

The pair (s,t) is determined by s; it does not require a second independent ell-sized catalog. This is the useful consequence of q(P)+q(Q)=q(N). It already accounts for all the information the two Fermat quotient conditions supply. The obstruction to using it as an integer relation is that c^(-1)Q is generally rational: for 1<c<ell<Q, c does not divide Q.

Clearing the denominator gives Q=ct+Hk. With cP=s+Hh,

    (N-st)/H = t h + P k.

This removes c algebraically, but h can be as large as P/ell, which is ell^2 in the balanced regime. Thus this identity replaces the ell-sized c label by an ell^2-sized h label rather than reducing the consumer count. Using the least positive modular inverse d=c^(-1) mod H makes the multiplier an integer but allows d<H and cd=1+jH with j<ell; dQ can be ell times larger than cQ.

## 2. Balanced linear consumer: no Gauss reduction and no quadratic c

For each s in S_A, define

    b_s = centered representative of -N/s modulo H,
    d_s = (N+s*b_s)/H.

Both are explicit integers, |b_s|<=H/2. The linear polynomial

    g_s(h)=b_s*h+d_s

satisfies H*g_s(h)=b_s*(Hh+s)+N. At a covered root Hh+s=cP,

    sigma = g_s(h)/P = (b_s*c+Q)/H.

This is an integer because b_s*c=-Q modulo H. If P,Q are within fixed multiples of sqrt(N)=ell^3 and c<ell, then |sigma|=O(ell). For an exponent base beta put theta=beta^N and q0=beta^H. Since Q=N modulo P-1,

    theta*(beta^b_s)^c = q0^sigma modulo P.

This is exactly the parent's improved bilinear consumer. Once s and sigma are localized, enumerating c<ell recovers Q=H*sigma-b_s*c and tests divisibility. Also q(b_s)=q(N)-q(s), so the b_s catalog itself is a union of the paired Teichmuller cosets q(N)-A, with centered representatives. Inversion or adding the Q-side coset catalog therefore gives the same b catalog, not an additional independent constraint.

For a general dyadic factor window P~P0 the same formula bounds |sigma| by O(ell+N/(H P0)). The balanced O(ell) bound does not automatically cover P0 near ell^2, where the second term is O(ell^2).

## 3. Why a tiny integer GP does not carry this cover

Every translate a-Q_C covers at most |C| quotient values. Therefore

    |A|*|C| >= ell.

Keeping |A| polylogarithmic forces |C|>=ell/polylog ell. This is a restriction on the cover architecture, not a general lower bound for factoring.

A positive-integer geometric progression g^j with g>=2 and all multipliers <ell has at most 1+log_2 ell members. A product of d such progressions with nonnegative exponents has at most (1+log_2 ell)^d exponent tuples. Consequently no constant-rank integer GP of this kind supplies the required multipliers while retaining a polylogarithmic A. The rank would need to grow at least on the order of log ell/log log ell. An ordinary arithmetic progression already has sufficient cardinality; that is the current C=[1,ell), and it leaves b_s*c bilinear.

A GP modulo H can have ell members, and a nonzero q(g) makes q(g^j)=j*q(g), but canonical integer representatives can be as large as H. In the balanced linear consumer, allowing c up to H changes the guaranteed sigma interval from O(ell) to O(ell^2). Keeping unreduced g^j instead increases the integer magnitudes still further. Reduction modulo H does not disappear in exponents: c'=g*c-H*k changes beta^(b*c') by the correction q0^(-b*k).

## 4. Fixed-product reciprocal pairs cannot be numerous at short height

One might seek c,d<ell with cd belonging to a tiny known list K, so the P/Q pair can share a fixed product. For a fixed positive k<ell^2, the number of ordered pairs with cd=k is at most tau(k). Uniformly for k<ell^2, tau(k)=ell^o(1). Thus a polylogarithmic list of such products supplies only ell^o(1) pairs and cannot supply ell/polylog ell distinct first multipliers. Any fixed-product list adequate for the cover has at least ell^(1-o(1)) distinct integers. This counts actual integer products; merely fixing q(cd) does not fix cd in the consumer's exponent.

The exact modular reciprocal d=c^(-1) mod H avoids this counting statement only by taking d up to H and actual products cd=1+jH. The magnitude expansion described in Section 1 then reappears.

## 5. Low-height rational multipliers: exact consumer tradeoff

Take c=u/v with 1<=u<=U, 1<=v<=V, and define coverage by

    uP=v*s modulo H.

For the same b_s=-N/s modulo H, multiplication gives

    u*b_s+v*Q=H*sigma.

Hence the exponent consumer is

    beta^(u*b_s+v*N) = (beta^H)^sigma modulo P,

with the rigorous balanced bound |sigma|=O(U+V*ell). A numerator/denominator box U=V=sqrt(ell), large enough to contain ell rational labels, therefore increases the sigma bound to O(ell^(3/2)). It does not preserve the original O(ell) baby interval.

There is also an immediate height-versus-coset constraint: |A|*UV>=ell. If one insists on V=O(1) to retain an O(ell) sigma bound and |A|=polylog ell, then U must again be ell/polylog ell. Rational denominators cannot simply split the ell-sized multiplier into two sqrt(ell)-sized parameters for free. This does not rule out a more elaborate consumer that exploits the two parameters jointly.

## 6. What a successful next construction must exploit

The balanced consumer is now a very specific multi-base bounded-exponent collision:

    theta * x_b^c = q0^sigma,
    b in B (|B|=soft-ell),  1<=c<ell,  |sigma|=O(ell),
    x_b=beta^b,
    B a union of polylogarithmically many centered Teichmuller cosets modulo H.

Explicitly enumerating (b,c) gives soft-ell^2 giants. Generic simultaneous multipoint evaluation handles ell points per b, still soft-ell^2 overall. The paired coset identity supplies no further independent P/Q restriction. I did not find an identity that turns this product catalog into soft-ell exponent labels, or a primary theorem guaranteeing a suitable short-height structured alternative C.

One concrete promising theorem would be an algorithm that localizes whether the displayed collision exists in soft-ell ring operations while preserving product/gcd localization over Z/NZ, using the Teichmuller structure of B. This is stronger than merely storing the bilinear catalog implicitly: its aggregate product has ell^2 factors, and fast evaluation of an implicit description has not been established here.

## Primary literature consulted

Ostafe–Shparlinski, *Pseudorandomness and Dynamics of Fermat Quotients*, Theorem 10, provides the value-set estimate used for the initial cover: https://arxiv.org/pdf/1001.1504v2 . Its homomorphism and shift identities are the basic tools used above.

Harman–Shparlinski, *Products of Small Integers in Residue Classes and Additive Properties of Fermat Quotients*, treats products of several short factors and Fermat quotient applications: https://arxiv.org/pdf/1408.4515 . Corollary 3 gives all quotient values using a sum of nine q(u_i), u_i<=ell^(1/(2*sqrt(e))+epsilon). Thus it gives a single-coset cover with c=product u_i, but only the worst-case bound c<=ell^(9/(2*sqrt(e))+9epsilon), approximately ell^2.729. The balanced linear consumer then has sigma of this size. Reducing c modulo H improves the magnitude bound to ell^2, still larger than the desired ell. These are guarantees from the theorem, not a lower bound on the minimal representation size. I have not substituted them into a claimed fast consumer.
