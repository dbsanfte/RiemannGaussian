# Composite row modulus after a small prime conductor: paid source and character contract

2026-10-24. Scratch only; no repository changes, examples or backend work. Choose the conductor FIRST: a public prime ell of sixth-root size, then row modulus k=ell-1. This removes the old unproved supply obligation ell=1 mod a previously fixed large prime row modulus. The scalar source, complete factor-or-NoHit preparation, native own-index cover, packed character primitive and shared Gauss-pair family are acquired below with correct composite-modulus arithmetic. A direct coherent QUARTER-exponent scalar representation is also acquired. None supplies a faster covered long query or a new Gauss-base order/recovery theorem.

Read the original uniform-setup-and-query-interface.md (SHA256 4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46), the packed-Gauss journal entry around lines 32100–32260, and the current Gauss-period construction/recovery reports. In the old packed primitive the algebraic algorithm already allowed arbitrary k|ell-1; the unpaid issue was SMALL conductor supply when k had been fixed first. That distinction is preserved here.

## 1. Public ell, composite k and all auxiliary data in soft k

Let r=ceil(N^(1/6)) and search for a prime ell>=max(5,r+2) by deterministic polynomial-bit primality tests. Bertrand's bound places one below twice the start, so at most O(r) candidates suffice. Put

    k=ell-1, H=k^2, C=16H.

Then k is even, N<=k^6 and k=Theta(N^(1/6)). No prime in a prescribed progression is sought. Parity and integer-square checks first handle even semiprimes and prime squares. The small C>=N-1 branch uses ordinary trial division through sqrt N<=4k+1, at soft k cost.

Factor the PUBLIC integer k by trial division/sieving in soft k, retain all prime powers and the unit predicate gcd(j,k)=1. A primitive root g modulo ell is acquired by testing candidates against the distinct prime divisors of k; at most ell candidates and polylogarithmic work per test give soft ell=soft k. Walking its powers gives the complete public logarithm table log_g(x), 1<=x<ell, in soft k. These are auxiliary-prime logarithms, not hidden-factor logarithms.

The eventually surviving hard branch has P,Q>C, so gcd(N,k*ell)=1 automatically. A preliminary proper gcd with k or ell may return a factor; if a small-input gcd saturates, the affordable small-factor branch is used instead of an invalid inverse. All subsequent k,ell and small-integer inverses are certified. Every metadata integer/exponent below has O(log N) bits unless explicitly described as a coefficient vector.

## 2. Complete scalar preparation works with this COMPOSITE size parameter

The original uniform setup's strong-order preparation does not require its size parameter to be prime. Primality entered its later tag arithmetic. Run the same paid procedure at parameter k:

1. HH large-global-order acquisition at C, followed by two-primary removal and the exact first-nonunit screen, returns a factor or gamma with odd local orders>C. Its exact-common-order branch recovers a common full order r0>C; r0^3>4096k^6>=4096N and P+Q<r0^2 give the original direct factor-sum recovery. No order factorization is supplied.
2. Put beta=gamma^(N-1). The projected local orders are coprime. The beta screen returns a factor or NoHit. Its exact-common-order branch is one, giving the ACQUIRED nonzero annihilator N-1 of the earlier gamma; the pinned unconditional short-annihilator consumer costs soft N^(31/192)<=soft k. This branch does not call a wide/QRH decoder.
3. Acquire q=beta^H and ACTUALLY screen it through C. Its orders remain coprime, but need NOT retain their old sizes. Any short unequal-order outcome gives a proper factor. An exact-common-order outcome must be one, which would force BOTH beta orders to divide H, impossible because they exceed16H. Therefore the only continuing outcome is NoHit certifying both q orders>C.

This is factor-or-NoHit preparation, NOT a statement that arbitrary composite-H powering automatically preserves large orders. A fixed number of screens cost soft sqrt C=soft k, and all modular powers have polylogarithmic exponent length. On the continuing branch beta has odd coprime local orders>C, global order>C^2=256H^2, q has both local orders>C, and P,Q>C. No numerical local order is an algorithm input.

## 3. All UNIT tags and exact native integer cover without a field modulo k

Use every j with 1<=j<k and gcd(j,k)=1. Define the actual integer representatives

    a_j=[N*j^-2]_k in {1,...,k-1},
    D_j=(N-a_j*j^2)/k,
    b_j=center_k(-j^-1 D_j),  -k/2<=b_j<k/2,
    ell_j=k*b_j-2*a_j*j,
    delta_j=a_j+ell_j.

All inverses in this definition are modulo the PUBLIC k and only at units. a_j is itself a unit. Enumerating all tags and acquiring this data costs soft k; no inverse at a nonunit tag is used. The even centered convention includes its tie explicitly.

The literal polynomial f_j(X)=a_j X^2+ell_j X+N obeys

    f_j(j)=0 mod H, f_j'(j)=k*b_j=0 mod k.

Thus f_j(j+k h)=0 mod H for EVERY integer h, by expansion. Since the true P is coprime to k, its own tag j=P modk is in this public unit catalog. P is a unit modulo H, so

    I=(a_j P+Q+ell_j)/H

is an INTEGER and

    N+delta_j-H*I=(P-1)(Q-a_j).                   (1)

Only unit arithmetic and divisibility are used; Z/k is never treated as a field.

The centered bounds give -3H<=delta_j<=H and |ell_j|<5H/2. Since P,Q>16H, I is positive. Also P<=k^3, Q<k^4/16 and a_j<k give

    I<(17/16)H+1/2<2H+1.

Hence the public L=2H+2 covers the true index. Fermat now proves the original scalar own hit

    Y_j=beta^(N+delta_j)=q^I modulo P.

Acquire beta^N once and all signed beta^delta_j in soft k. Sort/deduplicate the INTEGER deltas, retaining a representative label. Distinct deltas differ by at most4H, below both local beta orders, so distinct target differences are certified units at BOTH primes. This deduction needs no quadratic-field argument or small fiber bound. Seed differences are units because L<C. The full original scalar query with these J<=phi(k)<=k targets is therefore lawful, including hits, repeats before deduplication and public restrictions.

## 4. Saturation recovery and the parity quarter, with every order guard retained

For any retained original row and any i<4H, a saturated scalar leaf beta^(N+delta_j)=q^i gives a bounded ORIGINAL-beta collision. The same argument as the uniform interface applies: global beta order>256H^2, while

    P+Q<=16H+1+k^4/16

and |delta_j|<=3H force P+Q=1+H*i-delta_j. Exact integer square roots recover the factors. This proof did not require prime k. Proper leaf gcds factor immediately. Every selected canonical exponent is nonzero and O(log N) bits on the hard branch; if a different transformation instead gives a short global annihilator, its own nonzero exponent must be proved before using the pinned short consumer. A soft-k-bit annihilator is not silently assigned that short bound.

There is a real uniform parity simplification, stronger than a half exponent. Since k is even, every unit j and a_j is odd, ell_j is even and delta_j is odd. More precisely the EXACT integer identity is

    E_j=N+delta_j=a_j*(j-1)^2+k*(D_j+b_j).

The public inverse j^-1 modulo even k is odd. The b congruence therefore makes D_j+b_j even. Both terms on the right are divisible by FOUR, as is H=k^2. Acquire directly

    X_j=beta^(E_j/4), q_quarter=beta^(H/4).

These are known integer quarter exponents, not hidden-order root extraction. The working beta itself has odd local orders. Thus every X_j and q_quarter power has odd local order, and in

    Y_j-q^i=(X_j-q_quarter^i)*(X_j+q_quarter^i)
              *(X_j^2+q_quarter^(2i))

the last two factors are certified units: their ratios cannot equal -1 in the common odd-order subgroup. The smaller difference has EXACTLY the same zero support on EVERY restriction. No unacquired cross-companion product or square of a nonunit is divided away; the smaller expression is acquired directly from the known quarter exponents.

Moreover q=q_quarter^4. Since q_quarter has odd orders, its local orders equal those of q, so the ACTUALLY obtained q guard carries to this representation. Distinct quarter targets remain unit-separated by the same shortened integer-exponent bound. A saturated quarter leaf raises to its FOURTH power to give an original leaf, so the original decoder above applies. All quarter inputs cost soft k.

There is an additional exact content identity: for d=gcd(j-1,k), the b congruence gives D_j+b_j=0 modd, hence d^2 divides BOTH E_j and H. This is an integer statement only. Dividing group exponents by an ODD factor of d^2 is not automatically zero-support preserving, because the prepared beta orders may contain that prime. Such a general rowwise root would need a new coprimality/purification certificate. The uniform factor four is safe precisely because the orders are odd. Rowwise extraction of further powers of two can be guarded in the same way, but supplies different bases and does not shorten I's range.

The uniform quarter operation reduces integer exponents/stride by a constant but NOT the index horizon L or target degree J. The completed monic blocked scalar query still costs soft(J+sqrt(JL)), at most soft k^1.5. No equality of numeric original/quarter resultants is claimed.

## 5. Correct multiplicity and dense-character statements for composite k

Let G=(Z/k)^*. The map j->a_j has fibers of size

    h2=|G[2]|,

when nonempty, because it is a coset of the kernel of squaring. For k=2^e times an odd part with w distinct prime divisors,

    h2=2^w * c2(e),
    c2(1)=1, c2(2)=2, c2(e>=3)=4.

Thus the a palette has phi(k)/h2 values; a=1 may have h2 preimages, not at most two. No algorithm tests all those rows independently at soft k unless that work is separately bounded. The scalar product-tree query handles the actual acquired tags and deduplicates deltas, without invoking a false two-root bound.

The older inverse-tag formula kappa=rho*(1-j) modk remains a valid integer carry identity at unit j, but its prime-field NONZERO consequence does not: a product of two nonzero residues may vanish modulo composite k. rho=0 and all computed exceptional residues must be retained, not deleted by a prime-modulus argument. All are public metadata that can be classified within soft k; their classification is not itself a witness selector.

Use Jacobi only on the ODD part k_odd for an automatic character equality:

    Jacobi(a_j,k_odd)=Jacobi(N,k_odd).

For the full square coset, retain each Legendre symbol at an odd prime dividing k. At the 2-part: e=1 imposes only oddness; e=2 requires a_j=N mod4; e>=3 requires a_j=N mod8. These give the exact unit square-coset conditions, by CRT and the usual unit-square lifting. The factorization of k is acquired, so this finite public character data is lawful.

A Kronecker symbol with the EVEN denominator k need not be a function on residues modulo k: when v2(k)=1 its single 2-character requires modulus8, which k does not contain. At v2(k)=2 that factor is squared and is trivial on odd numerators; this particular failure does NOT occur. For odd v2(k)>=3 the needed modulus8 already divides k. A Kronecker symbol must not replace the preceding CRT character vector without this conductor check. No assertion that a quadratic polynomial over Z/k has only two roots is used.

For index colors, the own integer factor coordinate still gives

    I*P=a_j h^2+b_j h+c_j, P=j+k h,
    H*c_j-j*k*b_j+a_j*j^2=N.

Thus (2a_j h+b_j)^2=b_j^2-4a_j(c_j-jI) modulo k is a valid NECESSARY identity. At the even part 2a_j is not a unit, so the square-discriminant criterion alone is not an equivalent quadratic solver. At odd prime-power components the actual lifting/ramification cases must be retained; one Jacobi sign is not the complete image. No free sparse index mask or acquired colored long product follows from this descriptor.

## 6. Packed character primitive now has a supplied small conductor

Use the old GENERAL packed construction with this actual ell=k+1. Put A=R[X]/(X^k-1); for the proof only adjoin a primitive additive ell-th root via Phi_ell. The production algorithm uses the acquired public log table and length-k histograms, not the rank-k(ell-1) proof carrier.

For arbitrary a,b modulo k, each Jacobi sum histogram has ell-2 terms. The old idempotents

    h_a=k/gcd(a,k), E_a=h_a^-1 sum_(v=0)^(h_a-1)X^(a v)

and their two-trivial/cancellation corrections handle ALL nonprimitive and trivial components. Every h_a divides k and is a certified unit in R. Binary corrected Gauss multiplication acquires C_E defined by

    g_1^E=C_E*g_(E modk)

in soft(ell+k)*log(E+1) residue/bit work, hence soft k for E=N^O(1). Cyclic convolution, every histogram, logarithm table, projector and output coefficient is charged. In particular U=g_1^k=-C_k is actually acquired. This removes the old conductor-supply gap; it does not materialize all k conjugate output vectors.

Because k is EVEN, the full inverse-character identity must keep the sign component

    epsilon=X^(k/2), e0=(1/k)sum_(r=0)^(k-1)X^r,
    D=e0+ell*epsilon*(1-e0),
    g_j*g_(-j)=D for every UNIT j modulo k.

D is an acquired unit, with inverse e0+ell^-1*epsilon*(1-e0). It is NOT simply e0+ell*(1-e0), as in the older odd-k special case. Unit j is odd, so its automorphism fixes epsilon and e0. The primitive-character component specializes epsilon to -1; the packed algebra also retains all other components. No field assumption modulo k is involved.

For unit odd E, C_E*rho_(-1)(C_E)=D^(E-1), giving a cheap explicit inverse when C_E is needed. Production of the binary C_E itself uses no inverse at an unverified Gauss value.

## 7. Actual Gauss own source and a paid SHARED pair family, not a difference query

The old corrected native Gauss row is still valid with unit tags modulo composite k. For s=j^-1 and r=[Ns]_k,

    T_j=g_1^ell_j * g_j^a_j * rho_s(C_N) * g_r,
    q_G=g_1^H.

At its own P, full Frobenius acts on BOTH root systems. The unknown auxiliary-prime character phase cancels because a_j*j=Ns modulo k, and gives

    T_j=q_G^I modulo P

with the SAME integer I from (1). The integer grading ell_j+a_j*j+Ns is zero modulo k, as is the seed grade. Therefore grade zero alone still reveals no I residue. This proof does not supply an order/separation certificate or global-leaf decoder for the new Gauss base.

For a supplied j, its normalization into the packed A algebra uses U and C_j,C_r, all acquired at their actual per-row soft-k cost. A full independent list of k length-k T_j vectors would cost soft k^2 and is not claimed as soft k here.

There is, however, a genuine shared pair output. Opposite unit tags j,k-j have the SAME actual a_j, and centered carries give ell_j+ell_(k-j)=H*tau_j with tau_j in {-2,-1,0}. There are no self-antipodal unit tags for k>2. The corrected Gauss identities yield

    T_j*T_(k-j)=U^(k*tau_j)*D^(N+a_j).

Since N+a_j is EVEN, the epsilon phase cancels and

    D^(N+a_j)=e0+ell^(N+a_j)*(1-e0).

Precompute only the THREE length-k vectors V_tau=U^(k*tau), tau=-2,-1,0. Their e0 component is 1 because k is even. Every pair is then represented exactly as

    e0+ell^(N+a_j)*(V_tau_j-e0).

The common three vectors and O(phi(k)) scalar coefficients are actually acquired in soft k total: U inverse follows from its conjugate/norm identity, all signed vector powers have O(log N)-bit exponents, and ell^N is shared. This statement does not assume a=1 has only two tags or that distinct a centers remain separate. The proof uses only actual opposite-pair equal weights and their integer carries.

The pair product is a UNIT and is not product(T_j-q_G^i). There is a compulsory trivial-component warning specific to this even-k source: T_j(1)=(-1)^(N+delta_j)=1 and q_G(1)=(-1)^H=1. Thus EVERY difference T_j-q_G^i has zero e0 component. Its full cyclic regular norm is identically zero globally, for every row/index, not a usable collision selector. Removing that trivial summand or selecting primitive components requires its own support/recovery proof; no such query is supplied here.

One nontrivial scalar projection is completely explicit. At X=-1 the auxiliary character is quadratic and g_1^2=(-1)^(k/2)*ell. Every unit j is odd, so g_j=g_1, the index automorphisms fix this component, and C_N=g_1^(N-1). Consequently

    T_j(-1)=g_1^(N+delta_j)=ell^((N+delta_j)/2),
    q_G(-1)=ell^(H/2).

The sign drops because BOTH E_j and H are divisible by four. Equivalently this is the known scalar base ell^2 with target exponent E_j/4 and stride H/4. ALL these scalar values are actually acquired in soft k. The own equality survives: Q-a_j is even, so (E_j-HI)/2 is a multiple of P-1, and Fermat suffices. This is a genuine acquired nontrivial projection, but the order/separation of ell^2 is NOT inherited from beta. In particular a globally saturated projected difference is not assigned the original beta decoder. Its remaining long query has the same degree/horizon ledger.

No short long-query circuit, index selector, absolute useful colored norm, Gauss-base order screen or saturated-leaf bridge is obtained from the unit pair family or the scalar projection. The original prepared scalar beta route remains the valid covered fallback.

## 8. Full ledger and result

All conductor selection, k factorization, public primitive root/log table, scalar preparation, unit-tag row construction/deduplication, coherent quarter inputs, ONE packed C_E and the shared three-vector pair family fit soft k=soft N^(1/6), including residue bit costs and every short-annihilator branch. The scalar canonical query/restrictions still have the old soft(J+sqrt(JL)) acquisition/localization bound; the quarter representation changes no degree-times-horizon exponent.

The useful acquired refinement is now a genuinely supplied small conductor with a correct composite-modulus native source and a phase-correct packed shared family. The even-modulus Jacobi/root-count pitfalls and q-order screen are explicit. No all-input soft-k colored difference evaluator or new factoring exponent is proved. A next gain must acquire a source/recovery-preserving DIFFERENCE query or a different covered scalar selector, not only the known unit pair products or their grade cancellation.
