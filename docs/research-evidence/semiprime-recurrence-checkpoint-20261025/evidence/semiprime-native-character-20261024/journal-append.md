
## 2026-10-24: supplied character conductor, primitive norm, and native differences

This pass closes an auxiliary-conductor supply gap and constructs a
zero-safe primitive-character norm of one acquired packed element in
soft O(k). It also gives a paired-character bridge back to an original
scalar witness. These are supporting constructions: the whole weighted
row/long-index product is still unacquired in soft k. The original
covered scalar query remains soft(J+sqrt(JL)), J<=k,L=2k^2+2. No new
factoring exponent or completed bit/Lean composition is claimed.

Choose a prime ell of sixth-root size FIRST, then use k=ell-1 as the
row modulus. Now the order-k character conductor is actually supplied
at cost soft k, without a least-prime-in-a-prescribed-progression premise.
Factor k publicly, find a primitive root modulo ell by bounded candidate
tests, and acquire its complete logarithm table. Use ALL UNIT tags
j modulo this even composite k. Their native a_j,b_j,ell_j and own
integer index identities require only unit inverses, not a field modulo k.
The actual q=beta^(k^2) order screen remains necessary and paid: powering
by composite k^2 need not preserve large orders. Coprime-order preparation
and the exact common-order branches give a factor or the usual guards.

The original cover, delta deduplication and saturated original-leaf
decoder remain valid. A useful exact refinement is 4|E_j and 4|H, where
E_j=N+a_j+ell_j and H=k^2. Indeed E_j=a_j(j-1)^2+k(D_j+b_j), and D_j+b_j
is even. Direct targets beta^(E_j/4) and base beta^(H/4) preserve EVERY
local hit because beta's orders are odd; the two plus companions in the
fourth-power factorization are units. This changes neither J nor L.
General gcd(j-1,k)^2 content is also integral, but division by its odd
factors needs additional order coprimality. Composite square-map fibers
can have many elements, so old at-most-two exception counts cannot be
used. The even-denominator Kronecker issue is specifically v2(k)=1;
at v2(k)=2 its 2-character is trivial on odd inputs.

For the packed Gauss algebra A=(Z/N)[X]/(X^k-1), define

    e0=(1/k)sum_(r<k)X^r, epsilon=X^(k/2),
    D=e0+ell*epsilon*(1-e0), u=g_1, U=u^k.

For unit j, g_j*g_-j=D. The epsilon phase must be retained. The native
T_j=u^ell_j*g_j^a_j*g_(j^-1)^N has grade zero and preserves the own
collision with q_G=u^(k^2). Its pair product is
T_j*T_-j=q_G^tau_j*D^(N+a_j), tau_j in {-2,-1,0}; this whole pair family
has three acquired vectors plus soft-k scalar metadata. It is a unit
aggregate. Every raw difference T_j-q_G^i has zero trivial component,
since T_j(1)=q_G(1)=1. Its FULL cyclic norm is therefore identically zero,
including on restrictions with no useful collision. That norm cannot
serve as a detector; the trivial component must be removed.

One actual primitive norm is nevertheless acquired cheaply. The
Ramanujan projector e_prim=(1/k)sum_l c_k(l)X^l and a CRT decomposition
of (Z/k)^* into public cyclic generators are acquired in soft k. For a
generator g, form orbit products by binary recursion
N_(2h)=N_h*rho_(g^h)(N_h), with the usual final odd factor. Applying this
over the generators takes O(log phi(k)) rank-k multiplications and
coefficient permutations, with no inverse of the supplied element V.
The result is nu*e_prim, where nu is its primitive norm. Extract nu from
the constant coefficient by multiplying by k/phi(k), a certified unit.
This works at zeros and costs soft k, but requires the ACTUAL V vector.
It computes one supplied native leaf norm, not the long product.

The orbit shortcut was tested on native rows: rho_j(T_j) retains
u^N*g_(j^2)^a_j*g_j^ell_j and transforms the seed to g_j^H. Replacing
these varying weighted rows and seeds by one common orbit changes the
query. Stickelberger multiplicative ideal data likewise do not determine
the extra cancellation in a unit-minus-one difference. The group-ring
identity at an own hit is

    Lambda_j-HI=rho_(j^-1)*(P-rho_j)*(Q-a_j*rho_j).

Here P-rho_j annihilates the ZERO-GRADE intermediate
u^(Q-a_j*rho_j), since Q-a_j*j=0 mod k. It does not annihilate raw u,
whose Frobenius still contains the auxiliary additive-root phase.

Two actual difference normalizations were executed. Set
R_j=D^(-E_j/2)T_j and Q0=D^(-H/2)q_G. They have conjugation norm one,
preserve the own hit, and satisfy R_j*R_-j=Q0^tau_j. The pair difference
is z^2-S_j*z+Q0^tau_j, with S_j=R_j+Q0^tau_j/R_j. Its mixed traces and
their symmetric coefficients remain unacquired for the full family.
Alternatively V_j=beta0^E_j*R_j and q_V=beta0^H*Q0 preserve the original
prepared scalar base. For f=V_j-q_V^i there is the exact ideal identity

    (f,bar(f))=(f, beta0^(2E_j)-beta0^(2Hi)).

A paired hit at the SAME row/index therefore certifies an original beta0
collision, with its valid bounded decoder. An unpaired primitive norm
zero does not supply that certificate. The scalar augmentation of this
safe normalization is precisely the old original long query.

Root's single-quotient rewrite was also executed:

    T_j^j=q_G^c_j *rho_(j^-1)(C_j)^N*C_j^(-a_j*j),
    c_j=(N-a_j*j^2+k*b_j*j)/k^2, u^j=C_j*g_j.

Streaming the actual corrected histogram recurrence C_(e+1)=C_e*c_(e,1)
acquires a full fixed-index primitive scalar product in soft k^2 TIME
and soft k MEMORY. This is an actual overbudget completion, not an
output-size lower bound. The long seed interval is additional. Removing
the j power from a selected paired beta-coupled hit is legitimate after
the already paid BOTH-k-rough scalar preparation; j being a unit modulo
k alone is insufficient. No raw Gauss saturation is assigned that bridge.

Reports, primary-source checks, exact reviews and preservation validator:
/tmp/semiprime-native-character-20261024. Reviews corrected the precise
Kronecker conductor condition and the zero-grade Frobenius qualifier.
No example campaign, broad Lean build, commit or push was performed.
Preserve all previous prefixes,270 frozen entries and concurrent RH work.
