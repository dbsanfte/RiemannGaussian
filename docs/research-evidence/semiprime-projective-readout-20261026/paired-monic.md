# Paired monic families: exact swap, a quadratic exchange, and conjugate-cross evolution

26 October 2026. Read the frozen axis-supplier/hybrid handoff,
signed-weight source, coefficient-forms and earlier scalar swap/inverse
fusion audits. Paper only; no numerics, code, Lean or repository edits.

**Constructive result:** the two actual monic root lists have an exact
colour permutation and row-dependent Adams twist, and their +/-colour
quadratic factors obey a short explicit exchange. The regular twist
difference can be screened within soft K, including its legal saturated
branch. The remaining exchange correction is another explicit geometric
family, not an assumed unit. Conjugate-cross first-jet statistics have a
closed finite recurrence, but it retains long product amplitudes. No
cheap projective readout or complete factoring gain is obtained.

## 1. Actual colour permutation and phase equality, with no omitted carry

Use K,H=K^2 and the two families of `hybrid-handoff.md` Sections1-4.
For an A-colour j put

    a=[N*j^(-2)]_K, jstar=[N*j^(-1)]_K.

The B-row at jstar has b=a, so its coefficients are (1,a), the
swap of A's (a,1). Its phase is EXACTLY the same centered ell modulo H.
Indeed the stationary phase is

    ell(a,b,j)=-a*j-b*N*j^(-1) mod H.

Changing the lift of a stationary colour j by K changes this expression
by a multiple of H, because a*j^2=bN mod K. For B choose the lift
jstar=N/j modulo H, obtaining

    ell(1,a,jstar)=-N/j-a*j=ell(a,1,j) mod H.

The same deterministic centering then gives integer equality, not
ell equality with a discarded unknown H-carry. This is the needed
finite-parameter map; jstar is acquired by a unit inverse modulo K.

Write

    yA=pi^ell*barpi^(a+N),
    yB=pi^ell*barpi^(1+aN), gamma=barpi^(N-1).

Then the actual globally valid relation is

    yB=yA*gamma^(a-1),
    yA^a/yB=pi^((a-1)*ell)*barpi^(a^2-1).          (1)

The second relation genuinely cancels the large N exponent. Both
lists, twists and the right side are acquired within soft K; exponents
have O(log N) bits. This is a row-dependent twist, NOT equality of
root multisets and NOT an acquired integer q-shift.

At the nonsplit field R, put S=N/R. Their physical exponents are

    T_A=aR+S+ell, T_B=R+aS+ell,
    T_B-T_A=(a-1)(S-R).                            (2)

Even when A's row hits q^I, B's paired physical exponent need not be
divisible by H. It therefore need not have ANY integer physical clock
index there, much less the same I in [0,2H]. Modular q-indexing exists
under roughness but is not an acquired small integer. Old scalar
swap/common-index coverage concerned opposite factors and a scalar
base; it cannot be copied through a nonsplit Frobenius orientation.

For clarity, (1) can be regarded as evaluating the same a-coordinate
character at barpi and barpi^N, with interchanged prefactors. The
arithmetic N-power relation alone does not evaluate its long clock
norm or make N-powering additive.

## 2. New finite paired exchange after grouping +/-j

The A-colours j and -j have the same a and opposite phase residues.
Their centered phases are exactly opposite here: the potential centered
endpoint ell=H/2 is impossible since aN is a 3-unit whereas ell would
be divisible by3. Corresponding B-colours are +/-jstar and have the
same respective phases. Put

    T=pi^ell+pi^(-ell),
    cA=barpi^(a+N), cB=barpi^(1+aN),
    PA(z)=(1-z*cA*pi^ell)(1-z*cA*pi^(-ell))
         =1-cA*T*z+cA^2*z^2,
    PB(z)=1-cB*T*z+cB^2*z^2.

Eliminating the acquired common trace gives the EXACT finite identity

    cB*PA(z)-cA*PB(z)
               =(cB-cA)*(1-cA*cB*z^2).            (3)

This is an actual two-family exchange, not a generic relabelling of
one polynomial. At the physical clock z=q^(-i), its remaining factor is

    1-barpi^((a+1)*(N+1))*q^(-2i).                 (4)

No denominator was used in deriving (3). In particular at PA=0 it
relates PB to the correction (4); it does not erase that correction.

### Pay the regular twist gate

When a=1 the pairs coincide. The tags satisfy j^2=N mod K, so their
number is bounded by the constant unit-root branch count for the
actual at-most-three-prime conductor modulus (at most16). Original
one-row length-O(H) queries pay these cases in soft K with their
nonsplit quadratic consumer; unit results permit pruning them.
This is the familiar a=1/inverse-fusion exception, not new credit.

For a!=1, cB-cA is a unit times gamma^(a-1)-1. Acquire the gamma
power walk through K and classify each quadratic-algebra value by
its norm and coordinates, in soft K. A proper norm/coordinate gcd
factors. If the whole value is globally zero, taking its norm gives

    beta^[2*(a-1)*(N-1)]=1 globally.

This is a NONZERO short exponent on the supplied large odd beta;
the inherited generic extractor costs T_ext once. At the nonsplit
prime, a zero norm means the whole element is zero, so a saturated
norm with a nonglobal-zero element gives a proper coordinate gcd.
Thus the regular twist gate is a valid factor-or-UNIT certificate.
It does not assume every formal nonzero difference is a unit.

### Remaining correction and its full cost

The factor (4) is NOT proved unit by the twist gate. At R its exponent
in pi is

    (a+1)(R+S)-2H*i.

In the unbalanced case it can involve a*S of order K^5, beyond the
available O(H^2) integer-equality bound. Consequently a common clock
hit of both paired quadratics is not excluded by the good-family
unique-hit proof alone.

The entire correction bank is nevertheless an actual acquired GP
query: O(K) starts barpi^((a+1)(N+1)), common clock q^2, length2H+1.
The existing monic engine reads it in soft(K+sqrt(KH))=soft K^(3/2).
Every nonunit is safely decodable: at the nonsplit field it is a
whole point zero; coordinate/norm classification gives a proper
factor unless globally zero. In the global case its scalar norm gives
beta raised to

    2*((a+1)*(N+1)-2H*i),

which is nonzero for 0<=i<=2H because N>256H^2 and a+1>=2.
It has O(log N) bits and supports T_ext. All such labels and endpoints
are explicit; the gate is not silently certified by a weak unit bound.
Paying this correction at the current cost supplies no projective gain.
An unproved cancellation of its values across a would be a new theorem.

## 3. Why paired tags do not give two known factor ratios

Only ONE family has the unique-hit provenance at the nonsplit field:
A if R is smaller, B if R is larger. The other family can have zero,
one or multiple aliases on its chosen interval. Equations (1)-(2) do
not transfer the good first-jet ratio to it. Hence one cannot set
U_A/V_A=R mod n and U_B/V_B=S mod n at the same field and eliminate
an amplitude using PQ=N.

Moreover reduced integer tags are not field-valued factors. Even if
r=[R]_n and s=[S]_n are both supplied as small integers, rs=N MODULO n,
not as an identity in characteristic R. Replacing this by rs=N in
that field would be false (N=0 there). Complementation is the paid
INTEGER operation N*r^(-1) modulo n AFTER tag acquisition, not a
polynomial relation among the unacquired first-jet values in B.

## 4. Execute the conjugate-cross Wronskian proposal

For the finite leaf ordering put a_e=1-y_j/q^i and tag w_e=[j]_n.
Let the running product/first-jet states be P,V,U, initialized(1,0,0):

    P'=aP, V'=aV+P, U'=aU+wP.

Conjugate both coefficients and states. The proposed pure-conjugate
cross statistic is

    W=U*bar(V)-bar(U)*V.

At a good unique hit U/V is a base-field integer tag, so W=0 there.
This is a correct one-prime relation, not acquisition of W or a
licensed global annihilator when W vanishes additively.

The actual recurrence CLOSES if one retains the following amplitudes:

    N0=P*bar(P), X=U*bar(P), Y=V*bar(P),
    n_a=a*bar(a),
    N0'=n_a*N0,
    X'=n_a*X+w*bar(a)*N0,
    Y'=n_a*Y+bar(a)*N0,
    W'=n_a*W+a*X-bar(a)*bar(X)
                       -w*(a*Y-bar(a)*bar(Y)).     (5)

Initial values are N0=1,X=Y=W=0. N0 is base scalar, W is anti-
conjugate, and X,Y are quadratic elements; this is a fixed real-
linear state of rank six. Thus no missing state closure is being
asserted. The problem is its long amplitudes and advancement cost.

At a good zero both a and bar(a) vanish. Equation(5) resets N0,X,Y,W
to zero at that prime. The later recurrence cannot reveal WHICH tag
caused that reset from W alone. Dividing by N0 before or at the reset
is not licensed; on the unit branch it produces the same rational
cofactor sums and loses the desired singular normalization.

The root twist (1) does not identify the coefficient pairs a,bar(a):
conjugation also changes the clock to bar(q), while the paired B list
uses q and a row-dependent gamma power. No constant known clock shift
or same-boundary relation closes (5) on W alone. The direct finite
implementation computes U,V in the old constant-rank first-jet engine
then W in O(1), costing soft K^(3/2). Tensor/Gram descriptions do not
pay a faster invariant readout. At a global additive W=0 there is no
short beta label; only a proper coordinate/norm gcd is an immediate
factor branch, and the valid soft-K tag fallback still needs U,V.

## Outcome and strongest next candidate

The concrete new opportunity is the ACTUAL paired exchange (3): same
phase trace, different radial character, with its regular twist gate
paid and the remaining correction family explicitly initialized and
charged. A useful new identity would have to contract that correction
or the paired first-variation ratio at collisions, retaining both
families' finite endpoints. It cannot presume both weak pairs have
factor provenance at the same field.

The Wronskian state is exactly closed but does not supply such a
contraction. No source identity or scalar readout at soft K was found;
the inspected native constructions still retain the long correction
or amplitudes. The uniform weak-output target and its paid HH consumer
remain valid and open. This report claims neither an obstruction to
all paired-family algorithms nor a new factoring exponent.

## 5. Conditional pure-3-power modulus: exact AP reindexing of the correction

This section assumes the proposed conductor-removal preparation has
INDEPENDENTLY supplied a legal pure K=2*3^e with all needed beta,W,
pi/q promises. The algebra below does not prove that preparation.
The original conductor-aware result above is unchanged.

For pure K, the map j->a=[N*j^(-2)]_K has image EXACTLY

    a=a0+6t, 0<=t<K/6,
    a0=1 if N=1 mod3, a0=5 if N=2 mod3.

Each a has exactly TWO tags j,-j. This follows from the two roots
of a unit square modulo 3^e and the unique odd lift modulo2*3^e;
no other phase multiplicity is hidden. Grouping those two tags into
PA,PB is exactly the quadratic grouping in Section2.

If a=1 is removed by its separately paid original query, the remaining
AP is still a single progression: it starts at7 and has K/6-1 terms
when N=1 mod3; otherwise it starts at5 and has K/6 terms. Denote its
start a_start and length L. The correction (4), ONCE per +/-tag pair,
is exactly the two-GP rectangle

    product_(t=0)^(L-1) product_(i=0)^(2H)
        [1-Z0*B0^t*Q0^i],
    Z0=barpi^((a_start+1)*(N+1)),
    B0=barpi^(6*(N+1)), Q0=q^(-2).                (6)

All starts and generators are acquired from O(log N)-bit exponents.
Applying the exchange separately at j and -j would count the same
correction twice; (6) removes that duplication. It is exact for the
PA/PB paired exchange, and squared repetition would in any event
preserve local-zero/nonunit predicates over squarefree N. This is
not a claim that the correction alone has coverage of the main query.

Oddness supplies one further zero-safe simplification. Since a is
odd, set d=(a+1)/2 and C0=barpi^(N+1). Then

    1-C0^(a+1)*q^(-2i)
       =(1-C0^d*q^(-i))*(1+C0^d*q^(-i)).

The second factor is a certified unit at every local component:
C0^d*q^(-i) has odd order and cannot be -1. Thus, for predicates,
(6) is equivalent to

    product_(t<L,i<=2H)
        [1-C0^d0*(C0^3)^t*q^(-i)],
    d0=(a_start+1)/2.                             (7)

Only a monomial/unit-valued background is omitted, not a collision
factor. This halves the exponent/clock convention and replaces the
AP step6 by3; it yields no power-scale length reduction.

At the nonsplit factor R, Frobenius gives the TRUE arithmetic base
relation

    C0=barpi^(N+1)=pi^(R+S), S=N/R.               (8)

It follows from barpi^N=pi^S and barpi=pi^R. The integer R+S is
not acquired by (8); globally at the split other prime the same
pi-power formula is not asserted. Neither C0^3 nor q is an auxiliary
root of unity, and their ratio is not a supplied bounded q-shift.
The explicit related known identity C0^H=bar(q)^(N+1) retains bar(q),
not q with an acquired short exponent. Replacing C0^3 by a primitive
cube phase would therefore change the actual target.

Finite Ramanujan/cyclic multiplication would collapse a COMPLETE
auxiliary cubic orbit, product_(r=0)^2(1-z*zeta^r)=1-z^3.
The terms in (7) are powers of the arithmetic C0^3, not such an orbit.
Completing missing integer d residue classes instead only trades AP
step for a longer ordinary exponent interval; the finite cutoff and
long product must be retained. A root-of-unity normalizer is not a
paid native scalar substitute.

Finally the concrete old readout of (6) or (7) has L=Theta(K),
clock lengthTheta(H)=Theta(K^2), and cost

    soft(L+sqrt(L*H))=soft K^(3/2).

The acquired kernel polynomial, every GP start and finite tail are
included. The AP structure makes this ONE genuinely initialized
two-base rectangle rather than K unrelated bases, but its total
factor mass remainsTheta(K^3). This is an upper cost of the current
engine, not a lower bound against a new double-principal or cyclic
norm algorithm. The Frobenius relation (8) is the precise extra native
structure such an algorithm would have to exploit without acquiring
R or discarding the collision-bearing correction.
