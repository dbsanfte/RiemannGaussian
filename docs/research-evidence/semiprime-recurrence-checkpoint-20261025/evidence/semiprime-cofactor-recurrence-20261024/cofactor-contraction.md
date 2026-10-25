# Fixed-width contractions for unique-hit recovery and the actual cofactors

24 October 2026. Scratch only. This derives and EXECUTES a simpler three-state polynomial recurrence for two sufficient unique-hit recovery outputs, as well as a weighted recurrence for the actual two Bezout cofactors. The simpler cost is soft(sqrt(JL)+J), hence soft k^(3/2), without acquiring the full long remainder. Its dimension is constant but its polynomial degree J is paid; the exact-cofactor variant has degree J+1 and a q-factorial start. A tested telescoping shortcut and a shared triangular normalization do not improve the clock. No new all-input factoring exponent is claimed.

## Actual input, branch promise and prior boundary

Use unique-gcd.md SHA256 `8eba0f3676ef0de414f4b48fa463a54058aed4fed97db3a0557be0189ec8c862` and implicit-evaluation.md SHA256 `5600980cbd17a37e09c79ed9503766cd081df9753bf8593443cc66bc0d4c0646`. The canonical repaired MINUS family has acquired unit roots V_j, retained original row labels, unit-separated after the source's actual factor/separation preparation, and

    F(X)=prod_(j<J)(X-V_j), J=Theta(k), F monic,
    G_L(X)=prod_(i<L)(X-q^i), L=3H+2, H=k².

Every 1-q^r through C=16H is a certified unit. Actual q, beta,W have odd component orders, with the stated rough preparation; this is not inferred from an unscreened changed base. All metadata have O(log N) bits. The canonical one-representative family, not an extra multiplicity-doubled augmentation, is used here. J=1 is handled by its original one-row locator; assume J>=2 below.

When the SMALLER prime P is nonsplit, exactly one canonical minus row hits exactly one seed in [0,L), and its root is simple. This local branch promise will make one cofactor nonzero there. It does not supply the local field, hit position or any inverse of a hit factor. The final validation controller remains safe on the opposite orientation and falls back to the original covered query if required.

The earlier q-Pascal/Krylov and terminal-feedback calculations in the preserved journal around 38636--38922 did not acquire their terminal functional. The construction here is instead an explicit complementary-grid scalar sum with a supplied barycentric initial weight. Its degree-dependent q-product budget is not called a degree-free fixed-dimension algorithm. Old selected q-factorial/prefix acquisition is used and credited.

## The simpler sufficient output: acquire two derivative sums

For unique-index recovery the barycentric weights are unnecessary. Root supplied this simplification; here are its exact initialized recurrence and degree ledger. Set x_i=q^i and put

    T_s=sum_(i<L) x_i^s prod_(r!=i)F(x_r), s=0,1.

At the promised P-side unique hit I, T_0=prod_(r!=I)F(x_r) is NONZERO and T_1=x_I T_0. Thus the same validated root/row consumer as for the two cofactors applies to alpha=T_1/T_0. Its denominator norm is either a unit or gives a proper factor, never saturated in the promised branch. Test the actual F(alpha), localize to the supplied roots, then use the identified ORIGINAL row's length-L locator. On the other orientation use the original fallback if validation fails; no unproved cover is inferred.

The actual prefix state is

    A_n=prod_(r<n)F(x_r),
    T_s,n=sum_(i<n) x_i^s prod_(r<n,r!=i)F(x_r),
    [A_0;T_(0,0);T_(1,0)]=[1;0;0].

Here T_s,n has two subscripts. In column-vector notation its polynomial transition is

    [A_(n+1);T_0,n+1;T_1,n+1]
      =[[F(x),0,0],[1,F(x),0],[x,0,F(x)]]
                                      [A_n;T_0,n;T_1,n], x=q^n. (U1)

There are NO evolving-factor divisions, q-factorial starts or barycentric weights in (U1). It is also the exact commuting product in the fixed-rank algebra B[e,h]/(e²,eh,h²):

    prod_(i<L)[F(x_i)+e+h x_i]
                =A_L+e T_0+h T_1.                         (U2)

These are first derivative/Hasse coefficients of prod_i(F(x_i)+u+v x_i) at u=v=0, not Bezout cofactors and not a presumed local sparse-recovery oracle. The product identity is global and valid at every zero pattern. All three scalar outputs are acquired by the actual polynomial-matrix blocking construction of Section 3, now with degree J and initial vector (1,0,0). Choose b~sqrt(L/J), build its degree-Jb baby block, evaluate at L/b actual giant starts, and multiply. Total soft(Jb+L/b+J)=soft(sqrt(JL)+J); the clipped tail is paid. The alternative (U2) uses only rank-three scalar arithmetic and known monic/public-unit operations, not an inverse in a singular perturbed algebra.

Even the unweighted off-diagonal baby block has an exact degree test. Its two entries are

    U_0,b(X)=sum_(t<b)prod_(r!=t,r<b)F(q^r X),
    U_1,b(X)=X sum_(t<b)q^t prod_(r!=t,r<b)F(q^r X).

For dyadic b their leading coefficients are respectively

    q^[J b(b-1)/2] sum_(t<b)q^(-Jt),
    q^[J b(b-1)/2] sum_(t<b)q^((1-J)t).

Both sums factor into 1+odd-order-group-element factors and are units. Hence their degrees are EXACTLY J(b-1) and J(b-1)+1 on every prepared input. For b=2 the first entry is simply F(qX)+F(X), with unit leading coefficient 1+q^J. This tests the triangular/commuting simplification directly: it removes the barycentric overhead, but does not make baby-block degrees independent of J. No scalar-algorithm lower bound follows.

The sections below retain the stronger EXACT-COFACTOR output and its telescoping test, rather than mislabeling T_0,T_1 as those cofactors.

## 1. Rewrite the actual cofactors as complementary-grid sums

Let h=G_L mod F, and define the symmetric Bezout matrix K by

    sum_(r,s<J)K_(r,s)X^rY^s
       =[F(X)h(Y)-F(Y)h(X)]/(X-Y).

Let sigma=(-1)^(J(J-1)/2). From its actual Vandermonde diagonalization, the two cofactors are globally

    C_s=adj(K)_(0,s)
       =sigma sum_j V_j^s/F'(V_j)
                               *prod_(a!=j)G_L(V_a), s=0,1.  (1)

No G_L(V_j) is inverted. Every F'(V_j) is an acquired unit. One may first prove this using a diagonal matrix and the adjugate transformation law; it is valid at zeros as a polynomial identity.

Set x_i=q^i and lambda_i=1/G_L'(x_i), a known UNIT. Complementary partial fractions, or the sum of residues of X^s/(F(X)G_L(X)), give the exact alternate contraction

    H_s=sum_(i<L) x_i^s lambda_i prod_(r!=i)F(x_r),
    C_s=(-1)^[J(J-1)/2+JL+1] H_s, s=0,1.             (2)

The residue derivation is initially made over independent formal roots where all factors are units. Clearing the unit discriminants F'(V_j),G_L'(x_i) gives a universal polynomial identity, which proves (2) after substitution in the actual composite ring. It does NOT authorize inversion of any F(x_i). This preserves precisely the two true Bezout cofactors, rather than replacing the original norm by a different ordinary determinant.

## 2. Acquire the barycentric starts and derive the short recurrence

The exact grid derivative is

    G_L'(q^i)=(-1)^i q^[i(L-1)-i(i+1)/2]
                        (q;q)_i (q;q)_(L-1-i),
    (q;q)_n=prod_(r=1)^n(1-q^r).

In particular lambda_0=(q;q)_(L-1)^(-1). Acquire that prefix and (q;q)_L by the previously paid q-factorial-prefix algorithm in soft sqrt L work. All factors through L<C are guarded units; actual fixed-rank inverses are obtained, not just asserted. Their only long exponent metadata have O(log N) bits.

For 0<=i<L-1, the ratio, as an ACTUAL rational function of x=q^i, is

    rho(x)=lambda_(i+1)/lambda_i
          =q(1-q^(1-L)x)/(1-qx)
          =a(x)/b(x),
    a(x)=q-q^(2-L)x, b(x)=1-qx.                      (3)

For convenience extend lambda_L=0. Then the same ratio at i=L-1 has zero numerator and a UNIT denominator, so the final update is valid too.

Define the prefix states

    A_n=prod_(r<n)F(x_r),
    Z_n=lambda_n A_n,
    B_s,n=sum_(i<n) x_i^s lambda_i
                              prod_(r<n,r!=i)F(x_r).

Their TRUE initial column state [Z_0;B_(0,0);B_(1,0)] is [lambda_0;0;0]. Direct multiplication gives

    [Z_(n+1);B_0,n+1;B_1,n+1]
        =M(q^n)[Z_n;B_0,n;B_1,n],
    M(x)=[[rho(x)F(x),0,0],
          [1,F(x),0],
          [x,0,F(x)]].                              (4)

Here B_s,n denotes the s-labelled component, not a coefficient of a supplied full polynomial. At n=L, the second and third components are exactly H_0,H_1. The first vanishes because lambda_L=0; it is not a lost terminal amplitude. Every state variable and start has now been defined constructively.

Clear the UNIT denominator b(x):

    N(x)=[[a(x)F(x),0,0],
          [b(x),b(x)F(x),0],
          [xb(x),0,b(x)F(x)]], degree N=J+1.          (5)

Every b(q^n)=1-q^(n+1) is guarded for n<L. Thus the actual product of N(q^n), applied to the acquired initial vector, and divided by the acquired UNIT (q;q)_L yields (4)'s complete output. No F(x_n), cofactor, target resultant or evolving state is inverted. This is valid through the unique zero and through any other component's zero pattern.

## 3. Execute the entire q-matrix product and charge its degree

Choose a dyadic baby length b of order sqrt(L/(J+1)), with direct treatment of bounded lengths. Build the actual polynomial matrix

    N_b(X)=N(q^(b-1)X)...N(qX)N(X).

Fixed matrix size three gives degree at most (J+1)b and softly linear polynomial product-tree cost in that degree. The coefficient arrays of F, a,b and all q scales are actual data. Evaluate its entries by monic MPE at the actual giant starts X=q^(bg), g<floor(L/b), and multiply the resulting constant-size matrices in order. The clipped final block is built/evaluated with its actual length, at cost at most soft((J+1)b). Starts and matrix outputs cost O(L/b); none is a proof-only generator.

Including the two q-factorial prefixes and unit inversion, the COMPLETE work is

    soft((J+1)b+L/b+J+sqrt L)
      =soft(sqrt((J+1)L)+J+sqrt L).                  (6)

This acquires BOTH actual cofactors by (2), not only their update law, and never emits the J-coefficient remainder h or the L grid array. At J~k,L~k² it gives the retained soft k^(3/2) clock. It is a new initialized cofactor interface at that clock, not a whole-query acceleration.

At the promised smaller nonsplit prime, H_0 has exactly ONE surviving summand: lambda_I prod_(r!=I)F(x_r), a unit there. Thus Norm(H_0) is unit or gives a proper factor. In the unit branch alpha=H_1/H_0 has P-side value q^I. Use the pinned unique-gcd report's actual F(alpha) test and row-factor localization, obtaining a proper factor or identifying one original V_j globally. Its one-row interval locator costs soft sqrt L extra and uses the original bounded index consumer. A saturated norm leaf is never promoted to whole split equality. On a nonpromised orientation a failed alpha validation or unit one-row query invokes the original full-family fallback; no new cover is assumed.

## 4. Execute the triangular-factor sharing test

The recurrence's lower diagonal factors share F(x), suggesting cancellation of their whole baby product. That cancellation would be invalid at the hit. More precisely, the normalized B_0 baby-block contribution from an initial Z is

    sum_(t<b) q^t (q^(1-L)X;q)_t/(qX;q)_t
                                       *prod_(r!=t,r<b)F(q^rX).

Clearing its known denominator (qX;q)_(b-1) gives the polynomial

    W_b(X)=sum_(t<b) q^t(q^(1-L)X;q)_t
                      (q^(t+1)X;q)_(b-1-t)
                                       *prod_(r!=t,r<b)F(q^rX). (7)

This is an acquired exact block expression; its denominator only uses the already guarded local exponents on an actual block. The first nontrivial step is explicitly

    W_2(X)=F(qX)(1-qX)+q(1-q^(1-L)X)F(X).

All terms and additive cross contributions are retained. The dyadic leading-degree calculation, supplied independently by recurrence_review and checked here, is particularly strong:

    [X^((J+1)(b-1))] W_b
      =(-1)^(b-1) q^[(J+1)b(b-1)/2]
                           sum_(t<b) q^[t(1-L-J)].    (8)

For b=2^u, this sum factors as prod_(v<u)(1+q^[2^v(1-L-J)]). EVERY factor is a unit on the actual odd-order branch, since an odd-order group element cannot equal -1 in any local component. Hence W_b has EXACT degree (J+1)(b-1) on every prepared input, not just on a generic polynomial F. This prevents dropping the degree factor in THIS literal block construction. It is not a lower bound on scalar-only contractions using another representation.

There is a second direct hit test of a common-factor cancellation. On the actual block containing the unique P-side zero, its product prod_(r<b)F(q^rX), evaluated at the actual start, is zero, while W_b is nonzero: only the single hit-omitting summand survives and all its weights/nonhit factors are units. Therefore that whole F baby product does not divide the off-diagonal polynomial globally. A common diagonal factor cannot be canceled from the full state without erasing the detector. Alternate projective or commuting-dual-number representations may still be useful, but their nonconstant lambda data must remain acquired.

## 5. Test an explicit q-Gosper shortcut, with resonance scoped correctly

A tempting rational summand is lambda_i x_i^s/F(x_i). Seek the particular polynomial-numerator certificate

    Z_i=lambda_i r(x_i)/F(x_i), s=0 or1,
    Z_(i+1)-Z_i=lambda_i x_i^s/F(x_i).

Its ACTUAL polynomial identity would be

    a(X)F(X)r(qX)-b(X)F(qX)r(X)
                                  =b(X)F(qX)X^s.    (9)

For a polynomial r of degree d<=L+J-2, the highest coefficient has multiplier q^(J+1)-q^(d+2-L). If d>s this is a UNIT multiple of 1-q^(L+J-d-1), within the actual screen, so the coefficient cannot vanish. Thus any such short certificate has degree at most s. The low coefficients then force r=X^s/(q^(s+1)-1); its leading equation would require q^(L+J)=1, forbidden because L+J<C. This tests and rejects that short polynomial-numerator certificate on the actual source.

The degree L+J-1 is resonant: the leading multiplier vanishes identically. It is NOT excluded by that degree argument, and arbitrary larger degrees are not under its unit guard. One can acquire the unique formal solution of (9) through that long degree by relaxed convolution; its diagonal is F(0)(q^(n+1)-1), guarded through the required native range. This costs soft L and still requires verifying the resulting exact polynomial identity; resonance does not supply a free polynomial solution.

A useful optional boundary check is stronger but restricted. Acquire actual F(1) and F(q^L) in soft J; proper norm gcds factor. If either is not certified unit, make no optional-certificate conclusion and continue the core algorithm (4). In particular the outside index L is NOT silently passed to the original [0,L) decoder. If both norms are unit and the smaller-nonsplit promise holds, the unique hit I is interior. Set

    lambda_i(z)=lambda_0 q^i
                          (q^(1-L)z;q)_i/(qz;q)_i.

At z=1 these are the actual weights, units for i<L, and lambda_L(z) has a factor 1-z with a unit denominator. If a polynomial r of ANY degree satisfied (9), substitution X=zq^i and finite telescoping would give

    sum_(i<L) lambda_i(z)(zq^i)^s/F(zq^i)
      =lambda_L(z)r(zq^L)/F(zq^L)
                                  -lambda_0 r(z)/F(z).

At the P-side field, the left side has one simple pole at z=1, with nonzero residue: only the own seed is a root, F'(q^I)q^I and its weight are units. The right side is regular because both tested boundaries are units and r is polynomial. Contradiction. This excludes that PARTICULAR r/F certificate on this continuing branch, including a long resonant polynomial r. It does not exclude rational r with additional boundary poles, other telescopers, or scalar algorithms. Such extra poles and their residues would need actual acquisition and a lawful consumer.

## Completed primitive and remaining improvement

The main sufficient recovery primitive is the unweighted derivative product (U1)--(U2), with its acquired start and degree-J cost. The stronger exact-cofactor output is the globally valid sum (2), its acquired weighted three-entry start, and the zero-safe constant-width matrix product (4)--(6). It acquires the cofactors without acquiring the long remainder. The source-specific unique hit gives a short validated factor/row consumer. The degree-dependent block price is real in this representation, as the actual dyadic off-diagonal coefficient (8) shows. The tested cheap telescoping certificate does not remove it.

A genuine next improvement would contract this particular triangular q-product or its two scalar lower-left entries faster than soft sqrt(JL), retaining the q-hypergeometric weights and original label maps. Nothing here assumes an arbitrary short initial state for that improved operation: the existing initial state is already supplied. No generic recurrence/rank impossibility, numerical sample campaign, shared-file edit or all-input factoring-exponent gain is claimed.
