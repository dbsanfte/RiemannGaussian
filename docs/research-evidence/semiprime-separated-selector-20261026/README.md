# Short higher responses and a compact norm for the long collision query

26 October 2026. Reviewed paper derivations and small exact diagnostics.
The complete uniform query bound remains soft O(K^(5/4)); the guaranteed
sixth-rate acquisition and full bit/Lean proof remain OPEN.

This pass supplies an explicit soft-J algorithm for ALL higher Macdonald
relative responses and their fixed-rank marked variations. It also expresses
the original packed residue using an acquired pair of short row polynomials
and two geometric polynomials. The desired residue is retained by the latter
representation, but its fast contraction remains unconstructed. A separate
implemented cyclotomic certificate supplies a conditional soft-K factoring
branch through the existing restricted-residue consumer.

## The exact long query and its compact decomposition

For the [original packed target](../semiprime-six-domain-acquisition-20261026/README.md),
write

    C=[delta^-1] sum_(j,i) w_j/(delta+1-T_j*q^-i),
    D(Y)=prod_j(Y-T_j),
    A_w(Y)=sum_j w_j*prod_(k!=j)(Y-T_k).

Both D and A_w are acquired in soft J by a weighted product tree, even with
repeated roots. Define the compact first-order polynomial

    E_delta,epsilon(X)=D((1+delta)X)
                       +epsilon*X*A_w((1+delta)X), epsilon²=0.

The clock product Q=prod_(i<h) E_delta,epsilon(q^i) satisfies exactly

    C=[delta^-1] (partial_epsilon Q(delta,0))/Q(delta,0).

Split i=bv+u, with c=floor(h/b), and acquire

    B_b(Z)=prod_(u<b)(Z-q^u),
    G_c(S)=prod_(v<c)(S-q^(bv)).

Then

    Q=Res_S(G_c, Res_Z(B_b,E_delta,epsilon(SZ)))
        *prod_(bc<=i<h) E_delta,epsilon(q^i).

The two resultants are split and monic in their first arguments: no field
division, missing sign or leading factor is concealed. At b near sqrt(h),
the compact inputs have size soft(J+sqrt(h)). This is a compact formal input
bound, not an acquired dense delta expansion or Laurent coefficient. See
[the exact mapping](packed-to-norm.md) and its [review](review-packed-to-norm.md).

## The simpler unique-family output

The [previous retuned cover](../semiprime-residue-shortcuts-20261026/content-cover.md)
has J=O(K^(2/3)), h=O(K²), and exactly one good hit (j*,I), while retaining
ORIGINAL-K preparation. Give row j the integer mark j and form

    F_epsilon(X)=prod_j(X-T_j+epsilon_0+epsilon_1*j),
    prod_(i<h) F_epsilon(q^i)=P_0+epsilon_0*V+epsilon_1*U.

Here all products of two epsilon variables vanish. At the good hit,
U/V=j*, with V nonzero. The inherited guarded consumer can select that row
and run the one-row clock query in soft K. This is a different sufficient
output on a new covered family, not numerical equality to the original C.

The same two-geometric norm expresses this three-coefficient product with
all inputs acquired in soft(J+sqrt(h)). Its literal tail is also evaluated
in that budget. A rectangle-only weak pair requires first checking the tail
for a hit; otherwise request the full constant-plus-two-derivative jet.
The [construction](separated-recurrence.md) and [review](review-separated-recurrence.md)
include this distinction and all component/unit gates.

The target is now explicit: evaluate the marked norm without emitting the
degree-Jb intermediate polynomial, in soft(J^(3/2)+b+c). That would meet
the acquisition/recovery budget after retuning. The standard safe evaluator
costs soft(J+sqrt(Jh)), at most soft K^(4/3) here, so the existing original
family remains the better completed algorithm.

## An actual cancellation algorithm for all higher responses

Let D(X)=sum d_s X^s, b=q^(h-1), and (a;q)_r=prod_(k<r)(1-a*q^k).
After the actual row-separation and endpoint gates, the acquired generating
polynomial is

    chi(u)=1/D(b) * sum_(s=0)^J d_s*b^s
                     *(u;q)_s*(u*q^(h+s);q)_(J-s).

An explicit balanced two-basis recursion computes ALL J+1 coefficients in
soft J. It also computes every fixed-rank marked variation in soft J.
No J-by-J matrix is constructed. The [derivation](higher-macdonald.md),
[review](review-higher-macdonald.md), [marked extension](higher-marked-jets.md)
and its [review](review-higher-marked-jets.md) give the algorithm and gates.

This is a genuine cheap all-output calculation. Its response is regular at
an interior collision, and its matrix and I-minus-matrix are units after
the gates. The simplest logarithmic marker pairing receives nonzero
contributions from nonhitting rows. A selected singular pairing is still
needed to recover the collision; no general impossibility is inferred.

## A conditional arithmetic shortcut

[cubic_gate.py](cubic_gate.py) evaluates an explicit cubic Gauss congruence
in a rank-12 quotient algebra. It returns a verified factor, a certified
two-residue palette, or decline. On a global primitive pass, Schoof's
Proposition 3.3(i) implies every prime divisor p obeys

    p=+1 or -1 mod n, n=3^min(v3(N²-1),e).

If n>=ceil(cuberoot(K)), the existing restricted Harvey–Hittmeir consumer
fits soft K with these two residues and the original preparation. The
[report](cyclotomic-selector.md) and [independent audit](review-cyclotomic-selector.md)
check the actual constants and exact recovery. The implementation supplies
the palette; it does not implement HH or verify native preparation. Neither
the passing congruence nor the modulus threshold is guaranteed for every N.

## Validation and remaining work

The exact higher-response diagnostic compares the balanced formula against
independent dense determinant, principal-minor and subset calculations.
The cubic controls check the integer Gauss identity, prime Frobenius
identities, and factor/decline branches. These validate algebra and code,
not all-semiprime coverage or an asymptotic runtime implementation. Counts
and archive replays are recorded in [review.json](review.json).

The strongest general next target is the selected tangent norm with both
geometric factors retained throughout evaluation. The all-orders response
algorithm supplies a second possible ingredient if a residue-preserving
selection identity can be proved. The cyclotomic gate is a usable conditional
branch, with a universal supplier or affordable failure branch still missing.
No further backend theorem or numerical success is counted as closing these
acquisition gaps.
