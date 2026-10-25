# Exact quadratic transport with paid root clocks

23 October 2026. This records a legal coefficient-root construction and an exact transport of the quadratic small-multiple rows to the native residue tags. It does **not** prove a shared query bound. Smooth projection and outside-product roots have antecedents in the existing work; the root construction below is not being counted as a new factoring advance.

## 1. Quadratic row and native row

Let r be the auxiliary odd prime, H=r^2, and N=PQ. Work in the balanced factor regime P,Q=Theta(r^3). Suppose a small-multiple cover supplies s modulo H and an integer 1<=c<r with s=cP modulo H.

Use the explicit coefficient-one quadratic

    G_s(Z)=Z^2+B_s Z+C_s N,
    C_s=centered(s^2*N^(-1) mod H),
    B_s=H*b_s-2s,

where b_s is chosen so that G_s(s)=0 modulo H^2. Equivalently, put K_s=(C_sN-s^2)/H, take b_s=-K_s/s modulo H, and choose d_s=(K_s+s*b_s)/H. Then

    G_s(Z)=(Z-s)^2+H*b_s*(Z-s)+H^2*d_s.

At Z=cP, H divides Z-s, hence H^2 divides G_s(cP). Also P divides G_s(cP), and gcd(P,H)=1. Thus

    r^4*sigma=c^2*P+B_s*c+C_s*Q

for an integer sigma. The balanced coefficient bounds give |sigma|=O(r). The associated exponent is

    E_s,c=c^2+B_s*c+C_s*N,

and beta^(E_s,c)=beta^(r^4*sigma) modulo P.

The native tag associated to **any** public pair (s,c) is

    j=s*c^(-1) mod r,  1<=j<r.

Let a=a_j, ell=ell_j be the original native coefficients, so

    a=N*j^(-2) mod r,
    F_j(Z)=a Z^2+ell Z+N,
    F_j(j)=0 mod r^2,
    ell=-2a*j mod r.

For the own factor P=j+r*u, the native integer seed is

    I=(aP+Q+ell)/r^2.

Balanced native coverage allows I=O(r^2); this index is not automatically O(r).

## 2. Three integral transport carries

For every public pair (s,c), define

    kappa=(c^2-a*C_s)/r,
    lambda=(B_s*c-ell*C_s)/r,
    nu=(kappa*j+lambda)/r.

All three quantities are integers.

For the first, C_s*N=s^2 modulo r and s=cj modulo r imply a*C_s=c^2 modulo r. For the second, B_s=-2s modulo r and ell=-2aj modulo r give B_s*c=ell*C_s modulo r.

For the third, note that cj-s is divisible by r. The displayed expansion of G_s therefore gives G_s(cj)=0 modulo r^2. Also C_s*F_j(j)=0 modulo r^2. Their difference is

    G_s(cj)-C_s*F_j(j)
       =r*j*(kappa*j+lambda).

Since j is a unit modulo r, kappa*j+lambda=0 modulo r, proving nu integral.

These carries retain the full integer representatives, including signs of C_s and all reductions defining B_s.

## 3. Exact short-clock/native-clock relation

At an own factor P=j+r*u,

    r^4*sigma
      =C_s*(aP+Q+ell)+r*(kappa*P+lambda)
      =C_s*r^2*I+r^2*(kappa*u+nu).

Consequently

    r^2*sigma=C_s*I+kappa*u+nu.                 (1)

This is the exact transport of the short sigma clock. In particular, replacing sigma/C_s by a translated native integer seed without the kappa*u term is incorrect. The unknown u=(P-j)/r has O(r^2) possible integer values in a balanced factor window. The terms C_s*I and kappa*u can each be much larger than r^2*sigma and cancel.

The relation does not assert that u is a new independent algebraic unknown: P and I still satisfy the original semiprime equations. It identifies the carry that a shared evaluator must actually contract.

## 4. Legal simultaneous coefficient roots in soft-r work

This section pays root clocks rather than silently interpreting C_s^(-1) modulo N as an inverse group exponent. Assume the inherited prepared beta has odd coprime local orders greater than B=16r^2. There are soft-r coefficients C_s, each nonzero and |C_s|<=H. Put

    E0=r*product_s |C_s|,
    L0=ceil(log_2 N),
    K=E0^L0,
    gamma=beta^K.

The explicit binary length of E0 and K is soft-r. Every prime dividing E0 is removed completely from the local orders of gamma: its valuation in K is at least log_2 N, while every prime-power valuation in a divisor of P-1 or Q-1 is smaller than this. Thus both surviving gamma orders are coprime to E0. Computing gamma costs soft-r modular bit work.

Run the inherited first-nonunit detector through B. A proper factor finishes. Since the local orders remain coprime, an exact common order must be one. If gamma=1 modulo N, K is a known global annihilator of beta, but its binary length is soft-r rather than polylogarithmic; the short-annihilator theorem is **not** invoked on this K.

Instead use the known small-factor product tree for K: its leaves are r and the |C_s|, repeated L0 times, all <=H. Maintain a base a nontrivial in both fields and a tree-node product T with a^T=1 modulo N. Split T=A*D and compute a^A, then gcd(a^A-1,N).

* A proper gcd is a factor.
* If the gcd is N, retain (a,A).
* If it is one, retain (a^A,D).

The invariant holds at every step. At one leaf t<=H, the retained base has two nontrivial coprime local orders, both dividing t. The inherited detector through H therefore returns a proper factor. The path has logarithmic depth; the total exponent bit length processed along it is soft-r, and the final detector costs soft-sqrt(H)=soft-r. No factorization of E0 is needed.

On the NoHit branch, gamma retains large odd coprime local orders and all are coprime to E0. Set

    beta0=gamma^E0,
    beta_r=gamma^(E0/r),
    rho_s=gamma^(E0/C_s).

Signed exponents handle negative C_s. Then

    beta_r^r=beta0,      rho_s^C_s=beta0,

and all these bases have the same local orders as gamma. In particular, their orders are coprime to r and every C_s. The whole outside-power family rho_s is acquired softly linearly by a product tree: at a node with product A*D and incoming outside power x, pass x^D left and x^A right. At each tree level the total exponent bit length is O(log E0), and there are logarithmically many levels. The common native q=beta0^(r^2) retains the same large local orders because r was included in E0.

This is a legal useful primitive. It does not make the later two-index phase acquisition free.

## 5. Exact common-target/root-clock representation

Define

    delta_j=a_j+ell_j,
    Y_j=beta0^(N+delta_j),
    eta_j=beta_r^(N+delta_j),
    D_s,c=kappa+lambda.

There are only r native targets eta_j and soft-r root clocks rho_s. Coefficient roots turn the original same-leaf local equality into

    Y_j=rho_s^(r*(r^3*sigma-D_s,c)),

and the common r-root then gives the exact equivalent equality

    eta_j=rho_s^(r^3*sigma-D_s,c).              (2)

These steps preserve vanishing separately modulo P and Q. All values lie in the cyclic subgroup generated by gamma, on which raising to C_s or r is injective because the local orders are coprime to those integers. Equality of products as ring values is not asserted; equality of the local zero supports is sufficient for a properly implemented nonunit/localization interface.

To verify the exponent arithmetic directly,

    E_s,c=C_s*(N+delta_j)+r*D_s,c.

Thus after taking a C_s-root, dividing by the known phase, and then taking the legal r-root, the r^4 sigma clock becomes the r^3 sigma clock in (2).

For a fixed s and j, c is the unique representative of s/j modulo r in [1,r). Therefore D_s,c can be regarded as a public two-index phase D_s,j. Explicitly,

    D_s,j=(c^2+B_s*c-C_s*delta_j)/r,
    c=[s/j]_r.

A full transformed query has soft-r clocks, r targets, and a family of Theta(r^2) indexed phases. One may center D_s,j modulo r^3 and reorigin sigma by the known quotient; the centered phase is still indexed by (s,j). No proof here acquires all needed contracted phases in soft-r work. Merely counting r targets after discarding the phase matrix would omit part of the query.

## 6. Why modular Teichmuller factorization does not yet factor the clocks

For a Teichmuller-layer catalog, C_s satisfies q_r(C_s)=2q_r(s)-q_r(N). Modulo H its dependence can be expressed through multiplicative Teichmuller representatives. However outside powers rho_s depend on the **integer** C_s, not merely its residue after an arbitrary factorized lift.

Suppose C_s is replaced by C'_s=C_s+H*k. To preserve the quadratic lattice condition, write B'_s=B_s+H*Delta b with

    Delta b=-k*N/s mod H.

At the covered factor, the new clock must satisfy

    H*(sigma'-sigma)=Delta b*c+k*Q.             (3)

The kQ/H contribution is private. An unreduced factorized Teichmuller lift can make k large, increasing the guaranteed seed interval. Dropping this contribution, or reducing exponent coefficients modulo H because their integer residues agree there, does not preserve (2).

Similarly, c^2/C_s=a_j modulo r is a congruence in a small residue ring, not equality of rational numbers or permission to replace a group exponent by its residue modulo r. The kappa and nu terms in (1) are the exact correction.

## Frontier

The construction legally shares the r native curvature targets and pays the C_s-root clocks. The remaining operation is a restriction-stable acquisition for the two-index phase/clock family (2), or another contraction retaining equation (1). No soft-r bound for that operation follows from the paid single-shift/single-weight dyadic norm constructor. No operation lower bound is claimed, and no new sixth-rate factoring theorem is obtained.
