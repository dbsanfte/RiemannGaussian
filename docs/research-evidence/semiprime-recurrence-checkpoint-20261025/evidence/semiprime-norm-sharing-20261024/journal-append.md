
## Shared norm homotopy, native index palettes and local uniqueness, 2026-10-24

The previous pass supplied individual terminal norms and a complete cubic
alternative, but no nearlinear batch. This pass executes determinant
regularization, follows its rank-one perturbation into an exact joint
product, and acquires a short expansion of that product in soft k. It also
acquires the native index-residue map and proves a local uniqueness theorem.
These are initialized ingredients for a faster query, not a completed one:
the original full query remains soft k^(3/2), and the separate N^(1/5)
benchmark and the open one-sixth/full executable-Lean bit goal are unchanged.

Exact sources, independent reviews and the append validator are in
`/tmp/semiprime-norm-sharing-20261024`. Prior shared prefixes, all 270 frozen
evidence entries and concurrent RH work are preserved. No finite numerical
campaign is counted as uniform coverage or acquisition.

### Exact joint homotopy and short global coefficients

Use the canonical native F, with degree J after any reciprocal augmentation,
and the acquired Gamma_G(Z)=prod_(g<G)(Z-Q^g), Q=q^m, m=k, G=2k (3k for
the repaired main). All last-two tails remain separate. Write

    F_e(X)=X^J+e(F(X)-X^J),
    C_e=C_0+e u e_(J-1)^t, u=-(f_0,...,f_(J-1))^t,
    Delta(e,t)=det H_t(C_e), H_t(X)=X^G Gamma_G(t/X).

At e=0 the actual multiplication matrix H_t(C_0) is triangular Toeplitz
with unit diagonal d=t^G. Its r-th leading principal minor has constant
d^r. Thus every principal Schur pivot is a formal unit with constant d;
Bareiss minor pivots have the corresponding unit powers d^r. This is a
proved initialization, not a generic rank-profile assumption. The first
mixed Schur numerator retains the actual cross term
-h_1 h_(J-1) u_0; no q-binomial cancellation is assumed to erase it.

The finite Toeplitz inverse of tI-Q^g C_0 and the rank-one determinant lemma
give, exactly,

    det(tI-Q^g C_e)=t^J[1+e P(Q^g/t)],
    P(Z)=sum_(d=1)^J f_(J-d)Z^d, 1+P(Z)=Z^J F(1/Z).

Consequently Delta has e-degree at most G. Acquiring all F(t_i Q^-g) by
one MPE, then multiplying each node's G linear factors, gives all m
Delta(e,t_i) polynomials in soft(J+mG)=soft k². Evaluating those actual
polynomials at one is lawful; specializing truncated formal inverses is
not used.

More significantly, the entire matched batch fuses as

    Xi(e)=prod_(n=0)^(L0-1)[1+e P(q^n)], L0=mG,
    prod_(i<m)Delta(e,q^-i)
          =q^(-JG*m(m-1)/2) Xi(e).

All index pairs n=mg+i are retained. For the unaugmented original family,
U_V=prod_j V_j^L0 and E_main=U_V Xi(1). For reciprocal augmentation with
centre a0=q^(1-L0) and c0=(-1)^L0 q^(L0(L0-1)/2),

    E_main²=c0^J0 U_V Xi_aug(1).

Only the separately acquired ORIGINAL tail (or its square) restores the
full-query value. A reciprocal main leaf maps n to L0-1-n.

There is an actual short-output shared calculation. For requested s with
Js<=16H and s<P,Q, acquire P^r for r<=s and the weights

    Lambda_0=L0,
    Lambda_d=(1-q^(L0*d))/(1-q^d), 1<=d<=Js,
    S_r=sum_d [Z^d]P(Z)^r Lambda_d.

All denominator guards, polynomial coefficients and powers are paid. Then

    log Xi(e)=sum_(r>=1)(-1)^(r-1)S_r e^r/r

acquires the first s coefficients in soft(J s²+s²). Thus polylogarithmically
many GLOBAL coefficients cost soft k. In particular Xi_1=S_1 and
Xi_2=(S_1²-S_2)/2. This is a shared contraction, rather than m independent
Taylor evaluations.

A standard power-projection invocation uses B[Z]/Z^(Js+1) and the actual
functional vector Lambda_0,...,Lambda_(Js); that input alone has Js+1
entries. It does not supply an implicit-weight soft(J+s) algorithm. The
identity L(f(Z)-f(qZ))=f(1)-f(q^L0) is exact, but coefficientwise
q-antidifferentiation of P^r still processes Jr coefficients in the tested
execution. This leaves a specific short-output projection to investigate.

The endpoint cannot be inferred from a few expansion coefficients. Over
every local field component, the q seeds are distinct. Since P has degree
J and unit leading coefficient, Xi has degree at least L0-J. In contrast,
the multiplicity of its root e=1 is at most J. A small root multiplicity
therefore does not make Xi a low-degree polynomial. Substitution e=1 is
not a homomorphism from the truncated ring B[e]/e^s. The desired value at
one remains unacquired at soft k; no lower bound for other algorithms is
inferred from this degree calculation.

### Exact native index map and a supplied-palette factor algorithm

For P=j+kx, the original primitive identity is

    (j+kx)I=a x²+b x+c_j.

Under parity repair a'=a+epsilon*k, b'=b+epsilon*j-k*zeta and
c'_j=c_j-j*zeta, the true index is I'=I+epsilon*x-zeta. With the actually
acquired Hensel t satisfying 2a't+b'=0 modk, set X=x-t. Then

    I'=lambda_j X²+gamma_j modk,
    lambda_j=a'j^-1=Nj^-3 modk,
    gamma_j=j^-1(a't²+b't+c'_j) modk.

All coefficients and vertices are acquired in soft k. The unknown X is
precisely one next prime digit with a known shift; the equation does not
acquire it. For unit X, the fundamental character gives
chi(I'-gamma_j)=-chi(j); nonunit X must retain its actual character value.

For the controlled modulus k every square equation has at most 16 roots,
including nonunit residues. Enumerate one inverse-square lookup with k
entries in soft k. For an explicitly supplied palette A of s index
residues, invert the displayed quadratic for each j and r in A, then form

    S_A={j+k[(X+t) modk]} subset[1,H).

The catalog has at most16ks entries and is actually acquired in soft(k+ks).
It contains P modH whenever the actual own I' modk is in A. Its complete
factor consumer is especially simple: form prod_(v in S_A)(T-v), evaluate
at -Hn for0<=n<=k by monic MPE, and descend any saturated row. Every leaf
v+Hn is positive and smaller than N, so any nonunit leaf gives a proper
factor. All starts, outputs, labels and localization fit soft(k+ks).
Thus a supplied constant or polylogarithmic covering palette would suffice
for soft k, without the torus query. No such uniform palette is acquired.

The quadratic image has at least k/16 possible residues (phi(k)/16 on
units), but this is a statement about the public map, not a factoring
lower bound or a claim that actual primes fill its domain. Legal positive
lifts I_s=I+s*x-z_s retain a unit quadratic coefficient and cannot make
that polynomial universally constant. This does not rule out exploiting
the actual divisors. Likewise the rough cyclic groups have order coprime
to k, so unrestricted exponent modulo k is not a well-defined quotient
character. An interval-promised exponent algorithm remains possible;
it is not supplied by that group quotient.

### Guarded trace evaluation and a precise uniqueness branch

At an acquired unit t, guarded extended Euclid on F,H_t either finds a
factor/nonunit to localize, or supplies the actual inverse of H_t modF.
On the unit-resultant branch, with E=B[X]/F,

    R'(t)/R(t)=Trace_E((H_t^-1 partial_t H_t) modF)

is acquired in soft(J+G), using the first J supplied-root power sums.
Repeated roots in the augmentation do not invalidate this determinant
identity. No inverse is assigned at a collision. Across m nodes this
particular completed method still costs soft k².

For A(t)=F(Q^(-(G-1))t), B(t)=A(Q^G t) and theta=t*d/dt, differentiating
A(t)R(Qt)=B(t)R(t) BEFORE division gives the zero-safe system

    A² [R(Qt);theta R(Qt)]
       =[[AB,0],[A theta B-B theta A,AB]] [R(t);theta R(t)].

The known state at zero is fixed by dilation and does not initialize a
unit-node chain. Primary Chen--Singer Theorem4.13, Section4.1.3, is a
characteristic-zero/non-root-of-unity rational-certificate criterion;
the natural formal poles t/y_j move with t. It does not supply the desired
differential telescoper, nor a finite-ring nonexistence theorem. Mezzarobba's
complex D-finite approximation and Johansson's rectangular splitting
likewise retain their ODE, initial-value, scalar-work and coefficient-rank
costs. The literal integer-lift numerical reconstruction charges its full
O(D logN) upper height; that is not a lower bound for every other method.

There IS a stronger native arithmetic theorem when the SMALLER prime P
is the nonsplit side. Its odd beta/W orders divide P-1 and P+1, hence are
coprime; their product exceeds256H². For a repaired MINUS-row collision,
X=delta-Hi satisfies

    X=-N mod r_beta, X=N+2a mod r_W.

Their product therefore divides X+Q+(P-1)a. With P<=k³, a<2k,
Q<H²/16 and the actual horizon, that integer has magnitude<8H², so

    Hi=aP+Q+ell

holds exactly. The native expansion

    aP²+ell P+N=a(P-j)²+k b(P-j)+k²c_j

then forces k|(P-j): at every prime dividing k, a smaller valuation of
P-j would give a uniquely lowest-valuation first term. Thus EXACTLY ONE
canonical minus row hits this smaller nonsplit prime, at one index. This
uses the actual native coefficients and does not hold for arbitrary rows.

For plus rows, two hits force delta_j-delta_h=H(i_j-i_h) as integers,
using the same large product order. The strict delta span<5H and exact
fibers<=16 leave at most80 plus hit rows. The complete canonical product
therefore has at most81 colliding factors in this precise branch. This
is not asserted for the split side or the larger nonsplit prime. It can
bound the Hasse depth of a future valid solver, but it supplies neither
locations nor nonzero amplitudes nor a short remainder. In particular it
does not justify evaluating the preceding homotopy at one from its short
expansion at zero.
