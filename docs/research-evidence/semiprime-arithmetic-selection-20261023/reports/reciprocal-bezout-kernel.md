# Reciprocal and Bezout kernels on the actual coefficient catalog

23 October 2026. Scratch only. The 256 frozen entries and repository files
are untouched. **No new detector or soft-O(r) full-product evaluation was
obtained.** The useful check below concerns the actual carried source,
rather than a generic matrix counterexample. It excludes a direct
specialization of two specific reciprocal identities. It does not exclude
a different zero-preserving transform or a faster factoring algorithm.

## 1. Exact source and a paid difference screen

Retain the inherited setup N=PQ<=r^6, 16r^2<P<Q and
r<=4N^(1/6). Fix one public window and one leading coefficient a. Its J_a descriptors
have C in a clipped AP of stride r and satisfy

    1<=a<r/16, 0<|C|<=T<=r^2/2, CN=a (mod r),
    M=r^4, |B_C|<=M/2, B_C^2=4aCN (mod M).

Keep the actual canonical B_C, not a cubic approximation without carries.
The legally constructed common root rho_a gives

    beta=rho_a^a,
    W_C=rho_a^(CN), V_C=rho_a^(B_C), Q_a=rho_a^M.

Thus W_C is a GP, whereas V_C retains all the canonical carries. The
leaves, with the original endpoints, are

    L_(C,c,sigma)=1-W_C Q_a^(-sigma) beta^(c^2) V_C^c,
    1<=c<r, -4r<=sigma<=4r.                         (1)

For the full-interval norm identities below use the public N>5r^5
guard, which makes every source exponent nonzero. Its complement has
N<=5120^6 and uses the inherited finite fallback. This avoids silently
including deleted public-zero leaves in a raw product. No ratio below
cancels a source leaf.

Distinct descriptors in this fixed-a block have distinct integer B_C.
Indeed equality of B's and their discriminant congruences gives
4aN(C-C')=0 mod M. Since 4aN is a unit modulo M and
|C-C'|<=2T<M, this forces C=C'.

There is a soft-O(J_a) screen after which all differences V_C-V_C'
are units, or a factor is already acquired. Build the monic polynomial

    F_a(X)=product_C (X-V_C)

and evaluate F_a' at all its supplied nodes by monic product/remainder
trees. If every value is a unit then every pair difference is a unit.
Otherwise choose one node with nonunit derivative value and scan its
J_a-1 pair differences once. A proper gcd factors N. A saturated pair
has

    rho_a^(B_C-B_C')=1 mod N,

with an explicit nonzero O(log N)-bit exponent, so the inherited short
annihilator decoder applies. This never invokes that decoder on the
long discriminant product. Summing the screens across blocks costs
soft-O(sum_a J_a)=soft-O(r); only one failing pair scan is needed.

## 2. Actual-source rank defeats the direct reciprocal substitutions

For fixed sigma write L=E-Z, where E is the all-ones matrix and

    Z_(C,c)=W_C Q_a^(-sigma) beta^(c^2) V_C^c.

On the surviving branch of the difference screen, put
k=min(J_a,r-1). Any k rows and the first k multiplier columns of Z
form a Vandermonde matrix up to unit row and column scalings. Thus over
each hidden prime field

    rank(Z)=k, rank(L)>=k-1.                         (2)

In particular blocks with at least four rows and four multipliers have
ordinary leaf-matrix rank at least three. This is compatible with the
previous low *displacement* rank; those are different statements.

[Singer, Theorems 1.1 and 1.4](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v11i1r48/pdf/)
state Borchardt's reciprocal determinant/permanent identity and its
Carlitz-Levine extension for an ordinary rank-at-most-two denominator
matrix A. Taking A=L fails that hypothesis in (2). Unit row/column
scalings do not repair it. The general Hadamard determinant/permanent
identity in the same paper retains a sum over permutations; the special
rank condition is what removes those terms. No such cancellation is
supplied here.

The apparently more flexible reciprocal double alternant in
[Ishikawa-Okada-Tagawa-Zeng, Theorem 5.1](https://arxiv.org/pdf/math/0411280)
does not evade this test. Its denominator is a determinant with two
variable rows and all other rows fixed. Over a field, quotienting by
the span of the fixed rows leaves dimension two, giving

    f(x,y)=u(x)v(y)-v(x)u(y)

up to a fixed scalar; if the fixed rows have deficient rank the
determinant is zero. Consequently the cross denominator matrix has
ordinary rank at most two, including both generalized-Vandermonde
versions in that theorem. Equation (2) excludes direct equality with
the actual leaf denominators, even allowing unit row/column factors.
The elementary Schur Pfaffian's cross numerator/denominator differences
have the same two-parameter restriction. A new entrywise unit transform
could change ordinary rank while preserving zero support, but none was
constructed or acquired. This argument concerns these exact
specializations, not all Pfaffian or determinant identities.

Reciprocal entries also require a denominator ledger: the factors (1)
are precisely the unknown possible nonunits. They cannot be treated as
the previously certified short-binomial guards and inverted in bulk
without already acquiring a collision. A useful identity must clear
them to a polynomial, or supply a legally evaluated rational output
with the same local zeros. No reciprocal identity tested here does so
on the actual high-rank denominator matrix.

## 3. A restriction-safe Bezout norm, with its missing input explicit

The screen in section 1 permits soft-O(J_a) interpolation of the actual
row amplitudes:

    deg D_a<J_a, D_a(V_C)=W_C.

For this one block define the seed polynomial and the full residue

    P_a(Z)=product_(sigma=-4r)^(4r)(1-Q_a^(-sigma) Z),
    H_a(X)=product_(c=1)^(r-1)
             P_a(beta^(c^2) D_a(X) X^c)  mod F_a(X),
    deg H_a<J_a.                                      (3)

Then, exactly over Z/NZ,

    Res(F_a,H_a)=product_C product_c product_sigma L_(C,c,sigma).
                                                        (4)

This preserves every local zero and every endpoint. The usual Bezout
matrix of F_a,H_a is an alternative determinant for (4), up to a known
sign. More explicitly, if U is the Vandermonde evaluation matrix, its
Bezout matrix B satisfies

    U B U^t=diag(F_a'(V_C) H_a(V_C)),
    det B=(-1)^(J_a(J_a-1)/2) product_C H_a(V_C).

The diagonal identity follows directly by evaluating
[F_a(X)H_a(Y)-F_a(Y)H_a(X)]/(X-Y), so it is also valid over the base
ring after the unit-difference screen. General resultant/Bezout
definitions and their coefficient-input requirements are recalled in
[Andrews-Wigderson, section 2.4](https://www.math.ias.edu/~avi/PUBLICATIONS/AndrewsWi_Constant-Depth%20Arithmetic_2024.pdf).
No bound on the size of their arithmetic circuits is interpreted here
as a soft-linear sequential algorithm.

If the coefficients of H_a were supplied, monic MPE at the V_C followed
by multiplication would acquire (4) in soft-O(J_a). It would also locate
a nonunit row, after which the paid soft-O(r) one-row query recovers a
factor. Replacing F_a and D_a by those of a retained subcatalog gives
the corresponding restricted norm; there is no zero cancellation.

But H_a is the missing input, not a polynomial already acquired by a
Bezout routine. Even in the balanced a=1 subfamily, where F_a,D_a and
the single degree-O(r) P_a are all paid in soft-O(r), (3) remains a
product of r different chirp substitutions in a rank-Theta(r) algebra.
The available direct procedure computes one full row product by monic
MPE in soft-O(r), repeats for the J_a rows, and interpolates H_a. Its
cost is soft-O(J_a r), not soft-O(J_a+r). This is an available upper
bound, not a lower bound. For many a, separately materializing every
P_a additionally costs O(r A) coefficients; that cost is not waived.

The discriminant congruence has not supplied a low-degree algebraic
shortcut for (3). Its exact clock consequence is only

    D_C=(B_C^2-4aCN)/M in Z,
    V_C^(B_C)=W_C^(4a) Q_a^(D_C).                       (5)

Both the exponent B_C and carry D_C vary with the row. Equation (5)
is not a fixed-degree polynomial relation such as V^2=f(W), and dropping
Q_a^(D_C) changes the source. Interpolating W as D_a(V) retains the
relation honestly but does not prove D_a has bounded degree. No
low-rank Bezout input pair with coefficients acquired in soft-O(r)
and determinant having exactly the zero support of (4) was found.

The precise remaining subproblem in this avenue is acquisition of the
full residue (3), or a different restriction-safe scalar polynomial
norm with the same local zero set, from the supplied fixed-a GP W_C
and carried square-root clock V_C in total soft-O(r) bit work. The
short rank-J_a output size is consistent with that target; it is not
an algorithm for acquiring it. No prefixes, extra moments, or compact
operators are counted as resolving this subproblem.

## 4. Bit ledger and inspected primary files

All supplied clock exponents, B differences, and the carries in (5)
have O(log N) bits. Ring elements have O(log N) bits. Monic products,
derivative MPE, interpolation after screening, and row metadata use
soft-O(J_a log N) bit work; ordinary integer powering adds logarithmic
factors. The row-difference screen over all O(log N) windows remains
soft-O(r). No r-by-r table is used in that screen. The uncontracted
available full detector still costs soft-O(r sum_a J_a)=soft-O(r^2)
over the logarithmically many windows. There is no sixth-rate query.

The following primary PDFs were actually downloaded and the stated
identity sections inspected. Fingerprints are SHA-256.

* Dan Singer, *A Bijective Proof of Borchardt's Identity*, EJC 11
  (2004), R48, Theorems 1.1-1.4. Official PDF URL linked above;
  140,879 bytes; `ca93f229e1b43b55623d5b5df5556bb3d57c60bad099e165da33d1d1edaf6bf8`.
* Ishikawa, Okada, Tagawa and Zeng, *Generalizations of Cauchy's
  Determinant and Schur's Pfaffian*, arXiv:math/0411280v2, especially
  Theorem 5.1 and its definition of f. Author preprint URL linked above;
  330,651 bytes; `d7df164c163030a8ac6f3dce3f72c6155bf22411943b46ab4eebe18d34781d50`.
* Andrews-Wigderson, *Constant-Depth Arithmetic Circuits for Linear
  Algebra Problems*, author PDF linked above, section 2.4 definitions
  and resultant/Bezout identities. 1,050,882 bytes;
  `384597193f93b8601fd0d79807cdedd44ca78e3472864b17b702cfe22bfea84a`.

The source-specific rank proof, screen, and coefficient-acquisition
ledger are derived here. They are scope checks on these candidate
identities, not a general no-go theorem. This focused avenue stops
without an acquired full detector.
