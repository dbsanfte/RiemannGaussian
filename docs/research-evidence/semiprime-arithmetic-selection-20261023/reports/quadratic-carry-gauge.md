# An integral carry gauge and its finite quadratic-norm test

23 October 2026. Scratch only; all 256 frozen entries and repository
files are unchanged. **No new full collision evaluator was obtained.**
The construction below exactly absorbs each discriminant carry into
public integer interval translations. It does not acquire the resulting
translated-window product. The focused finite quadratic-norm candidate
still requires a different clock specialization.

## Prior-work check

I first checked the October 16 constructive-frontier index, the October
22 query-continuation reports direct-product.md and
squaring-query-prefix.md, the lifted-norm report
finite-character-products.md, and the October 23 detector reports
count-acquisition.md and discriminant-relations.md. Their already paid
facts include completed squares, odd-order companion squaring, sparse
cyclic norms on supplied carriers, and the failure to replace actual GP
seeds by roots of unity. None is counted below as a fresh evaluator.
In particular no cyclic dilogarithm or short operator descriptor is
reintroduced as acquisition.

## 1. The exact integral gauge

Keep the actual source, with M=r^4, a>0, gcd(a,r)=1,

    D_C=(B_C^2-4aCN)/M in Z,
    K_(C,c,sigma)=a c^2+B_C c+CN-M sigma,
    1<=c<r, -4r<=sigma<=4r.

Every B_C is the canonical centered lift; no carry is dropped. For
each nonempty branch indexed by a and

    b=B_C mod 2a, 0<=b<2a,

compute the following ordinary integers:

    t_C=(B_C-b)/(2a),
    d_b=(M^(-1)b^2 mod 4a), 0<=d_b<4a,
    e_b=(b^2-M d_b)/(4a),
    k_C=(D_C-d_b)/(4a).                              (1)

The inverse is modulo the public integer 4a, not a hidden group order.
It exists since r is odd and a<r. Also B_C^2=b^2 mod 4a, so
MD_C=b^2 mod 4a and k_C is integral. Expanding gives the exact identity

    CN=a t_C^2+b t_C+e_b-M k_C,
    K=a(c+t_C)^2+b(c+t_C)+e_b-M(sigma+k_C).           (2)

Thus, for the legally acquired rho_a and Q_a=rho_a^M, define the ONE
quadratic clock on each observed branch

    F_(a,b)(j)=rho_a^(a j^2+bj+e_b).

The entire source product is exactly the product, over its descriptors,
of

    product_(j=t_C+1)^(t_C+r-1)
      product_(tau=k_C-4r)^(k_C+4r)
          (1-F_(a,b)(j) Q_a^(-tau)).                 (3)

This is an equality of leaves, not merely a formal equality of moments.
It preserves every local zero, individual leaf label, and seed endpoint.
It involves no group roots, unknown inverse exponents, or division by
a source factor. Retaining any subset of descriptors restricts (3)
literally. Use the already stated N>5r^5 guard and finite fallback if
raw full intervals without public K=0 deletion are wanted.

For the balanced a=1 case there are at most TWO clocks:

    b=0: d_b=e_b=0,
    b=1: d_b=1, e_b=(1-M)/4.

This removes varying row constants from the clock formula by keeping
their information in the actual two interval translations. It does
not remove that information from the query.

All metadata in (1) is acquired in soft O(r) total bit work. Indeed
|aC|<r^2, |B_C|<=M/2 and N<=r^6 imply

    |D_C|<M/4+4r^4,
    |t_C|=O(M/a+1), |k_C|=O(M/a+1), |e_b|=O(M+a).

These integers and all clock exponents have O(log N) bits. Only
observed (a,b) branches need be stored; their count is at most the
O(r) descriptors, not the sum of all possible 2a branches.

## 2. Why this is not already an overlapping-window acquisition

For fixed (a,b), the actual B_C=-2a mod r gives

    t_C=-1-b(2a)^(-1) mod r.                         (4)

Distinct fixed-a descriptors have distinct integer B_C: equality of
B's and B^2=4aCN mod M forces C=C', since 4aN is a unit modulo M and
|C-C'|<M. Consequently distinct t_C in one (a,b) branch differ by a
nonzero multiple of r. Their j-intervals in (3), of length r-1, are
disjoint. Their common-clock form therefore supplies no interval
overlap by itself. The relation between starts is exactly

    N(C'-C)=(t_C'-t_C)[a(t_C'+t_C)+b]
                  -M(k_C'-k_C).                    (5)

Equation (5), including its last term, is the information a more
effective translated-window algorithm would have to use. I do not
replace these separated starts by adjacent ones or cancel prefix
products containing possible collisions.

## 3. Focused candidate: a complete finite quadratic-clock norm

The candidate's first step was to use a complete public r-cycle of the
common clock F_(a,b), so that each r-1 window is a full quadratic norm
with one endpoint removed. Such a finite
quadratic norm really has a degree-r polynomial description when its
phase is an r-th root of unity: for a primitive root lambda, one can
enumerate lambda^(a j^2+bj+e), j=0,...,r-1, and build their monic root
polynomial in soft O(r). Completing the square permutes the indices
and doubles the nonzero quadratic-residue multiplicities. That finite
identity follows directly from the two-to-one square map; it is not an
infinite theta evaluation. Once that polynomial is supplied, its values
at O(r) points cost soft O(r). This is not a claim that the actual query
has only O(r) such points: the translated seed intervals in (3) can
supply O(r^2) arguments, and omitted-endpoint corrections need their
own acquisition. A cycle identity would only be a first contraction,
not a completed whole-family evaluator.

The actual clock after the integral gauge does NOT have that cycle.
For any positive candidate cycle R its exact boundary is

    F_(a,b)(j+R)/F_(a,b)(j)
       =rho_a^(2aRj+aR^2+bR).                       (6)

In either hidden prime field let d be the prepared odd local order
of rho_a, with d>16r^2 and gcd(a,d)=1. For (6) even to be a
j-independent scalar monodromy, comparison at j and j+1 requires
d|2aR, hence d|R. Thus the hoped-for public R=r cycle is absent; a
genuine local cycle has rank at least d>16r^2 and is not acquired.
Moreover replacing rho_a by an r-th root would make Q_a=lambda^M=1,
which destroys the actual seed clock rather than representing it.

The discriminant carry has already been fully and exactly accounted
for by k_C in (1)-(3). It does not modify the boundary (6). A further
unit gauge on F(j) inside 1-ZF(j) is not harmless: multiplying F by a
unit changes that difference's zero set unless an additional identity
is proved and evaluated. No such correction with acquired aggregate
cost was found. The finite cycle test stops here; it is not a theorem
excluding other noncyclic or support-preserving norm algorithms.

This is consistent with, rather than an improvement on, the inherited
root-of-unity specialization audit. The additional exact fact here is
that even after eliminating all row-dependent discriminant constants
by the integral gauge, their replacement is the translated two-clock
query (3), not a finite quadratic norm at the prepared scalar.

## 4. Honest acquisition ledger

For one descriptor, the r-1 target values F_(a,b)(t_C+c) can be
generated in soft O(r), and the actual O(r) seed points are a GP.
Monic product/remainder trees therefore evaluate that complete row
in soft O(r), including localization and inherited nonzero-leaf
recovery. Repeating for O(r) descriptors gives soft O(r^2), as before.
Common branch clocks and formula (5) have not reduced this charge.

The newly constructed object is the exact gauge metadata and identity
(3), not its value. A genuinely useful continuation would evaluate
the product over these separated translated rectangles using (5),
with all endpoints and possible zeros retained, in total soft O(r).
No such evaluator, integer factor witness, or improved factoring
exponent is proved in this report. No code experiment or examples
campaign was used.
