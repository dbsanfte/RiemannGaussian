# AP small-multiple catalog: exact carries and scalar-product acquisition

Date: 2026-10-23. Scratch research only; no repository files changed. The constructive-frontier index and the applicable tail of AGENTS.md were read. Original row sharing, the Bostan growing-degree charge, selected q-Newton/jets, the Hensel square-image mask, and the spiroid explicit-input gap are inherited constraints, not new results of this note.

**Status.** I did not construct a restriction-stable soft-O(r) acquisition for the full quadratic AP query. The explicit calculation below exposes two separate carries, gives a finite |sigma|<4r cap, and identifies a paid soft-O(r) resultant for the C-only component. Primary Euclidean staircase recursions do compress the first affine carry as an additive generating function. Their published interface does not contract the correlated native scalar product. This report gives exact identities and costs rather than a general impossibility claim.

## 1. Catalog and quadratic rows

Let r>=3 be prime, H=r^2, r not dividing N. The elementary catalog is

    s_t=1+r t, 0<=t<r.

Every unit P modulo H has exactly one pair (t,c), 1<=c<r, with cP=s_t modulo H: c is the inverse of P modulo r and then t is determined by the next digit. Equivalently,

    (t,c) -> s_t/c modulo H

is a bijection onto all r(r-1) units modulo H. This is a uniform elementary cover, but restoring all labels still creates r(r-1) pairs.

Use centered representatives in [-(H-1)/2,(H-1)/2]. Define

    C_t=center(s_t^2/N modulo H),
    K_t=(s_t^2-N C_t)/H,
    b_t=center(K_t/s_t modulo H),
    B_t=H b_t-2s_t,
    d_t=(N C_t+H b_t s_t-s_t^2)/H^2.

All divisions displayed as integer divisions are exact. The polynomial

    F_t(X)=X^2+B_t X+C_t N

has F_t(s_t)=0 modulo H^2, and

    H^2 g_t(h)=F_t(s_t+Hh),
    g_t(h)=h^2+b_t h+d_t.

Thus, for the true cP=s_t+Hh,

    g_t(h)=sigma P,
    H^2 sigma=c^2 P+B_t c+C_t Q.

For P,Q<=2r^3 and c<r,

    |sigma| <= c^2 P/H^2 + |B_t|c/H^2 + |C_t|Q/H^2
            < 2r + r/2 + 2/r + r <4r.

Here |B_t|<H^2/2+2H and |C_t|<H/2. Therefore the finite common cap |sigma|<=4r is safe for r>=3; no unspecified asymptotic constant is needed.

For a unit beta, put q=beta^(H^2),

    E_(t,c)=c^2+B_t c+C_t N.

Then beta^E_(t,c)=q^sigma modulo P at the true covered leaf, since their exponent difference is

    E_(t,c)-H^2 sigma=(P-1)(C_t Q-c^2).

The acquisition target is the product or a sufficient restriction-safe factor query over

    q^sigma-beta^E_(t,c),
    0<=t<r, 1<=c<r, |sigma|<=4r.

This has Theta(r^3) labeled leaves. That count alone is not a computational lower bound.

## 2. Exact first carry: an affine permutation of an AP

Write the least nonnegative inverse

    U=N^(-1) modulo H=u+r v, 1<=u<r, 0<=v<r,
    w=(N u-1)/r,
    a0=(1-N U)/H.

For h0=(H-1)/2, define

    k_t=floor((U+2r u t+h0)/H).

Then exactly

    C_t=U+2r u t-H k_t.

Indeed s_t^2=1+2rt modulo H, and U(1+2rt)=U+2r u t modulo H. Centering gives the displayed floor, valid also at all endpoints because H is odd.

The coefficient of t modulo r in the second digit is 2u, which is a unit. Hence {C_t} is exactly one AP of r centered integers

    {u+r z : z_min<=z<z_min+r},

where z_min is determined by the centering interval. More explicitly, with h=(r-1)/2, z_min=-h when u<=h and z_min=-h-1 when u>h.

The sequence k_t is a mechanical-word carry with reduced slope (2u modulo r)/r, plus an easily removed integer part. Its adjacent increments have two possible values. This is the piece to which rational-staircase/Euclidean recursions naturally apply.

## 3. The second carry and exact interval transport

The remaining row coefficient is not an independent affine permutation. A direct integer calculation gives

    K_t=t^2-2w t+a0+N k_t.

Set

    W_t=(t^2-2w t+a0+N k_t)(1-r t),
    ell_t=floor((W_t+h0)/H).

Since s_t^(-1)=1-rt modulo H,

    b_t=W_t-H ell_t.

Thus there are two distinct carries: k_t from the affine first coefficient, and ell_t from centering a cubic polynomial plus the t*k_t term. Dropping ell_t does not preserve the query.

There is an exact way to transport it. Define the uncentered phase

    E0_(t,c)=c^2+(H W_t-2s_t)c+C_t N.

Then

    E_(t,c)=E0_(t,c)-H^2 c ell_t,

and

    q^sigma-beta^E_(t,c)
      =q^(-c ell_t) [q^(sigma+c ell_t)-beta^E0_(t,c)].

Consequently ell_t can be removed from the phase only by replacing the common sigma interval I with the moving interval I+c ell_t for that (t,c), together with a unit factor. Its length stays O(r), but its position depends on the row and c. This is a valid carry-aware identity, not a contraction of those moving interval products.

Even before the second centering, E0 contains the term -r^3 c t^3, as well as the mixed t*c*k_t phase. The native exponent is not a linear image of the two-dimensional rational staircase (t,k_t). A linear-floor generating function cannot simply be specialized to represent these nonlinear exponents.

A useful low-digit check is

    E_(t,c)=(c-s_t)^2 modulo H
           =(c-1)^2-2r(c-1)t modulo H.

For c!=1, varying t runs through all r lifts of the residue (c-1)^2 modulo r. For c=1 it is zero modulo H for all t. This is the familiar translated Hensel square-image structure flagged by the inherited frontier; it does not acquire the higher carry-correlated phase.

## 4. A genuinely paid component: the C-only two-progression product

The affine permutation does pay the complete component that depends only on C_t and sigma. For supplied unit gamma and supplied scalar A,

    product_t product_(sigma in I) (q^sigma-A gamma^C_t)

is a product between two geometric progressions, because C_t=u+r(z_min+j), 0<=j<r. Build the degree-r polynomial whose roots are A gamma^(u+r z_min) (gamma^r)^j, then evaluate it at the O(r) points q^sigma using a monic remainder tree. Construction, evaluation and scalar multiplication cost soft-O(r) ring operations and soft-O(r log N) bit operations. Target differences need not be units. This includes ordinary interval restrictions in the reindexed AP variable.

For the native query the factor A is instead

    A_(t,c)=beta^(c^2+B_t c),

which varies with t and c and is correlated with C_t. It cannot be substituted as a single supplied A into that paid resultant. This is an actual boundary between the affine-permutation gain and the remaining product, not a claim that the native correlation is arbitrary.

For one fixed t, the entire (c,sigma) rectangle is also paid soft-O(r): explicitly compute the r-1 values beta^E_(t,c), form their monic root polynomial, and evaluate it at the O(r) q^sigma points. This costs soft-O(r) per row, hence soft-O(r^2) for all r rows. It makes no inversions of target differences. It is not the desired shared bound.

## 5. What primary Euclidean staircase algorithms actually compute

Breuer and von Heymann, *Staircases in Z^2*, Integers 10 (2010), 807-847, Lemma 16 and Theorem 24, give an explicit Euclidean recursion for Dedekind-Carlitz generating polynomials. Their short rational representation has O(log a) terms, and construction is polynomial in log a+log b. The positive set decomposition uses disjoint unions and Minkowski sums of intervals; the paper explicitly warns that expanding the numerator products can destroy shortness. [Primary paper, pp.823-824 and 838-840](https://math.colgate.edu/~integers/k58/k58.pdf).

This applies constructively to the first carry graph (t,k_t), after a known integer shear and translation. It pays its compact description and additive monomial moments. It does not directly compute the product of one-minus-monomial factors attached to all points, especially after inserting the cubic and mixed carry phase from Section 3.

The precise operation mismatch can be seen without an asymptotic argument. If S=A disjoint-Minkowski-sum {0,v,...,(h-1)v}, and

    P_A(Z)=product_(a in A)(1-Z X^a),

then the scalar-root product transforms as

    P_S(Z)=product_(j=0..h-1) P_A(Z (X^v)^j),

rather than as a scalar product of the generating functions. It is a q-factorial with multiplier polynomial degree |A|. Supplying a short additive expression for the point set does not supply P_A. This is where a new carry-aware scalar-product algorithm would have to do work.

Beck, Haase and Matthews, *Dedekind-Carlitz polynomials as lattice-point enumerators in rational polyhedra*, Theorems 4-5, use Barvinok to obtain polynomial-time short rational generating functions in fixed dimension. Beck and Kohl, *Rademacher-Carlitz Polynomials*, Theorem 1, cover affine shifts through reciprocity. Both results are additive integer-point transforms, not factor-product evaluation algorithms. [Primary paper, Section 4](https://page.mi.fu-berlin.de/chaase/papers/carlitz.pdf), [primary affine-shift theorem, pp.3-5](https://arxiv.org/pdf/1310.0380).

No cited theorem gives a multiplicative scalar functional that turns those short rational expressions into the present restricted product for free. Formal logarithm/exponential conversion would require enough power sums to recover the desired long norm and checked inversions modulo N. A fixed number of additive floor moments is insufficient to establish that conversion. This identifies an unproved reduction, not an impossibility theorem.

## 6. q-holonomic, resultant and spiroid accounting

The generic q-holonomic parameter issue is already inherited. Bostan-Yurkevich Theorem 5 charges recurrence order and coefficient degree: scalar length-L factorials with degree-d multipliers cost soft-O(sqrt(L d)), not a bound uniform in d. [Primary degree analysis, Section 3.4](https://arxiv.org/pdf/2012.08656).

The Minkowski-factorial identity above therefore needs both a construction of P_A and its degree charge. More fundamentally, the actual per-step multiplier involving beta^(c^2+B_t c) is not a polynomial of fixed degree in one geometric sequence merely because the exponent is quadratic: a quadratic phase is itself q-hypergeometric, but taking products of one-minus-that-phase does not thereby produce a supplied fixed-order q-recurrence. No low-order recurrence for the full AP query was constructed here.

A bivariate resultant can encode the whole query exactly after its relevant polynomials are supplied. If all r^2 values beta^E_(t,c) are formed, their root polynomial has degree r(r-1); computing it costs soft-O(r^2) bits up to log N factors. The final evaluation at O(r) q points is then cheap relative to that construction. The endpoint resultant does not acquire its root polynomial.

Similarly, monomial/spiroid evaluation algorithms operate on a supplied polynomial with charged representation size. Encoding beta^E by exponents or a formula does not make an implicit product of r^2 factors a supplied soft-r dense polynomial. This is the inherited explicit-input gap and was not reopened as a fresh algorithmic result.

Kronecker packing does not remove this charge: degree-d coefficients modulo N require O(d(log N+log d)) packed bits. A bivariate dense support pays its actual number of slots. No general lower bound on a scalar-only special algorithm follows.

## 7. Inherited global-leaf recovery and restriction scope

Quadratic leaves do not need a new decoder premise. The inherited `docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md`, Section 1, paid prerequisite 3, accepts a nonzero polylog-bit global annihilator of a supplied unit with both local orders odd and >16r^2. Its unconditional unbalanced short-annihilator extractor costs soft-O(N^(31/192)), strictly below soft-O(r) at this scale.

Here any globally colliding leaf supplies exactly

    K=C_t N+c^2+B_t c-H^2 sigma,
    beta^K=1 modulo N,
    bit_length(|K|)=O(log N).

If K is nonzero, the inherited extractor applies directly. An unrelated global leaf is therefore harmless; no true-row or bounded-|K-C phi(N)| premise is required for it. A proper leaf gcd of course already factors N. This is inherited factor recovery, not new acquisition.

A public K=0 leaf is a tautological equality and must be excluded. It never removes the true witness on the surviving setup branch: at that leaf,

    K=(P-1)(C_t Q-c^2) !=0,

because Q>16r^2, 1<=c<r, and the integer C_t is nonzero (indeed C_t is a unit modulo r). If C_t>0 then C_t Q>c^2; if C_t<0 equality is also impossible.

There is an exact all-size O(1) zero screen for this AP catalog (found by the sibling/root proof check). Put y=c-s_t. Since F_t(s_t)=H^2 d_t,

    K=y^2+H b_t y+H^2(d_t-sigma).

If v_r(y)<2, the first term has valuation 2v_r(y), strictly below both other terms: v_r(H b_t y)>=2+v_r(y), and the last has valuation at least 4. Thus K cannot be zero. Hence K=0 implies c=s_t modulo H; as 1<=c<r and 1<=s_t<H, it forces c=s_t as integers. In the AP catalog the only possibility is t=0, s_t=c=1. The sole candidate sigma is d_0, so compare d_0 to the supplied sigma interval and delete that one leaf if present. There is no r^2 label-restoration cost and no large-r dominance premise. A normalized trace representation excludes this zero leaf by subtracting its multiplicity h0 (zero or one) from every power sum.

For a true covered pair, if the local order of q=beta^(H^2) exceeds the searched sigma-interval diameter, local-order uniqueness identifies its true sigma. It then recovers P as a tested root of

    c^2 P^2+(B_t c-H^2 sigma)P+C_t N=0.

In the inherited prepared setting that additional comparison follows from the supplied order and size bounds, rather than from a general rule about powering. Both primes exceed B=16r^2 and N<=r^6, so each is <r^4/16. If d is either local beta order and r^2 divides d, then ord(beta^(r^2))=d/r^2<r^2/16, contradicting the certified value >B. Therefore v_r(d)<=1, and ord(beta^(r^4))=ord(beta^(r^2))>B. This exceeds the diameter 8r of the stated sigma cap. The prime r assumption is used in this valuation argument.

This optional inherited refinement is not needed for arbitrary nonzero global leaves, because the short-annihilator extractor already handles them. Without those prepared size/order bounds, the local-order/diameter condition must be retained explicitly.

Products for arbitrary subsets of t or c retain monic product/remainder validity, but generally lose the AP permutation in Section 4. After transporting ell_t, the sigma interval has row-dependent endpoints. Any proposed shared algorithm must explicitly support whichever restrictions its localization/controller needs.

The concrete missing constructor can be stated with no literature shorthand: from the O(r) explicit triples (s_t,C_t,b_t), acquire a sufficient factor query or restricted product over all beta^(c^2+B_t c+C_tN) against q^sigma, with c<r and |sigma|<=4r, in soft-O(r) bit work, including its needed restrictions. Proper and nonzero global leaves already have paid inherited recovery. Neither the first affine carry nor the cited Euclidean generating-function theorems supply the acquisition.

## 8. Exact finite checks and limits

An independent inline Python check used r=3,5,7,11,13 and semiprimes (P,Q)=(17,19),(101,103),(307,311),(1201,1213),(2011,2017). Each satisfies N<=r^6, P,Q<=2r^3, and r not dividing N. It verified:

* the displayed k_t, K_t, W_t and ell_t formulas against direct modular inversion;
* C_t's complete AP set and the H^2 root congruence;
* the phase transport E0-E=H^2 c ell_t for every native t,c;
* the low-digit square-image formula for every t,c;
* integrality and |sigma|<4r at the uniquely covered true pair.

A separate exact check over r=3,5,7,11,13 and several auxiliary moduli verified that every public K=0 leaf in the cap is the single candidate (t,c,sigma)=(0,1,d_0), including cases where that candidate is present.

These are algebra sanity checks, not a native factorization coverage campaign or runtime evidence. The research used primary staircase/reciprocity papers rather than heuristic number-theory assumptions. It found no actual full-query soft-r acquisition theorem; a carry-aware scalar-product recursion of the stated scope remains a constructive target.
