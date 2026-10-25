# Direct arithmetic detection for the AP multiplier family

23 October 2026. Scratch research; no repository or frozen-packet changes. The whole-input short-clock family is acquired, but this investigation does **not** acquire its all-input detector in soft O(r). It supplies an exact arithmetic reduction, a cheap genuine restricted decoder, a check of the root's new structured catalog, and quantitative checks of relevant primary reconstruction theorems. It claims no generic lower bound.

## 1. Input and inherited boundary

Use the paid setup N=P Q<=r^6, r=Theta(N^(1/6)), P<Q, P,Q>16r^2, and H=r^2. Public factor windows are P0=16r^2*2^j<=sqrt(N), P in [P0,2P0], with X=2P0/r. There are O(log N) windows. AP residues are s=1+r t, 0<=t<r. At the covered row c=P^(-1) mod r, 1<=c<r, and

    cP=Hh+s, 0<=h<X.

The inherited exact quotient-Gauss construction, with its general nearest-lift bound, gives

    g(h)=a h^2+b h+d,
    d^2+X^2 b^2+X^4 a^2 <=(5/2)H^2 X^2,
    |a|<r/20, |b|<2H, |d|<2HX,
    CN=H^2d-Hbs+a s^2 !=0.

Both quadratic and controlled linear a=0 rows are legal. At the true row g(h)=sigma P, |sigma|<6r. These are established in the preceding unbalanced-geometry report and the archived uniform-trace packet, not new detector theorems.

I read the constructive-frontier index, the sparse-residue Gauss derivation/code contract, and the query-continuation lattice-route and quotient-centering reports before making comparisons. In particular: a supplied direct factor-residue catalog already has the inherited N^(1/5)-optimized consumer; the GFHP second-vector route still pays its quotient search; an extra integer relation is not automatic from a multivariate lattice.

## 2. Exact arithmetic forms

Put Y=Hh+s and L=Hb-2as. The basic identity is

    H^2 g(h)=aY^2+LY+CN.                                  (1)

At the true row Y=cP and c g(h)=sigma Y. Eliminating h gives

    a c^2 P^2+(Lc-H^2 sigma)P+CN=0,                       (2)
    H^2 sigma=a c^2 P+Lc+CQ.                              (3)

Thus the discriminant condition is

    (Lc-H^2 sigma)^2-4a c^2 C N = square.                  (4)

When a!=0, a supplied (c,sigma) yields at most two integer roots P of (2), found and checked in polynomial bit work. When a=0, (2) is linear; its constant CN is nonzero, so there is no identically zero polynomial. This is a recovery rule, not acquisition of (c,sigma).

There is also a useful exact conic form. Set

    Delta=b^2-4ad,
    z=c(2ah+b)-H sigma.

Then

    z^2=H^2 sigma^2-2Lc sigma+Delta c^2.                   (5)

Indeed L^2-4aCN=H^2 Delta, and the square root in (4) is H z. The conic already has the rational points c=0, z=+H sigma and z=-H sigma. Rational-point existence therefore adds no information. Its bounded integral points with c>0, and the integrality/size condition for the recovered h, are the actual search. Parametrizing this known rational conic simply returns the rational function

    sigma/c=g(h)/(Hh+s).

It does not select the small-height rational value at the hidden integer h.

The Euclidean resultant also has an exact interpretation. Equation (1) implies

    gcd(g(h),Hh+s) divides CN,

because H is coprime to Hh+s. At the true witness

    gcd(g(h),Hh+s)=P*gcd(|sigma|,c).

Writing delta=gcd(|sigma|,c), one even has delta|C: delta<r<Q and delta divides CQ. This is useful normalization of a found witness, but it does not find h. For a!=0, Res_x(Hx+s,g)=CN. For a=0, the actual-degree formula gives Res_x(Hx+s,g)=Hd-sb=CN/H. Computing either supplies an already known multiple of N, rather than an unknown factor. More sharply, for every supplied ratio u/v in a quadratic row,

    Res_x(Hx+s, v*g(x)-u*(Hx+s))=v*CN.

It is independent of u. Thus this specific elimination is globally singular modulo N for every ratio and loses the bounded INTEGER-root condition. Linear rows have the analogous v*CN/H formula while the perturbed polynomial remains linear; if its degree drops, use its actual degree. This is an exact limitation of this resultant, not a lower bound for a richer elimination.

Two different quotient-Gauss polynomials for the same s do not automatically provide independent integer equations: both already vanish at -s/H modulo N. Their common modular linear factor is public. A resultant of their modular vanishing relations therefore need not separate P and Q.

## 3. A genuine soft-r arithmetic decoder for a supplied ratio menu

A particularly simple direct acquisition is available for a **supplied** common menu R of reduced rational values u/v, v>0, with polylogarithmic bit length.

For each row and each u/v in R, find all integer roots of

    v g(x)-u(Hx+s)=0.                                    (6)

This polynomial is nonzero: otherwise g would be an exact rational multiple of Hx+s, contradicting C!=0 in (1). Its degree is at most two. At each integer root h in [0,X), compute gcd(N,Hh+s), returning a proper factor if found. In the covered window Hh+s<r*2P0<=2r sqrt(N)<N for the setup's surviving range, so the true root gives a proper factor.

If the true ratio sigma/c belongs to R, this procedure finds the factor. It costs soft O(r*|R|) over all O(log N) windows, including root tests and gcds, since all coefficients have O(log N) bits. In particular R={0} handles every true sigma=0 witness in soft O(r), without enumerating c at all. This is an actual cheap restricted arithmetic consumer; it does not assume a collision query.

The all-input bound |sigma|<6r, 1<=c<r does not supply a small R. The alphabet contains Theta(r^2) different reduced fractions: already numerator and denominator in [1,r-1] give Omega(r^2) coprime pairs. Enumerating that entire menu in (6) would cost soft O(r^3). This is a statement about this explicit enumeration, not a lower bound for another arithmetic algorithm. Finding an acquired small ratio menu covering one row would be a concrete sufficient improvement.

## 4. Check of the root's new explicit (a,C) catalog

The following construction was proposed by the parent during this task; the coverage and size checks below pass. It replaces opaque per-row Gauss output by a structured grid and excludes a=0.

For each factor window let

    A=floor(sqrt(N)/P0),
    T=floor(H/(A+1)), M=H^2=r^4.

Here 1<=A<r/16. Enumerate

    1<=a<=A, 0<|C|<=T, CN=a modulo r.                    (7)

For each pair, CN-a is divisible by r. The unique AP residue s=1+rt satisfying CN=a s^2 modulo H is

    t=((CN-a)/r)*(2a)^(-1) modulo r.                     (8)

This uses an ordinary inverse modulo the public prime r, not division modulo the hidden factors. The congruence CN=a modulo r ensures consistency. Define the canonical centered integer B modulo M by

    B=-a s-CN*s^(-1) modulo M.                          (9)

Then B=-2as modulo H and a s^2+B s+CN=0 modulo M, so both root and derivative congruences hold. All inverses exist because s is 1 modulo r.

For a hidden s, let alpha=s^2*N^(-1) modulo H. Among the A+1 distinct points j alpha modulo H, 0<=j<=A, a shortest circular gap has positive length at most floor(H/(A+1)). The absolute difference of its two labels is a in [1,A]; orienting its sign gives nonzero signed C with |C|<=T and C=a alpha modulo H. Nonzeroness follows also from alpha being a unit modulo H and a<r. Thus (7)-(9) include the hidden s. There are at most

    A*(2T/r+1) <2r+A=O(r)

pairs. They can be enumerated by their C progressions in O(r) arithmetic operations; no scan over a rectangle of area r^2 is needed.

At the true c,h, division of a(cP)^2+B(cP)+CN by P gives the integer seed

    M sigma=a c^2 P+B c+CQ.

The three absolute contributions divided by M are respectively less than

    2sqrt(N)/r^2, sqrt(N)/r^2, r/2.

For the middle bound use T<H P0/sqrt(N) and Q<=N/P0. Hence |sigma|<3.5r for all factor windows. Also |aC|<H. The source is genuinely uniform and acquired in soft O(r) descriptors over logarithmically many windows.

This catalog has structured rather than arbitrary metadata: for each fixed a, C lies in an arithmetic progression of stride r; aC has magnitude <r^2; and a,C determine s. The centered B in (9) carries exact information modulo r^4 and must be retained. Discarding its integer lift, its wrap, or the small multiplier c changes equation (3). I found no argument converting this organization alone into a soft-r arithmetic detector.

The earlier Gauss and the new explicit-grid constructions must not be conflated. The direct relation in Sections 2-3 applies to either after replacing L by B and using the corresponding g=(a(Hx+s)^2+B(Hx+s)+CN)/H^2. The old a=0 analysis below applies only to Gauss rows.

## 5. Linear rows and a precise rational-divisor check

In an exact shortest Gauss row with a=0, u=Hd-sb=+N or -N. Write u=epsilon N. Then C=epsilon H and b is a unit modulo H. Equation (3) simplifies to

    H sigma-bc=epsilon Q.                               (10)

Moreover gcd(c,sigma)=1: any common divisor divides the prime Q and is <r<Q.

Equation (10) fits an actual primary unknown-denominator rational-divisor algorithm: Bernstein, *List decoding for binary Goppa codes*, Section 3, author manuscript dated 2011-03-03. Given n,u,v with gcd(v,n)=1, coefficient box 1<=j<=G, |k|<=K, and fixed integers ell>kappa>0, its lattice finds every coprime pair (j,k) for which j u+k v is a divisor of n and

    j u+k v > ell^(1/(2kappa))
                  *(2GK)^((ell-1)/(2kappa))
                  *n^((kappa+1)/(2ell)).               (11)

Both signs of (10) can be tested by changing u,v; negative v causes no difficulty in the modular-quotient proof. Here G=r-1, K=6r, n=N. For fixed slack and appropriate fixed ell,kappa, the asymptotic divisor threshold is N^(1/sqrt(3)+o(1)), since GK=Theta(r^2)=N^(1/3). Thus a truly sufficiently unbalanced linear-form divisor would be found in polynomial bit work per row, but a balanced Q=Theta(sqrt N) misses the bound.

Crucially, the controlled a=0 rows themselves force a balanced window. Their F=N^2 and the same Hermite inequality imply

    N <=(2/sqrt(3))*X*sqrt(s^2+H^2X^2)
       <=2sqrt(2)*H X^2=(8sqrt(2))*P0^2.

Consequently P0=Omega(sqrt N), P=Theta(sqrt N), and Q=Theta(sqrt N). The apparently promising unbalanced application of (11) therefore does not cover these rows asymptotically. It would be incorrect to advertise it as an all-input shortcut, or even as a newly guaranteed nonempty unbalanced Gauss subfamily.

Source: https://cr.yp.to/codes/goppalist-20110303.pdf . The author PDF was downloaded and Section 3 read directly; the local PDF/text are in this scratch directory. The finite formula (11), not an asymptotic slogan about rational reconstruction, is the relevant condition.

## 6. Small-root theorem checks and their remaining costs

For a **fixed supplied c**, the direct integer polynomial is

    F_c(h,sigma)=c g(h)-sigma(Hh+s).                     (12)

It is irreducible over Q when C!=0: as a primitive linear polynomial in sigma its two coefficient polynomials have gcd 1, since g and Hh+s have nonzero resultant. Constants/content can be removed first. Quadratic rows have total degree two; linear rows are bilinear. Thus bivariate integer small-root theorems are relevant, but neither c nor the row is free input to a whole-family algorithm.

For quadratic (12), the standard scaled coefficient size at |h|<=X, |sigma|<=6r is W=Theta(r^3 X): its h*sigma coefficient alone gives 6r^3 X, and the Gauss bounds upper-bound the other terms by a constant multiple. The total-degree-two sufficient bound is XY<W^(1/2-epsilon), with Y=6r. Its no-slack comparison requires X=O(r); the balanced windows have X=Theta(r^2) and are outside it. The separately bounded-degree-two criterion W^(1/3-epsilon) is weaker here. This is a failed sufficient-condition check, not a theorem excluding all tailored lattices.

Alternatively, using the structured catalog in P coordinates gives

    a c^2 P^2+(Bc-M sigma)P+CN=0.                       (13)

At |P|<=2P0, |sigma|<=4r, W=Theta(r^5 P0) (the P*sigma coefficient supplies the lower bound). A fixed positive power separation P0<=r^(3-delta) can satisfy the total-degree-two bivariate bound for a sufficiently small fixed epsilon. It can therefore make a *supplied row/c* arithmetic root computation cheap. There are still O(r) c for each of O(r) rows: invoking this per pair costs soft O(r^2), even before considering the balanced boundary. The inherited supplied-residue consumer already handles explicit row/c residues; this is not new whole-family acquisition.

Keeping c unknown makes c*g(h)-sigma(Hh+s)=0 a three-variable equation, of total degree three for a!=0. Linear independence of lattice vectors does not ensure the two extra algebraically independent relations required for guaranteed elimination. Coron's primary paper explicitly marks its three-variable extension heuristic for this reason. A resultant of multiples of the one known relation is not a second relation.

Primary references inspected: Coron, *Finding Small Roots of Bivariate Integer Polynomial Equations Revisited* (EUROCRYPT2004), Theorems 4-5 and Section 6, https://www.iacr.org/cryptodb/archive/2004/EUROCRYPT/2177/2177.pdf ; official conference slides https://www.iacr.org/conferences/eurocrypt2004/slides/session14talk2.pdf . The paper's bound/statements were accessible through primary indexed text and its slides, but the direct paper download returned HTTP403 in this pass. I do not claim a fresh local full-PDF pin. Coppersmith's original author-affiliated publication page is https://research.ibm.com/publications/small-solutions-to-polynomial-equations-and-low-exponent-rsa-vulnerabilities .

## 7. Algebraic dependence and weighted Lehman comparison

The supplied-dependency theorem is not an acquisition theorem. Agrawal-Saxena-Srivastava, *Integer Factoring Using Small Algebraic Dependencies*, MFCS2016, Proposition1.1/Theorem1.2, explicitly assumes a dependency is supplied; its proposed fast cyclotomic consumer also carries stated number-theoretic conjectures. For fixed (row,c,sigma), our relation a c^2 P+B c+C Q-M sigma=0 is already linear in P,Q, so exact polynomial recovery suffices without that consumer. The difficulty is finding a correct dependency among the family.

Source read directly: https://www.cse.iitk.ac.in/users/nitin/papers/integerFact.pdf . Its existence-by-pigeonhole proposition does not construct the unknown coefficient choice.

For a,C>0, equation (3) has the weighted Lehman form

    (a c^2)P+C Q=M sigma-Bc,
    ((a c^2)P-CQ)^2=(M sigma-Bc)^2-4aC c^2 N.

The structured catalog gives |aC|<r^2, but the actual integer coefficient product is aC*c^2, potentially order r^4. The square c^2 in the discriminant cannot just be deleted: division by c makes M*sigma/c a rational with unknown denominator. Signed C also cannot be discarded from the covering catalog. A short interval around 2c sqrt(aCN) would need an additional approximation/stationarity proof; the short bound on sigma supplies no such proof by itself.

Harvey's *An exponent one-fifth algorithm for deterministic integer factorisation*, Section3 and Lemma3.1, gives the genuine weighted-Lehman consumer and explicitly charges its shared search. Source: https://arxiv.org/pdf/2010.05450 . The earlier repository explicit Lehman-start family already pays O(r^2) giants; I do not repackage it as O(r) from the label product aC alone.

## 8. Concrete remaining arithmetic target

A sufficient positive next result would be a deterministic algorithm, for these explicitly acquired O(r) structured rows per window, finding any integer solution of

    a c^2 P^2+(Bc-r^4 sigma)P+CN=0,
    P0<=P<=2P0, 1<=c<r, |sigma|<4r,

that produces a proper gcd with N, in total soft O(r) bit work. It may exploit the common congruence CN=a modr, fixed-a C progressions, |aC|<r^2, and the exact centered B. No generic per-row metadata model is needed or assumed.

An alternative sufficient result is an acquired soft-O(1)-size/common-polylog ratio menu covering sigma/c for at least one row, so Section3 applies directly. A third is a proved elimination method producing an independent low-degree integer relation with total descriptor and bit work soft O(r), without assuming multivariate algebraic independence.

At present the genuine cheap arithmetic result obtained here is the supplied-ratio decoder (including all sigma=0 witnesses). Coverage, coefficient organization, conic parametrization and fixed-c root extraction do not yet acquire the full detector. No claimed factorization exponent improvement follows, and no generic impossibility of a structured arithmetic or ring acceleration is asserted.
