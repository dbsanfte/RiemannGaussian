# Exact varying-weight diagonal: reciprocity and carry-aware reductions

22 October2026. No examples, backend, frozen edits or numerical coverage claims. This examines the actual power piece

    H_a=CT[rho_(a/b)(B) R^a], R=W/X,
    W=t(1+gamma X)/(X+gamma), B=W^N, b=N modm,

in the full cyclic algebra, at native unit a=a_j=Nj^−2. CT is AFTER reduction modulo X^m−1. The fixed-weight trace theorem is paid in the adjacent weighted-rational-trace.md; the issue here is the varying automorphism weight. No all-a near-linear constructor was found. The exact constructions below narrow the remaining transform rather than assuming the m-by-m table.

## 1. Exact specialization when B=W^N

Constant-term invariance under rho_b gives

    H_a=F(a,N),
    F(a,c):=CT[X^(−ac) W(X^c)^a W(X^a)^c].         (1)

The exponent maps X^c are reduced modulo m, but the INTEGER powers a,c are not. Equation(1) is symmetric in a,c. This is an exact extra structure for B=W^N, absent for arbitrary acquired B.

There is also exact cofactor reciprocity without an unknown tag in the final scalar. At a hidden P, write N=P Q. Frobenius over the WHOLE local algebra gives W(X^a)^N=W(X^(aP))^Q. Apply rho_(P^-1) to the full constant-term expression; since P is a unit modm,

    F(a,N)=F(a,Q) modP,
    F(a,N)=F(a,P) modQ.                            (2)

This is not a hidden-cofactor input algorithm: it derives a local interpretation of the public expression. It does not compute the right-hand sides or reveal their hidden integer parameter. Symmetry and Frobenius supply exact identities, not a factor guarantee or an unknown-index locator.

## 2. Diagnostic W=1+X exposes the mixed transform exactly

For this diagnostic ONLY, take an arbitrary acquired B=sum B_r X^r and 1<=a<m. Since (1+X)^a has degree a<m,

    H_a=sum_(k=0)^a binom(a,k) B_(b*k/a modm),
    H_a/a! =sum_(k=0)^a B_(b*k/a modm)/(k!(a−k)!). (3)

All factorials are units under P,Q>m. Formula(3) is a Pascal/binomial convolution multiplied ENTRYWISE by a multiplicative-ratio kernel. An ordinary additive FFT computes a fixed Pascal transform; a multiplicative FFT computes a ratio-circulant transform. The desired output is the common diagonal coupling both, not either transform separately. No near-linear algorithm for this combined transform follows merely from the fact that both constituent matrix-vector actions are fast.

For the specialization B=(1+X)^N, applying rho_b to the unreduced polynomial expression gives coefficient classes of

    X^(−aN)(1+X^N)^a(1+X^a)^N.

If gcd(a,N)=1, its UNREDUCED exponent-zero term is2: Nr+as=aN in 0<=r<=a,0<=s<=N has only the endpoint solutions. But the CYCLIC constant term also includes EVERY exponent equal to a multiple of m after the shift. Explicitly the exact value is

    sum_(0<=r<=a,0<=s<=N, Nr+as−aN=0 modm)
             binom(a,r)binom(N,s).                (4)

Discarding the nonzero multiples of m would erase the actual query. The weights in(4) are high-order binomial weights, not unit weights or a fixed-degree polynomial weight on a two-dimensional lattice. This diagnostic is not substituted for the prepared W or its recovery contract.

## 3. Carry-aware Euclidean transport, with its actual boundary weight

For the ACTUAL W define weighted F_C(a,c) by inserting ONE acquired weight C(X) inside CT in(1). Write c=q a+r, 0<=r<a. Then exactly

    F_C(a,c)=F_(C E)(a,r),
    E=[X^(−a²)W(X^a)^a]^q * [W(X^c)/W(X^r)]^a.   (5)

All substitutions are cyclic; all integer powers/carries are retained. The identity follows by multiplying the integrands, not by a limit or dropping a boundary. Each W(X^r) is a unit, including r=0 where W(1)=t. A single E is actually acquired in soft m by binary powering and automorphism permutations. Thus a Euclidean reduction is valid and has a paid correction for ONE parameter pair.

Crucially E is a packed NONCONSTANT weight, not a scalar boundary term that can be pulled outside CT. Repeated reductions transport the weight rather than close on the original two-parameter scalar family. The fixed-weight resolvent can consume a supplied final weight, but generating a separate chain for every a still uses separate rank-m data. No theorem sharing all these transported weights in soft m was found. Equation(5) is the precise candidate one would have to sharpen into an actual reciprocity algorithm: either a bounded-dimensional closed family of weights or a shared near-linear total weighted contraction.

### Primary Dedekind/Carlitz check

Beck–Haase–Matthews, *Dedekind–Carlitz Polynomials as Lattice-Point Enumerators in Rational Polyhedra*, author PDF dated3Sep2007, Theorem1 and introductory computational discussion inspected: https://page.mi.fu-berlin.de/chaase/papers/carlitz.pdf . Its exact reciprocity is (v−1)c(u,v;a,b)+(u−1)c(v,u;b,a)=u^(a−1)v^(b−1)−1 for coprime positive a,b, with c recording floor/carry monomials. This really handles the carries of geometric lattice-point weights. It does not assert the same law after replacing the lattice weights by the binomial weights(4) or the rational W powers(1). Such a replacement is a coefficientwise/Hadamard operation with its own cost; evaluating u,v at scalars is not that operation. No scalar-boundary Euclidean law for(1) was found in the inspected primary theorem.

Cached sources/carlitz.pdf SHA2564392e867fe5327c284163565d605726d878fe942c2928001eea165e2c1d21448. Hall–Wilson–Zagier, *Reciprocity formulae for general Dedekind–Rademacher sums* (Acta Arith.73(1995)), author PDF introductory generalized Bernoulli-weight setup also inspected: https://people.mpim-bonn.mpg.de/zagier/files/acta/73-4/fulltext.pdf . Its weight parameters are Bernoulli orders and shifts; no bound treating growing orders as free is imported.

## 4. One precise shared-eigenweight consumer

There is an actual near-linear extension of the fixed-weight theorem under a representation characteristic worth targeting. Suppose a decomposition

    B=sum_(nu=1)^s B_nu,
    rho_r(B_nu)=lambda_nu(r) B_nu for every r in U_m

has been ACQUIRED, with s=polylogm, each lambda_nu publicly computable in the scalar ring, and total vector/extension rank soft m. Then

    H_a=sum_nu lambda_nu(a/b) CT[B_nu R^a].         (6)

Each fixed-weight sequence on the right is paid by the verified rational resolvent theorem, so all native H_a are acquired in soft O(sm)=soft m. This is an actual algorithm once the short eigenweight decomposition is supplied, not m separate degree-m vector operations.

There is NO claim that B=W^N has such a decomposition. A full character expansion has up to m−1 components, and roots/eigenvalues in a growing extension cannot be treated as scalar constants. Constructing m eigenvectors or paying extension rank m for every component restores the large work. A useful positive arithmetic target is a short scalar/small-total-rank eigenweight representation forced by the particular W^N, or a direct analogue of(6) that avoids expanding that representation. Neither is proved here. This is a representation interface, not a claimed selected-input coverage family.

## 5. Rational-diagonal and near-linear composition literature: exact model

Kinoshita–Li, *Power Series Composition in Near-Linear Time*, arXiv:2404.05177v2,22Sep2024, full primary12-page PDF opened, Theorem1 and Graeffe/power-projection model inspected: https://arxiv.org/pdf/2404.05177 . It works over arbitrary commutative rings, computing f(g(x)) modulo x^n in O(M(n)log d+M(d)) arithmetic operations. Its near-linear bivariate balance halves the TRUNCATION-variable degree while doubling the other. This is a genuine useful algorithm, not barred merely because the coefficient ring is composite. But replacing our CYCLIC modulus X^m−1 by X^m is invalid; choosing the cyclic algebra as its coefficient ring instead retains rank-m work per coefficient operation. No reduction of(1) or(3) to its small input interface was established. Cached sources/kinoshita-li.pdf SHA2566ae924a2766d31e1a5f47d966e9e8225591c84c37b811b17e3f61ef871b508ef.

Bostan–Dumont–Salvy, *Algebraic Diagonals and Walks: Algorithms, Bounds, Complexity*, arXiv:1510.04526v1, primary27-page paper opened, introduction and stated diagonal/recurrence preprocessing model inspected: https://arxiv.org/pdf/1510.04526 . It gives algorithms for supplied bivariate rational functions; constructing a minimal polynomial can have exponential degree-dependent size, while specific walk-series prefixes can be expanded quasi-linearly after the relevant algebraic/recurrence data. This is not a theorem that any expression labelled a constant-term diagonal has O(m) input or preprocessing. Our varying B(X^(a/b)) has an index PRODUCT a*k in its exponent; no bounded-bidegree rational presentation with paid O(m) size and the needed diagonal was constructed.

## 6. Exact residual and full-source limitation

For general B the exact generating function is

    sum_(a>=0) H_a z^a
      =(1/m)sum_(x^m=1,k) B_k/(1−z R(x)x^(k/b)).

The unweighted denominator has compressed z^m structure, but the weighted numerator is not supplied by its norm. With B=W^N, identities(1)–(2) provide genuine symmetric/Frobenius structure; (5) retains Euclidean carries with an acquired one-pair correction; (6) specifies one actually sufficient short representation. None currently computes all H_a or a restriction-stable support aggregate in soft m for the actual B.

Even a solved H_a power piece would not by itself acquire the full native target: the original Z_j contains the remaining W_j^ell_j factor and the same unknown seed index. Those factors and original scalar/nonzero-annihilator recovery have not been discarded. No new all-input collision algorithm or factoring-rate gain is claimed.
