# Finite quiver / Bailey contraction audit — 2026-10-25

Target: C_M(Z)=prod_{r=1}^M(Z-q^r-q^-r) modulo monic G of degree J, or D_m= sum_{j=0}^{M-1}q^(mj)C_j for m=-1,0,1. Desired cost soft(J+sqrt(M)); available baseline soft(J+sqrt(JM)). No improvement of that cost is established here. The most concrete successful rewrite below is an exact finite Pfaff–Saalschütz specialization, valid with paid scalar inverses, which turns a factorial-weighted descendant into C_M. It does not match the requested three unweighted descendants.

## Sources and the finite identities actually used

* Kato–Mizuno–Terashima, https://arxiv.org/html/1611.05969, Theorems 4.1–4.2, Proposition 4.3, Remark 5.3, equation (5.9): shifted quantum-dilogarithm ratios yield finite Gaussian-binomial mutation sums. The A2 five-term example is a one-index sum whose length is min(a,b)+1. Fixed quiver width does not bound that length.
* Aritram Dhar, *Pfaff's Method Revisited*, https://arxiv.org/html/2405.08705 and https://arxiv.org/pdf/2405.08705, Theorem 1.3, equation (1.6), Section 2.3: finite q-Pfaff–Saalschütz evaluation. The PDF retains formulas absent in the browser's HTML rendering. Formula used: sum_{j=0}^n (a,b,q^-n;q)_j q^j/(q,c,abq^(1-n)/c;q)_j = (c/a,c/b;q)_n/(c,c/(ab);q)_n.
* *Bailey pairs and quantum q-series identities. I. The classical identities*, primary publisher text https://link.springer.com/article/10.1007/s40065-025-00594-0, Section 2, equations (2.4)–(2.6), Lemmas 2.2–2.4: finite Bailey transforms mix indices 0 through n; the simple chain maps multiply alpha_n by q^(n²+n), and convolve beta_k with q-factorials. These explicit formulas are sufficient to audit the coefficient weights, without invoking infinite identities.

## Native two-Pochhammer representation (own algebra)

For any unit u with Z=u+u^-1,

    C_M(u+u^-1)=(-1)^M q^(-M(M+1)/2) (uq;q)_M(u^-1q;q)_M.       (A)

This follows factor by factor: (1-uq^r)(1-u^-1q^r)=-q^r(Z-q^r-q^-r). No denominator or choice of square root occurs. It holds over R and modulo any polynomial after reciprocal lifting. In particular H(U)=U^J G(U+U^-1) is monic reciprocal of degree 2J. Working modulo H requires only a constant factor increase in quotient dimension and recovers the original symmetric remainder. Thus (A) is a legitimate algorithmic reduction to a product of two long q-Pochhammers, not a speedup.

For native roots, take u=beta^E directly: no discrete logarithm or extension is needed. Each evaluation becomes (beta^(E+k²);beta^(k²))_M times its inverse-E counterpart, with the scalar in (A). The native description saves extracting roots of G but does not pay for these long products at all J points.

## Explicit finite Pfaff specialization (constructive, validated)

Set n=M, a=u, b=u^-1, c=q in q-Pfaff–Saalschütz. Its second lower parameter equals q^-M. For 0<=j<=M its Pochhammer has no zero factors, so the equal upper/lower factors may be canceled before specialization. The exact result is

    (uq,u^-1q;q)_M/(q;q)_M²
       = sum_{j=0}^M q^j (u,u^-1;q)_j/(q;q)_j².               (B)

Equivalently, entirely in Z,

    (-1)^M q^(M(M+1)/2) C_M(Z)/(q;q)_M²
       =1+q(2-Z) sum_{i=0}^{M-1}
             (-1)^i q^(i(i+3)/2) C_i(Z)/(q;q)_(i+1)².        (C)

This identity is also proved without hypergeometric specialization: if A_j=(uq,u^-1q;q)_j/(q;q)_j², then A_j-A_(j-1)=q^j(u,u^-1;q)_j/(q;q)_j². Summing gives (B). This proves every boundary including M=0. It avoids any questionable cancellation at j=M+1, which is outside the finite sum.

All scalar inverses in (B),(C) are legitimate under the promise M<16k²: 1-q^r is a unit in R for 1<=r<=M. A failure of a scalar gcd gives a factor. The coefficients can be generated in O(M) scalar work and O(M) storage, or streamed. C is a clean finite identity, but explicitly generating its weights already exceeds soft(J+sqrt(M)) when M>>J. Faster factorial evaluation only addresses endpoint scalar factorials, not the weighted whole-family contraction.

Crucially, the weights are w_i=(-1)^i q^(i(i+3)/2)/(q;q)_(i+1)², not q^(mi). Their ratio is -q^(i+2)/(1-q^(i+2))². No choice m=-1,0,1 equates them throughout a long interval under generic q. Thus (C) must not be reported as summing D_m.

## Why the unweighted descendants do not have this simple telescope

Here is a specific failed algorithm, with an exact limited obstruction (own proof). Try q-Gosper telescoping q^(mj) C_j by an endpoint rational certificate R(q^j):

    q^m (Z-qt-q^-1 t^-1) R(qt)-R(t)=1.                      (D)

Over the rational function field Q(q,Z)(t), with q indeterminate, (D) has no rational solution. A nonzero finite pole t0 of R(t) forces another pole at qt0 to cancel the pole from -R(t); iterating gives infinitely many poles. The Laurent coefficient multiplying R(qt) can remove poles, but cannot create the required pole, so does not invalidate this implication. Hence R is Laurent polynomial. If its greatest and least exponents are d and e, the left side has noncancelable extreme exponents d+1 and e-1. A constant RHS requires d<=-1 and e>=1, impossible for nonzero R. This rules out only a first-order rational endpoint certificate, not higher-order recurrences or accelerated matrix products.

The known three-descendant relation does not evade this: q^(m+1)D_(m+1)+(1-Zq^m)D_m+q^(m-1)D_(m-1)=1-q^(mM)C_M. At m=0 it reconstructs C_M from three D values, but leaves all three whole-family contractions to be computed. The validation script checks this exact finite boundary.

## KMT and Bailey attempt, with supports charged

KMT (5.9) rewrites a product of Gaussian coefficients as a sum indexed by t=0..min(a,b). Applying the finite q-binomial expansion to either factor in (A) yields M+1 coefficients; the product has Laurent support -M..M. KMT rearranges that convolution and can remove a sum when both coefficient weights match its balanced pattern. An arbitrary remainder modulo G contracts against the vectors rem_G(Z^j), or equivalently against G-dependent recurrence weights. These are not the fixed Gaussian factors in (5.9). Matching them requires computing their transformed vector; no short formula is supplied by KMT. This is the exact unpaid interface, rather than a claim that quiver identities never help.

A Bailey transform is lower triangular with nonzero diagonal when the scalar q-factorials are units. It does not reduce the dimension of an arbitrary input vector. The simple Bailey chain's quadratic q twist partially resembles the numerator in (C), but its q-factorial convolution changes the C_j coefficient vector and reintroduces a length-M sum. Keeping it as a formal transform is a short description, not an evaluation modulo G. A usable adaptation would need a fast action of this triangular transform on the particular G-dependent recurrence vector, costing soft(J+sqrt(M)); neither the cited formulas nor the native exponents supply that action.

## Can the native exponent congruence force a short Pfaff boundary?

The native congruence alone gives the following necessary condition for E=a+bN+lambda to vanish modulo k²:

    E=0 mod k² implies (a+bN)²=lambda²=4abN mod k²,
    hence (a-bN)²=0 mod k².

The input description does not supply this extra vanishing condition for every root. Accordingly no short q-power relation for u=beta^E is used in this audit. Multiplicative coincidences can occur modulo an unknown factor; those are the collisions being sought and cannot be assumed beforehand. The earlier illustrative k=5 example has been removed because it was outside the native k=2*3^e parameter family and used a centered lambda.

One may test an explicitly guessed boundary beta^(E±rk²)=1 by gcd; checking all r<=M and all native roots explicitly costs JM exponent comparisons. A Pfaff/Chu specialization that presumes u=q^-s for known small s would therefore assume the unpaid collision location. The quadratic congruence creates no terminating parameter in (B) at a generic root: the only supplied termination is M itself.

## Decision and precise remaining constructive lemma

No claimed soft(J+sqrt(M)) contraction. The finite normalized identity (C) is an actual useful rewrite and a checkable starting point: it exposes exactly which factorial/quadratic weights have a product endpoint. To obtain a new algorithm, one must efficiently convert the three q^(mi)-weighted descendants or the G-dependent remainder functional to these summable weights, with all transformed coordinates compressed to O(J+sqrt(M)). The current Bailey/KMT transformations preserve the missing long contraction instead. The accompanying script verifies (A)–(C) and the three-descendant boundary in exact rational arithmetic, including sample reduction modulo monic G.

## Follow-up appendix: weights are freely choosable for a weak locator

Correction of emphasis: matching the original D_m weights is unnecessary. Write S_M for the sum on the right of (C), and U_M=(-1)^M q^(M(M+1)/2)/(q;q)_M², a scalar unit. Computing S_M gives C_M=U_M^-1[1+q(2-Z)S_M]. Equivalently, the left side of (C) is already H_M=U_M C_M. Therefore the weighted family deserves independent evaluation analysis. No conversion to D_m is required. The remaining issue is evaluating the weighted contraction itself.

Set H_j=(-1)^j q^(j(j+1)/2)C_j/(q;q)_j² and Psi(z)=sum_{j>=0}H_j z^j. Infinite series notation in this appendix is first interpreted over Q(q,Z), with q indeterminate. Over the actual finite coefficient ring R or its polynomial quotient, every series and transformation is used only to precision z^(L+1) with L below both local q orders, so every scalar denominator (q;q)_j for j<=L is a unit. No all-orders series over R is asserted. With Z=u+u^-1,

    Psi(z) = 2phi1(uq,u^-1q; q; q,z).                       (E)

This is a reciprocal-parameter basic hypergeometric function; retaining both upper parameters is essential. It does not generically degenerate to a one-parameter q-Bessel or one-Pochhammer q-binomial function: uq and u^-1q are both present and neither cancels the lower parameter q unless u is special.

Heine's third (q-Euler) transformation has an unusually favorable exact specialization here:

    Psi(z) = (1-z)^-1 Phi(z),
    Phi(z)=2phi1(u,u^-1; q; q,qz).                          (F)

The infinite prefactor (qz;q)_infty/(z;q)_infty cancels *exactly* to 1/(1-z). Thus (F) is a genuine rational gauge transformation, not an unpaid infinite product. Source: NIST DLMF https://dlmf.nist.gov/17.6.E8 (Heine's third transformation); its formulas and constraints are also visible at https://dlmf.nist.gov/draft1/17.6. For this specialization, the identity can be checked coefficientwise from (B), so it is valid formally to finite precision over R with the already justified scalar inverses. This is the generating-function version of the successful Pfaff identity.

### Cheap initialization and exact finite operator

Let T f(z)=f(qz). Direct coefficient comparison gives

    [(1-T)^2-z(1-uqT)(1-u^-1qT)]Psi=0,

or, without adjoining u,

    (1-z)Psi(z)+(Zqz-2)Psi(qz)+(1-q²z)Psi(q²z)=0.           (G)

Initialization is cheap: Psi(0)=1, and H_1=(1-Zq+q²)/(1-q)². All coefficients of G are degree at most one in Z and z. This is an actual order-two q-difference transfer with constant-size initialization over S=R[Z]/G. Equation F preserves order two; it removes a cumulative-sum factor but does not turn the target into a rational function with known constant-size coefficients.

The coefficient recurrence extracted from G is

    H_j = (1-Zq^j+q^(2j))/(1-q^j)² H_(j-1).                (H)

This is already first order and has the same degree-one Z numerator as the original product. Hence the weighted formulation improves the description/initialization of the family, but not yet its evaluation. Using ordinary geometric baby-step/giant-step on H modulo G costs soft(J+sqrt(JM)), including scalar denominator products. Doing it separately at each native root costs about soft(J sqrt(M)); the desired additive bound does not follow from the low operator order.

### Finite boundary audit

For Psi_<M=sum_{j=0}^{M-1}H_j z^j and the operator L in (G),

    L Psi_<M = -(1-q^M)² H_M z^M.                          (I)

Every lower coefficient vanishes; the displayed coefficient is the sole upper boundary. Thus a proposal to solve the truncated operator with short rational starts but omit its source term loses precisely H_M, the locator. Likewise,

    (1-z)Psi_<M = sum_{j=0}^{M-1}(H_j-H_(j-1))z^j
                      -H_(M-1)z^M,    H_-1=0.

The rational gauge in F does not delete the endpoint when truncating. At z=1 it simply returns the boundary term. There is no valid substitution z=1 into an infinite formal series over a discrete finite ring, unless a separate termination proof is supplied.

Heine's first and second transformations introduce uncanceled infinite factors (u^-1q,uqz;q)_infty/(q,z;q)_infty or their reciprocals and an infinite transformed sum. They are less suitable over R. The q-Gauss special value would require z=q^-1; its denominator contains (q^-1;q)_infty and the series is not a paid finite identity. No such special value was used.

### Native root specialization

Putting u=beta^E in E–I makes all constants explicitly computable by powering. It gives neither uq=q^-s nor u^-1q=q^-s with a known short s. Such a relation would itself locate a desired collision. Thus the native exponents do provide the correct branch and cheap initialization, but do not establish terminating/summable transformed series. A useful new lemma would need fast extraction of [z^M]Psi for the entire native family, or a finite boundary-preserving q-Euler contraction, in soft(J+sqrt(M)). Equations F–I isolate that missing operation precisely.

## Last parity probe: quadratic transformations and exact parameter growth

The condition ab=c² for E is not the standard well-poised condition qa=bc. For a=uq, b=u^-1q, c=q, well-poisedness requires u²=1. Likewise the Heine-gauged series Phi has a=u,b=u^-1,c=q and requires u²=1. Thus the classical well-poised 2phi1 quadratic transformations cannot be applied just because the upper parameters are reciprocal up to q². The relevant primary transformation literature is Gasper–Rahman, *A Nonterminating q-Clausen Formula and Some Related Product Formulas*, https://doi.org/10.1137/0520084, and Rahman–Verma, *Quadratic transformation formulas for basic hypergeometric series*, https://doi.org/10.1090/S0002-9947-1993-1074149-8. Their stated starting classes are well-poised 2phi1 / very-well-poised 8phi7. I did not find a generic ab=c² transformation closing our coefficient decimation to two parameters.

An actual q-ultraspherical quadratic formula is (Koekoek–Swarttouw, author-hosted https://tudelft.roelofkoekoek.nl/documents/as98.pdf, Section 3.10.1, remarks, printed p.88):

    RogersC_(2n)(x;q^lambda|q)
       =(q^lambda,-q;q)_n q^(-n/2)
          / (q^(1/2),-q^(1/2);q)_n
           * P_n^(lambda-1/2,-1/2)(2x²-1;q).               (J)

Here RogersC denotes the Rogers polynomial, not our cyclotomic C. The former has parity RogersC_(2n)(-x)=RogersC_(2n)(x). Our C_(2n)(Z) lacks this parity: already C_2(Z) has Z coefficient -(q+q^-1+q²+q^-2). Consequently J does not identify H_(2n)(Z) with a scalar-normalized Rogers polynomial at x=Z/2. It also changes from ultraspherical to Jacobi parameters; it is not an automatic indefinitely repeated closure in the original family. Half-q parameter notation in J would require a justified extension if actually used over R. No such extension is needed for the exact decimation below.

### Exact decimation, including all scalar denominators

For any d>=1,

    H_(dn)= prod_{s=1}^d
          (u q^s,u^-1 q^s;q^d)_n / (q^s;q^d)_n².          (K)

The generating function sum_{n>=0}H_(dn)w^n is a 2d-phi-(2d-1) at base q^d: upper list {uq^s,u^-1q^s:1<=s<=d}; lower list has two copies of each q^s with one copy of q^d removed, since it is the built-in factorial. At d=1,2,4,8 the upper/lower list lengths are (2,1),(4,3),(8,7),(16,15). Explicitly after one split,

    H_(2n)= (uq,uq²,u^-1q,u^-1q²;q²)_n
                        / (q,q,q²,q²;q²)_n.               (L)

The decimated successive ratio, with t=(q^d)^n, is

    H_(d(n+1))/H_(dn)
      =prod_{s=1}^d(1-Zq^s t+q^(2s)t²)
                         /prod_{s=1}^d(1-q^s t)².         (M)

Over Q(q,u) all these numerator/denominator factors are generically uncanceled. The numerator has degree 2d in t and degree d in Z. The relation ab=c² has not removed any factors; it only makes the reciprocal pairs combine into the displayed quadratic trace factors. Describing the d offsets as an interval compresses storage, but evaluating the interval product is precisely the long-product operation that remains to be paid.

All denominator exponents that arise for dn<=M are positive and <=M, hence units under the supplied local-order bound. No dividing by u±q^s is authorized. If a numerator becomes zero modulo one unknown prime, that is a useful collision, not a permitted cancellation with an unavailable inverse.

### Why squaring the trace almost helps, and the extra branch it needs

There is the exact finite identity

    C_M(Z;q) C_M(-Z;q)=(-1)^M C_M(Z²-2;q²).               (N)

It follows from (q^r+q^-r)²=q^(2r)+q^(-2r)+2. Thus adjoining the negative-trace branch does yield compact trace squaring. But N does not halve M: it combines two length-M targets into one length-M target at base q². It is the already-known norm/parity mechanism, not a new coefficient-decimation algorithm. Repeatedly taking these norms would require paying for the additional branches or proving that a whole-family norm can be acquired cheaply and remains a useful factor locator. The native exponent list supplies u=beta^E, not -u; representing the latter as another beta power would require extra group information unless -1 is explicitly supplied as a scalar branch. Adding that branch doubles inputs and is not free.

Outcome of this probe: no quadratic identity closing H_(2n) to the same two-parameter family with a paid bounded-size prefactor was found. The exact directly obtained sequence is K–M, whose parameter lists and rational ratio degrees double at each parity step. This is an audit of this route, not a general impossibility theorem for a more sophisticated quadratic transform.
