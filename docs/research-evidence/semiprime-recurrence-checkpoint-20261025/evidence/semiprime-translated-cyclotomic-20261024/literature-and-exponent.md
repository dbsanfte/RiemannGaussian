# Translated cyclic powers: structured discrete logs and the exact wrap datum

2026-10-24. Scratch only; repository read only. Read the preserved cyclotomic-row-cancellation README under `docs/research-evidence/semiprime-cyclotomic-row-cancellation-20261016/`. Its global anti-invariant vanishing concerns u=1+zeta and the self-reciprocity law; u=beta+zeta escapes that particular theorem. No new all-input exponent extractor is supplied here. The useful positive result is an initialized soft-m extractor from an ACTUAL first-order quotient lift, with an explicit proof that the supplied reduced element does not itself initialize that lift.

## Model and paid inputs

Write R=Z/N, g=X^m-1, A=R[X]/g, u=beta+X, d=m², q=u^d, and 0<=I<=L=2m² (a harmless constant enlargement handles the original strict endpoint convention). The exponent is n=dI=O(m^4). A multiplication in A costs soft m residue operations. Computing u^N, q, and any one supplied power by binary powering costs soft(m log N), hence soft m when logarithms are suppressed. Acquiring m different full row elements separately is not soft m.

When the original beta local-order screen exceeds 16m², u is a unit in the FULL cyclic algebra: the identity
  (beta+X) sum_(k=0)^(m-1)(-1)^k beta^(m-1-k) X^k = beta^m+X^m
reduces to beta^m+1, whose vanishing at a prime would force beta^(2m)=1. Thus the required scalar inverse is certified (or its gcd returns a proper factor). Without this screen, u-unit status is an additional guarded condition. The cyclotomic quotient is a separate algebra; the full cyclic norm below should not be silently assigned to it.

A promised equality T=q^I in A over all of R differs from native coverage: the native own-tag equality is only in one unknown residue field. A global discrete-log routine alone does not detect all such local hits. Also, uniqueness of I requires a suitable order bound on q, which is not automatically a consequence of high order of beta.

## Primary structured-log literature and precise applicability

1. Qi Cheng, *On the Bounded Sum-of-Digits Discrete Logarithm Problem in Finite Fields*, SIAM J. Comput. 34 (2005), [primary publisher](https://doi.org/10.1137/S0097539704446037), [author paper](https://cr.yp.to/bib/2004/cheng-digits.pdf), [preprint](https://arxiv.org/abs/math/0311120). The main theorem uses a KNOWN field F_(q^r), r|q-1, an irreducible Kummer generator alpha with alpha^r in F_q, prescribed base alpha+b, and a bounded q-ary sum of digits of the exponent (at most r in the displayed preprint theorem). Its polynomial-time algorithm is randomized. It reconstructs a low-degree product of conjugate linear factors. Here X^m-1 is reducible and étale, not an irreducible degree-m Kummer binomial. In the cyclotomic field components the extension degree is ord_m(p), and the required Kummer/Frobenius scaling hypotheses are not provided. An integer bound n=O(m^4) also does not imply p-digit sum <=m for hidden p>16m². This theorem is therefore not the desired deterministic composite-ring extractor.

2. Xiao–Zhuang–Cheng, *Factor base discrete logarithms in Kummer extensions*, FFA 53 (2018), [primary publisher](https://doi.org/10.1016/j.ffa.2018.06.008), [author preprint](https://eprint.iacr.org/2015/859.pdf). Its setting is a known Kummer finite field and linear-factor logarithm relations. The improved algorithm is explicitly heuristic, with correctness reduced to a lattice-determinant conjecture; the paper disproves a proposed sufficiency of a smaller degenerate relation system. Neither its field input nor correctness/complexity mode is available here. No heuristic rank or smoothness claim is counted.

3. Menezes–Wu, *The Discrete Logarithm Problem in GL(n,q)*, Ars Combinatoria 47 (1997), [primary author PDF](https://www.math.uwaterloo.ca/~ajmeneze/publications/glnq.pdf). Matrix/circulant representation reduces to logarithms in finite-field eigenvalue components, rather than making those logs trivial. Applying such decomposition here would require the unknown local field and appropriate irreducible factors/orders. A circulant multiplication operator is a valid representation, but its dimension-m operations and eigenvalue DLPs remain charged.

4. Agrawal–Kayal–Saxena, *PRIMES is in P*, Annals 160 (2004), [primary article](https://annals.math.princeton.edu/2004/160-2/p12). The polynomial congruences modulo X^r-1 and group-size argument yield deterministic primality testing. A failing congruence is a compositeness witness, not a guaranteed coefficient with proper gcd. Their proof may reason in an unknown prime-field factor without supplying it as an algorithmic input. No bounded exponent recovery or general factor extraction follows directly from that proof.

5. Rubin–Silverberg, *Compression in Finite Fields and Torus-Based Cryptography*, SIAM J. Comput., [primary publisher](https://doi.org/10.1137/060676155). Compression is of finite-field multiplicative subgroup representations; it does not recover exponents. Granger–Vercauteren's [primary CRYPTO 2005 record](https://doi.org/10.1007/11535218_5) studies index calculus on tori. These do not give deterministic all-input soft-m logs over an unknown composite base ring. No expected subexponential attack is counted.

These are focused source applicability findings, not an exhaustive absence theorem.

## Exact failed logarithmic-derivative shortcut

There is no nonzero R-derivation of A: from X^m=1 one obtains m X^(m-1) delta(X)=0, and both m and X are units. Thus delta(X)=0. In particular D=X partial_X does not descend, since D(g)=m X^m=m in A, a unit.

For the ACTUAL unreduced polynomial P=(beta+X)^n, write the exact Euclidean division
  P=f+g Q, deg f<m.
Differentiating before reducing and using uP'=nP gives in A
  u f' - n f + m X^(m-1) u Q = 0.
The quotient remainder Q mod g is an unknown wrap datum. It cannot be discarded or read from f'. If f and u are units, the displayed equation expresses Q mod g as an affine function of the unknown n; it does not solve for n. Coefficients of f are wrapped binomial sums over all exponents congruent mod m, not a short consecutive binomial prefix.

A finite jet around X=0 of the unreduced power would reveal n from its first derivative, but reduction modulo g does not supply that jet: g has unit constant coefficient, so its multiples affect every low coefficient. Treating the first m reduced coefficients as the first m unreduced coefficients is invalid.

## An initialized positive extractor from the actual first-order lift

Suppose, as a STRICTLY STRONGER INPUT, that H is supplied modulo g² and equals the raw power (beta+X)^n modulo g². Let f=H mod g. Ordinary differentiation of a representative of H is well defined modulo g, because the derivative of a multiple of g² is divisible by g. Then
  w=u*(H' mod g)*f^(-1) mod g = n*1.
Acquire f inverse by guarded fast polynomial Euclidean arithmetic: a nonunit pivot with proper gcd factors N; unit pivots are legal. Under the promised raw-power input, f is a unit, so otherwise its inverse is obtained. All explicit polynomials have degree <=2m, and the operation costs soft m residue work. Multiply the scalar n by d^(-1) modulo N to obtain I; 0<=I<=2m²<N makes that bounded representative unique. Check the result by binary powering in A, costing soft m. No unknown prime or group order is required in this stronger-input algorithm.

This is an actual initialized extraction theorem, but acquiring H from only f is missing. The canonical degree-<m representative lift sets Q=0 and generally is not H. The cost of computing a raw lift when the exponent is already known is soft m, but knowing the exponent is precisely the problem.

There is a particularly instructive canonical étale lift. In R[X]/g² put
  y=X*(1-g/m).
Then y^m=1 modulo g², and y'=0 modulo g. Consequently lifting f to f(y) is cheap and gives H'=0 modulo g, so the extractor returns zero. This section preserves the quotient relation by erasing the desired normal derivative. It is not the raw lift (beta+X)^n.

Native Frobenius equalities transport naturally through this étale section. They do not promise equality of arbitrary raw first-order lifts: modulo a hidden p, Frobenius kills the nilpotent part, whereas raw translated powers have exponent-dependent derivatives. Computing dual beta-derivatives of the known u^N is possible, but their equality to derivatives of a native unknown-index power is not implied by equality at the single scalar beta. Derivative information cannot be transported across a pointwise equality without an additional identity.

## Root refinement: the natural mixed raw lift has the wrong jet on every own row

The following sharper construction was supplied by root and checked independently here. Retain y=X(1-g/m) modulo g², raw u=beta+X, and let sigma_k act on the étale subalgebra by y->y^k. For the native row define the actually acquired lift
  U=raw_u^ell * (beta+y^j)^a * sigma_k((beta+y)^N) modulo g².
All factors are explicit degree-2m elements, powers cost soft m for one row, and negative ell uses the certified u inverse. Modulo g this reduces to the original translated row. On its own prime p=P, j=P modulo m, Frobenius gives
  U mod g = raw_u^(aP+Q+ell)=q^I, n=m²I=aP+Q+ell.
But y'=0 modulo g implies
  U'/U=ell/raw_u modulo (p,g),
whereas the ACTUAL raw power has logarithmic derivative n/raw_u. Their difference is
  (n-ell)/raw_u=Q/raw_u modulo (p,g),
a unit because P and Q are distinct and raw_u is a unit. Therefore these first-order lifts NEVER agree at the own prime: their derivative difference is nonzero in every component. This uniformly refutes the particular attempt to initialize the raw-power extractor from this natural Frobenius-compatible mixed lift.

Equivalently the raw-lift extractor applied to U returns ell (hence ell/m²) in that component, rather than n (hence I). The discrepancy is Q/m² modulo P, nonzero. This is stronger than merely an absent proof of lift compatibility. A fully étale lift has zero derivative and loses the same exponent channel, but this review does not claim its derivative is unequal to n on every input: n modulo P could occasionally vanish. Neither statement is a general obstruction to other invariants or lift constructions.

## Paid ordinary branches and their limits

For a GLOBAL promised T=q^I, generic baby/giant search with b=ceil sqrt(L+1)=O(m) acquires b baby algebra elements and O(L/b) giant algebra elements. Each algebra multiplication has soft m cost. Exact vector sorting/matching and final verification give soft(m sqrt L)=soft m² residue work and O(m sqrt L) residue storage. This is a lawful fallback, but misses the target scale. It is not by itself a local-prime hit oracle for every native row.

The augmentation X->1 and full cyclic norm are acquired scalar homomorphisms:
  aug(u)=beta+1,  Norm_A(u)=beta^m+1.
For the cyclotomic quotient the norm instead is (beta^m+1)/(beta+1), with the denominator guarded. Their images of q are the d-th powers of these scalars. A scalar bounded-log branch costs soft sqrt L=soft m when its image has sufficient order, followed by full algebra verification. But those scalar order/uniqueness conditions are extra, and high order of beta does not establish them. Processing the entire native row family via such scalar images restores the old growing-degree scalar query. Norm-one components can lose all information under one chosen norm; a failed or ambiguous scalar log is not proof of no native algebra hit.

## Cost ledger and remaining constructive primitive

| Operation | Paid cost in residue arithmetic | Acquired output |
|---|---:|---|
| u^N and one q | soft m | full degree-m elements |
| One ordinary product/inverse | soft m, guarded | full algebra element or proper factor |
| Reduced logarithmic derivative | soft m | known f', with unknown wrap Q remaining |
| Actual raw g² lift supplied | stronger input | degree-2m target |
| Exponent from that raw lift | soft m | I or proper factor |
| Canonical étale lift | soft m | valid lift with zero normal derivative |
| Global generic bounded log | soft m² | bounded exponent if promised |
| One informative scalar-image log | soft m conditional | candidate plus full verification |
| Entire native local-hit family | no new bound here | existing whole query remains soft m^1.5 |

A useful next primitive would acquire the exponent-bearing first-order wrap of the actual unknown power, or a different shared invariant that detects native local equality across rows while charging their acquisition. The original reduced power, an AKS-style pointwise congruence, Kummer terminology, and scalar norms alone do not initialize it. No lower bound or sixth-rate claim is made.
