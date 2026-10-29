# Finite root-system / denominator trial on the actual native conic catalogue

26 October 2026. Scratch only. The native indices do admit an exact ternary quadratic-lattice description. The inspected denominator identities do not evaluate its truncated multiplicative query: the finite theta replacement has an explicit nonconstant endpoint boundary, while a Borcherds completion changes both multiplicities and support. No new full-query cost is established. This is a source-specific mapping/correction calculation, not a general obstruction to DAHA or automorphic methods.

## 1. Exact lattice map, including the factor of two

Keep the original complete catalogue labels: H=k², k=2*3^e, 0<|ab|<k plus the four original axes, 0≤lambda<H, lambda²=4abN mod H, E=a+bN+lambda. Public integer-zero deletion and any paid content/diagonal filters remain attached to the original labels; replacing them by an unfiltered lattice product would need a coverage proof.

Every allowed lambda is even, since its square is zero modulo 4. Set ell=k/2, lambda=2r. The conic condition becomes exactly

    Q(a,b,r):=r²−Nab = 0 mod ell²,
    0≤r<2ell².                                       (1)

It is not the equality Q=0. The even integral bilinear form

    <(a,b,r),(a',b',r')>=2rr'−N(ab'+a'b)

has norm 2Q and signature (2,1). The recentered native monomial is exactly

    beta^(E−H/2)=beta^(a+bN+2r−2ell²).                (2)

Thus the obvious formal torus substitution is A=beta, B=beta^N, C=beta², with a common beta^(−H/2) factor. It retains the arithmetic N and the uncentered representative of r. If Q=ell²*c, the integer c is an acquired carry for that label, not a relation beta^(Q)=1. The generic lattice monomials A^a B^b C^r are specialized at a known one-dimensional torus point; they are not assumed algebraically independent after specialization.

This is a genuine indefinite-lattice resemblance. Its multiplicity function, however, is the finite indicator of (1), the product cut |ab|<k, the r representative window, the exceptional axis list, and the actual deletion/filter flags. It is not yet the coefficient system of a root denominator.

## 2. Execute finite theta quasi-periodicity with its exact boundary

Primary source: Rosengren–Schlosser, *Elliptic determinant evaluations and the Macdonald identities for affine root systems*, https://www.mat.univie.ac.at/~schlosse/pdf/determinants-new.pdf , §2 equations (2.1)–(2.3), Proposition 3.4 and Theorem 4.4. Their nome p satisfies 0<|p|<1; the polynomial p=0 limits are treated separately. The infinite theta function has exact quasi-periodicity theta(px;p)=−x^(-1)theta(x;p). The master determinant needs such theta functions; its proportionality constant is not generally an evaluated input.

The legitimate finite replacement for the paired native clock is

    Theta_m(x;q)=(x;q)_m (q/x;q)_m.

Shifting the two finite factors and clearing, rather than evaluating a quotient at a possible zero, gives the exact Laurent-polynomial identity

    (1−q^m/x) Theta_m(qx;q)
       =−x^(-1)(1−x q^m) Theta_m(x;q).               (3)

For m=0 the function is 1 and the same identity still holds; empty products need no inverse. For m≥1 it follows by canceling formal common factors, with (1−1/x)=−x^(-1)(1−x). No target is inverted in (3).

Equation (3) is the actual finite boundary missing from the naive theta substitution. The ratio is not −x^(-1): its endpoints are (1−x q^m)/(1−q^m/x). These are potential native comparison factors. One can screen a constant number of endpoint products with the existing acquired root polynomial in softly O(J) and use the licensed original-label recovery when the screened endpoints belong to the legal label/clock range. A saturated auxiliary/out-of-range endpoint cannot be silently fed to that consumer. Keeping (3) cleared avoids every such division. Even when the endpoints are units, the scalar value of Theta_m at an initial x is still an unacquired long product.

The Rosengren–Schlosser factor-identification proof uses the exact scalar quasi-periodicity to show the determinant quotient is constant. Substitution of Theta_m changes that premise by precisely the two factors in (3). Thus their Proposition 3.4 does not give the same constant for this finite native kernel. Restoring those factors in every shifted row is a new finite boundary problem, not a licensed application of the infinite theorem. Setting the analytic nome p to the native q does not define the infinite products in R. Setting p=0 is a valid polynomial specialization but removes the entire affine clock string instead of evaluating its truncation.

## 3. The finite Weyl identity that does apply

The polynomial A-type denominator is exactly the Vandermonde. If X is the length-m clock alphabet and V is the acquired complete recentered root alphabet, then

    Vandermonde(X concatenated V)
      = Vandermonde(X) Vandermonde(V)
           *∏_(x in X,v in V)(v−x).                  (4)

Its cross product is the original scalar product up to acquired powers and normalization units. Equation (4) is finite and valid with repeats over R; no division is necessary. Native clock differences are units in the supplied short range. Target-target differences are not assumed units; if a separate paid original-label separation is available they may become units, otherwise retain the cleared identity. In particular a zero in Vandermonde(V) is background degeneracy and is not itself a prefix collision.

The C/D denominators add paired factors 1−v_i v_j. A reciprocal native root list contains v,v^(-1), so these factors can vanish identically; they cannot be divided away to obtain the desired cross norm. Auxiliary phase rotations can repair selected unwanted factors as in the already audited DW construction, but then one must retain the altered cross factors. No source identity here declares that completion scalar equal to the original query.

The determinant in (4) has order m+J, not the square root of the number of factors. Acquiring its explicit entries or alphabets already costs Omega(m+J), above the target when m~k^(3/2). The smaller acquired polynomial description of V does not acquire the cross-resultant. This finite identity is therefore a lawful comparison, not a new algorithm. The additional free parameters in Theorem 4.4 still require its prescribed theta/polynomial column functions and their endpoint values; arbitrary native conic masks do not automatically supply that basis.

## 4. Exact multiplicity and finite-support mismatch for a Borcherds lift

Primary source: Borcherds, *Automorphic forms with singularities on Grassmannians*, Invent. Math.132 (1998),491–562, Theorem 13.3 and its product expansion: https://math.berkeley.edu/~reb/papers/aut/aut.pdf . Its exponents come from coefficients of a specified vector-valued modular form, indexed by a norm and discriminant-lattice coset, and its product is over a Weyl-chamber half of an infinite lattice. Neither modularity of an arbitrary cutoff indicator nor numerical evaluation over R follows from recognizing a discriminant.

The actual candidate input would have to encode

    multiplicity(a,b,r)=1_(Q=0 mod ell²)
                        *1_(0<|ab|<k or listed axis)
                        *1_(0≤r<2ell²)
                        *1_(actual retained label),                 (5)

with any repeated scalar values retaining original integer labels. This is a precise required multiplicity, not just a theta series supported on Q=0 mod ell².

The original axes make one mismatch transparent: for fixed r=ell (lambda=k), Q=r² on the entire line (a,0,r), independent of a, but only a=+k and a=−k are original horizontal axes. A norm/coset coefficient cannot select just those two a-values from that line: every fixed finite discriminant module repeats its coset along some nonzero period in a. A chamber's linear positivity cannot retain the selected point while deleting all sufficiently distant translates in both directions along that line: one direction remains positive, or the functional is constant on the line. Some of these labels might have been pruned in a later actual packet; then (5) becomes still more label-dependent rather than a direct root-multiplicity theorem. This is an exact mismatch for the naive norm/coset coefficient proposal, not a theorem against more elaborate vector-valued boundary encodings.

Away from the axes the bounded hyperbola |ab|<k and the finite r window likewise supply boundaries independent of a norm-only Fourier coefficient. The conic includes all admissible ramified root lifts, with counts depending on the valuations of ab at 2 and 3; these are not a uniform list of affine real-root strings. A construction may encode them by enlarging its discriminant data, but it must acquire that data and prove the required modular transformation law and boundary correction. Those obligations are not discharged by (1).

Completing (5) to a full denominator product adds factors with monomials still in the native odd-order subgroup. No −1/2-primary separation makes them automatically units. For example omitted lambda=0 axis values a other than ±k give exponents a−H(i+1) at an odd clock after the recentering; these exponents can exceed the certified order margin, so the short-difference guard does not certify their factors as units. This does not assert that a specific added factor vanishes in every native instance. It identifies the exact missing unit test before a completion/quotient argument can preserve zeros. Infinite analytic products or a formal identity at a cusp cannot replace that test in the finite composite ring.

## 5. Narrow constructive interface left open

The useful positive output is the exact Lorentzian lattice/torus map (1)–(2) and the finite endpoint correction (3). A genuinely applicable finite denominator theorem would need to accept the actual multiplicity (5), retain the hyperbola and representative boundaries, and produce an acquired determinant/alternating sum whose entries and scalar normalizer cost softly O(J+sqrt m). Any added lattice factors must be certified units or supplied with original-label recovery; no formal cancellation through unknown zeros is allowed.

The inspected Macdonald/Weyl formulas do not provide that finite masked identity. Their polynomial specialization yields (4), and their infinite theta formulation loses its defining quasi-periodicity at the precise finite boundary (3). A Borcherds construction would additionally need the specified modular input and cutoff correction. No complete native query improvement is established, and the paid bound remains softly O(J+sqrt(Jm)). No general lower bound for automorphic, DAHA or native arithmetic methods is claimed.
