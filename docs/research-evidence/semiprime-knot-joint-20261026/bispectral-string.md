# Initialized string moments and the exact short Christoffel determinant

26 October2026. Read `exact-string.md` and executed a dual-entry construction. Positive result: not only S_m(F), but an entire O(J)-moment sequence for a J-dimensional Hankel candidate is acquired in soft(J+sqrt m) by one convolution. Its determinant is not the string norm. The exact finite Christoffel/characteristic-polynomial dual determinant for that norm has J rows, but its entries retain the full off-grid string polynomial. This report separates the two matrices and pays their initialization; no complete-query gain is claimed.

## 1. Primary duality sources and their exact role

Mukhin–Tarasov–Varchenko, *Bispectral and (gl_N,gl_M) dualities, discrete versus differential*, https://arxiv.org/html/math/0605172, constructs correspondences between specified special trigonometric Gaudin and special XXX Bethe problems through integral transforms. It is not a theorem identifying every multiplicative XXZ polynomial residue Jacobian with a small determinant. The present roots have exact neighboring q-ratios and polynomial endpoint regularization; a regular Bethe-vector map, its norm normalization and its singular extension still need proof. Taking logarithms of arithmetic q to turn its shifts into additive XXX shifts is not a finite-ring operation.

A more explicit determinant source is Claeys–Van Neck–De Baerdemacker, *Inner products in integrable Richardson–Gaudin models*, https://arxiv.org/html/1706.05511, Sections3–5, and Claeys et al., *An eigenvalue-based method and determinant representations for general integrable XXZ Richardson–Gaudin models*, https://arxiv.org/html/1501.05827, SectionsIV.1–IV.3, equations(49),(50),(67). Their Cauchy/dual-state formulas need acquired eigenvalue variables and retain normalization factors; the latter paper explicitly distinguishes the product of two normalizations from their ratio. “Absorbing” a parameter-dependent prefactor into a state does not preserve native collision zeros automatically.

For example its rational Cauchy determinant uses the raw diagonal variable sum_alpha1/(v−z_alpha), rather than only an endpoint transfer ratio. For a geometric string the acquired TQ data gives

    Q(qv)/Q(v)=q^m*(v−z_0)/(v−z_m),
    q Q'(qv)/Q(qv)−Q'(v)/Q(v)
                   =1/(v−z_0)−1/(v−z_m),           (1)

where interpreted after clearing denominators. It supplies a shifted DIFFERENCE of logarithmic derivatives, not an initialized value of each raw sum. Collision denominators in these formulas cannot be inverted. Thus neither cited source directly supplies the missing matrix entries from the short TQ coefficients. The finite construction below goes further without importing physical norm claims.

## 2. Entire cheap moment sequence, initialized by one convolution

Use exactly the source string z_r=z_1 q^r, 0<=r<=m, weights

    w_r=(-1)^r q^[r(r+1)/2−2mr] [m choose r]_q,
    B_t=(q^(t+1−2m);q)_m.

For F(z)=sum_(j=0)^J f_j z^j define

    mu_t=S_m(z^t F)=sum_(r=0)^m w_r F(z_r) z_r^t
         =z_1^t sum_(j=0)^J f_j z_1^j B_(j+t).      (2)

Take eventually 3J<m; this follows from the actual asymptotic scales J=soft k,m=Theta(k^1.5). Small/exceptional prefixes retain the old evaluator, not this guard. Initialize B_0 by one scalar Pochhammer BSGS in soft sqrt m. The exact ratio

    B_(t+1)/B_t=(1−q^(t+1−m))/(1−q^(t+1−2m))

acquires B_0,...,B_(3J) in soft J. All numerator/denominator exponents here are nonzero, of magnitude<2m, and their factors are certified units. Let a_j=f_j z_1^j. Reverse the length-J+1 list a and convolve it with B_0,...,B_(3J): convolution coefficient J+t is sum_j a_j B_(j+t). Multiply by z_1^t. Thus ALL mu_t for0<=t<=2J are acquired in soft(J+sqrt m), including starts and unit inversions.

Consequently the Hankel matrix H_s=(mu_(a+b))_(0<=a,b<s), s<=J, has an initialized displacement/moment descriptor of length2s−1 at that same cost. This is a real small structured matrix entry map; it does not require m F-evaluations. Dense materialization has s² entries and is not charged as free. A fast Hankel determinant algorithm would additionally need its own pivot/zero-divisor treatment over R; even granting such an algorithm would not make the following matrix the desired norm.

## 3. What the cheap determinant actually evaluates

Cauchy–Binet gives the exact finite identity

    det H_s =sum_(A subset {0,...,m}, |A|=s)
                 product_(r in A)[w_r F(z_r)]
                 product_(r<t in A)(z_t−z_r)^2.     (3)

This identity is division-free and holds over R. For s=J<m it is a weighted selected-J-point ensemble; it does not contain every F(z_r) as a factor. Equivalently, its degree in the free constant coefficient f_0 is at mostJ, whereas the full product has degree m+1. This is a check of this PARTICULAR candidate identity, not an arithmetic/circuit lower bound or a prohibition on an F-dependent extra normalization. Such a normalization would have to be explicitly proved and initialized.

At the full support size n=m+1, however, (3) has only one subset:

    det H_n = D_n(1)*product_(r=0)^m F(z_r),
    D_n(1)=product_r w_r * product_(r<t)(z_t−z_r)^2.  (4)

The base factor D_n(1) is a mathematical unit under the native guard. Its optional numerical acquisition is not assumed cheap. Formula(4) proves why the full moment determinant contains the target, and why replacing its size by J changes its scalar.

## 4. Execute the exact J-dimensional dual determinant

Factor F(z)=product_(a=1)^J(z−v_a) using the acquired native roots. Set

    Q_n(z)=product_(r=0)^m(z−z_r), n=m+1.

The finite Christoffel/characteristic-polynomial determinant at n-point full support can be derived directly, with no orthogonal-polynomial existence assumption. Choose the monic vanishing polynomials p_(n+h)(z)=z^h Q_n(z),0<=h<J. Then

    det_(a,h)[p_(n+h)(v_a)]
       =product_a Q_n(v_a) * det_(a,h)[v_a^h].       (5)

After the usual (-1)^(nJ) resultant sign, product_a Q_n(v_a) is exactly product_r F(z_r). Thus the short dual determinant exists and is explicit; its entries are

    M_(a,h)=v_a^h Q_n(v_a).                          (6)

Vandermonde division in (5) may be done formally as the alternating polynomial identity, not by an untested numerical inverse at repeated/nonseparated native roots. Confluent rows contain derivatives and need not individually retain a Q_n factor. The final polynomial quotient identity extends with multiplicity by polynomial continuation. No generic field unit premise is silently specialized into R.

Equation(6) exposes the scalar initialization exactly: each row contains the FULL off-grid Pochhammer Q_n(v_a). Acquiring these values jointly is the original geometric product evaluation problem (and their product is the original target norm). The existing completed bound is soft(J+sqrt(Jm)); the cheap moment convolution(2) has not computed them. In this exact full-support duality the high-degree polynomials collapse to Q_n times monomials, not to the already-acquired cheap S_m coefficients. This revisits the prior off-grid issue only after providing the new initialized moment sequence and deriving precisely where it fails to supply the actual norm matrix.

## 5. Match to the actual exact-string Jacobian

The qhol report proves

    det normalizedJacobian
       =product_(i=2)^m F(z_i) * S_m(F),             (7)

with S_m(F)=mu_0. Its tridiagonal/Dirichlet contraction already isolates a one-dimensional auxiliary readout. The additional acquired mu_t do not replace the multiplicative factor in (7): their small Hankel determinants are (3), and the exact full-support dual is (5),(6). Endpoint omission and S_m simply multiply the corresponding known/auxiliary factors; they do not remove its interior Q_n evaluations.

No division by S_m or a native F value is licensed. A proper gcd of a cheap moment/determinant may of course factor N, but a saturated additive moment relation is not an original exponent gap and has no automatic short-annihilator decoder. A physical Bethe-norm duality would need to match (7) with all of these zero factors and supply the missing initialized entries, not just identify a transfer spectrum or a normalized Bethe vector.

## Outcome

The concrete acquisition gain is an entire O(J)-moment/eigenvalue-like alphabet in soft(J+sqrt m), rather than a single S transform. The tested small determinant of that alphabet is the wrong subset scalar; the exact J-dimensional dual determinant of the full norm has the right scalar but unacquired Q_n(v_a) row factors. No complete native collision query or new factoring bound is established. A further identity relating this PARTICULAR finite moment alphabet to the full-support norm with paid, collision-safe normalization remains a precise possible target. Scratch only; no numerical campaign or repository edits.

## Addendum: the degree-at-most-J epsilon core and its normalization

The newly supplied exact factorization S_epsilon(F)=C(epsilon)T_J(epsilon) is compatible with the initialized moment alphabet above. Here C(0)=1 and T_J(0)=F(z_1), so the pencil identity gives

    det M_epsilon=[product_(i=2)^m F_i] C(epsilon)T_J(epsilon),
    det M_0=product_(i=1)^m F_i.                     (8)

On a generic regular pencil this separates m−J fixed generalized eigenvalues from a core of degree at most J, but still leaves the common scalar. At a native collision the determinant polynomial can be identically zero; only its division-free factorization is asserted without genericity. One can identify the normalization loss concretely. Write the actual tridiagonal pencil as A+epsilon D, with A upper bidiagonal having diagonal F_i and upper −F_i, and D lower bidiagonal with diagonal kappa_i F_(i+1) and lower −kappa_i F_(i+1). On the generic unit branch,

    det(I+epsilon A^-1 D)=C(epsilon)T_J(epsilon)/F_1. (9)

The operation A^-1 has divided out det A=product_i F_i, exactly the target normalization. At a native collision this inverse is illegal. A constant known-unit basis change can move spectral blocks but does not license that inversion; if its block elimination is valid without it, the determinant of the eliminated block must still be included in (8). Recovering that block determinant is the additional scalar algorithm to supply.

The leading epsilon coefficient does not fix this gap for free either: det D=(product_i kappa_i) product_(i=2)^(m+1)F_i, so on the generic unit branch its ratio to det A is (product_i kappa_i)*F_(m+1)/F_1. After formal cancellation this expression can be evaluated whenever F_1 is a unit; no inversion is licensed at F_1=0. Each determinant individually retains the interior product. The explicit small core may encode F and support a further nontrivial algorithm; this calculation only identifies what normalization the immediate spectral reduction removes. It does not assert a general impossibility for such algorithms or for a source-specific singular duality.
