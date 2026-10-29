# Independent review: bispectral-string.md

26 October 2026. Read-only review; no numerical campaign or repository changes. Verdict: principal finite identities and acquisition claim pass. Two genericity qualifications below should accompany the epsilon-spectrum language; neither affects the stated non-advancement.

## One convolution and units: pass

Expanding F gives mu_t=z1^t sum_j f_j z1^j B_(j+t). With reverse list c_(J-j)=f_j z1^j, coefficient J+t of c*B is exactly that sum. B through index 3J suffices for t<=2J. Computing B through 3J uses the stated ratio at indices 0<=t<3J. Under 3J<m, its numerator exponent t+1-m and denominator exponent t+1-2m are nonzero, negative, and of magnitude below 2m; all are native units. B0 is a single length-m scalar Pochhammer. Thus the initialized descriptor really costs soft(J+sqrt(m)); dense Hankel acquisition and determinant readout are correctly not free. Eventual 3J<m is sufficient, with the explicitly retained old evaluator covering other prefixes.

## Finite support and Christoffel signs: pass

Let V_(a,r)=z_r^a. H_s=V diag(w_r F(z_r)) V^T. Cauchy–Binet gives exactly the stated subset sum, with positive squared Vandermonde and no missing factorial. At n=m+1 only the full subset remains. Every w_r is a unit: its Gaussian-binomial numerator/denominator consists of short nonzero q-differences. Every z_t-z_r is likewise a unit for 0<=r<t<=m. Hence D_n(1) is a mathematical unit; the report properly makes no free numerical-acquisition claim.

For monic F=prod_a(z-v_a),

    prod_r F(z_r)=(-1)^(nJ) prod_a Q_n(v_a).

The row-a/column-h determinant of v_a^h has sign convention prod_(a<b)(v_b-v_a), so Eq. (5) and its stated resultant sign are correct. The chosen p_(n+h)=z^h Q_n is a direct finite vanishing-polynomial identity, not an unjustified assertion of nondegenerate orthogonal polynomials beyond support. Repeated roots are handled by polynomial continuation of the quotient identity.

Minor wording: confluent determinant rows include derivatives of Q_n, and these individual rows need not retain a factor Q_n(v). The final polynomial quotient still equals prod_a Q_n(v_a), with multiplicity, by continuation. The source report's conclusion remains correct; interpret “retain the same Q_n factors and derivative data” at the final-identity level, not as rowwise divisibility.

## Epsilon core: normalization passes, degree needs qualification

The exact factorization can be stated without an external supplied formula. Put

    C(eps)=(eps*q^(J+1-2m);q)_(m-J),
    T_J(eps)=sum_(j=0)^J f_j*z1^j
         *(eps*q^(j+1-2m);q)_(J-j)
         *(eps*q^(1-m);q)_j.

Indeed the common exponent interval in each length-m term is [J+1-2m,-m], and the two complementary strips have lengths J-j and j. Consequently C(0)=1, T_J(0)=F(z1), and deg T_J<=J. This proves the addendum's factorization over R without division. The fixed C factors have known clock parameters; it does not acquire the common interior norm.

For A the upper bidiagonal part and D the lower bidiagonal part, det A=prod_(i=1)^m F_i and det D=(prod_i kappa_i) prod_(i=2)^(m+1) F_i. On the generic branch where every F_i is invertible,

    det(I+eps A^-1 D)=C(eps)T_J(eps)/F_1.

This follows directly by dividing det(A+eps D) by det A; thus it divides out exactly the target, as the report says. At native collisions the polynomial determinant factorization remains valid but the inverse formula is unavailable. Similarly det D/det A=(prod_i kappa_i)*F_(m+1)/F_1 requires the generic branch (or F1 invertible after formal cancellation); endpoint ratio cannot be inverted silently at F1=0.

Required precision: “degree-J core” means degree **at most** J. Its leading coefficient may vanish after specialization. “m-J fixed generalized eigenvalues” is a generic regular-pencil statement, not an unconditional statement when the retained scalar prod_(i=2)^m F_i vanishes and the determinant polynomial may be identically zero. The division-free C*T factorization is unconditional and is the preferable native-ring formulation.

## Primary-source scope and overall conclusion

Checked the primary HTML displays of [Mukhin–Tarasov–Varchenko](https://arxiv.org/html/math/0605172), [Claeys–Van Neck–De Baerdemacker](https://arxiv.org/html/1706.05511), and [Claeys et al.](https://arxiv.org/html/1501.05827). Their model-specific bispectral/dual-state and normalization scope does not supply an automatic finite-ring singular-string norm identification. The report appropriately derives its actual finite identities separately rather than claiming that identification. Equation (1)'s logarithmic-derivative difference follows by differentiating the displayed finite Q-ratio, with no error in its q factor.

No complete-query improvement is claimed or established. The new paid moment alphabet is genuine; its small Hankel determinant has the wrong subset scalar, and the correct short resultant determinant retains unacquired full Q_n row values. Existing scalar/native decoder distinctions remain intact.
