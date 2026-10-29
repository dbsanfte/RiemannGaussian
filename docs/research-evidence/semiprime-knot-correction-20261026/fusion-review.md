# Independent review: twisted free-fermion TQ closure

2026-10-26. **PASS for the displayed algebra, seed acquisition, unit ranges and conservative continuation costs in `fusion-correction.md`.** No experiments, source edits or repo edits. The rational eigenvalue remains distinct from its polynomially cleared transfer at singular points.

## Source TQ convention and seeds

Using Zhao–Yang–Zhang arXiv:hep-th/0506070v4 (II.17),(II.23),(II.24), put z=e^(2u), w=e^(2v), h=eta, h²=q. Their weights give

    a(u,v)=h(z-w)/(qz-w),
    c(u,v)/a(u,v)=(z-qw)/(h(z-w))=1/a(v,u).

Therefore the two scattering products really coincide and equal h^b Q(z/q)/Q(z), with no missing fermionic sign or inverse shift. Replacing the supertrace D-A by D-kappa A gives the generic factor (1-kappa A(z)); for the factored vacuum polynomial, A(z)=h^d F(z)/F(qz). Thus zeta=kappa h^d and equation (4)'s eta^b, z/q shift, and F(qz) denominator are correct. The source Bethe equation becomes kappa A(w)=1 on its regular generic locus; no physical Bethe basis is asserted at collisions.

With kappa=eta, zeta=eta^(d+1), d=2L is even. Hence q^j-zeta=eta^(d+1)(eta^(2j-d-1)-1), whose exponent is odd, nonzero, and of absolute value at most d+1. The stated range d+1 below both local eta-orders certifies every coefficient pivot. Publicly checking d+1<16H suffices when using the prepared lower bound; outside the stated asymptotic range the promised inherited fallback must remain explicit. Batch coefficient inversion and powers do cost soft O(L), and the leading F coefficient is unit. The coefficient identity F(qz)-zeta F(z)=S(z) holds exactly.

The passed roots are correctly recentered: v=x/eta and v^-1=eta/x. Equation (1)'s c^-m and eta^[L m(m+2)] factors follow directly from K(t)=c t^-L S(t). No unrescaled-root ambiguity from the earlier DW report remains.

## Cleared occupied transfer and telescoping

For Q=S and b=d, the rational identity has a common monic S(z) factor. Cancellation is legitimate as a formal polynomial/rational-function derivation; the resulting **defined cleared polynomial** is

    T_full(z)=eta^d S(z/q).

This polynomial identity remains valid upon composite-ring specialization. It does not say that Lambda_full(z)=T_full(z)/F(qz) can be numerically evaluated where F(qz) is nonunit, nor that it is a regular physical eigenvalue there. The report keeps that distinction.

For z_i=q*t_i, z_(i+1)=q*z_i, the Q ratios telescope with endpoints Q(z_1/q) in the numerator and Q(z_m) on the cleared left side. Equation (6) has the correct endpoints and eta^(bm). For the actual occupied seed its polynomial content can be checked without any cancellation of values: substitute T_full and both sides become eta^(dm) prod_(i=0..m)S(z_i), where z_0=z_1/q. Thus it holds even if intermediate factors vanish. For a general unspecified Q, equation (6) is still only the rational TQ identity unless its needed polynomial transfer has separately been established; the report's executable specialization is Q=S.

The stronger direct equation (7) is exact:

    prod_i T_full(z_i)=eta^(dm) prod_i S(t_i).

Its prefactor is unit, so it gives the claimed zero/nonunit equivalence without invoking any F-value or endpoint inverse. This, rather than multiplying by unknown nonunits in equation (6), is the safe predicate equivalence.

## Singular pivots and actual cost

The three branches are correctly separated. Coefficient pivots are units. Native Q endpoint values are not units by assumption and may factor or require original-row localization; z_m=eta^(2m+3) is one beyond this prefix, so the original consumer cannot silently be applied if that endpoint lies outside its declared global range. Inhomogeneity values F(q z_i) have no native leaf interpretation: proper gcds are useful, but saturated zeros do not automatically license an exponent relation. Keeping T_full cleared avoids both unjustified divisions.

F is acquired by its coefficients; its roots, inhomogeneity list, Bethe vectors and large physical chain matrices are not thereby acquired. The seed is a genuine soft-O(L) coefficient-diagonal inverse for any supplied native S. It does not reduce the remaining scalar product: the cleared full sector is a shifted S, and the inherited paid evaluator still costs soft O(L+sqrt(Lm)). The report neither charges the inverse seed as an evaluated norm nor claims that a formal endpoint quotient supplies the desired rate.

No genuine algebraic or cost gap found within this scope. A future use must preserve the explicit polynomial/rational distinction and the endpoint deletion-range qualifications already present in the report.
