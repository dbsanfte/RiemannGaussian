# Independent review of the exact-string Jacobian and epsilon core

26 October2026. Read current `exact-string.md`; independently checked the formulas algebraically by hand, including the supplied forthcoming epsilon-core factorization. No numerical campaign, new literature search or repository edits. The stated contraction and cost pass. The report correctly leaves the interior native norm uncomputed.

## TQ, derivatives and unit normalization

The finite ratios Q(qz)/Q(z) and Q(z/q)/Q(z) have the displayed q^m and q^-m factors and endpoints. Multiplying by a=(z−z_m)F and d=epsilon(z−z_1)F(qz) gives the acquired T_epsilon exactly, without a Q coefficient expansion.

In the interior derivative only the neighboring vanishing factor contributes. Its coefficient is z_(i+1)a(z_i)Q'(z_(i+1)) for the upper difference and z_(i−1)d(z_i)Q'(z_(i−1)) for the lower difference. Endpoint coefficient derivatives give z_1 epsilon F_2 Q(z_0) and z_m F_m Q(z_(m+1)), with no derivative of F surviving there. Thus the proposed C_i normalize only clock factors. Each difference is a unit times1−q^r,0<|r|<=m, so C_i and their product Omega_m really are units. No F-related inverse occurs.

The displayed cofactor formula for Q'(z_j) is correct. Its ratio at j=i−1,i+1 gives the exponent q^(i−2m), a minus sign from the canceled1−q^(i−1), and the remaining factor (1−q^(m−i+1))/(1−q^i). This verifies the printed kappa_i for interior rows and the endpoint formulas match it. For m=1 the single normalized entry is F_1−epsilon q^-1 F_2, consistent with the same formula. “Logarithmic tangent coordinates” here means the algebraic substitution delta u_i=z_i delta e_i; it takes no logarithm of a field element or zero equation.

## Determinant and actual auxiliary cost

The path continuant sum has products D_1...D_r A_(r+1)...A_m, with the row-i lower coefficient D_i as printed. It factors product_(i=2)^m F_i polynomially and gives the w_r product of kappa values. Its q-power is r(r+1)/2−2mr. Expanding F(z_1q^r) therefore matches the finite q-binomial theorem exactly. This verifies S_m(F), including the shifted exponent j+1−2m.

For J<m, B_0 has a length-m scalar factorial acquired in soft sqrt m; every ratio needed through B_J uses nonzero exponent with magnitude<2m. The consecutive coefficient acquisition, unit batch inverses and dot product cost soft J. Hence S_m(F) is genuinely paid in soft(J+sqrt m). Numerical Omega_m remains optional: direct acquisition may cost soft m, but its proved unit status suffices for zero/nonunit predicates. Neither the full m-by-m matrix nor all its F_i entries is claimed acquired at the target scale.

The initial prefix-unit exponent c^m eta^(-Lm(m+2)) is correct. The m=0,1 direct cases are correct. For m<=J the old soft(J+sqrt(Jm)) evaluator is soft J, so these prefixes need no new argument. For m>J the explicitly required2m order guard suffices for all stated inverses. Asymptotic J=soft k,m=Theta(k^1.5) ensures J<m eventually; finite guard exceptions correctly retain the old evaluator rather than assuming a uniform numerical threshold.

## Supplied epsilon core: factorization and paid conversion

For J<m the intersection of the exponent intervals [j+1−2m,j−m],0<=j<=J, is [J+1−2m,−m]. Thus

    S_epsilon(F)=C(epsilon) T_J(epsilon),
    C=(epsilon q^(J+1−2m);q)_(m−J),
    T_J=sum_j f_j z_1^j U_j,
    U_j=product_(r=j+1)^J(1−epsilon q^(r−2m))
          product_(r=1)^j(1−epsilon q^(r−m)).

These are exact polynomial identities, with C(0)=1 and T_J(0)=F_1. The coefficient vector of T_J, of degree at most J, is acquired in soft J, not J²: write A_r=1−epsilon q^(r−2m), B_r=1−epsilon q^(r−m). For coefficients c_j define the local sum

    P_[lo,hi]=sum_(j=lo)^hi c_j
       product_(r=j+1)^hi A_r product_(r=lo+1)^j B_r.

Splitting at mid gives P_left times product_(r=mid+1)^hi A_r, plus P_right times product_(r=lo+1)^(mid+1) B_r. Product trees and balanced polynomial multiplication acquire this recursively in soft J. There is NO inversion of an epsilon-dependent value. The root's proposed initialization therefore passes independently of a specialized q-basis-conversion theorem. The long C coefficient vector is not acquired for free; its factored descriptor and individual scalar evaluations have the stated finite-factorial interface.

On a generic regular pencil this core identifies m−J known generalized eigenvalues and at most J remaining finite ones. At collisions the determinant polynomial may be identically zero; the division-free factorization remains the valid statement. It does not fix the common determinant scale. At epsilon0 the determinant is product_i F_i; any reduction through A^-1 for the upper-triangular epsilon0 matrix divides out precisely this target product and is illegal at its collisions. A known-unit basis change alone does not authorize dropping the eliminated block determinant. This agrees with the separate `bispectral-string.md` normalization audit.

## Decoder and scope

F_(m+1) occurs only in the auxiliary endpoint sum, not in the original m-position prefix. Its zero, or a saturated zero of S_m(F), T_J, C, or any selected auxiliary determinant, receives no original-leaf decoder automatically. A proper gcd of any acquired scalar is useful regardless of its interpretation; a saturated additive relation is not a nonzero beta-annihilator. Known C(epsilon) roots may make the pencil determinant identically zero for spectral reasons and must not be treated as collision witnesses. F_1 is genuinely an original leaf and is correctly handled separately.

The finite polynomial on-shell condition and cleared residue Jacobian are established; physical Bethe-vector nonvanishing, singular Gaudin normalization and universal norm identification are expressly not assumed. The report's positive result is the cheap TQ/weighted-sum/core acquisition, with the actual interior product retained. No full-query speedup or native coverage gain has been proved.
