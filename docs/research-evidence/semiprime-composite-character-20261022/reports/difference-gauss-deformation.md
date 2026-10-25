# Antipodal differences: paid scalar norm screen, unresolved trace acquisition

22 October 2026. Scratch continuation of the reviewed `gauss-weighted-norm.md`. No repository edits, new agents, examples, or backend claims. The exact paid positive output below is a degree-O(m) scalar norm-screen polynomial for a common seed. It is not the native target-difference polynomial and supplies no sixth-rate factor guarantee.

## Setup and the exact paired difference

Retain the full packed algebra A=(Z/N)[X]/(X^m−1), m odd prime, gcd(N,m ell)=1, E0=m^−1 sum X^r, D=E0+(1−E0)ell, U=g_1^m, qG=U^m. All Gauss exceptions are retained. Native targets obey

    T_j T_-j = K_j = U^(−m s_j) D^(a_j+N),
    bar(T_j)=D^ell_j U^(m s_j) T_-j,
    T_j bar(T_j)=D^E_j,   E_j=N+a_j+ell_j.

Here bar=rho_-1; centered b lifts give s_j in {0,1,2}. The K_j are paid by three vectors plus O(m) descriptors, not m expanded vectors.

For a common seed t the exact antipodal difference is

    (T_j−t)(T_-j−t)=t²−t S_j+K_j,
    S_j=T_j+T_-j.

Thus extending the acquired constant term requires the trace S_j, or an aggregate contraction that bypasses its list. The different known multiplier D^ell_j U^(m s_j) relating T_-j to bar(T_j) does not supply that trace. The whole product over j does not remove these linear terms merely by commutativity.

The more intrinsic conjugate deformation gives

    (T_j−t)(bar(T_j)−bar(t))
      =D^E_j+t bar(t)−[T_j bar(t)+bar(T_j)t].

Its two norm terms are paid in the seed case below. The remaining mixed trace is precisely the phase-sensitive information. Inserting an additive parameter into these identities is not an algorithm for acquiring it: coefficient extraction needs a construction of that coefficient. Hasse–Davenport product identities used in the preceding report control multiplicative Gauss products; they do not identify the mixed trace in this displayed equation. No additional literature theorem is being attributed here.

## A genuinely acquired common-seed group observable

There is a useful weaker output, directly from the established conjugation norm. Compute the scalar residues

    b_j=ell^E_j mod N,
    B(Z)=product_(j=1)^(m−1)(Z−b_j) in (Z/N)[Z].

Negative E_j use the paid inverse of ell. All |E_j| have O(log N) bits in the native regime. Scalar binary powering for all rows costs soft O(m) bit work, and a monic scalar product tree constructs the complete degree-(m−1) B in soft O(m) bit work, retaining polylog N factors. This is an actual coefficient output, not a formal logarithm. Neither C_j nor any degree-m target vector is acquired per row.

For a COMMON specified seed t=qG^I, its norm is D^(m²I). On every primitive character component, the scalar screen is

    B(ell^(m²I))=product_j(ell^(m²I)−ell^E_j).

It is paid in soft O(m+log |I|) native bit work for polynomial-size I. A true equality T_j=t in the WHOLE local character algebra modulo P implies the jth factor is zero modulo P. Equality only at one character component is insufficient to conjugate it; equality at both conjugate components is enough for that componentwise norm implication. The trivial character component is explicitly vacuous: D is one there, so the norm screen is identically zero there. Consequently one must use the scalar primitive-component screen above, not gcd of a packed vector containing its unavoidable trivial zero.

A proper gcd of the acquired scalar B value with N is a factor. A product tree can localize a saturated product to rows; a row whose scalar difference is already zero modulo N remains saturated and provides no factor by itself. Norm projection introduces extra zeros. There is no claim that this procedure always gives a proper factor or that all original target differences have been evaluated.

This is a constant-seed screen for ALL rows, not an existence theorem for a useful known common seed. It also extends immediately to any publicly acquired seed whose whole-algebra norm has the form E0+(1−E0)tau for a known scalar tau: evaluate B(tau).

## Long seed family: exactly what remains unpaid

For I in an interval of length L, the screen asks for

    B(v^I),   v=ell^(m²),

or its zero-support aggregate. The degree-O(m) polynomial B really is paid. It is nevertheless the familiar explicit-polynomial/geometric-orbit collision query: conventional baby/giant polynomial batching costs soft O(m+sqrt(mL)) rather than soft O(m+sqrt L). For J~m and L~m² this has the same m^(3/2) residual scale. Computing each common-seed screen separately would instead cost soft O(mL). The argument here supplies no lower bound, only no new evaluator for these actual inputs.

Moreover v inherits no reviewed prepared order or local-order separation from qG or the original gamma. Replacing the original H query by the scalar norm screen requires handling its saturated extra zeros, not just computing a field norm. Its true-source inclusion is sound but is weaker than a recovery-preserving equivalence.

## Scalar rescaling: exact family, no free phase recovery

For a public scalar unit c, replacing g_1 by c g_1 and all conjugate g_j by c g_j consistently gives

    C_E -> c^(E−1) C_E,
    T_j -> c^E_j T_j,
    qG -> c^(m²)qG.

Thus the scalar norm screen base becomes ell*c². A constant/polylogarithmic family of such screens is acquired for a COMMON known I in soft O(m) work. This is an exact public deformation retaining the exceptional character as well: its trivial target norm is c^(2E_j), not automatically one after rescaling.

The information obtained is still exponent/order information. Writing d_jI=E_j−m²I, simultaneous primitive screens for c=1 and a unit c say ell^d=1 and c^(2d)=1 modulo the factor. If c has odd order the latter is c^d=1. It does not reveal the mixed Gauss trace. At the own-tag native true index, the identity m²I=a_j P+Q+ell_j gives

    d_jI=(P−1)(Q−a_j),

so all these scalar unit screens have the expected true-source inclusion by Fermat. The rescaling therefore returns the original scalar orbit-collision structure, rather than acquiring its unknown index or its whole long-product value. Requiring the SAME row/index across bases is also essential; independent zeros from different rows/indices cannot be intersected for free.

## Precise remaining constructive target

A sufficient next primitive would acquire, in soft O(ell+m), either (i) the product of the paired quadratics t²−t S_j+K_j at a supplied common t, without m degree-m S_j outputs, or (ii) a restriction-stable nonunit test on the mixed traces T_j bar(t)+bar(T_j)t, including all exceptional components. No algorithm for either primitive follows from the sparse Jacobi histogram or the already acquired antipodal norms. For the long orbit, even the paid scalar norm projection still needs an evaluator for B(v^I) at the requisite total cost and a saturated-hit recovery argument. This report supplies the actual degree-m scalar B acquisition, but no new universal factor-producing algorithm.
