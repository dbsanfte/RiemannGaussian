# Whole native weighted Gauss aggregate: acquired antipodal collapse, no support query

22 October 2026. A concrete WHOLE weighted product is acquired without constructing m separate degree-m vectors. Its collapse uses the exact native integer-weight symmetry, including all carries and the trivial character. It does not compute the original collision product or a sufficient factor-support observable. No repo changes, tests, examples or new agents.

## Exact acquired weighted product

Let the public auxiliary prime ell satisfy m|ell-1, m odd prime, gcd(N,ell*m)=1. Work in the reviewed packed algebra A=(Z/N)[X]/(X^m-1), with g_j the conceptual auxiliary Gauss sums, g_0=-1 and g_1^E=C_E g_E. Let

    U=g_1^m=-C_m,
    E0=(1/m)sum_(r=0)^(m-1)X^r,
    D=E0+(1-E0)*ell.

D is a unit, with inverse E0+(1-E0)/ell. For every 1≤j<m, the FULL packed identity is

    g_j g_(m-j)=D,
    C_j C_(m-j)=U/D.                              (1)

At a nontrivial order-m character, chi(-1)=1 because m is odd, so the first identity is the ordinary inverse-character Gauss product ell. At the trivial character it is (-1)²=1. E0 retains that exceptional component. The second identity follows by multiplying the two defining quotient equations; j+(m-j)=m as INTEGER exponents, so the numerator is U, with no discarded carry.

The actual canonical weights are a_j=Nj^(-2) modm, represented in [1,m). Therefore EXACTLY a_(m-j)=a_j as integers. Put h=(m-1)/2 and A=sum_(j=1)^h a_j. Pairing (1) gives

    product_(j=1)^(m-1) C_j^(a_j)=(U/D)^A.          (2)

Thus this Stickelberger-like weighted product is genuinely acquired in soft O(ell+m) native bit work: acquire C_m by the reviewed histogram primitive, construct E0,D, sum the O(m) public integer weights and perform O(log(m²)) cyclic modular powers. No C_j list, m-by-m coefficient array, per-j inverse or hidden character value is required. A has O(log N) bits in the native polynomial-size regime. All factors and denominators are certified units.

The exact evenness a_(m-j)=a_j is indispensable. Replacing the weights by their modular residues does NOT authorize changing their integer powers: adding m b_j to a weight introduces C_j^(m b_j)=U^(j b_j)rho_j(U)^(-b_j), which is generally not one. Equation (2) uses the actual integer weights and their exact pairing, not a reduction of exponents modulo m.

## Entire corrected native target product also collapses

Use the already proved corrected Gauss target, with r_j=Nj^(-1) modm,

    T_j=g_1^(ell_j) g_j^(a_j) rho_j^(-1)(C_N) g_(r_j).

These targets live in the character base algebra because their additive character grade is zero. Pairing j and m-j gives r_(m-j)=m-r_j, so their Gauss product is D. Also the archived reciprocal correlation gives

    C_N rho_(-1)(C_N)=E0+(1-E0)ell^(N-1)=D^(N-1).

Applying rho_j^(-1) preserves D. Therefore, without materializing ANY T_j,

    product_j g_j^(a_j)=D^A,
    product_j g_(r_j)=D^h,
    product_j rho_j^(-1)(C_N)=D^((N-1)h),
    product_j T_j=g_1^(sum_j ell_j) D^(A+Nh).       (3)

Every factor's trivial component is included correctly: the Gauss factors paired there multiply to one and C_N(1)=1 for odd N. Native centred antipodal lifts give ell_j+ell_(m-j)=-m² s_j with the explicitly acquired bounded carry s_j. Thus S=sum_(j≤h)s_j is an integer and sum_j ell_j=-m²S. Writing q_G=g_1^(m²)=U^m, (3) becomes

    product_j T_j=q_G^(-S) D^(A+Nh).               (4)

This WHOLE target aggregate is acquired in soft O(ell+m), including all integer carries, signed powers and output coefficients. It is a real aggregate acquisition, rather than the statement that individual targets could be described compactly.

## Why this aggregate has not supplied factor support

All C_j,T_j,U,D and q_G above are units. The desired source signal is a DIFFERENCE T_j-q_G^I at a covered own tag/index, or a source-preserving scalar gamma version. Taking the product of the targets themselves is not the product of those differences. The norm identities (2)--(4) do not test which target equals which seed at either hidden prime.

For a fixed known common seed t, an identity for product_j(T_j-t) would be a different, potentially sufficient aggregate. Expanding it requires the elementary symmetric functions of the varying T_j, not only product_j T_j. No construction acquiring that polynomial/its needed coefficient at soft m was found. Allowing distinct unknown true indices I_j requires still more source information. In particular the root coverage supplies one correct target, not an equation that EVERY j has an assigned covered index, so a product comparison with an assumed total index is unjustified.

Comparing the acquired weighted aggregate to its paired RHS returns an exact global identity, hence zero at both factors. Comparing it to another public power is an ordinary auxiliary-unit order test; no theorem forces different local outcomes, and q_G is not the prepared scalar gamma with its inherited order/decoder contract. No useful separator is inferred merely because unknown C_P,C_Q disappear from the globally valid aggregate.

The same fact delimits additive correlation of the sparse (log x,log(1-x)) histogram inputs. An aggregate PRODUCT can collapse by pairing while an aggregate of target-minus-seed factors or a weighted SUM still needs its own exact acquisition theorem. The histogram's O(ell) sparse description does not make the required nonlinear m-by-m contraction available. This is not a lower bound against another weighted norm or asymmetric correlation.

## Primary distribution literature inspected

Kubert–Lichtenbaum, *Jacobi-sum Hecke characters and Gauss-sum identities*, Compositio Mathematica 48(1) (1983), 55–87, Proposition 2.10 (Hasse–Davenport distribution), Proposition 2.13 (Stickelberger), and Section 6: https://www.numdam.org/item/CM_1983__48_1_55_0.pdf . The paper uses MODIFIED Gauss sums -sum, with trivial sum 1, whereas our g uses +sum and g_0=-1; equations (1)--(4) are proved directly above to keep signs and exceptions exact. Its distribution identities concern complete character families and explicit Gauss/Jacobi products, not finite native target-minus-seed windows. Its Stickelberger statement determines ideal factorization, not a selected modular value or source locator. No theorem from it was used as a free hidden-prime phase oracle or a shared H evaluator.

A fresh primary preprint Adrian–Diamond–Kramer–Tam, *Distinguishing Gauss sums*, arXiv:2609.28211v1, 23 September 2026, investigates when equality of Gauss sums over a supplied F_(p^f) implies Frobenius conjugacy, using p-adic digit criteria: https://arxiv.org/abs/2609.28211v1 . Its characteristic/field and character data are supplied; it does not compute unknown P-dependent Frobenius tags from unfactored N, and supplies no acquisition theorem for the original finite H product. Only its primary abstract/input scope was inspected; no unseen theorem is attributed to it.

Outcome: the native weighted C_j norm and even the product of all corrected native targets ARE cheaply acquired by exact antipodal distribution. They collapse to known unit powers. A source/recovery-preserving product of DIFFERENCES, additive symmetric coefficient, or guaranteed asymmetric comparison remains unacquired. No universal separator or factoring-rate improvement was obtained.

## Pair-level shared acquisition, carries and full bit charge

Here the canonical lift uses CENTERED b_j in [−(m−1)/2,(m−1)/2], as in the frozen antipodal shared-block proof. Since a_(m−j)=a_j and b_j+b_(m−j)=2a_j−m s_j, the integer s_j lies in {0,1,2}. Consequently ell_j+ell_(m−j)=−m²s_j exactly. Before multiplying the pairs, the same argument proves

    T_j T_(m−j)=U^(−m s_j) D^(a_j+N).

The two rho factors give D^(N−1), the terminal Gauss factors give D, and the middle factors give D^a_j. This includes the trivial component. It acquires all pair products in a SHARED representation: precompute only three length-m vectors V_s=U^(−ms). With delta_s=(−1)^s their trivial components, each pair is

    delta_s E0 + ell^(a_j+N)(V_s−delta_s E0).

Only O(m) additional scalar coefficients and public descriptors are needed. Expanding all pair vectors separately would have m² coefficient output and is not claimed. The whole-family product is one actual length-m vector. Its equivalent exact formula is U^(sum_j ell_j/m)D^(A+Nh).

For B=ceil(log2 N) and polynomial-size public parameters, quasi-linear cyclic polynomial arithmetic costs soft O(mB) bits per multiplication, and O(B)-bit exponentiation costs soft O(mB²). A constant number of such vector powers, plus O(m) scalar powers/modular inverses of O(B)-bit integers, is soft O(m) in the native convention retaining polylog N factors. The packed acquisition of U=−C_m costs soft O(ell+m), including its reviewed histogram preparation and logarithmic exponentiation. Computing weights, centered lifts and carries costs soft O(m). Thus total bit work is soft O(ell+m), with O(m log N) bits for the actual aggregate output and the shared pair representation. No per-row vector or unknown-prime arithmetic is free.

This bound presumes a supplied suitable auxiliary prime ell, character table/histogram metadata, and gcd(N,ell*m)=1. The packed primitive pays its O(ell) table/histogram work. No theorem here supplies a prime ell≡1 modm of size soft m, together with the needed public metadata, deterministically in soft m. For larger ell the bound stays soft(ell+m). Failed public inverses are handled by gcd before invoking the unit identities.

## Exact conjugation norm and its source boundary

Let bar=rho_(−1). The full identity bar(g_1)=D/g_1 implies

    bar(T_j)=D^ell_j U^(m s_j) T_(m−j),
    T_j bar(T_j)=D^(N+a_j+ell_j)=D^E_j.

For the first equation, conjugation swaps all character tags in T_j except the exponent ell_j of g_1; using −ell_j−ell_(m−j)=m²s_j gives precisely the displayed U power. Multiplying by the proved pair product gives the second equation. Likewise q_G bar(q_G)=D^(m²), so an equality T_j=q_G^I in the WHOLE local character algebra modulo a hidden prime implies D^E_j=D^(m² I) in that algebra. This whole-algebra equality is what the true own-tag Frobenius argument supplies. Equality at both conjugate character components is also sufficient for the corresponding componentwise norm conclusion; equality at only one character component is not sufficient, because conjugation need not preserve that component. On every primitive character component this is the scalar congruence ell^E_j=ell^(m²I); on the trivial component both sides are one. Thus a genuine Gauss collision projects to a scalar-base-ell collision. This is a necessary source-preserving implication, not equivalence: taking a norm can introduce collisions, and no prepared-order or factor-recovery contract for ell has been established. In particular it does not identify ell with the original prepared gamma or acquire the original H values.

Scope: the full unit product, its constant-term interpretation, and a shared pair family are acquired. The product of target-minus-seed differences, other elementary symmetric coefficients, and restriction-stable H-zero localization remain unacquired.
