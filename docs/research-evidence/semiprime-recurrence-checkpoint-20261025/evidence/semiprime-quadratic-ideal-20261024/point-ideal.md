# Paid point ideals for the native quadratic coordinates

24 October 2026. Scratch only. This constructs an exact factor-or-point-ideal representation in soft J, including coordinate collisions and original labels. A measured rectangular fiber configuration gives actual total-degree O(sqrt J) equations within that budget. No native theorem guarantees that configuration, and low-degree equations alone do not acquire the common-index seed query. An actual original-source degeneration is derived, then the requested cheap Cayley repair is executed without promoting characteristic-zero nontorsion to a finite-field position certificate.

## Source, inputs, and intended support

Read `/tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md`, SHA256 `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`, and its independent review SHA256 `147ed84ea489fb61e8e2b47e2c6d09a90cf247f743df017e48314b613f815a97`. It supplies the rank-two algebra

    B=R[tau]/(tau²-D), R=Z/N, bar(tau)=-tau,
    V_j=x_j+y_j*tau, z=(beta W)^H, H=k²,
    V_j=beta^E_j W^[ell_j+chi_D(j)(N+a_j)],
    E_j=N+a_j+ell_j, L=2H+2, J<=k.

All actual coordinates and metadata are acquired in soft k. Exactly one unknown local B is a field. Both beta and beta^H have the paid odd-order margins, and the actual z short-difference screen is retained. The native own tag gives V_j=z^I as a WHOLE local quadratic-algebra equality for an ORIGINAL I in [0,L).

The point-ideal query is whole coordinate equality at one local prime, not an arbitrary split-component zero of Norm(V_j-z^i). This still covers the native own hit. Once an original row/index norm is nonunit, the source's proper-gcd / nonsplit saturated-leaf beta consumer applies. Auxiliary interpolation pivots receive no saturation decoder.

Let n<=J be the number of globally distinct ACTUAL coordinate pairs after exact sorting in R². Global duplicates are removed with one original representative and its label retained. This does not deduplicate just by delta. The original target vectors are literally equal for a removed duplicate, so every local hit remains a hit of its retained representative.

## 1. Uniform factor-or-separated-fibers acquisition in soft J

Sort the points by exact equality of x coordinates modulo N. Let the distinct global x values be alpha_1,...,alpha_s; these need not initially be separated modulo either hidden prime. Acquire

    A(X)=product_(r=1)^s (X-alpha_r)

and its product tree. By monic multipoint evaluation acquire A'(alpha_r) for every r, in soft s. Compute their gcds with N.

* If every gcd is one, EVERY difference alpha_r-alpha_h is a unit: each derivative is the product of all those differences at its node.
* A proper gcd factors N immediately.
* If one derivative gcd is N, its product can be localized to a nonunit difference. Construct the factor tree of A/(X-alpha_r) from the already known other roots and descend at alpha_r, keeping a nonunit child or a proper factor. This costs soft s in addition to the first acquisition. A leaf cannot have gcd N, because the globally distinct alpha values have nonzero difference in R. Hence the descent MUST yield a proper factor before terminating.

This pays only ONE failing descent, since it factors and stops. It does not scan all s² pairs. All successful derivative evaluations and gcds total soft s. Product and remainder trees are monic; no separation is assumed before it is certified.

Within each global x fiber, sort and deduplicate actual y values. Apply exactly the same derivative-product certificate to that fiber's y polynomial. The sum of all fiber sizes is n, so all these tests cost soft n, including the one possible failing descent. On the continuing branch, x differences between different fibers and y differences within each fiber are certified units at BOTH primes.

Therefore the fiber partition, its cardinalities d_r, and distinct points remain exactly the SAME after either local reduction. This is a proved uniform statement, not a general-position assumption. All points are now separated by some certified coordinate difference; the evaluation algebra of the finite point set is R^n.

## 2. Actual monic component ideals, all acquired coefficients paid

Group the x fibers by their cardinality d. Write R_d={r:d_r=d}, s_d=|R_d|, and acquire

    A_d(X)=product_(r in R_d)(X-alpha_r),
    B_r(Y)=product_(points in fiber r)(Y-y_j).

All these monic polynomials and their product trees have total degree soft n+s. The sum s_d*d=n.

For each fixed d interpolate the coefficients of B_r(Y) over its s_d x nodes. The derivative inverses of A_d at those nodes are certified by Section 1. This produces an ACTUAL coefficient-vector polynomial

    G_d(X,Y), deg_X G_d<s_d, deg_Y G_d=d,
    G_d(alpha_r,Y)=B_r(Y) for r in R_d.

Because each B_r is monic of the same degree d, G_d is monic in Y: its leading coefficient is the constant one. Each of its d lower coefficient interpolations costs soft s_d. Thus ALL G_d coefficients, including every denominator and start, cost soft(sum_d s_d*d)=soft n. No J-by-J nullspace computation or field oracle is used.

The exact component ideal is

    I_d=(A_d(X),G_d(X,Y)).                         (1)

Indeed CRT first splits R[X]/A_d into the x fibers; in each fiber the quotient by G_d becomes R[Y]/B_r, which splits into its d certified separated y roots. Hence

    R[X,Y]/I_d = product_(r in R_d) product_(j in fiber r) R.

Distinct A_d are comaximal because ALL x nodes are unit-separated. Therefore the exact full point ideal is the acquired component intersection

    I=intersection_d I_d,
    R[X,Y]/I = R^n.                               (2)

Equations (1)--(2) deliver fully acquired component polynomials, not an unevaluated Groebner-basis promise. Their total stored coefficients are O(n+s), and their acquisition costs soft n. They encode precisely the original finite point set at both primes, with no extra curve points.

## 3. A real cheap low-degree branch, and its exact cost

The cleanest branch is an ACTUAL rectangular fiber profile: s distinct x values, each with d distinct y values, sd=n. Then there is only one component,

    I=(A(X),G(X,Y)),
    deg A=s, deg_X G<s, G monic of Y-degree d,
    total_degree G<=s+d-1.                        (3)

Both coefficient vectors are already acquired in soft n. If the measured s and d are O(sqrt n), (3) really supplies two low-total-degree equations containing ALL points and no extra common zeros. The criterion is tested from actual coordinates in soft n. It is not asserted for the native source without that test. The quotient still has rank sd=n: low equation degree is not free norm/terminal acquisition.

Variable fiber sizes can be retained exactly too. Let Dmax=max d_r. All-point generators are

    A(X), H_d(X,Y)=[A(X)/A_d(X)]*G_d(X,Y).         (4)

Together they generate I: modulo A, at a node of group d the complementary factor A/A_d is a unit and all other H_e vanish; the surviving equation is precisely B_r(Y). Their degrees satisfy total_degree H_d<=s+d-1. If both measured s and Dmax are O(sqrt n), these are also low-degree all-point generators. Their FACTORED inputs are paid: total G_d coefficients are O(n), and all monic quotients A/A_d cost soft(s*number_of_groups)<=soft(s*Dmax)=soft n under this balance condition.

No full expansion of the H_d is claimed for free. Such expansion can have a larger aggregate coefficient size, even though their factors and degree bounds are acquired. In an unbalanced configuration the monic component list (1) still costs soft n, but expanding every complementary quotient or every global generator must be charged separately. A low-degree equation through only one component is not an all-points equation until (4) or the actual union representation is retained.

These are genuine initialized conditional branches. They need no generic Vandermonde hypothesis or arbitrary composite-ring pivot. They do NOT cover generic x-distinct data by a sqrt n degree claim: when all fibers are singletons, (3) gives degree n in X, and another bivariate interpolation method would still have to acquire its own coefficients and valid pivots.

## 4. Uniform rational-univariate data, without a free separating projection

A second soft-n representation is useful for checking what “univariate interpolation” has actually acquired. Assign the retained original points distinct PUBLIC integer labels u=0,...,n-1. Their differences are nonzero integers smaller than P,Q, hence certified units. Acquire

    Q(U)=product_(u<n)(U-u),
    Xlab(U),Ylab(U) of degree<n,
    Xlab(u)=x_u, Ylab(u)=y_u.

Monic product trees and two interpolations cost soft n, with every coefficient explicit. The denominator may be taken to be one. The point set is exactly the image of this finite etale label algebra, and the labels are already original row metadata. This construction neither factors an unknown polynomial nor finds an unacquired separating linear form in the coordinates.

It has degree n, not sqrt n. The map from a new coordinate pair back to a label requires common-root/membership work; its inverse is not supplied by the small labels. Eliminating U or finding a short relation among monomials Xlab(U)^a Ylab(U)^b modulo Q is an additional computation. A dimension count proving existence of a degree about sqrt n relation does not compute its coefficients or exclude extra zeros. No such nullspace/contraction is priced as an automatic consequence of the acquired label representation.

## 5. Exact one-index consumer, zero and saturation safe

The fiber representation provides a complete actual membership algorithm for ONE supplied original seed index i. Compute z^i=a+b*tau by binary powering.

1. Evaluate A(a) and its gcd with N. A unit proves no whole-coordinate point hit at either prime. A proper gcd factors. If saturated, descend A's product tree at a. A proper child gcd factors; otherwise a saturated leaf gives a=alpha_r globally, with the actual fiber label retained. If the two hidden sides matched different fibers, descent would instead produce a proper factor.
2. Evaluate the acquired B_r(b). A unit gives no point in that globally selected fiber at either side. Proper gcd factors. Saturation descends its factor tree to a retained original y node, or yields a proper factor along the way.
3. A saturated final y leaf gives z^i=V_j as a WHOLE coordinate equality modulo N at an ORIGINAL row/index. Thus Norm(V_j-z^i) is saturated, and the original beta leaf consumer applies. No unbounded or altered index was introduced.

Every polynomial evaluated above was acquired. Along each localization path the sum of polynomial degrees is O(n); the entire one-index algorithm costs soft n+polylog N, including zero and saturated branches. No nonunit endpoint or derivative is divided out. This also applies to acquired row subsets after rebuilding their component data at the actual subset cost.

The predicate is SAME-index and SAME-row. Products of A(seed_x(i)) and G(seed_x(i),seed_y(i)) separately over the interval can have zeros at different indices or components; their gcd does not certify a common native leaf. Likewise multiplying the two equations tests their union, not their intersection. These shortcuts do not execute the desired point-ideal query.

For the rectangular balanced branch, a seed-side spectral conversion would pay O((s+d)²)=O(n) initial coefficients/starts for the two low-degree equations. That is an acquired startup, not their common-index long zero test. For multiple components the corresponding conversion must pay sum_d(s_d+d)² (or the actual chosen all-point generator degrees), not merely sum_d s_d*d. No free simultaneous query is inferred from the component-ideal coefficient budget.

## 6. An actual native degeneration of the ORIGINAL Cayley choice

The original source allows D=-3 and used W=(1+tau)/(1-tau). In this exact arithmetic branch,

    W=(tau-1)/2, W²+W+1=0, W³=1.

There is no numerical example or generic point-set counterfamily here. Since |D|=3 divides k, every unit tag satisfies chi_-3(j)=j modulo 3. Also a_j j²=N modulo 3 and j²=1 modulo 3. Consequently

    Texp_j=ell_j+chi(j)(N+a_j)
       =a_j*(j-chi(j))=0 modulo 3,

where ell_j=k b_j-2a_j j was used. As 3|H, all ACTUAL targets and seed collapse to scalars:

    V_j=beta^E_j, z=beta^H, y_j=0.                (5)

After actual point deduplication, distinct x differences are units by |delta_j-delta_h|<=4H and the local beta order margin. With n such distinct points, their exact ideal is

    (Y, product_(j<n)(X-beta^E_j)).               (6)

Any polynomial of total degree<n vanishing at all these points restricts at Y=0 to a univariate polynomial of degree<n with n unit-separated roots, hence is the zero polynomial. Thus every such equation is divisible by Y. No collection of only those low-degree equations defines the finite point set: it leaves the entire line. Some exact point-ideal equation must retain degree at least n. This is a scoped statement about exact equations for the permitted original configuration, not a lower bound on scalar query algorithms or on implicit circuits.

The degree-one equation Y=0 is especially unhelpful as a detector: the entire seed trajectory in (5) also lies on that line. Retaining the second equation in (6) returns precisely the old original scalar degree-n query. Thus “a cheap low-degree vanishing curve exists” is not sufficient coverage-preserving acquisition of the exact point set.

## 7. Execute a fixed-torsion repair, without assuming general position

Root proposed the following concrete repair of that characteristic-zero torsion defect. Choose the PUBLIC Cayley parameter

    eta=2 if D=-3, eta=1 otherwise,
    Weta=(eta+tau)/(eta-tau)
         =(eta²+D+2eta*tau)/(eta²-D).              (7)

The denominator eta²-D<=|D|+4<=k/2+4 is a certified unit on the hard branch; one gcd/extended gcd acquires its inverse. Norm(Weta)=1. The same Frobenius character relation and local order divisibility p-chi_D(p) hold, so replacing W by Weta in ALL actual rows preserves the native own cover and the exact nonsplit saturated-leaf beta consumer. All rows are recomputed in soft k.

RERUN the actual factor-or-unit seed screen for zeta=(beta Weta)^H. The old split-side unit certificate does not transfer automatically. Its field-side nonvanishing proof uses only Norm(zeta)=beta^(2H), so the same paid soft-k screen gives a proper factor or all needed short units. No new beta order oracle is required.

This repair removes characteristic-zero torsion uniformly, without needing a classification of quadratic roots of unity. Put c=|D|. Its rational trace is

    Tr(Weta)=2(eta²-c)/(eta²+c)=-2+4eta²/(eta²+c).

For c>=4, eta=1 makes this strictly between -2 and -1, hence nonintegral. For c=3, eta=2 gives 2/7, again nonintegral. A root of unity and its inverse are algebraic integers, so their rational sum must be an integer. The nonintegral trace therefore excludes characteristic-zero torsion for EVERY negative fundamental D. The old fixed D=-3 cubic-root collapse does not apply to the amended source. At D=-4 the chosen trace is -6/5; this parameter is deliberately kept at one, since eta=2 there would instead create a fourth root of unity.

This is a paid positive constructor repair, not a finite-field order certificate. Reductions modulo the hidden primes can have small orders or special point configurations. No theorem here bounds their actual fiber profile by s,Dmax=O(sqrt n), guarantees a generic bivariate evaluation matrix, or proves the existence of a cheaply acquired exact sqrt n-degree ideal for the REPAIRED family. Those remain arithmetic acquisition questions, even though all coordinates and pivot certificates in Sections 1--5 are actually available. The point-ideal algorithms work unchanged for the repaired coordinates; their measured degree profile must still be charged.

## Ledger and query outcome

| Acquired operation | Cost | Actual scope |
|---|---:|---|
| All original or repaired quadratic coordinates, native labels | soft k | existing safe constructor; changed seed actually rescreened |
| Exact point sorting/dedup and coordinate derivative certificates | soft J | proper factor or separated fibers at both primes |
| ALL monic component A_d,G_d coefficient vectors | soft J | exact full finite point ideal as component intersection |
| Balanced rectangular complete intersection | soft n | actual total degree O(sqrt n), conditional on measured profile |
| Balanced variable-fiber all-point generators | soft n factored inputs | expansion and later joint query not free |
| Public-label rational-univariate representation | soft n | degree n; no free inverse projection or elimination |
| One original-index membership and row recovery | soft n | factor, exact NoHit, or original saturated beta witness |
| Literal scan of L seed indices | soft(JL) | complete but overbudget joint test |
| Retained quadratic norm query and original recovery | soft(J+sqrt(JL)) | unchanged guaranteed worst case soft k^(3/2) |

The constructive result is an actually acquired, nongenericity-dependent factor-or-point-ideal representation, plus a real balanced-profile low-degree branch and a paid fixed-torsion repair. The original D=-3 collapse pinpoints why unqualified all-input sqrt J exact-equation claims were invalid for the unamended source. Its repair does not supply the missing profile theorem or common-index terminal contraction. The whole covered query and one-sixth/full bit-and-Lean goal remain open; no generic algorithmic impossibility is claimed.
