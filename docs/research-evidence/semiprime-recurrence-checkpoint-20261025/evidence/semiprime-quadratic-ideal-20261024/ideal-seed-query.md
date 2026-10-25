# Seed-side simultaneous recurrence test for a low-degree point ideal

24 October 2026. Scratch only. This report executes one route: convert the TWO low-degree coordinate equations to a shared rational generating function, acquire both complete recurrences/starts, test the proposed simultaneous-Pade contraction, and complete the query with explicit extraneous-point routing. Startup is soft J, but the executed completion costs soft(J+L), worse than the existing soft(J+sqrt(JL)) query. No sub-3/2 exponent is obtained. This is the cost and closure of this particular attempt, not a generic lower bound.

## Actual source and conditional point-equation input

Use `/tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md`, SHA256 215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363, with its original bounded norm-leaf consumer. The acquired algebra is B=R[tau]/(tau²-D), R=Z/N, with conjugation bar. Exactly one unknown local side is a field. All J<=k actual targets V_j=x_j+y_j tau, the seed z=x_z+y_z tau, and original source labels are acquired in soft k. H=k², L=2H+2, t=Norm(z)=beta^(2H) has both local odd orders >16H, and every z^r-1 for 1<=r<=16H is a certified unit. No target-separation assumption is added.

Let G(X,Y),K(X,Y) in R[X,Y] have total degree at most d=O(sqrt J), with ALL their O(d²) coefficients actually supplied. They vanish at every supplied target coordinate pair. Write T_ideal for the ACTUAL cost to construct/certify these two equations; it is added to every ledger below. An equation oracle is not free. The seed-side route does not assume that their common zero set equals the target list, or that their ideal is radical, zero-dimensional or etale. If another construction supplies those stronger properties they may reduce candidate counts, but they are not needed for the completed, more expensive algorithm here.

For each i, acquire the seed coordinates

    z^i=x_i+y_i tau,
    x_i=(z^i+bar(z)^i)/2,
    y_i=(z^i-bar(z)^i)/(2tau).

The intended coarse candidate test is G(x_i,y_i)=K(x_i,y_i)=0 at a local prime. Such a joint zero alone is not an original norm leaf; extraneous intersections must be removed before saturated recovery.

## 1. Execute shared two-base startup in soft d²

Introduce formal U,V and substitute

    Ghat(U,V)=G((U+V)/2,(U-V)/(2tau)),
    Khat(U,V)=K((U+V)/2,(U-V)/(2tau)).            (1)

All inverses are explicit units: 2 and tau, with tau^-1=tau/D. For each homogeneous degree e<=d, the invertible linear change of binary-form variables can be executed with polynomial Taylor shifts/binomial transforms in soft(e+1) operations. For one shear, the coefficients transform as b_j=sum_(r>=j) a_r binom(r,j)c^(r-j), a single factorial-scaled convolution; the inverse shear uses the reversed coefficient vector. The constant invertible matrix in (1) decomposes into such shears and unit scalings. Summing over e costs soft d². If factorial-scaled transforms are used, their integers are at most d and are units because both primes exceed 16k²; they can instead be guarded directly. Thus every actual transformed coefficient is acquired at the claimed startup cost.

Write Ghat=sum_(a+b<=d) g_ab U^a V^b, and similarly k_ab. Acquire all

    lambda_ab=z^a bar(z)^b, a,b>=0, a+b<=d,
    M=(d+1)(d+2)/2=O(J).

Two length-d power tables and the M pairwise products cost soft M. There is no field oracle or inverse of a spectral difference. Build the actual constant-one common denominator and two numerators

    Q(S)=product_(a+b<=d)(1-lambda_ab S),
    NG(S)=sum_ab g_ab Q(S)/(1-lambda_ab S),
    NK(S)=sum_ab k_ab Q(S)/(1-lambda_ab S).      (2)

The displayed quotients are EXACT polynomial products, not specializations followed by division. A weighted product tree computes them: combine denominator pairs by multiplication and combine numerators as N_left Q_right+N_right Q_left. This costs soft M for each numerator and denominator. It remains correct if many lambda_ab coincide or some coefficients vanish. No distinctness or genericity assumption is used.

Conjugation swaps a,b and conjugates their coefficients in (1). Therefore Q,NG,NK are fixed by bar and have scalar coefficients in R. They may be computed in B with constant overhead and their scalar coordinate extracted; no hidden local field is chosen. Exactly,

    NG(S)/Q(S)=sum_(i>=0) G(x_i,y_i) S^i,
    NK(S)/Q(S)=sum_(i>=0) K(x_i,y_i) S^i.       (3)

Because Q(0)=1, power-series inversion and multiplication acquire ALL first M values of BOTH sequences in soft M. The reversed Q is an actual common monic recurrence of degree M, with every coefficient and required start paid. This is a usable initialized compression from many original rows to two scalar sequences. It does not have order O(d) merely because the coordinate degree is d.

## 2. Execute the simultaneous-Pade step and identify its retained meaning

Equations (2)--(3) already supply an exact simultaneous rational representation. Guarded fast polynomial gcd/subresultants of Q,NG,NK can remove common polynomial factors in soft M, returning a proper factor of N on a proper nonunit pivot. Unit pivots are inverted and globally zero heads dropped. A successful cancellation only shortens the spectral recurrence; the resulting numerators/denominator and their constant-one series representation remain actual acquired data.

This operation does NOT decide whether the TWO coefficient sequences vanish at the SAME index. Its variable S is the generating-function variable, not i or z^i. The distinction is explicit. In a proof-side distinct-spectrum field, evaluating NG at a reciprocal spectral node gives

    NG(lambda_r^-1)
       =g_r product_(h!=r)(1-lambda_h/lambda_r), (4)

whereas its i-th sequence value is sum_r g_r lambda_r^i. A numerator gcd at spectral poles tests coefficient/spectral cancellations as in (4), not that weighted sum, and certainly not simultaneous vanishing of the two sums. No actual algorithm in this report divides by the differences in (4); it is only the identity explaining what the tested gcd sees. Repeated spectral bases do not rescue a same-index inference: (3) remains the exact rational representation before any cancellation.

After the paid Pade/subresultant operation, the remaining state is two coefficient-extraction problems of order at most M=O(J), over i=0,...,L-1. No closed transfer for their joint zero mask or an interval-product accumulator has been acquired. In particular, importing the short four-start recurrence of each ORIGINAL row does not make these two equation sequences order four. Their actually acquired common support is the triangular set in (2).

## 3. Norm coordinate and trace/Dickson reduction do not make one argument fixed

The actual norm coordinate is

    x_i²-D y_i²=t^i.

It varies with i and has local order greater than the entire query range. In U,V coordinates each monomial can be written

    U^a V^b=(t^i)^min(a,b)
       * (z^i)^(a-b)          if a>=b,

or the corresponding power of bar(z)^i otherwise. Symmetric powers U^r+V^r are Dickson polynomials in U+V and UV, but here those arguments are Tr(z^i) and t^i, BOTH varying. A norm-one substitution UV=1 would change the actual seed. Fixing the conic x²-Dy² to one scalar therefore discards the moving t^i coordinate.

One can instead eliminate X,Y from G,K and T-(X²-DY²). If a separately certified finite-free intersection algebra has rank D0<=d², multiplication by the norm coordinate has a characteristic polynomial of degree D0. Its construction requires the actual quotient/multiplication data; two short displayed equations do not supply a dense D0-by-D0 matrix or its characteristic polynomial for free. Even granting an ideal-side algorithm that acquires this projected polynomial cheaply, its degree can be O(d²)=O(J), and testing it at T=t^i is again a degree-J, horizon-L geometric query. Extra intersection points are included, so its saturated zeros still need actual-target routing.

For the supplied ACTUAL target list there is a simpler initialized norm projection: acquire product_j(T-Norm(V_j)) directly in soft J. In this source it is precisely the original-beta family beta^(2E_j) at seed t=beta^(2H), with its existing original decoder. Its completed cost is already soft(J+sqrt(JL)). This is the preserved baseline, not a new use of point-ideal equations, and it has not reduced J to d. No conic-elimination result is priced as a faster acquisition here.

## 4. Fully execute the joint-sequence query, including extra intersections

The following controller is complete even if G,K share components or have extra zeros.

1. Compute Q^-1 modulo S^L (its constant coefficient is one), then both series (3) modulo S^L. This costs soft(M+L), with all L actual pairs of scalar values acquired.
2. For each i<L, compute gcd(N,G(x_i,y_i),K(x_i,y_i)). A proper gcd factors immediately. A unit discards that time. If it is N, retain i as a coarse joint candidate. These are ordinary scalar gcds, not a decoder for a point-ideal zero. No hidden factor sign is inspected.
3. Acquire the original monic F_B(X)=product_j(X-V_j) in soft J. Initialize every retained actual point z^i (at most L), either by a full geometric table or binary powering with suppressed logarithms. Batch monic multipoint evaluation of F_B at them costs soft(J+number of candidates). This uses no target-difference inverse. Norm each value and compute its gcd with N.
4. Unit original products discard extraneous intersection candidates. A proper gcd factors. A saturated ORIGINAL row product is split to one actual original row j, using the retained index i, and passed to the source's same-leaf norm consumer. At the nonsplit side this gives the original paired beta condition; a proper beta gcd factors and a saturated bounded scalar leaf has the original checked sum decoder.

Coverage is proved before pricing output. At the guaranteed own original index I, the entire element V_j=z^I modulo the own prime, so BOTH supplied equations vanish there. If step 2 gives a proper gcd there, a factor is already found. Otherwise I is a saturated candidate and is not lost. Step 3 at that candidate has a nonunit ORIGINAL norm product. Hence the process must factor or reach an original bounded witness; a purely extraneous saturated joint zero is never used as a factor witness.

A zero-dimensional intersection certificate could bound the number of saturated candidates by its geometric point count on the nonsplit side, since the guarded orbit is injective for i<L. That certificate is not inferred from two degree-d equations; common components can exist. The controller above requires no such bound and charges up to L points. Even if another construction certifies O(J) candidates, step 1 still acquires L coefficients in this attempt, so it does not lower the terminal cost.

All cancellation and recurrence operations are zero-safe. Products at zero are not inverted; the only power-series inverse has constant coefficient one. The original saturation consumer is invoked only after actual F_B evaluation and row localization, not at an arbitrary Pade residual, resultant, projected extra point or common equation zero.

## 5. Specialization to actually acquired fiber-profile ideals

The companion point-ideal attempt supplies a sharper conditional input than arbitrary interpolation: group actual distinct x coordinates by their fiber cardinality d0. For a component with s fibers, it acquires A(X)=product_r(X-x_r) and a monic-in-Y G0(X,Y), with deg_X G0<s and deg_Y G0=d0, by coefficientwise interpolation of the actual fiber polynomials. The component coefficient budget is s*d0; its ideal is exact, provided that companion algorithm's coordinate separation/factor guards succeed.

For a REGULAR balanced profile, s*d0=J and s,d0=O(sqrt J), these are one genuine complete intersection with total degree O(s+d0)=O(sqrt J). The startup (1)--(3) therefore applies in soft J, with no extra intersection points to remove. Exactness strengthens the candidate interpretation but supplies no faster common-index coefficient-zero operation; the completed expansion still costs soft(J+L).

For general profiles, sum_components s*d0=J does NOT pay sum_components(s+d0)^2. The actual transformed spectral startup in this method must charge the latter quantity, and processing every component's two sequences through L additionally charges one length-L expansion per component. No free single degree-sqrt(J) equation pair or globally soft-J startup is inferred from the aggregate coefficient budget. The companion's profile acquisition and separation costs are also paid. In particular, the native source has no proved uniform balanced-profile theorem; the old W can have torsion degenerations such as D=-3. A repaired seed may change that geometry but still requires an actual profile proof, not a generic-point hypothesis. This report's small-degree branch is explicitly conditional on the acquired equations and does not hide that source issue.

## Ledger and exact result

| Actual operation | Bit work | Delivered state |
|---|---:|---|
| Construct/certify point equations | T_ideal | full supplied coefficient vectors; not free |
| Linear coordinate change and all two-base nodes | soft d² | actual triangular spectral input |
| Weighted product trees Q,NG,NK | soft d² | exact shared rational functions, collisions permitted |
| Both common recurrences and all first M starts | soft d² | initialized order-M coefficient sequences |
| Guarded simultaneous Pade/gcd | soft d² | recurrence cancellation only, no index-zero detector |
| Expand to L and scan joint gcds | soft(d²+L) | all actual same-index coarse candidates |
| Batched actual-target cleanup and one safe leaf | soft(J+L) | no extraneous saturated witness |
| Total tested ideal-seed route | T_ideal+soft(J+L) | complete, at worst soft k² |
| Existing original norm projection/blocking | soft(J+sqrt(JL)) | old worst-case soft k^(3/2) |

The real startup saving is that BOTH low-degree equations and all their starts are initialized in soft J by exact rational-function product trees, without a generic bivariate MPE oracle. The tested simultaneous-Pade step does not contract their common coefficient-zero search: its gcd variable is spectral. Norm/trace reduction retains the moving t^i argument, and the actual projection has degree O(J). This attempt therefore gives no saving below the existing 3/2 query exponent and no sixth-rate claim. The missing operation is an actual restricted common-index zero search for the two initialized triangular-spectrum sequences, together with the above original-target cleanup; it is not the already paid construction of their recurrences.
