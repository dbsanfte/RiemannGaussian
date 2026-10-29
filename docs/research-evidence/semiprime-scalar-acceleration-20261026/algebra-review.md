# Independent algebra and initialization review

26 October 2026. Read `sectioned-newton.md` and `integrable-closure.md` in full. Paper-only review; no tests, new literature or repository changes. **PASS for both reports; no substantive algebraic error found.** Their failed contractions and costs are appropriately scoped.

## Sectioned Newton report

The additive regularizer D_delta=D+delta is explicitly different from physical leaf regulation. Its clock-value partial fractions nevertheless have globally at most simple delta poles because their denominator is D(a_i)+delta, with unit coefficient of delta. At the unique good hit the residue is exactly the reciprocal clock Vandermonde product. Consequently R_(n−1)=(theta−a_n)R_n and the PLUS locator in (2) are correct, including the last-node hit.

The geometric divided-difference denominators give the factor q^(−m(m−1)/2) in (3). Hence converting to C_m introduces the essential q^(n−1) multiplier in locator (4). The q-Euler relation B(qz)=B(z)/(1+z), and B*D_delta(S)*B^-1=D_delta((1+z)S), hold modulo z^h using only the supplied finite q-factorial units. No infinite-order q assumption is used.

Both executed Graeffe products have correct signs. The first highest-shift linear coefficient is (1−q^(2J))/(1−q). The second is −(1−q^J)^2/(1−q). These are certified global units, and lower shift powers cannot cancel that highest-shift coefficient. The displayed J=1 commutator is 2(1−q)z*S². The Vandermonde test on q^0,q²,...,q^(4J) correctly shows a genuine cross-parity action when h>4J+1; its differences have screened gaps<=4J. It does not claim a general sectioning lower bound.

The even/odd generator matrix [[1,q*u],[1,q]]*S_(q²) is correct in the convention C(z)=C_even(z²)+z*C_odd(z²). The nonzero residues of F_m for every m>=I justify the stated both-parity singular support, with the explicit final-node exception. Neither branch may be discarded merely from uniqueness.

Short D(q^i) values, their actual nonunit localization, unit-prefix inversion, Newton convolution and transformed short right sides are charged. No unclassified D(q^I)+delta inverse is treated as an ordinary unit-start series. Exact fallback residues assembled from row flags require separation to avoid repeated clock-point overcounting, which the report explicitly distinguishes from the weaker one-good-field output. The claimed retained bound is consistent.

## Integrable closure report

The cleared Christoffel identity (1) follows from the companion update. Monic normalization (2) is legal only when the actual leading coefficients AND its p_t(a_t) denominator pass unit gates; the report conditions the normalization and does not use it through arbitrary prefix zeros. The raw frontier (3) has the correct sign, node shift and denominator a_(t+k+1)−a_t. All such gaps are units. Geometric extrapolation from J values is independent of the common node scale and is acquired once. Its rolling D evaluations and J dot products cost soft J per step, giving the stated Jh bound without a hidden h-by-J matrix oracle.

The Hankel moments use p_n=product(a_i−X), so their evolution is a_n*mu_k−mu_(k+1), as stated. Both signs in (5) are correct: H_(J−1)^(0)(n)=(-1)^(J(J−1)/2+n)E_n and H_J^(0)(n)=(-1)^(J(J−1)/2)product D(a_i). The separated-locus proof clears to polynomial identities, so repeated nonhit roots and composite B do not require numerical D′ inverses. The Desnanot–Jacobi relation (6) has the correct r+2 shifts and minus square.

At n=-1, all entries of a leading m-by-m moment matrix vanish when 2m−2<J−1. These are genuine prescribed zero initial pivots; a field no-zero-pivot qd/Toda ratio theorem cannot be used. Fraction-free condensation stays valid but does not solve an unknown minor from 0=0. A moving O(J) moment frontier can be extended using the supplied monic D recurrence in the moment index, so the direct Jh cost does not hide growing state. Final moments from p_n mod D are cheaply extracted only AFTER that long remainder is supplied.

The native D(qX) screen is fully paid: coefficient scaling, MPE at J known roots, then ONE localized row-factor scan, all soft K. A nonunit aggregate is not assumed to be a single edge. Norm/coordinate classification yields a proper factor or a genuine global edge before its mixed-label decoder. The exponent pair in (8) cannot vanish simultaneously: Delta(a+bN)=0 forces equal a,b, while centered phase difference cannot equal H. Their actual magnitudes may be O(KN), still O(log N) bits and inside the existing short-label contract. Any terminating extraction is once-only. Thus continuation really certifies a unit resultant, even with repeated row roots, and rules out THIS adjacent-q cancellation rather than all integrable reductions.

## Final scope

Both reports initialize their finite short data and keep singular final denominators under explicit gates. They obtain exact candidate structures, not a soft-K acquisition algorithm. No lowest-order recurrence claim, genericity hypothesis, root-of-unity specialization or blanket complexity lower bound is needed for their conclusions. No correction beyond the normalization caveats already present is required.

## Pole-kernel handoff review

Read `pole-kernel-handoff.md`. **PASS; no substantive correction required.** The finite Euler series has constant term one and satisfies B(qz)=B(z)/(1+z), hence B*S*B^-1=(1+z)S exactly modulo z^h. Its use is a proof/conjugation, not an assertion that the h-entry B array has been acquired cheaply. The diagonal operator D(S) has entries D(q^i); exactly one is zero at the promised good field, so its kernel and the conjugate kernel are ONE-dimensional there. No statement of rank one for the full operator, or global one-dimensionality at other components, is made.

Direct extraction of the singular A-series coefficient gives c(z)=(-1)^I z^I B(z)/(q;q)_I, with the displayed normalization and no D′ factor for the D+delta regulator. Its coefficients from I onward are units at the good field because their q-factorial factors are short units. Therefore the final denominator is nonzero, including I=h−1, and the formula q^(h−1)+q^(h−2)c_(h−2)/c_(h−1) has the correct sign and power. Any vector with NONZERO good component in that kernel gives the same projective root; arbitrary global nonzero output need not have that property, and the target explicitly requires it.

The final norm gate and the separate H_u(theta)/D′(theta) gate are legitimate good-nonzero-to-factor-or-unit branches. The simple common row root follows from the unique leaf even if D repeats elsewhere. Wrong bins remain bounded attempts. The new pair is correctly described as a sufficient replacement for the factoring/mark consumer, not a numerical identity with the original packed C or its old multiplicity. The stated compact O(J) generator input and unpaid acquisition are honest; diagonal conjugacy does not provide the unknown singular index or a nonzero initial homogeneous prefix.

## Stable coupled-section review

Read `coupled-section.md` including the final uniform-K phase/cost clarification. **PASS.** Its section generator is (I+Z_b)Q_b*S_(q^b), and the four-component matrix has the correct q powers and wrap q^3*u. The original z^h truncation must be retained as the corresponding componentwise finite cutoffs; the displayed formal generator does not assert equal component lengths when b does not divide h.

Semilinearity is essential and correctly retained: YX=qXY even at the wrap because S_(q^b)(u)=q^b*u. Therefore E=XY satisfies E^b=q^(b(b−1)/2)*u*Y^b. The ordered q-binomial inversion in (3) has L^(b−k)Y^k in the correct order and coefficient (-1)^k q^(k(k−1)/2)[b choose k]_q. It follows by q-binomial inversion after expanding (Y+E)^m with YE=qEY; no false commutation of L,Y is used. The good-mode formula Y^k c=theta^k c/product_(t<k)(1+q^t z) is exactly the q-Euler shift and has formal unit-constant denominators. It is explicitly good-field/known-mode conditional, not a global acquired theta assertion.

The section carry u^(s+1_(e<r)) and [e−r]_b in (5) are correct. The coefficient ratio in (6) is q^(b*(bm+e)+b(b−1)/2) divided by its b successive q-factorial factors, within the stated finite range. The Euler-gauged state has a single active phase only in the promised good field; its symbolic description does not acquire the full gauge action or phase index. These scope distinctions are explicit.

For an ACTUALLY supplied I mod b, T'_j=T_j*q^(-r) and base q^b retain exactly the original indices r+bt, with literal clipped lengths and empty phases handled. Choosing b>=h/J gives length<=J and a soft-J SHORTENED QUERY by explicit monic clock polynomial/MPE. Identifying this b as O(sqrt K) requires J=Omega(K), not merely its upper bound, and the author now says so. The uniform choice b_K>=max(1,h/K) gives length<=K and b_K=O(sqrt K), requiring no lower bound on J. Its complete query plus the inherited once-only factor/tag recovery is soft K; soft-J acquisition is not incorrectly promoted to soft-J recovery when J is small.

The optional conversion guards b*gap<h and b*ceil(h/b)<=h+b<3h<16H are valid on native K>=54. The explicit monic product/MPE version needs no new difference inverse or projected-order oracle at all. Wrong phases/bins may fail and must continue; a phase must cover the actual I, not an artificial stretched/relabelled origin. No phase supplier is claimed.

Finally, solving (theta−q^m)v_m=q^(m−1)v_(m−1) backward from v_n=1 gives the exponent m(m−1)/2−n(n−1)/2 and product range m+1 through n in (8). The first boundary is exactly -(q^(-n(n−1)/2))*W_h(theta), with the stated minus sign. Thus D(theta)=0 alone does not make the candidate a finite kernel vector; the unacquired clock-intersection boundary remains. Products with O(J) factors are cheaply acquired as individual short products, not as a free full h-array. No substantive correction remains.
