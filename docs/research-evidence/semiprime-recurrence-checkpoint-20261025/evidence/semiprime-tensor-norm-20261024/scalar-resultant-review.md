# Independent scalar resultant / early-pivot review

24 October 2026. Reviewed exact bytes of /tmp/semiprime-tensor-norm-20261024/scalar-resultant-algorithms.md.

SHA-256: `680d3a937f7b30f504c01f007f151442d850ffac44c100ec31ba12ea8ff5d34b`.

Verdict: **PASS. No required fixes.** No source/repository mutation, examples or backend work. This checks the actual two-step algebra, guards, acquisition/recovery ledger and limited structured/sparse scope.

## Two pivots and the unit-leading quartic

Let g_k=B_k Y^-k and r_k=A_k-g_k. Dividing monic G_Y by R=A_n-G_Y on a unit-r_1 branch uses quotient X/r_1+(g_1*r_1-r_2)/r_1². Its next leading coefficient is therefore

    (g_2*r_1²-r_3*r_1-g_1*r_2*r_1+r_2²)/r_1².

Expanding the numerator and multiplying by Y^4 gives exactly the displayed five coefficients of P2. In particular the Y^4 coefficient is A2²-A1*A3, the Y^3 coefficient is B1*(A3-A1*A2), and the constant term is B2²-B1*B3. The mixed Y² and Y coefficients also agree term by term; no sign or missing cross term was found.

For A_n's geometric roots, A_k=(-1)^k e_k, so A2²-A1*A3=e_2²-e_1 e_3=s_(2,2). Substituting the q-binomial expressions or the rectangular hook product yields precisely the report's q² product. Every exponent in its numerator/denominator lies between 1 and n+1 (and n>=3), hence within the certified short range. Thus the leading coefficient is a UNIT independently of F, and P2 has literal degree four over R before outer reduction. No generic nonvanishing assumption on B1,B2,B3 is used.

This verifies the narrow closure test: the proposed class containing only linear Y pivot denominators/geometric shifts does not survive the next displayed pivot. It does not exclude another compact representation, and the report explicitly says so. The first two numerators still have constant-degree descriptions; a quartic alone is not a runtime lower bound.

## Norm guards and the actual adaptive factor branch

Y is a unit in S. Since r_1=P1/Y,

    Norm(r_1)=H1/Norm(Y), H1=product_b P1(Q^b).

On the unit-H1 branch, the second pivot has norm

    H2/[Norm(Y)^4*Norm(r_1)^2],
    H2=product_b P2(Q^b).

All denominator factors are known units on that branch. Hence unit H1/H2 really licenses the respective S pivot, while a proper scalar gcd of either norm is an independently valid factor of N. Multiplicativity and the adjugate norm identity justify this even when S is split and has zero divisors.

Each H_i is acquired by the ordinary geometric product constructor with an EXPLICIT polynomial of degree one/four. Blocking costs soft sqrt t, with all coefficients, powers, starts and short tails charged, and no P_i value is inverted. The top input coefficients and q-metadata are acquired or read at soft n cost; the two extra screens fit soft(n+sqrt t). Full rank-t inverses are NOT counted as constant-cost merely because a norm guard passed.

A saturated norm is correctly treated as an auxiliary degree/pivot degeneration. Its zeros may occur at different outer components at the two primes, and even a globally vanishing auxiliary component is not an original beta collision. The branch therefore falls back to the original complete query, rather than applying an inherited decoder to a pivot. The resulting whole procedure keeps the old soft m^(3/2) bound plus soft-m extra work, without claiming coverage by the early-pivot screens.

The balanced split's short last interval is an ordinary paid tail. Row restrictions must acquire their own actual F coefficients, and short dimensions use the paid direct case. No unrestricted inverse or missing saturation branch was identified.

## Generator and coefficient-algebra costs

A Sylvester matrix has two Toeplitz column blocks, hence constant mosaic displacement rank. Its initial generators have short scalar/monomial descriptions f_kY^k, but expanded entries live in S of rank t. This distinction is maintained consistently. An O(n)-operation structured routine over S gives at best soft(nt) base-ring work once its compatible generator entries are acquired; S remains a product algebra even if the underlying residue field were known. Rank profiles can differ between components, so field/generic-profile assumptions cannot be transported silently.

A geometric Vandermonde change sends the diagonal monomial coefficient array to entries F(q^aY), or truncated/scaled forms. Describing those entries by one F is cheap; maintaining that secondary description through arbitrary Schur complements is an additional algorithmic requirement. The report does not assume the structured solver performs that operation at scalar unit cost.

## Sparse and coefficient-linear statements are correctly limited

For horizontal, vertical and diagonal segments, the pairwise normalized mixed volumes are st,sJ,tJ by direct parallelogram determinants. The scalar E is monic degree st in f_0 with the other coefficients fixed. Thus a universal determinant with entries affine-linear in ORIGINAL coefficients must have matrix size at least st: its f_0 degree is at most its size. This conclusion applies to that coefficient-linear class only. It neither bounds general arithmetic circuits nor excludes nonlinear/rational compressed entries; the report makes these distinctions explicit.

The native rescaling also checks. B_k=beta^(kN)B_k0 and every P2 term has weighted total degree four after giving Y weight one and B_k weight k. Hence P2(Y)=beta^(4N)*P20(Y/beta^N). This normalization shifts acquired arguments by a known unit but does not turn elementary symmetric sums into individual native beta powers or supply an auxiliary-pivot decoder.

## Primary-source applicability spot check

The cached primary PDFs have exactly the stated hashes:

- structured.pdf: `9834268a83b91fd33ffa92bfcd3e3aeb3946a573f39051ffce6660a7c6805ef7`.
- cejsc95.pdf: `9ad39a8b1706be441bcbfd3463a67d762e6cb483d320b9b1bf4b640ff0972dfd`.

I also freshly opened the Hyun–Lebreton–Schost author PDF. Its framework explicitly counts operations over a field, represents matrices by actual displacement generators, and discusses generic rank profile/regularization. The paper's mosaic rank bound p+q supports rank at most three here. It does not give the missing composite rank-t secondary-generator contraction. [Primary PDF](https://cs.uwaterloo.ca/~eschost/publications/structured.pdf).

The sparse parameter conclusion above was checked directly from this object's supports and f_0 degree, so no stronger unverified complexity statement from the second paper is needed for this review.

## Final scope

The reviewed report delivers a real, initialized optional proper-factor branch and a precise two-step secondary-closure test. It pays rank-t arithmetic, preserves the original native fallback/decoder, and claims no covered fast norm, no all-input exponent improvement and no generic lower bound. The exact reviewed bytes pass.
