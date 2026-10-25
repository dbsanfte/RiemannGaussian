# Independent quadratic period constructor review

24 October 2026. Reviewed exact current bytes of /tmp/semiprime-gauss-period-20261024/period-constructor.md.

SHA-256: `c7b338819761dddd0838f81a21ad65c7e9d830f48bcc9da4b4c4c99b6d2e14b5`.

Verdict: **PASS. No required fixes.** Read the universal proof, coefficient algorithm, norm/unit ledger, all-row acquisition and full cyclic correction independently. No repository modifications or finite examples; no assertion that this review certifies an executable/Lean backend.

## Universal Gauss identity and injection over zero divisors

The Gauss-square sign checks: the quotient-ring character-sum calculation gives G*bar_star(G)=m, while bar_star(G)=chi(-1)G. Hence G²=chi(-1)m=D. Permuting exponents gives sigma_j(G)=chi(j)G. These identities use Phi_m, not the full cyclic relation alone.

The base-change injection is proved explicitly rather than inferred from preservation of injectivity under tensoring. If A+B G=0 in R[Z]/Phi_m, the degree-<m coefficient vector is (A,B chi(1),...,B chi(m-1)). Since Phi_m is monic of degree m-1, a polynomial of degree <=m-1 in its ideal is a SCALAR multiple of Phi_m over any coefficient ring. Therefore all displayed coefficients equal A. The character takes both +1 and -1, so A=B=-B and 2B=0. With 2 a unit, B=A=0. No domain, reducedness, field embedding, square root or unlicensed cancellation is used. This validates the claimed injection after every stated specialization, including R=Z/N with zero divisors.

The invariant-subalgebra argument also checks. Automorphisms permute degree-<m representatives and preserve the constant coefficient. If two such representatives are equal modulo Phi_m, their difference is a scalar multiple of Phi_m; its zero constant coefficient forces that scalar to be zero. Hence QR invariance is actual constancy on the two nonzero character orbits. Modulo eta_++eta_-=-1 and eta_+-eta_-=G, its span is precisely rank two when 2 is invertible.

The quadratic conjugation tau->-tau exchanges QR/NR. It need not coincide with complex/star inversion zeta->zeta^-1 when chi(-1)=+1; the report correctly uses the Gauss character action rather than making that identification.

## Entire degree-h polynomial is acquired

For 1<=k<=h=(m-1)/2, k is nonzero modulo m and multiplication by k permutes the QR set to its character coset. Thus p_k=(-1+chi(k)G)/2, with the stated sign. Logarithmic coefficients for product(1+T zeta^r) are (-1)^(k-1)p_k/k.

Every integer 1,...,h is a certified unit in R under the prepared prime cutoff. Fast exponential therefore legitimately acquires C mod T^(h+1). Since the actual product has degree h, this is its full polynomial; evaluating the acquired coefficients at the unit/scalar beta does not discard an unknown tail. Horner evaluation sum c_k beta^(h-k) equals product(beta+zeta^r), including its leading coefficient and all signs. This is the essential positive distinction from a short jet of a degree-JL product.

Character-table enumeration is O(m) small-integer work, denominator acquisition is soft m, and rank-two series operations use a constant number of base-ring polynomial operations. All arrays have O(m) coefficients. No multiplication of h expanded degree-m factors is hidden in the ledger.

## Norm, Frobenius, and all native rows

The product over QR and NR is exactly (beta^m+1)/(beta+1) for odd m. Its displayed quotient is a polynomial identity; algorithmic scalar inversion is guarded by the original odd-order promise. Both beta+1 and beta^m+1 are units, so U inverse is explicitly bar(U)/norm(U) in either split or nonsplit local algebra. No specialized order of U or W follows.

Frobenius on the universally embedded Gauss element is G^p=chi(p)G. Injectivity transfers this identity to B mod p even in the split case. Consequently the original own-tag row equality and the SAME bounded integer index follow exactly as stated. This is a proof-level use of an unknown prime, not an algorithm requiring that prime as input.

All O(m) rank-two rows are acquired in soft m: U^N is shared, automorphisms are identity/conjugation, and each row needs a constant number of signed powers of constant-dimensional unit data with O(log N)-bit exponents. The explicit outputs contain only O(m) residue coordinates. Their cheap acquisition is valid; it does not acquire the O(m)-by-O(m²) comparison family.

## Full cyclic rank-three correction

Since m is a unit, the comaximal factors Z-1 and Phi_m give the full cyclic algebra as R times C_R. The idempotents e0=(1/m)sum Z^r and e1=1-e0 satisfy e0 G_full=0 and G_full²=D e1. Thus replacing G_full² by D*1 in this full algebra would be wrong; the report expressly avoids that error.

The rank-three QR-invariant coordinates (s,A+B tau) are therefore correct. The full period product has scalar/augmentation component (beta+1)^h and cyclotomic component U. Each native rank-three row has scalar coordinate (beta+1)^(h*(N+delta_j)), because ell_j+a_j+N=N+delta_j; automorphisms fix that coordinate. A shared common basis plus O(m) triples is acquired in soft m. Expanding all rows to all m cyclic coefficients would cost m² output, and is not promised.

The full relative-norm own equality follows componentwise, or by applying the multiplicative QR norm to the original cyclic own equality. This norm commutes with sigma_j because the automorphism group is abelian. No augmentation summand is lost.

## Scope and relation to the query refinement

The constructor proves a valid paid character projection and compact full rank-three representation. It asserts neither large translated/period order, a long interval query, nor saturated recovery. This scope is faithful.

Separately, period-query-attempt.md has been refined to use period-recovery.md conditionally: with its surviving-point coprime large-order guards, the scalar antipodal fold has no additional recovery obstruction. The two difference norms identify an actual direct/partner row leaf; proper gcds factor and saturated global row collisions use that controller's signed sum/difference decoder. This does not import the original beta decoder for free. Its three carry classes and terminal polynomial costs are charged, retaining soft m^(3/2), while unconditional supply of a surviving period point remains open. These later facts do not alter the constructor's acquisition claim.
