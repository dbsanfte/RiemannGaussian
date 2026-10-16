# Independent actual-source all-scalar spectral review

PASS. The final artifacts give an exact finite actual-source counterexample to the stated universal collision-forces-scalar-spectral-nonunit implication. No correction requested. This is not an infinite counterfamily, a sufficiently-large-input refutation, an acquisition algorithm, or an operation lower bound.

## Exact reviewed bytes

- actual/report.md: 9527 bytes, SHA256 ab4ce6e96436ac4b02249ec2d0adb3f409821371033edf8f4a1fdbd4cf640b0c.
- actual/manifest.json: 1211 bytes, SHA256 fee63e2edf4c04e0e4eee87bac2834796591fbf28a12b3324c180cb16d203ed2.
- actual/certificate.json: 4007 bytes, SHA256 4956ee63a417867643193bc1e07b7ce9b4d6918dab304a9286b025ef3557547c.
- actual/orbit-certificate.json: 5649 bytes, SHA256 8179fcef510e6b677c32ff10b5dafaca26c342b993a5f6ff2acd361bf0b94f57.
- actual/scalar-certificate.json: 4698 bytes, SHA256 f0dcc51c184a29deca79e9822dbfd84c92617f455d33977655a14ad77cd2da46.
- actual/source-pins.json: 1173 bytes, SHA256 bf9a50dc340a7756d7890e472b24b4b6e1beb01cf85a963e30c135e995891b59.

All eight manifest file sizes/hashes and all five inherited source pins independently match. Unmanifested initial candidates, counterexample.json, find.py and v1 are not used by this review and must not be confused with the final witness.

## Independent reconstruction

Wrote a separate standard-library checker without importing or executing the author's verify.py, orbit.py, or scalar.py. It reconstructs the mathematical data directly from m=43, P=69263, Q=70163. The checker is sibling independent-spectral-check.py: 4933 bytes, SHA256 41f6e663962d311657d7caf7ab7db74137fe283421d197c8f937038607eba5ec. Its polynomial multiplication, division, modular powering, gcd and Gaussian determinant routines are independently implemented. The checks passed.

1. Exhaustive trial division proves primality of 43, 69263, 70163, 34631 and 35081. Checked N=P Q=4859699869, P-1=2*34631, Q-1=2*35081, distinct orders, cross-period exclusions and units P,P-1,Q,Q-1 modulo 43^2. Exact integer powers establish R^1000>P^677 and the Q analogue. Both orders exceed 16m^2. The ratio/bin and sixth-power inequalities hold. Hence the literal sixth width is 42 and the least prime at least that width is 43. Exact inequalities 1^50<=42<2^50 certify the first-menu bound floor(42^.020)=1.

2. Recomputed the SPECIFIC public projection as pow(pow(2,N-1,N),(43!)^33,N), with the integer logarithmic exponent 33. It gives gamma=3896048378. Then q=gamma^(43^2)=1007400003. In each prime field gamma^R=q^R=1 and neither element is one, so prime R certifies the exact local orders. CRT gives global order 1214890111, above 16m^4. No privately chosen CRT generator replaces the public base.

3. Rebuilt every inverse, canonical numerator, exact quotient, centered b, c and literal delta for all 42 native tags. Both divisions are exact and all offsets satisfy the native span. They match the certificate list exactly; all offsets are distinct. Built every actual node and verified every pairwise difference has gcd one with N. Multiplied the 42 monic linear factors independently to reproduce the entire H coefficient vector modulo N.

4. Constructed phi by separate prefix/suffix polynomial products from H, q and q^L. Reproduced phi(0)=4699488932, its unit gcd, and all 88 scheduled values at q^(42n). More importantly, constructed the row companion M directly and the pencil (I-q^L M)-X diag(q^s)(I-M). Gaussian elimination at ALL X=0,...,42 in EACH prime field agrees with the reconstructed phi. Since both determinant and formula have degree at most 42 and the 43 points are distinct, this certifies the entire polynomial identity, not merely agreement at a few sample points.

5. Independently computed X^R-1 modulo each reconstructed field phi by repeated modular squaring. It matches each saved remainder. Full coefficient multiplication verifies A*phi+B*remainder=1 for both saved Bezout pairs. A separately implemented Euclidean gcd also returns a nonzero constant. Therefore gcd(phi_P,X^34631-1)=gcd(phi_Q,X^35081-1)=1. Since every q^v in its field is an R-th root of unity, this proves ALL integer-index q-power spectral values are units, including negative/unbounded/advised indices. Phi(0) is separately unit. The conclusion is algebraic, not inferred from the 88 scheduled samples.

6. Independently enumerated the local q orbits and reconstructed the complete canonical hit lists. They agree exactly: P hits (6,281),(13,2023),(33,1535),(39,186); Q hits (6,2162),(8,208),(16,2674),(17,2086),(30,568),(36,2522),(39,1212). The own tags P mod43=33 and Q mod43=30 have exact native numerator quotients 1535 and 568, slopes 40 and 14, inside L=3700. Thus both hidden fields have genuine row zeros and the full norm is zero modulo N. In particular the own leaves also carry proper single-field factor information.

7. On the SAME reconstructed phi, independently computed X^p-X modulo phi for each p=P,Q by modular squaring and subtraction of X. Both vectors exactly match scalar-certificate.json. Full coefficient multiplication verifies its new Bezout identities C*phi+E*remainder=1, and a separate Euclidean gcd computation independently gives nonzero constants. Every base-field scalar satisfies x^p-x=0, so these identities exclude every base-field root of phi. CRT therefore proves gcd(phi(x),N)=1 for EVERY scalar x modulo N. This strengthens the orbit result and rules out input-dependent, privately advised, coset or arbitrary scalar schedules for THIS same phi on this witness. It does not merely check a finite schedule or extrapolate from samples. The earlier orbit certificates are unchanged and still independently verified. The report properly credits the same-input root-agent co-derivation rather than presenting a new search.

## Scope

All input promises explicitly listed in the report are verified. The witness is not certified as surviving every unrelated historical exceptional-set deletion, and the report correctly makes no such claim. One exact input refutes a universal finite implication under these promises but does not establish infinite or asymptotic avoidance, nor refute a theorem restricted to an unspecified sufficiently-large threshold. For this same phi the all-scalar certificates now cover arguments outside the q subgroup as well. Different spectral polynomials, determinant deformations and factor-only acquisition remain open. Hidden-field inversions and orders in this proof-side checker are not granted to a factoring algorithm. No repository file was modified, and no Lean build or benchmark was performed.
