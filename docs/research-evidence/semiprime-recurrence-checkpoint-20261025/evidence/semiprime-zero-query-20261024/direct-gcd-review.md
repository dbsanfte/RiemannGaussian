# Independent audit of direct-gcd.md

24 October 2026. **PASS. No source corrections requested.** Exact frozen source: `/tmp/semiprime-zero-query-20261024/direct-gcd.md`, SHA256 `9cc5a04f1acdcda8a30edfa80b37b6a468112bc98db2ac0af65383ef5d67a386`. No audited source, shared document or repository file was changed.

## Arbitrary acquired B coefficients and guarded polynomial gcd

The factor/unit/global-zero primitive is correct for EVERY acquired coefficient x+y*tau, not just a native row value. If its norm is a unit, the explicit conjugate/norm inverse is lawful. A proper norm gcd factors. If the norm gcd is N, the nonsplit side is a field, so both x,y vanish at that prime. Unless both coordinates are globally zero, gcd(x,y,N) is consequently a proper factor. This closes the split-component saturated-norm case without falsely calling it whole equality or using the original beta decoder on an auxiliary coefficient.

Thus nonzero leading coefficients can be normalized, globally zero heads dropped, or a factor returned. On a continuing execution all needed leading units have consistent degree profiles under local reduction. The corrected complexity statement permits Theta(J) leading tests and charges scans to actual arrays in a standard fast half-gcd recursion; it does not confuse logarithmic recursion depth with pivot count. Stored/reused degrees, soft-linear per-level arrays and logarithmically many levels give the stated soft-J scan/test ledger. Ordinary Euclid is only claimed lawful, not assigned that bound. None of this acquires an implicit P_L remainder.

A successful monic positive-degree gcd is also consumed correctly. F splits into the actual separated roots; at the nonsplit side some original V_j is a root of the gcd. Monic MPE therefore finds a nonunit acquired G(V_j). The coefficient primitive returns a factor or a GLOBAL zero selecting an original row. The resulting geometric-index collision still needs its actual one-row product/localization, paid at soft sqrt L; a globally zero G(V_j) is not an acquired common prime-side q-log. Degree-zero gcd gives a Bezout coprimality certificate at every local component. Restrictions retain original rows and intervals.

## Complete remainder algorithms and phases

The direct coefficient-algebra implementation is initialized. B_s is an ACTUAL degree-s polynomial, q^(-sg)x are actual elements of B[X]/F, and MPE divisors over that ring are monic. Zero divisors cause no illicit inversion. A coefficient-algebra operation is correctly paid at soft J base operations, including monic reduction and its represented inputs/outputs. The clipped tail and q^(s²g) block phases yield the complete degree-<J remainder at soft(s+J(s+L/s)), optimized soft(J sqrt L). It is not counted as a scalar operation merely because only a final gcd is wanted.

The native-value comparison has the correct full phase s²*a(a-1)/2+a*s*d. All J*a mixed arguments, per-row products and exact tail values are actually acquired. Interpolation uses the already certified F'(V_j) units and returns the unique residue. Its soft(s+JL/s+J) optimum is the existing soft(J+sqrt(JL)), and the source expressly says it acquired the native values. Neither completion hides a free implicit remainder or faster scalar-only query.

## Actual anchor groups and interval maps

Under the stated original native delta range [-3H,H], each residue r modulo H admits at most FIVE exact delta values. The controlled-modulus bound of sixteen tags per delta gives at most eighty raw tags in one residue group. Computing A_j=V_j*q^(-t_j), t_j=(delta_j-r)/H, is actual soft-J work, and every anchor in that group has exactly the SAME unit norm beta^[2(N+r)]. No unknown local orbit label is inferred.

Pair tests inside these constant-size groups cost only soft J. A proper gcd factors. Norm saturation forces equality at the nonsplit side; at the split side the shared unit norm makes equality of one component force the other. The coefficient classification likewise gives a factor or global equality. Thus global equal anchors are legitimately grouped. After global target dedup, two rows with the same t cannot survive as different targets of that anchor, so each anchor has at most five stored original shifts, spanning at most four. Cross-residue global equality would contradict the short beta norm margin.

For the original row interval i in [0,L), the anchored condition is exactly A=q^n with n=i-t. Its union is [-t_max,L-1-t_min] when L>4, of length at most L+4. Known initial q shifts are actual units. For shorter restrictions, retaining/merging only the true stored intervals avoids filling holes. Given a located n, a stored interval containing it selects an actual row and returns i=n+t; that ORIGINAL bounded index, not a possibly negative anchor index, is passed to the norm/beta consumer. This preserves same-row/same-index recovery even at saturation. No unrestricted q-dispersion or global q-log was acquired. The at-least-J/5 anchor count is a cardinality ledger for this bounded normalization, not a generic algorithmic lower bound.

## Primary contracts and final scope

I checked the cached primary statements and all four PDF hashes against the source ledger.

* Abramov's setup is a computable characteristic-zero field, non-root-of-unity q and transcendental x. Its q-suitability assumption explicitly obtains ALL indices with p(q^n)=0, and qUD first obtains the largest resultant index before its downward loop. Up to the known inverse-q convention, this is precisely the missing geometric-orbit information here; neither the premise nor its loop is a nearlinear finite-ring bounded-query algorithm.
* Chen--Paule--Saad Theorem 2.1 is the ADDITIVE-shift characteristic-zero stabilization after the supplied/computed dispersion. Its introduction obtains that dispersion as the largest integer resultant root. It is not a finite-modulus multiplicative-window theorem.
* Kaltofen's straight-line gcd result is randomized over its usual coefficient fields and explicitly polynomial in UNARY input degrees as well as binary SLP data and failure probability. It does not supply the proposed deterministic soft(circuit size+J) interface independent of L.

Verified PDF SHA256 values are Abramov `af8f32f0a8325c86992a47f058efa8f2a2a73c91742fd2e64582aefbf666c0e0`; Chen--Paule--Saad published `f307722e204ce34795b621d710c3fcb493f60de010318429fb91e92ec2e7fd5d`; its arXiv version `63e97424e583062c3025de2da0973f1d565db603cc1ff956a27c14cda5a52582`; Kaltofen `36f8c6e9e1c184ea9d6dd2270aa24843ebbd26c78881c7e69b69b75904d15731`.

Finite local q-orbits recur periodically, so the characteristic-zero largest-index premise cannot be imported. Short certified point differences give uniqueness inside the window, not acquisition of the belonging indices. The report correctly leaves fast remainder/gcd construction open, retains the old complete query and introduces no auxiliary-coefficient decoder or factoring-exponent claim. Exact reviewed bytes pass.
