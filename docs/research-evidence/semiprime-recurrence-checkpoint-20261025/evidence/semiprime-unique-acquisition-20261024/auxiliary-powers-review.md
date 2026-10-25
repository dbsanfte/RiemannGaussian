# Independent exact-source auxiliary-power audit

24 October 2026. **PASS**, no remaining corrections.

Final auxiliary-powers.md SHA256:
`3aeb1f40b72340face8154ac40657003fdea4078f5ca9cc766868767d4cd6be2`.
The author corrected the supplied-local-order branch: an arbitrary supplied local order is consumed first through gcd(beta^r-1,N), whereas native bounded-index recovery is separately restricted to a covered side. No source/shared files changed by reviewer.

The homogeneous power identity is exact modulo each actual local beta order, without dividing H in the constructor. All selected-power exponents have the charged O(d log N) bit length, and the stated literal selected/all-power upper costs soft(Jd+d) and soft(Jd²+d) account for actual integer and modular exponentiation work. No lower bound on other acquisition methods is inferred.

The conditional deterministic two-stage BSGS count is valid over the SUPPLIED prime-order group and known exponent field. With h=zeta^d of order n, store g^(h^(B*l)) and compare babies A_(j,d)^(h^(-b)); n/B+JB entries/searches recover v_j modulo n. For the second shared search explicitly normalize each A_(j,1) by the known scalar zeta^(-v_j), obtaining g^((zeta^n)^w_j). This gives the claimed shared order-d search. Zero exponents are separate. Clamping baby lengths to at least one handles J exceeding a subgroup size; the additional +J term covers that case. Primitive scalar startup and d|(p-1) are genuine missing inputs, not supplied by roughness. The cost balances and illustrative k^(5/3) ledger are correct for this construction.

The revised universal ready branch is complete: any exact local order r makes gcd(beta^r-1,N) nontrivial; a proper gcd factors, while gcd N supplies explicit nonzero short global annihilator r to the existing extractor. Under the full coprime-order controller the gcd must already be proper. If the known order is specifically on the smaller/covered side, H^-1 modr gives the unique bounded index and the stated native tests. Larger-side order alone is no longer assigned an unsupported bounded own-index promise. Near-N original K is nonzero on the continuing branch; changed families retain their own zero-exponent prechecks.

A nontrivial prime-global-order projection of the coprime-order controller has exactly one identity component and immediately factors by gcd(g'-1,N). A hidden local prime factor is not a supplied representation of that subgroup. Extra power fibers and potentially long polynomial annihilators are not promoted to original witnesses or short-decoder inputs.

The cached Cheon Theorems 1--2 match the prime-order, divisor, auxiliary-power and ERH qualifications stated. The independent BSGS derivation does not depend on the unavailable Kim PDF or on a random-target theorem. The source clearly labels this as a compact applicability/duplicate audit, not a new rate or generic unknown-order impossibility result.
