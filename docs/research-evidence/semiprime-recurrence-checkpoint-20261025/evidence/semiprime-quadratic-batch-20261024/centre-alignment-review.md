# Independent review: native centre nonalignment

24 October 2026. **PASS**, no required corrections.

Exact reviewed centre-alignment.md SHA256:
`8c2d18c27951d5b07c67fcc852f4cd0d7d688d8de41e5429658f5d935cf011e5`.

Checked against the pinned quadratic-product.md and its actual prepared contract. At the unique nonsplit prime, the scalar beta subgroup and norm-one W subgroup have coprime odd orders: these divide r-1 and r+1 respectively. Hence the assumed product equality separates the two powers. The W exponent H(mu+1) lies in [-7H,H], below its nontrivial order >16H, forcing mu=-1. This step needs neither split-side coprimality nor coprime W orders across primes.

The remaining equality is global scalar beta^(2(N+a))=1. Odd global beta order removes the factor two; coprime local beta orders give D_beta>256H² and D_beta divides (P-1)(Q-1). Thus D_beta divides the positive integer P+Q+a-1, which is <H² under the stated continuing bounds. The contradiction is valid. No small bound on N+a itself was used.

The coefficient classifier also has the stated complete branches. A proper norm gcd factors; a unit norm certifies a unit. If the norm gcd is N, field-side vanishing forces both base coordinates divisible by that nonsplit prime. The joint coordinate gcd is therefore proper unless both coordinates vanish globally, which the theorem excludes. Consequently O(k) actual centre tests cost soft k and return a factor or unit, never a global alignment. Local split-coordinate zeros are routed through a factor and are not inferred absent from mere global inequality.

Scope is exact: no native centre equals q^-1 on the continuing prepared branch. This rules out that literal finite-theta specialization, while leaving the general four-boundary query, its soft k^(3/2) cost and possible different evaluators unchanged. Source and shared files were not modified.
