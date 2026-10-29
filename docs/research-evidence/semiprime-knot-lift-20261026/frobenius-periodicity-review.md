# Independent review: Frobenius screen and periodicity scope

26 October 2026. Read-only review of the two root reports; primary periodicity theorem checked; no experiments or repository edits. Own scratch lift-collision.md was clarified separately as recorded below.

**PASS.** The prepass is a valid soft-k factor-or-order-coprimality refinement, and the periodicity statement is correctly restricted to ordinary fixed-axis periodic realizations and the eventual native degree range.

## Frobenius screen

P<Q is only a proof convention. Since r_P divides P-1, gcd(r_P,N)=1. At Q the only possible common prime is P, and squarefreeness gives gcd(r_Q,N)=P or1 even if r_Q has a higher P valuation. Thus q^N has exact Q-order r_Q/P or r_Q respectively. If P divides r_Q, its reduced order is at most (Q-1)/P<N/P²<=N/A² and therefore at most B=floor(N/A²). At P its order remains r_P>16k²>B. Hence the computed product has gcd exactly Q in that case, never N, and gcd1 otherwise. This is a proper-gcd recovery proof requiring no short-annihilator decoder for arbitrary auxiliary zeros.

A=16k²+1 is below both primes on the prepared branch. N<=k^6 gives B<k²/256, so the initialized degree-ceil(sqrt B) product/multipoint implementation fits soft k. The actual product uses modular q^N, not a materialized N-fold exponent. Repeated points cause no inversion in the monic multipoint tree. The tail indices cover exactly j=1,...,B. All initialization and gcd work is accounted for.

The beta/eta extension is correct: ord(beta)/ord(q) divides H, and neither prime dividing N divides H since P,Q>H. Thus no N-primary order component can disappear under beta->q. The same follows for eta. On a continuing prepass, N-th powering is a bijection of each relevant cyclic subgroup, but neither its inverse exponent nor a subgroup logarithm is output.

## Periodicity scope and exact primary source

Checked Hillman–Livingston–Naik, AGT6(2006),145–169, Theorem2 in the published PDF https://msp.org/agt/2006/6-1/agt-v6-n1-p05-s.pdf . It states the stronger prime-power-period version q=p^r with congruence Delta_K=Delta_quotient^q * delta_lambda^(q-1) mod p. The report uses only r=1, so its displayed formula is exactly the needed special case. The Laurent-unit ambiguity does not affect span.

Reduction of a normalized knot Alexander polynomial is nonzero because its value at1 is1. For lambda!=0, delta_lambda has extreme coefficients +/-1 and span |lambda|-1, including negative lambda. Lambda=0 would make the congruence zero, impossible. Field span adds under nonzero products, yielding D=p*D_quotient+(p-1)(|lambda|-1). Therefore 0<D<p-1 is impossible. Native unit extreme coefficients give exact span 2L at each hidden prime; soft L=soft k and P>16k² imply the needed strict inequality eventually. The report correctly states no all-small-k threshold from soft notation. Restricting an ordinary N-periodic rotation to its order-P subgroup retains the same disjoint fixed axis. Freely periodic actions, twisted invariants and unrelated detectors are expressly outside this argument. No general knot-algorithm obstruction is asserted.

## Sharpened lift law and correction of a self-audit sentence

Appended the stronger post-screen interface to my lift-collision.md: W=u^N now generates the same subgroup as u at BOTH primes. The earlier larger-component loss is a prepass-only possibility. With the existing coprime local orders, local membership at both primes also combines globally by CRT; this still does not acquire inverse exponent N^-1 modulo the unknown global order or target logarithms.

Also corrected one sentence in that report: in F_P, target^N=target^Q, but Q-th powering generally does NOT distribute through a rational expression. Only the actual P-th-power Frobenius is additive (and is identity on F_P). Thus N-th powering must not be treated as a ring homomorphism or as substitution u->u^Q in the target rational formula. The affine lift law itself used only multiplicative exponentiation and was unaffected. No other material gap found.
