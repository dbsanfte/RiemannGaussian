# Affine batching and shared triangular norms: focused primary-source audit

2026-10-24. Scratch only; repository not edited. Input model: O(m) acquired row metadata, m rows, scalar modulus N=PQ with unknown primes above the prepared cutoff. The target is the product/gcd support of varying triangular or rectangle norms, not their full output tables. No theorem checked here initializes a soft-m whole covered query. This is a scoped conclusion about these sources and reductions, not a general absence or lower-bound claim.

## Latest relevant primary algorithms and their actual parameters

**Neiger–Salvy–Schost–Villard, ISSAC 2026.** [Faster modular composition using two relation matrices](https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/comp2.pdf), DOI [10.1145/3815436.3815451](https://doi.org/10.1145/3815436.3815451). Theorem 1.1: field K, explicit degree-n f, bidegree-(u,d) G with ud=Theta(n), and coefficient vector of a in a specified nonempty Zariski-open set; G(X,a) mod f costs soft(u*d^((omega+2)/3)). Theorem 1.2 transfers that bound to n explicit points with pairwise distinct first coordinates and generic second coordinates. Theorem 1.3 gives generic univariate composition soft(n^((omega+3)/4)); failure of genericity is detected, with fallback required. These are genuine new improvements, but neither compressed point input nor scalar-product-only output appears in the hypotheses. Composite-ring use needs lawful pivots and separate verification of genericity in both local fields.

**van der Hoeven–Lecerf, Faster multi-point evaluation over any field.** [Author HTML, dated August 2025](https://www.texmacs.org/joris/bieval/bieval.html), [author PDF, dated November 2024](https://www.texmacs.org/joris/bieval/bieval.pdf). The available versions have different dates; this audit does not silently treat their bytes as identical. The PDF describes deterministic algebraic algorithms and charges fixed-point precomputations; its bivariate total-degree-d, O(d²)-point deterministic bound is soft(d³). Later amortized refinements still take explicit coefficients/points and charge preprocessing. These do not constitute a compressed affine-line norm evaluator.

**van der Hoeven–Lecerf, Fast multivariate multi-point evaluation revisited, J. Complexity 2020.** [Primary PDF](https://www.texmacs.org/joris/kucomp/kucomp.pdf). The introduction explicitly permits finite rings (Z/rZ)[Z]/theta with theta monic. Its quoted Kedlaya–Umans bound for v variables, individual degree <ell and T explicit points is ((ell^v+T)log r)^(1+c epsilon), provided v<=ell^epsilon. The paper refines the Turing-machine analysis. Therefore unknown factorization of r is not itself an exclusion: these methods can legitimately operate modulo composite N. They still count dense polynomial size and every evaluation point; m² points remain m²-scale input. The n^(1+o(1)) style bounds must not be rewritten as soft n without proof.

**van der Hoeven–Lecerf, Amortized multi-point evaluation of multivariate polynomials.** [Primary PDF](https://www.texmacs.org/joris/genamp/genamp.pdf). Arbitrary fixed point sets are allowed in this extension of earlier generic-set work, but expensive point-dependent precomputation remains part of the model. An O(m²)-point set is not free preprocessing merely because it has a short affine description. The theorem evaluates polynomials supplied through coefficients, rather than an unevaluated long product circuit.

**van der Hoeven–Lecerf, Fast computation of generic bivariate resultants, 2020.** [Primary text](https://www.texmacs.org/joris/resultant/resultant.html). The quasi-linear expected bound is for finite fields, Las Vegas randomization, and grevlex-lex-generic input. Complexity is measured against explicit bivariate input/output size. No deterministic composite-ring scalar specialization theorem for the present family follows. At a fixed scalar parameter, an acquired ordinary univariate resultant is cheap; acquiring its implicit degree-m² operand is the present issue.

**Fischer–Kallmayer–Wennmann, ESA 2025.** [A Simple Algorithm for Trimmed Multipoint Evaluation](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2025.89). It evaluates bounded-individual/total-degree polynomials on specified trimmed Cartesian grids near-linearly in that grid size. The triangular support shape is relevant, but the theorem returns all grid evaluations, and its coefficient/grid size includes the triangle area. A short description of the triangle does not replace that size by its boundary.

## Degree audit of the tempting reductions

Let B_s(X)=prod_(h<s)(X+h). All slope inverses below are acquired certified units.

1. **One arithmetic progression per row, common length s.** For AP leaves c_j+d_j h,
   prod_j prod_(h<s)(c_j+d_j h) = (prod_j d_j^s) prod_j B_s(c_j/d_j).
   Construct B_s once and evaluate at r row nodes: soft(s+r), including input acquisition and scalar multiplication. Variable slopes alone cause no problem. Variable lengths <=s can be handled by binary length decomposition: common B_(2^k) polynomials have total degree O(s), with O(r log s) paid shifted nodes. Thus a family of r individual APs costs soft(s+r). This already absorbs a large apparently bivariate subproblem without new literature.

2. **A rectangle per row.** The menu norm is prod_(j,K) B_m(z_j+v_j K), times known units. For fixed j and L K-values, monic MPE costs soft(m+L), avoiding its mL leaf area. Across r rows the literal targets are rL. A single global MPE on B_m costs soft(m+rL), so r~L~m gives soft m². No bivariate MPE is needed for this expanded problem.

3. **Product-only resultant.** Define Q(X)=prod_(j,K)(X-z_j-v_jK), degree rL. Then prod_(j,K)B_m(z_j+v_jK)=Res(Q,B_m), with the usual monic resultant convention. Scalar output is indeed sufficient, but writing all Q coefficients or all roots costs rL. Replacing Q by Q mod B_m would be enough to compute its norm, yet fast acquisition of that remainder from the compressed lines is exactly an additional primitive. It is not an input delivered by generic resultant algorithms.

4. **Universal homogeneous factorial.** R_s(U,V)=prod_(k<s)(U+kV) has total degree s and up to Theta(s²) dense bivariate coefficients, but equals V^s B_s(U/V) at unit V. Evaluating it on O(m) scalar row pairs is cheap through item 1. Substituting it at quotient-algebra elements to obtain all line annihilators at once changes the base ring to dimension m; ring-operation costs must be multiplied by the actual polynomial arithmetic cost. A field-operation count does not survive this substitution at unit cost.

5. **Triangular Euclidean stages.** Each original row contains a_j-1 inner APs of lengths q_j i. The native first-stage maximum length is O(m), because q_j a_j<=m. With all r=Theta(m²) inner AP nodes explicitly acquired, item 1 already shares their common binary factorial polynomials and costs soft(m+r)=soft m². Thus generic MPE accelerations solve a problem whose expanded input was already quasi-linear; the missing gain is avoiding acquisition of these inner AP nodes while preserving the scalar norm.

6. **Interpolation in the row label.** The public j=1,...,m-1 have unit differences modulo N. Thus interpolate degree-<m-1 polynomials Z(j),V(j) through O(m) metadata in soft m. This is legal but gives potentially degree Theta(m) row maps. Forming B_m(Z(j)+V(j)K) before reducing has degree O(m²) in j and degree m in K. Reducing modulo prod_j(X-j) bounds the j degree by m but still leaves O(m²) coefficients in (j,K). Taking one norm after another does not yet avoid this array. A modular-composition theorem helps only after the required explicit input polynomials/remainders have been acquired.

These are charges for specific reductions, not lower bounds on other scalar-output algorithms.

## What the native inverse-quadratic slope supplies

The preparation gives a_j=[N*j^-2]_m as an integer in [1,m-1], with m prime. This is a relation modulo m, whereas the queried product is modulo N and m is a unit there. There is an integer carry e_j=(a_j*j²-N)/m, and the exact identity is a_j*j²=N+m e_j. Dropping m e_j modulo N is unlawful. Interpolating the known carries or residues is paid O(m) input but need not produce a low-degree rational row map over Z/N. Likewise, b_j carries depend on the canonical representative operation. The congruence alone does not initialize a small-degree bivariate norm.

There is nevertheless an exact useful row pairing. Put j'=m-j. Then a_j'=a_j=a. With d_j=(N-a*j²)/m and b_j=center_m(-j^-1*d_j), direct substitution gives
  b_j+b_j'≡2a (mod m).
Since both b values are centered, write b_j+b_j'-2a=m t with t in {-2,-1,0}. Define
  eta=ma, v=m/a, z=(m*b_j-a*j)/(ma).
The paired parameter obeys z'=1+t v-z. Rising-factorial reflection gives the exact scalar identity
  B_m(z'+vK)=(-1)^m B_m(z+v(-K-t-a)).
For any supplied K interval I, paired rows therefore use one slope with K sets I and -I-t-a. Both sets/endpoints are acquired from O(1) metadata. For gcd support, duplicates in their intersection may be removed by taking the union: multiplicities do not change zero support modulo squarefree N. For exact product values their multiplicities must be retained. No evaluated factor is divided.

This transformation preserves safe physical leaves: the reflected leaf is the negative of the paired original leaf with h replaced by m-1-h. It introduces no new zero or N-multiple outside the source envelope. If an acquired scalar saturates, retain lawful interval/row descent.

However, each a has at most two j-preimages (the two square roots modulo the prime m), so the number of slope classes remains (m-1)/2. Pairing can merge intervals and save a constant factor, but proves neither a subquadratic aggregate nor a smaller covering menu. It is a concrete native simplification, not an exponent advance.

## Constructive next primitive

A precise remaining target is: from r=Theta(m) acquired unit pairs (z_j,v_j), interval endpoints of length O(m), and explicit B_m, compute factor-or-Res(B_m,Q) in soft m without acquiring the rL roots/coefficients of Q; handle restrictions by the same cost and never invert an untested product value. The inverse-quadratic row pairing can be applied first at soft m cost. None of the primary theorems examined above supplies this compressed-input norm primitive. The existing sufficient clipped factorial cover retains soft m^1.5; no new all-input factoring rate follows from this audit.
