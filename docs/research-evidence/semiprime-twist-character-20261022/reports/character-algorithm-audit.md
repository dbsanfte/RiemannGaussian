# Exact native character-count acquisition: algorithm check

22 October 2026. No soft O(J+sqrt L) exact count or alternative factor-producing aggregate was obtained. This pass checked actual character-sum algorithms and their input/precision charges; it does not add another Fourier/unknown-totient reformulation, obstruction packet, success-example campaign or Lean backend.

## 1. A genuine incomplete-character-sum algorithm, fully charged

Hiary, *Computing Dirichlet character sums to a power-full modulus*, arXiv:1205.4687v5, Theorem 4.4, evaluates

    K^(−j) sum_(0<=k<K) k^j chi(v+k) exp(2pi i(alpha k+beta k^2))

to prescribed additive epsilon. Its main operation count is C times a fixed polynomial in logarithms of the input sizes and 1/epsilon, where

    q=product_p p^(a_p),   C=product_p p^(ceil(a_p/3)).

There is also character-table preprocessing of soft O(sum_(p|q) p), with the factorization supplied or paid. The proof's actual recurrence splits into the C progressions l+Ck and applies the Postnikov formula to chi(1+inverse(l)Ck), obtaining quadratic phases. These phases are computed by a length-halving quadratic-sum algorithm. Taking epsilon<1/2 can recover an integer-valued sum by rounding; desired exactness is not intrinsically the problem here.

For q=N=PQ squarefree, C=PQ=N. Thus the theorem does not become a sixth-rate character-sum algorithm: even ignoring preprocessing, its stated charge is soft O(N). Principal chi_N^2 does not improve the progression count in this theorem; the ramified zero classes are still present. Artificially inducing the character to modulus N^a gives C=N^(ceil(a/3)), never a smaller charge. Moreover, the theorem's character argument is affine in k; z−u q^i is a geometric-orbit argument. An additional paid transformation would be required even if its modulus charge were small.

Section 6 supplies a separate factorization-free completion method for general real primitive characters, costing conductor^(1/2+o(1)), up to its precision parameters. At conductor N it is too expensive, and it is meant to help ordinary interval sums longer than sqrt(N), not to process J shifted geometric orbits of length L~N^(1/3). These statements concern the concrete theorem interface, not an impossibility of better character computation.

Primary: https://arxiv.org/html/1205.4687v5 . PDF downloaded and pinned.

## 2. Fast Jacobi sums: finite-field size and character order are input parameters

Van Wamelen, *Jacobi sums over finite fields*, Acta Arithmetica 102.1 (2002), gives complete finite-field Jacobi-sum computation via ideals and shortest vectors, followed by exact root-of-unity resolution. The finite field F_(p^r), its characteristic and the character/generator are given. The lattice dimension is phi(e), for character order e; the discussed exact shortest-vector step is exponential in that dimension, while polynomial in log(field size) for fixed dimension. The algorithm computes a complete field sum, without an incomplete exponent-window selector. Its finite-ring primality-testing discussion does not assert a corresponding unfactored-semiprime geometric-window count algorithm.

No direct application to D(S,I) was found. In particular, neither the unknown hidden finite fields nor an arbitrary growing-order character can be treated as fixed setup. This is an inspected parameter mismatch, not a generic character-sum hardness claim.

Primary: https://www.impan.pl/shop/en/publication/transaction/download/product/83146 . PDF downloaded and pinned; Sections 1–2 and final algorithm discussion inspected.

## 3. Factorization-free quadratic exponential sums: an actual paid primitive

Cai–Chen–Lipton–Lu, *On Tractable Exponential Sums*, arXiv:1005.2632, Theorem 1.1, computes complete sums of a supplied quadratic polynomial over Z/N in polynomial time in its number of variables, log N and coefficient-description size, without factoring N in advance. Its proof can itself discover a proper factor when a coefficient or an elimination coefficient has a suitable nonunit gcd. It does not claim soft-linear dependence on a growing number of variables.

For a single original collision difference h, the simple instance is

    sum_(x,y mod N) exp(2pi i hxy/N)=N*gcd(h,N).

This is genuinely computable quickly from h, but the ordinary gcd already gives exactly the same factor information. Trying to combine all entries requires retaining h_(j,i)=z_j−u q^i as coefficients or as a variable-dependent phase. The supplied quadratic theorem does not provide a compact quadratic presentation of that native geometric dependence. Encoding repeated squaring with multiplier variables uses terms y*(x_next−x^2), which are cubic; invoking the quadratic theorem on such an encoding would be invalid. No cheap source-preserving quadratic conversion was constructed. The paper's hardness claims are not used here.

Primary: https://arxiv.org/abs/1005.2632 . PDF downloaded and pinned.

## 4. Explicit Euclidean/floor-sum assessment on native exponent metadata

Let the native metadata be q=beta^s and z_j/u=beta^(E_j), with the E_j recorded integers. At a hidden prime P, put r_P=ord_P(beta), g_P=gcd(s,r_P), d_P=r_P/g_P. A collision can occur only if g_P divides E_j. If so, its seed index has the one residue

    tau_(P,j)=(s/g_P)^(-1)*(E_j/g_P) mod d_P.

The count on an integer interval [A,A+L) is then exactly

    floor((A+L−1−tau)/d_P)−floor((A−1−tau)/d_P).

This explains precisely which modulus and boundary phase a floor-sum computation would need. They are r_P/g_P and tau_(P,j), not the known ambient modulus N or the known exponent step s. Supplying them is not a public N-only algorithm; no acquisition of those periods/phases within the desired budget was obtained. Native exponent metadata alone has not paid this floor operation's modulus.

Without hidden periods, there is a public exact block recurrence. Let D_h(Z,u) count the admissible original nonunit differences from target set Z and seeds u q^i, 0<=i<h. Since q is a unit and Jacobi(q,N)^2=1,

    D_(2h)(Z,u)=D_h(Z,u)+D_h(q^(−h)Z,u).

Ragged lengths split into the corresponding two intervals. The length-one base case computes J ordinary gcds/Jacobi symbols. This is an explicit computation recurrence, but both transformed-target children must be evaluated: its literal cost is soft O(Jh), not soft O(J+sqrt h). No coverage-preserving sharing of those transformed character sums was established. Thus this recurrence is not proposed as progress on the target clock.

The actual quadratic-reciprocity algorithm for a Jacobi symbol reduces individual integer numerators by Euclidean quotients. Applied to this recurrence's numerators, the first reduced values are z_j−u q^i modulo N, an affine multiplicative-orbit sequence, rather than a known arithmetic progression in i. The inspected fast incomplete-sum algorithm above does not batch these Euclidean chambers. A claimed floor-sum shortcut must explicitly pay their endpoints or provide a different aggregate transition.

## 5. Complementary nonzero signs

The signed sum of Jacobi values and its unit deficit are different outputs. The equation chi(h)^2=1 on units and 0 on nonunits is exactly why nonzero sign oscillations can cancel while retaining a tiny, positive zero deficit. The inspected algorithms do compute certain signed sums cheaply, but none supplies both the native geometric argument and the required square/principal-mask output at the target cost. No source-preserving use of the complementary signs was found that returns a guaranteed factor or paid locator on every input.

## Outcome

The new facts from this pass are the fully parameterized Hiary evaluation charge, the exact finite-field/order charge of the Jacobi-sum constructor, and the legitimate factorization-free quadratic-sum primitive with its precise native-conversion gap. No old full-Fourier or unknown-phi observation is substituted for an acquisition algorithm. The all-input character-count route remains open; no complexity improvement or new theorem is asserted.
