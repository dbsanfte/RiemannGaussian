# Independent audit of D.1: arithmetic, packing, recursion, and implicit-entry cost

26 October2026. Scratch-only proof audit of the supplied 67-page ETH draft. Goal is active by explicit resumption; no frozen file or repository edits. Assigned scope: D.4.1,D.4.2,D.4.7, LemmaD.3, parameter bounds(D.5)-(D.6), precision(D.11), and applicability of the implicit-entry contract. Other agents separately audit the Hermite and mode identities. **No fatal gap found in these assigned complexity parts.** This is not an independent certification of all D.1 algebra, nor a claim that the earlier formal SAT theorem already formalizes D.1.

## 1. Coefficient extension and unit interpolation

Let lambda=ceil(log2 s), e=4lambda. Enumerating2^e≤16s^4 monic binary candidates and trial-dividing modulo2 by all monic polynomials of degree≤e/2 costs polynomial time in s: the second enumeration is O(2^(e/2))=O(s²), with polynomial-log arithmetic. This is a genuinely deterministic field construction, not an oracle.

A monic f irreducible modulo2 is irreducible over Q by the monic Gauss lemma. Thus K=Q[U]/f is a field. In O=Z_(2)[U]/f, a vector with a nonzero coordinate modulo2 is invertible: its multiplication matrix has invertible reduction over F_(2^e), hence odd determinant and inverse over Z_(2). Factoring out each coordinate-minimum power of2 proves the claimed multiplicative valuation. This reasoning handles negative valuations in K as well.

Arithmetic in A_p=O[V]/(V^ell,2^p) uses e*ell*p bits up to polynomial overhead, and field/odd-unit inversions are exact. Distinct binary-coordinate lifts differ by a nonzero residue-field element, so their differences are genuine units. There are2^e≥s^4 lifts. The needed degree bound M(2L_packet-1)+1< s^4 follows from M≤Cs,L_packet≤s^(1/1000) for all sufficiently large s; all these counts are computable integers. Polynomial interpolation therefore does not pivot on a native zero divisor.

## 2. Immutable canonical entry lifts are consistent

A tensor created at precision p_c is always evaluated modulo2^p_c, then its coordinate representatives are lifted to any later precision. Those lifts need not preserve arithmetic, but that is not used: each call defines its own deformation using the SAME fixed lifted entries. Its target at T=0 is the contraction of those specified tensors, and the induction only promises that target modulo the call's precision.

When a parent constructs a new packet tensor modulo its child precision, the child fixes those representatives. It need not reproduce a hypothetical unreduced parent rational formula at still higher precision. Retained tensors keep their old creation precision, exactly as prescribed. Consequently the non-homomorphic canonical lift does not introduce an inconsistency between the parent identity and child target.

A packet-tensor entry depends only on local packet data, interpolation node/value, its mode tuple, and its CREATION precision. It does NOT invoke the values of its ancestor tensors. Original tensor values remain separate retained vertices. Thus evaluating a newly created vertex does not recursively expand an ancestor evaluator or multiply its cost by an exponential depth factor. This detail is essential for high-arity implicit tensors.

## 3. Derive the depth and all parameter margins

The global s is FIXED through recursion. With H=ceil(s/floor(sqrt(lambda))), active calls have M>H and M≤Cs*8^(-d). Hence

    d≤(log2 lambda)/6+O_C(1).

For u_d=floor(epsilon lambda/2^d), epsilon=2^-17, the floor is harmless uniformly at active depths once s is sufficiently large. Therefore

    u_d=Theta_C(lambda/2^d)≥c_C*lambda^(5/6).

Since5/6>4/5 this eventually implies u_d≥lambda^(4/5); constants merely make the threshold enormous. Also u≤M. No bound u≈sqrt(lambda) is needed.

Write a_d=2 sum_(j≤d)u_j. Then a_d≤4epsilon lambda. Crucially D_arr=r^(2a_d), NOT r*2^a_d: r=64 gives log2 D_arr=12a_d≤48epsilon lambda. Since48epsilon<1/1000, both D_arr and L_packet=2^a_d are≤s^(1/1000) eventually (ceil(lambda) adds only a fixed factor). Consequently

    2D_arr² Delta=O(s^(.902))=o(s/sqrt(lambda)),
    L_packet D_arr≤s^(.002)=o(s/sqrt(lambda)),
    2L_packet≤Delta=ceil(s^.9),

which proves(D.6) at EVERY active call, not just the root. New packet degrees≤2L_packet and unchanged original degrees≤Delta preserve the same global degree invariant. Children need not satisfy a degree bound relative to their own edge count; that is neither assumed nor required.

## 4. Collision packing, including exact construction

For the pair-label load X_gamma, expansion gives E sum_gamma(X_gamma-M/D_arr)^2 as a sum over ordered edge pairs of label-agreement probability minus1/D_arr. Disjoint-endpoint pairs contribute zero. At most2M Delta ordered pairs share an endpoint (parallel edges included), each contributing at most1. Thus the variance bound2M Delta is correct.

Conditional expectation is computable exactly by enumerating pairs of edges and labels of at most four vertices. Each probability has denominator dividing r^(4a), with O(log s) bits, and the candidate label set r^a is polynomial in s. No tensor-entry oracle is needed here. The procedure supplies every load≤M/D_arr+sqrt(2M Delta).

Rounding the maximal load to a multiple of L_packet gives H_pad≤3M/D_arr because M≥2D_arr² Delta and M≥L_packet D_arr. For a fixed unordered symbol pair in each coordinate, its2^(a') orientation labels each supply L_packet/2^(a') slots per packet. H_pad divisible by L_packet makes this grouping exact. It gives≤3M/L_packet packets and≤3M/r ports on EACH side for any fixed group symbol. Hence each child has≤6M/r=3M/32<M/8 edges. Padding slots have no ports and do not create summation variables or count multiplicity.

## 5. Independently derive precision(D.11)

Assume the neighboring agents' recovery identity and its prescribed increment

    p_t=p+8h_taper D_t+8M(a+1), h_taper≤4M/u.

At depth d the preceding increments are each at most s times a fixed polynomial in lambda times2^(a_(d-1)); there are O_C(log lambda) depths. The root P0≤Cs has the same bound. Thus

    p≤s*lambda^O_C(1)*2^(a_(d-1)).                 (A)

For every retained level i<u, D_t=2^(a_d-i)≥2^(a_(d-1)+u). Since M>H≥s/sqrt(lambda),

    p / (M D_t/u)
       ≤lambda^O_C(1)*u*sqrt(lambda)/2^u = o(1).

Similarly 8M(a+1)/(M D_t/u)≤8u(a+1)/D_t=o(1). The remaining increment is≤32M D_t/u directly. This proves p_t=O_C(M D_t/u) uniformly, including inherited precision and not only the new local loss. The cumulative a_d, rather than resetting it to2u_d each time, is what supplies2^u beyond the inherited scale.

All precisions are polynomial in s: (A) uses a_d≤4epsilon lambda and polynomial-log factors. Coordinates in the coefficient extension and V-truncation therefore remain polynomial-bit. This also covers leaf precisions. No bit-cost factor exponential in p is required by the stated exact arithmetic.

## 6. Enumeration and total time, with high-arity evaluators charged

Given the mode divisibility/count statements(D.13)-(D.14), the generating product gives

    log(number tuples)≤theta p_t+(6M/D_t)*sum_(j≥1)-log(1-exp(-theta j))
                      ≤theta p_t+O(M/(D_t theta)).

Taking theta=Theta(sqrt(M/(D_t p_t))) yields O(sqrt(M p_t/D_t))=O_C(M/sqrt u). Weight values below p_t and variables per weight are polynomial in s, so tuple descriptions and a depth-first enumeration stack have polynomial size. Every partial feasible tuple extends by zeros, bounding traversal overhead by a polynomial factor per complete tuple.

At depth d the exponential branching contribution is at most

    exp[O_C((s/sqrt(lambda))*(sqrt(2)/8)^d)].

Interpolation nodes, interpolation values, group count and tensor descriptions supply only polynomial-in-s factors per call. Their product over O_C(log lambda) depths contributes exp(O_C(lambda log lambda)), which is absorbed in exp(O_C(s/sqrt(lambda))). Summing the geometric exponent gives the asserted total call bound.

At a leaf, at most2^H assignments are enumerated. Each uses polynomially many original or created tensor ENTRY evaluations. Original entries cost (s+D_len)^b*2^(A s^.9) by hypothesis. A new packet entry expands≤L_packet affine factors with polynomially many choices each, costing exp(O(L_packet log s)) times polynomial arithmetic. Since L_packet≤s^.001, this is below exp(O(s^.9)). Creation precisions are polynomial, and old descriptions are shared rather than nested. Therefore

    leaf time≤poly(s+D_len)*exp[O_C(H)+O_(C,A)(s^.9)]
             ≤poly(s+D_len)*exp[O_(C,A)(s/sqrt(lambda))].

The same factor per generated call/term is absorbed in the total call count. The exponent of the polynomial description factor stays fixed: it is not raised once per recursion level, because work is bounded per node and summed over nodes.

## 7. Polynomial space and uniform fallback

Depth-first processing stores one sum over mode tuples and one product over groups, one call's polynomially many interpolation/Taylor values, current indices and immutable packet descriptions. Ring elements have e*ell*p polynomial bits. There are only O_C(log lambda) active stack levels. Rational interpolation recovery uses polynomially many rational factors with polynomial-bit numerators/denominators; their common denominator remains polynomial-bit even if constructed as their product. This agrees with the space bound, conditional on the separately audited recovery formula.

The construction can check u≥1, its integer degree/count bounds, field-point availability and(D.6); a failed check triggers direct enumeration. For fixed C,A,b these failures occur only below a finite root-size threshold by the inequalities above. Their contribution is absorbed by the theorem's fixed constants, and input description length is still paid polynomially. A valid fallback must not truncate the recursion or guess tensor values. Fractional comparisons can be checked with integer powers, e.g. u^5≥lambda^4; Delta is a computable ceiling tenth root of s^9. No uncomputable asymptotic threshold is needed for correctness.

## 8. Does the actual high-arity factor network fit this scope?

YES, as far as the assigned proof interface is concerned. It is not merely a bounded-arity SAT application: original macro-FFT vertex degree O(L_bits^(3/4))≤s^.9 at s=1024L_bits, and its deterministic 0/1 entry verifier is polynomial-time/space. Both satisfy the hypotheses used in packing, leaf evaluation and immutable lifts above. No step in these assigned parts secretly substitutes a constant-size truth table for an implicit high-arity entry. The auxiliary coefficient extension and increasing p require no higher-precision version of that Boolean predicate; its initial0/1 output is canonically lifted.

The correct conclusion is conditional on the ENTIRE D.1 contraction identity and recovery/mode proofs, not merely on the earlier Lean theorem for the n(log log n)^2/sqrt(log n) SAT endpoint. This audit finds no complexity/interface obstruction to applying D.1 to the O(L_bits)-wire factor network. It does not independently settle the other agents' algebraic obligations, establish polynomial-time factoring, or certify that the present D.1 statement is formalized.

## 9. Stronger fallback for OUR network: main shared-summary lemmas suffice

This is a separate positive construction, derived after the D.1 audit. It does NOT use TheoremD.1, tapered2-adic Hermite recovery, or modes. It applies Proposition3.4 and Lemma4.7 directly to the macro-FFT network, with an explicit extension of the factor-evaluation/bit-cost argument. Its correctness depends on those main lemmas as stated; it is not inferred merely from the formal SAT endpoint.

### 9.1 Exact tensor-to-polynomial input

Let n be the ACTUAL number of Boolean bit-edges of the bipartite factor network, so n=Theta(L_bits). Every edge variable belongs to exactly two vertex factors: b=2 and total incidence M_inc=2n. The largest scope w is O(n^(3/4)). Isolated scalar vertices can be multiplied out first.

For each0/1 tensor entry predicate T_f on its w_f ports, define the unique Boolean multilinear extension OVER Q by

    Phi_f(Y)=sum_(eta in{0,1}^w_f) T_f(eta)
                   prod_v [eta_v Y_v+(1-eta_v)(1-Y_v)].     (B)

Its values on Boolean assignments are exactly the tensor entries, degree≤w_f. Therefore the total degree in SEPARATE incidence variables is d≤sum_f w_f=2n, satisfying(3.2). The total sum/product is the exact network contraction. This is not a characteristic-two lift and loses no integer carries.

The explicit2^w_f table need not be emitted: evaluate(B) at arbitrary truncated rational input jets by streaming its Boolean eta and the given polynomial-time entry verifier. This takes2^O(w) polynomial(n+description) time and polynomial space per factor evaluation, not2^(wJ). Each summand only multiplies w_f supplied length-J jets.

### 9.2 Lemma4.7 hypotheses hold beyond the polylog-scope application

Set lambda=ceil(log2 n), nu=ceil(log2 lambda). Copy the NUMERICAL parameters of Lemma4.8 with beta=1,

    r=floor(sqrt(lambda)/nu²), Q=floor(lambda/(128nu)),
    R=4ceil(sqrt(lambda)), tau=1/(r lambda), D=r^(2Q).

Do NOT apply Lemma4.8's polylog-w hypothesis. Instead verify Lemma4.7 itself. Since log2 r≤nu/2,

    D≤2^(lambda/128), D²≤(2n)^(1/64).

Consequently, with w≤C_w n^(3/4),

    2(b+w)D²=O(n^(3/4+1/64))=O(n^(49/64))<2n=M_inc

for all sufficiently large n. Also2Qr² is polylogarithmic and eventually≤n. This is the ONLY place where w enters the construction quantitatively beyond polynomial bookkeeping/evaluation. Lemma4.5 explicitly proves that its collision variance is M_inc(b+w), and its construction time is polynomial in w, rather than exponential in w. All factors sharing one vertex are already counted by that bound.

The binomial-tail requirement uses epsilon=tau/(r b)=1/(2r²lambda), independent of w. Center the R-term interval at floor(Q(r-1)/(2r)) as in the source. For R≥32 and6R≤Q it contains the mean's R/4-neighborhood. Hoeffding gives tail≤2exp(-R²/(8Q))≤2exp(-256nu), which is eventually smaller than1/(2r²lambda). Alternatively the precise tail can be checked as a rational number with denominator(2r)^Q, requiring only polynomial-log bit arithmetic. The large value of w does not alter that test.

Thus Lemma4.7 supplies the actual replacement rows/partitions/measurements in polynomial(n+description) time. Its rational construction depends only on the scopes, NOT on explicitly listing Phi_f's exponential truth table. The number of scoped incidences is only2n.

### 9.3 Count and evaluator exponents

Use Proposition3.4 over A=Q. With d≤2n, its Taylor order satisfies q=floor(dR/Q)=O(n nu/sqrt(lambda)). The three counting exponents satisfy

    (R/Q)log(2Q/R)=O(nu²/sqrt(lambda)),
    tau log(2D+1)=O(1/r)=O(nu²/sqrt(lambda)),
    1/r=O(nu²/sqrt(lambda)).

It follows that vector/factor evaluation count is polynomial times2^O(n nu²/sqrt(lambda)). Multiplying by the streaming factor evaluator cost gives

    poly(n+description)*2^[O(n nu²/sqrt(lambda))+O(w)]
      =poly(n+description)*2^O(n(loglog n)²/sqrt(log n)).   (C)

The w=O(n^(3/4)) term is strictly lower order. There is no assumption that each tensor has constant-size scope or that its entire multilinear coefficient array is supplied.

### 9.4 Rational coefficient and denominator audit

Lemma4.6 gives a COMMON denominator dden=(R-1)!Q! for the replacement rows, with total coefficient absolute sum after scaling≤2^O(QlogQ). Shifting T to t+z (t≤Q) and inserting Boolean x or1_U retains coefficient bit height O(QlogQ), since R<Q. The same bound holds for1 minus an input. Hence a factor evaluation of(B) on w_f such inputs has denominator dividing dden^(w_f) and numerator height O(w_f QlogQ): multiply w_f factors and sum2^w_f terms, adding only w_f bits to the height.

Every group product and then the product over all groups can use the fixed global denominator dden^(2n). Its bit length is O(nQlogQ), polynomial in n. Sums over exponentially many Boolean assignments, measurement tuples or Möbius pairs add only the logarithm of their number, O(poly(n)), to numerator height. They do NOT require multiplying a different denominator for each enumerated term. An implementation can explicitly rescale to the fixed common denominator; reduced fractions give the same bound because their denominators divide it.

The final rational Hermite system has QJ=O(nR+Q) rows. Its entries are binomial coefficients and powers of integers≤Q, with polynomial bit length. Standard exact rational inversion has polynomial bit-height by determinant bounds; equivalently use the source's fixed Hermite formula. Its common denominator is polynomial-bit. The reconstructed value is the integer contraction, with no approximation or modular rounding. This supplies the bit-cost obligation that Proposition3.4 leaves to its application.

### 9.5 Space, guard, and factor consequence

Stream eta in(B), Möbius pairs(E,U), measurement tuples, and local group assignments. Store only their polynomial-bit indices, one factor jet, group-product jets and the polynomially many Hermite data. Factor-entry verifiers use polynomial space. Thus space is polynomial(n+description), even though time includes2^w.

All numerical hypotheses (including r≥2, R<Q, balance and the exact rational tail) are explicitly testable. For the fixed scope constant C_w only finitely many n fail; use direct network summation on those inputs. The fallback is honest exact enumeration and preserves polynomial space. No threshold oracle is needed.

Since our verified macro-FFT network has n=Theta(L_bits), (C) gives factor counting and O(L_bits)-query witness self-reduction in

    2^O(L_bits (loglog L_bits)²/sqrt(log L_bits))

bit operations and polynomial space. This is2^o(L_bits), hence eventually below2^(L_bits/6), WITHOUT TheoremD.1. Fixing an input bit is implemented in an existing local validity predicate, so it introduces no new variable, factor incidence, or high-degree port. The same uniform scope/degree/time analysis holds at every conditional-count query.

This fallback is slower than the claimed D.1 sqrt-log rate but already meets the original asymptotic sixth-rate target IF the generic shared-summary and row-construction lemmas are sound and available for this instantiation. It isolates a substantially earlier proof/formalization dependency: Proposition3.4 + Lemma4.7 + the explicit multilinear/evaluator/bit-height lift above. An earlier formal theorem only for k-SAT must still be connected to those generic interfaces; its endpoint name alone is not a proof of this macrovertex application.
