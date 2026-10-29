# Independent reconstruction of D.4.5–D.4.6

26 October 2026. Active dependency audit, scratch only. Source: supplied ETH paper [PDF](/tmp/semiprime-eth-paper-20261026/paper.pdf), printed pp62–64, with D.3 packet hypotheses and D.4.1 creation-time convention. **Disposition: the local mode expansion, weighted truncation, exact child identity and implicit-entry cost pass this audit. No essential flaw or exponent-changing repair found in these sections.** This is not a claim to have independently proved every other part of Theorem D.1.

The sparse-incidence degree-cap typo in EQUATION(D.1), §D.3, is separate from THEOREM D.1's contraction proof in §D.4. It is not used below or in the proposed direct macro-FFT application.

## 1. Reconstruct the crossing expansion, including valuations and signs

Fix one packet of L=2^a slots, t!=0 with i=v2(t), alpha=2^(a+1), and T=t+alpha*zeta. Let C(T)=product_(r=-L)^(L-1)(T-r), and C0'=C'(0). LemmaD.4 supplies coefficientwise divisibility

    v2(C(t+alpha*z)/C0')>=a+1.

This is an identity in the unramified coefficient algebra, not a claim that a numerical even denominator may be inverted. It follows by dividing the known powers of two out of the individual integer factors before any unit inversion.

In the selected packet coordinate, the row and column group labels agree exactly when their slot bits differ, unless the two packet symbols already agree (then all entries are local). A nonzero W_xy(t) requires y-x=t, which flips bit i. Thus W(t) is local. This only requires locality; the surviving value C'(t)/C'(0) is generally a unit, not necessarily one.

For a crossing tile write y=y0+2^(i+1)j and d=T-y0+x. Crossing means x and y0 have the SAME bit i. Hence v2(t-y0+x)<=i, and adding alpha*zeta does not change that valuation. Write d=2^v d_unit, v<=i, with d_unit an actual unit. Then

    1/(d-2^(i+1)j)
      =sum_(k>=0) (2^(i+1))^k j^k/d^(k+1).

The sign is POSITIVE. Multiplying by C(T)/C0' gives coefficient valuation at least

    a+1-v+k*(i+1-v)>=k+1.                        (1)

This also proves that every coefficient is integral. The term of mode weight k+1>=p_t vanishes modulo2^p_t; the geometric tail does too. No inverse of the nonunit d is taken numerically: remove its known2^v, cancel the resulting powers against the numerator, and invert only d_unit. This reconstruction gives exactly(D.12), including its strict cutoff k+1<p_t.

The statement holds for zeta in the UNRAMIFIED EXTENSION, not merely scalar integers. The constant term of d_unit modulo2 is nonzero, so its unit status is unchanged by the extension coordinate zeta. Multiplication/truncation by the independent V marker cannot decrease any coordinatewise power-of-two divisibility.

## 2. One source and one target really suffice

A tile fixes its column bit i, hence its column group. Every crossing row to that tile belongs to the OTHER group in this packet coordinate pair. Therefore the mode

    Z_(packet,y0,k) -> L_Z(X)=sum_(real y in tile) j^k X_y

has exactly one source and one target, independent of which targeted row uses it. Its coefficient varies with row x, which is allowed and retained. Tiles with no real column give L_Z=0; exponent zero means0^0=1 here, and positive exponents give zero. A target group with no real row has only the constant coefficient of its empty row product.

There are at most2^(i+1) tiles in each packet and at most3M/L packets, so each weight has <=6M/D variables, D=L/2^i. This bound counts actual packet/tile labels rather than distinct numerical mode values; no deduplication assumption is needed.

In every product of the affine l_Y row factors, a monomial Z^beta has coefficient divisible by2^(sum w_Z beta_Z), by(1). Local coefficients are integral. Substituting the L_Z, multiplying old tensors and summing bits cannot undo that divisibility, since none of those operations introduces an even-denominator inverse. Thus the TOTAL weight cutoff in(D.14) is exact; separate per-variable truncation would not be the same algorithm.

## 3. Count and enumerate exactly the weighted tuples

Let n_w<=6M/D be the number of variables of weight w. For theta>0 the number of tuples of weight<p_t is bounded by

    exp(theta*p_t)*product_(w>=1)(1-exp(-theta*w))^(-n_w).

The logarithm is at most theta*p_t+C*M/(D*theta), since sum_w-log(1-exp(-theta*w))<=pi²/(6theta). Taking theta proportional to sqrt(M/(D*p_t)) gives exp(O(sqrt(M*p_t/D))). The square root in the source's choice of theta is present in the PDF/raw text; it is not the unsquared ratio M/(D*p_t).

Using the independently stated precision bound p_t=O_C(MD/u) yields exp(O_C(M/sqrt u)). The number of mode labels and each exponent's bit length are polynomial in global s. A depth-first enumeration that chooses0..floor(remaining_budget/w) for each variable has no failed feasible prefix: every such prefix extends by zeros. Its visited prefixes are bounded by the number of completed tuples times the polynomial number of mode labels. Thus polynomial delay and polynomial space are justified, rather than assumed from the mere existence of a generating product.

This audit uses the precision bound as supplied by D.4.4/D.11. It does not replace the separate audit of tapered Hermite recovery.

## 4. Reconstruct D.16 as finite Fubini and coefficient extraction

The vertex labeling of LemmaD.3 is crucial: ALL ports of an OLD tensor belong to its vertex's group. If only ports had independently chosen labels, this factorization could fail. The paper labels vertices, so no old tensor straddles two child groups.

For fixed global beta, group g's packet factor is:

1. the coefficient in its row-factor product for every mode TARGETED at g;
2. multiplied by L_Z(X)^(beta_Z) for every mode SOURCED at g.

Every mode exponent is extracted exactly once and substituted exactly once. Original row and column tensors remain separate old vertices, together with their original ordered ports; they do not disappear into a mode coefficient. After fixing beta the remaining variables separate into groupwise independent bit sets. Expanding the affine factors, then distributing the old tensor products and summing these bit sets, gives precisely the product of child contractions in(D.16). The sum over beta with weight<p_t is exact by §2. There is no missing binomial coefficient: coefficient extraction from the original affine product already includes all choices giving that monomial.

The argument is packetwise but allows an old tensor to correlate several packets, since all its ports still stay in ONE child group. Empty tiles, empty target sets, unused slots and isolated old scalar vertices obey the stated empty-product conventions and lose no assignments.

Each child has the old real ports of one group, at most6M/64<M/8. A new packet vertex has at most2L ports. Old degrees remain unchanged. Thus the claimed edge reduction is compatible with actual tensor arities; a tile mode is a substituted polynomial, not an additional uncounted Boolean wire.

## 5. Implicit entries and creation-time lifting

At a fixed packet-entry assignment all local X,Y bits are supplied. Each row factor is an affine polynomial in polynomially many formal modes. Enumerating one term per row factor uses at most poly(s)^L=exp(O(L log s)) choices. One may keep only the current exponent vector, product and modular accumulator, checking the prescribed beta on each choice. This is polynomial space. Each L_Z(X)^beta is acquired by modular summation and repeated squaring with polynomial-bit exponents. This is an explicit entry evaluator, not a dense coefficient table hidden in its description.

A NEW packet tensor calls no OLD tensor entry evaluator inside that expansion. The old tensors are retained as separate vertices. Its description contains only current local kernel/packet parameters, beta, interpolation value and creation precision. At later levels an old packet vertex is evaluated by this own creation-time recipe and reduced at its recorded precision; its coordinate residues are then lifted as those SAME integers. Hence entry routines are not recursively composed with the network depth. The original macro-DFT predicates, if used as initial tensors, likewise remain separate original entry programs.

Canonical lifting is not multiplicative, and the proof does not need it to be. At a call of precision p, it first fixes entrywise representatives. Its deformed contraction F(T) is built from those fixed entries and agrees with the desired contraction modulo2^p at T=0. The children are created modulo2^p_t and contract to F(t+alpha*zeta) modulo that precision by D.16. Their own recursive deformations may use different higher-precision polynomial values, but they compute only that specified residue; this is sufficient for the parent's precision-recovery invariant. Re-evaluating an old defining formula at higher precision instead of its creation-time representative would be a DIFFERENT, unjustified protocol.

All coefficient arrays have polynomial rank/precision in s. With L<=s^(1/1000), exp(O(L log s)) fits the theorem's exp(O(s^(9/10))) local-entry allowance. This conclusion depends on the already stated polynomial precision bound and immutable shared descriptions, both explicitly used, not on counting one extension operation as constant bit time.

## 6. Exact independent controls

`check_modes.py --output PATH` is a standard-library tiny algebra checker. Its ring is(Z/2^p)[u]/(u²+u+1), a nontrivial unramified extension, so the test is not confined to integer interpolation values. It computes W_xy DIRECTLY by the omitted-factor polynomial, and computes crossing expansions separately by exact rational power cancellation and odd-unit inversion.

Recorded `mode-controls.json`: **PASS, 288 crossing-entry comparisons and six complete contraction fixtures.** The entry checks cover positive and negative t, valuations0 and1, scalar and extension-valued zeta (including zero), and several precisions. The complete fixtures compare the direct sum over ALL real X,Y assignments against the product of the actual child coefficient/substitution contractions. They include correlated two-port tensors, fixed-assignment probes, missing slots, empty source tiles and a group with no target rows. The mode construction retains the0^0 convention. Discarding all crossing modes changes the answers in the recorded negative controls, so these are not all tests of an identically local/zero case.

A small separate control exhibits nonmultiplicativity of creation-time lifts (7*2 modulo8 gives6, whereas their lifted product modulo128 gives14), while contracting canonical entrywise lifts still reduces to the original contraction modulo8. It illustrates, rather than substitutes for, the invariant proved in §5.

The packet size in these controls is four and does NOT meet the asymptotic packing inequalities of D.4.2; they test the exact LOCAL algebra only. The control code uses naive finite expansions and does not implement the theorem's asymptotic contraction algorithm or the macro-FFT factorer. No native factoring-success campaign was run.

## Conclusion

These sections provide a real exact contraction, not a symbolic low-rank analogy: divisibility truncates modes, source/target separation factors each retained term, and the child entries have directly bounded evaluators with stable lifts. No essential flaw was found in D.4.5–D.4.6. The conditional macro-FFT consequence still depends on the other parts of TheoremD.1 (packing, local integrality, precision recovery and global recursion) and the independently verified O(L)-wire multiplication encoding; this report certifies neither dependency by implication alone.
