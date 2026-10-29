# Appendix D tensor counting and Appendix B arithmetic: transfer audit

26 October 2026. Requested paper study only. Read supplied [paper.pdf](https://raw.githubusercontent.com/openai/math/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf), printed pp47–50 and53–64, together with main Lemma5.2/§5.3, printed pp37–38. The factorization goal remains PAUSED. No repository edits or new factoring algorithm. This note audits stated interfaces and finite identities; it does not independently certify the entire paper's claimed ETH refutation.

**Result.** The paper supplies a concrete recursive finite contraction identity: deform Boolean wire equality by a Cauchy polynomial, expand only modes that survive a TWO-ADIC precision budget, and contract smaller packet networks. Its cost depends on actual wire count and entry-evaluator bounds, not only the number of named indices. A sparse-system consequence extends to suitable known small characteristic-two extensions after charging coordinates. The direct native odd-modulus residue encoding audited in §6 supplies neither that valuation truncation nor a small Boolean circuit/low-degree sparse system. A subsequently supplied constant-stage MACRO-FFT encoding is different: §7 checks that it meets the standalone tensor theorem's interface and yields a conditional subexponential-in-bitlength factoring corollary. That does not acquire the original long residue numerically or resume the paused goal.

## 1. Exact theorem interface: it is not uniform in arbitrary local width

TheoremD.1, printed p53, fixes constants C,A,b. The input is a BIPARTITE Boolean-edge tensor network with:

* at most Cs actual one-bit wires and maximum vertex degree <=ceil(s^(9/10));
* polynomially many vertices and total description length L;
* entries in (Z/2^P0)[V]/V^ell, with 1<=P0,ell<=Cs;
* a uniform entry evaluator of time(s+L)^b*2^(A s^(9/10)) and space(s+L)^b.

It claims deterministic contraction in(s+L)^O(1)*2^O(s/sqrt(log s)) bit operations and polynomial space, with constants depending on those FIXED bounds. This is not a polynomial-time contraction theorem, a treewidth-only bound, or a theorem allowing an arbitrary degree-s tensor for free. Its description length may include implicit tensor programs, but the arity and entry time are still separately constrained.

For fixed clause density the equality-tree encoding has O_k(n+m) wires and bounded degree; the output is computed modulo2^(n+1), enough to recover the integer count in[0,2^n]. For unrestricted density, LemmaD.2 (pp54–57) first fixes high-incidence variables, then uses degree-limited incidence monomials. Its k,c are fixed constants: at most cn equations, degree<=k, each a list of at most(log n)^c monomials over F2. Nothing in that statement permits k to grow with native J or the bit size without redoing the constants and input construction.

## 2. What the recursive contraction actually counts

D.4, printed pp57–64, builds an unramified two-adic coefficient extension of rank e=4ceil(log2 s), with residue field F_(2^e). Its binary-coordinate lifts give polynomially many interpolation points with UNIT differences. Canonical lifts are entrywise and retain creation-time representatives; the paper explicitly does not assume lifting preserves multiplication.

LemmaD.3 packs M wires into <=3M/L_packet packets of L_packet=2^a slots. A conditional-expectation labeling balances each group to <=3M/64 ports. This is paid polynomial-time graph processing, not a supplied small separator. The Cauchy deformation is

    W_xy(T)=C(T)/(C'(0)*(T-(y-x))),
    C(T)=product_(t=-L_packet)^(L_packet-1)(T-t).    (D.7)

The displayed denominator factor cancels polynomially. W(0)=I, so replacing wire equality by its multilinear extension gives the finite polynomial F(T) in(D.8), with degree<=M(2L_packet-1) and F(0) the exact original contraction. Both row and column Boolean assignments occur in this expression; their potentially exponential sum is what recursion evaluates, not an already supplied coefficient array.

At a nonzero node t of valuation i, W(t) couples only equal groups. Crossing terms at t+2^(a+1)z have the tile expansion(D.12). A mode of weight j has coefficients divisible by2^j. Modulo2^p_t, ONLY exponent tuples with sum_Z w_Z beta_Z<p_t can survive. There are <=6M/D_t variables of each weight, D_t=L_packet/2^i; their weighted-partition count is

    exp(O(sqrt(M*p_t/D_t)))=exp(O(M/sqrt u)).       (D.15)

This is NOT the full Cartesian box product of independent degree bounds. The actual weighted budget is essential. Each surviving tuple factors the evaluation into64 child contractions, each with <M/8 wires, by the explicit finite identity(D.16). New packet entries are computed by expanding at most L_packet affine factors; their cost is charged as exp(O(L_packet log s)), fitting the theorem's entry bound.

Tapered Hermite recovery, LemmaD.5, uses q_t=ceil(3M/u)*max(0,u-i), not a common multiplicity at every node. The precision p_t=p+8ceil(3M/u)D_t+8M(a+1) covers the actual two-adic losses. It reconstructs F(0) from LOCAL evaluation polynomials; the local polynomials themselves are interpolated at polynomially many residue-distinct extension points. Thus coefficient recovery, larger precision and field extension rank are all charged. M decreases by8, u decreases by2, and the depth exponents sum geometrically to O(s/sqrt(log s)). The finite identity does not say a generic polynomial's selected coefficient is acquired from its short descriptor.

## 3. Actual incidence-box compression and a degree-cap discrepancy

In LemmaD.2 the selected incidence set is indexed by counts d_gh between test and variable groups. For each count array, the network uses sum_gh ceil(log2 binom(N_gh,d_gh)) Boolean wires. The proof's bound is J_groups²+K_degree*log2(e(N_inc+K_degree)/K_degree), not the size of all incidence subsets. Invalid indices have tensor value zero. Counting EACH array is necessary; its total number contributes2^O_k,c(sqrt n log n). The bounds on total degree and incidence list length supply the claimed O_k,c(n log log n) wire budget.

There is a literal degree-cap mismatch in the supplied text, communicated to the parent. Main Lemma5.2, p37, correctly gives degree d_*(m_test+2(ell-1)), and main(5.5), p37, gives d_H=kR(m_test+2(ell-1)). In SECTION D.3 (the proof of LEMMA D.2), p55, the preceding coefficient bound is k(1+2j), but(D.1) prints

    K_degree=k*a+2(ell-1),

where direct summation yields k*a+2k(ell-1). AppendixB.2, p48, similarly prints d_H=kR*m_test+2(ell-1), inconsistent with main(5.5). As written these smaller caps need not include every retained term; a term cap is a correctness condition, not just an estimate. Replacing them by the main lemma's bounds preserves K_degree=O_k,c(n) and the polynomial arithmetic bounds for fixed k,c. A direct nonzero incidence-polynomial control confirms that this is not just a loose summation estimate. Take n=a=20,k=3,ell=p=21, with three disjoint cubic monomials per test. For every ell>=2 the first two h-adic coefficients are e0=1-Y,e1=2Y-1. Choose the degree-nine monomial in ten test fibres at V-degree1 and a degree-three monomial in the other ten fibres at V-degree0. Its V^10 coefficient is 12^10*(-1)^10, of two-adic valuation20, so it survives modulo2^21. Its incidence degree120 exceeds the printed cap100. Distinct test fibres have disjoint incidence indeterminates, even if their underlying Boolean scopes coincide. This disproves that literal polynomial degree bound; it does not assert that one isolated omitted monomial alone changes the final Boolean count. The corrected main-lemma cap180 includes it.

This concerns EQUATION (D.1), not THEOREM D.1: the standalone tensor-contraction theorem is stated in §D.1 and proved in §D.4 without this sparse-incidence encoding. The repair is k*(a+2*(ell-1)); it preserves the fixed-k asymptotic and is not a claimed refutation of the standalone contraction theorem or the full paper. No source file was edited.

## 4. Appendix B: exponential summation does not imply exponential coefficient bits

AppendixB, printed pp47–50, uses ONE fixed denominator at each aggregation stage. Replacement rows have denominator d_den=(R-1)!Q!, equation lifts use Delta=d_den^k and Gamma=Delta^(2ell-1), and every full contribution is padded to Omega=Gamma^m_test. Adding M_* terms increases the numerator bit bound by log M_*, rather than multiplying denominators anew. This is the exact useful arithmetic principle; it does not reduce the NUMBER of terms or the box count.

The explicit measurement enumeration is bounded by

    M_*<=3^n*(2D+1)^c_rows, c_rows<=2tau n.

Those measurement dimensions cannot be dropped when transporting the algorithm to another problem. Arrays live in Q[z,V]/(z^J,V^ell), so each has J*ell rational coordinates, all counted. The final Hermite constant coefficient is obtained by the common integer denominator Omega and two fraction-free integer determinants(B.1); polynomial minor bounds control numerator lengths. Only a selected output coefficient is used, but its whole prescribed Taylor input is still acquired by the earlier algorithm. No arbitrary nonunit is inverted modulo a composite modulus.

This fixed-denominator technique can be reused in a RATIONAL lift of our finite identities. It does not by itself accelerate the modular long query: its base-ring arithmetic already had fixed O(log N)-bit residues and explicitly bounded constant-rank jets. The missing work there is evaluation/contraction, not unnoticed denominator blowup.

## 5. A precise known-field-extension consequence

A conditional extension of the sparse-system interface is elementary, not an additional paper theorem. Suppose equations over a KNOWN F_(2^e) have r field variables, a<=c*r equations, fixed degree k, and S listed monomials each. Expand every variable in a supplied F2 basis. There are n=r*e Boolean variables and at most a*e<=c*n coordinate equations. A degree-k field monomial expands into at most O(e^k) coordinate monomials per output coordinate after its known structure constants are acquired. The count is preserved bijectively.

Therefore if S*e^k<=(log n)^C for FIXED C, and the basis/multiplication constants are constructed within the charged input budget, LemmaD.2 applies with its actual n and constants k,c,C. For example e and S polylogarithmic in n fit after changing the fixed exponent. It does not allow a large extension coordinate count to be hidden in one field operation, nor does it apply automatically to odd characteristic, Z/N, or an unknown prime factor field. The two-adic rank-O(log s) extension in D.4 has precisely its explicit limited role.

## 6. Test the native query bridge, with bit and width costs

There are two concrete attempted embeddings.

**Coefficient/product network.** Make the J*h physical leaves into scalar factors, or expand their first jet as a marked cofactor network. This has J*h acquired factors/ports unless another exact compressed local representation is constructed. Naming a single vertex whose entry is the long norm simply makes the unacquired query its entry evaluator. The contraction theorem does not pay that evaluator. In particular a constant number of first-jet markers does not imply a constant number of Boolean wires or low-degree equation factors.

**Count candidate collisions.** A Boolean witness may contain only O(log J+log h) index bits; a modular power and gcd predicate can test an ACTUAL candidate. But putting this entire predicate in one tensor gives a vertex of that full degree, violating the s^(9/10) cap if one takes s proportional to its index-bit count. Raising s to the needed power worsens the exponent. A gate-by-gate Boolean encoding restores bounded local degree but charges all multiplication, modular reduction, lookup and gcd gates as wires/auxiliary variables. The selected-row lookup can itself carry J coefficients; on the original unselected Gauss bank one must instead explicitly compile its arithmetic row generator. Neither cheap construction is supplied by AppendixD.

Quantitatively let L_N=ceil(log2 N). If an actual bounded-density fixed-width Boolean circuit/CNF with n=O(L_N) variables were constructed for the required witnessed event, the paper's claimed fixed-density bound2^O(n/sqrt(log n)) would be N^o(1). That WOULD be a useful conditional bridge, with the unknown constant asymptotically harmless. It is not proved here. A merely n=L_N*log L_N size encoding gives exponent O(L_N*sqrt(log L_N)), which does not beat N^(1/6); polynomial(L_N) encodings give still less. More generally all constants and the actual n must be charged, not replaced by the number of named arithmetic variables. For a soft-K guarantee one needs the full exponent plus polynomial factors <=(1/6)log2 N+O(log log N), or a truly smaller asymptotic exponent.

There is also a RING mismatch specific to the proposed contraction shortcut. D.12–D.16 discard crossing monomials because powers of2 vanish modulo2^p. In the native odd ring, 2 is a UNIT, so those monomials do not vanish. There is no unital map Z/N -> Z/2^p for odd N. Computing an exact integer lift of the original product would require precision proportional to its output bit bound, generally J*h*log N, not log N. Counting a Boolean gcd predicate has a small integer output, but then its circuit/wire cost above is the outstanding input. Introducing a formal nilpotent marker cannot simply substitute for2: the tile geometric expansion and the Hermite valuation losses use the actual arithmetic valuations of integer differences t-y+x. That exact replacement would need a new proved deformation, not just a renamed coefficient ring.

## Conclusion

The concrete reusable idea is to deform a compatible identification kernel so that a PRECISION-weighted mode expansion splits it into smaller contractions, while a tapered interpolation recovers the selected scalar. The direct-residue limitations in §6 are not a general prohibition on implicit arithmetic tensors; the subsequently supplied macro-FFT construction is audited separately below. AppendixB separately explains why enormous exact sums can have manageable numerator bit length. Neither supplies the native valuation, low-degree sparse encoding or actual low-wire tensor needed for our modular residue. The degree-cap discrepancy above should be resolved in any literal implementation of the paper's counting reduction. No factoring rate, universal-in-k consequence or resumed goal work is claimed.


## 7. Subsequent macro-FFT bridge: adversarial audit of the tensor input interface

The parent supplied a DIFFERENT construction: integer multiplication through a constant number of coarsened DFT stages over a public Fermat ring, with O(L_N) Boolean wires, word length O(sqrt(L_N)), macro arity O(L_N^(1/4)) words, and polynomial-time local predicates. This supplies the specific encoding missing from §6; the following is an interface audit conditional on its asserted arithmetic correctness and wire ledger. It does not use the sparse zero-system theorem, LemmaD.2, or the erroneous equation(D.1) cap.

**Implicit tables are expressly permitted.** A macro tensor can be the0/1 predicate that its output words equal the direct DFT of its input words, with known twiddles and modulus. It need not list2^(arity) entries. A naive direct DFT of O(L_N^(1/4)) words entails O(L_N^(1/2)) word products/sums. Each word has O(sqrt(L_N)) bits, and ordinary integer modular arithmetic is polynomial time/space in L_N. Thus every possible port assignment has a uniform polynomial-time entry check, meeting fixed constants A,b in TheoremD.1. This is true without a fast implementation of that local DFT.

**The actual port degree fits.** Counting input AND output bits gives O(L_N^(3/4)) incident Boolean edges per macro. At s=1024L_N this is below ceil(s^(9/10)) beyond an absolute finite threshold; the usual bounded exceptional inputs can be handled directly. A word is not one Boolean edge, but after charging every bit the claimed degree still fits. Internal dense DFT linear combinations do not require additional external wires: they are computed by the allowed local entry routine. The central remaining construction obligation is genuinely O(L_N) TOTAL wires, using a fixed number of macro stages, rather than the uncoarsened O(L_N log L_N) bit-wire circuit. The parent construction specifically asserts that obligation. Descriptions/twiddles and graph construction must be uniform polynomial size/time, which the stated macro arithmetic permits.

**No field or ring embedding is needed.** The tensor COEFFICIENT ring is(Z/2^(2L_N+1)), ell=1. Its entries are the ordinary integers0 or1. The public odd Fermat ring is used solely INSIDE an entry predicate to check a word relation. Its values are not embedded as coefficient-ring elements, so the odd-modulus obstruction in §6 does not apply. The theorem requires neither a prime Fermat modulus, a field square root, nor a supplied factorization of that modulus. The multiplication encoding must of course independently verify its root-of-unity/DFT arithmetic and carry reconstruction, as the companion authors are doing; those are arithmetic correctness obligations, not additional tensor theorem hypotheses.

**Representations and count precision matter.** Each local predicate must reject out-of-range word encodings or otherwise use a canonical representation so that an input pair has exactly one consistent internal assignment. All copies/fanouts must be explicitly bounded-degree equality tensors. Any nonbipartite graph may be subdivided by a binary equality vertex per edge, preserving the contraction and increasing wires by only a factor two. The theorem explicitly allows parallel edges with distinct ordered ports. With functional internal stages and at most2L_N freely chosen factor-input bits, the total count is <=2^(2L_N). Thus P0=2L_N+1 is sufficient, and with s=1024L_N it satisfies P0<=Cs for a FIXED constant C. Pinning product bits to N and excluding trivial factors must also be included, with their actual O(L_N) Boolean-wire checks.

**Canonical lifting is harmless for these inputs.** Initial entries are0/1, hence have identical creation-time representatives at every larger two-adic precision. The later packet tensors are handled by the immutable-creation-precision rule in D.4.1. There is no need for an external arithmetic homomorphism between the Fermat ring and the two-adic extension used by the contraction proof. Local evaluators read finite bit assignments and return one bit, so no norm oracle, unknown-prime automorphism or factor-field arithmetic is hidden.

Under these checked interface conditions, TheoremD.1 yields

    poly(L_N)*2^O(L_N/sqrt(log L_N))

bit operations and polynomial space for the factor-pair count. O(L_N) conditional pinning/count calls recover an actual factor pair by ordinary self-reduction; this only changes the polynomial factor. The constants remain absolute provided the number of macro stages, graph-wire constant and entry-evaluation exponent are fixed, not functions growing with L_N. This is N^o(1), conditionally on the standalone contraction theorem AND the supplied macro-FFT encoding. No hidden theorem assumption found here requires expanding the macros into Boolean gates or their complete tables.

**Disposition:** the proposed macro-FFT tensor is admissible at the stated interface; §6's earlier absence-of-encoding discussion does not block it. I have not re-proved all D.4 or independently rebuilt the companion FFT construction. In particular the equation(D.1) sparse-degree typo is logically separate and does not invalidate this direct application of TheoremD.1. This remains requested paper study; no factoring implementation, goal resumption or unconditional certified theorem is claimed.
