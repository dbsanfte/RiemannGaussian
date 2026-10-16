# Independent review: odd-source norm doubling and explicit branching

2026-10-15. Verdict: PASS. No substantive correction requested. No new Lean build, general scalar lower bound or full-query evaluator is claimed by this review.

## Exact reviewed pins

- norm/norm-doubling-audit.md SHA256 2e9dd71c2bb5e0da0e5e2ef9772d7c85375e265b8686b9ad8e6c0ad16447ac2d.
- Saved primary bernstein-norm-2023.pdf SHA256 4c63a950c3934bfa59dfa7317d45eb4962b7894e579c75a36c13447cd7be7d6b, matching manifest.json.
- Saved primary bernstein-norm-2023.txt SHA256 86868954e9f8d0aec070b248131df8c8239ff2055e391fa37c333db2498bc2c1.
- Native SemiprimeGlobalPhaseCancellation.lean SHA256 9e061d01e511f908a33256c229ca87aab1a3401077e63941f6fc2cf025720a1a.
- Native SemiprimeSeedSumAcquisition.lean SHA256 6223962bcacaf9f3325e3838fe221f8cf69f3b5e4c865d3e3d1335b0a039273e.

## Odd-source collision transform

The factor identity (1-x)(1+x)=1-x^2 proves the Pochhammer squaring identity over any commutative ring. On the actual order-qualified source, each z_j q^i lies in an odd-order subgroup of an odd-characteristic hidden field. Therefore it cannot equal -1, and every negative-complement factor 1+z_j q^i is nonzero in both hidden fields, hence a unit modulo the squarefree N. Multiplication by this complement unit preserves gcd with N. No target-collision factor or unacquired complement product is inverted by the zero-support argument.

The same proof works for target subsets and exact contiguous subintervals by absorbing the start into z_j. This leaves z_j in the same odd subgroup. Repeated squaring also stays in it. Thus the transform is genuinely restriction-stable. Its limitation is correctly stated: dimensions J,L remain unchanged and no exact scalar equality is inferred from the gcd equality.

The time split has children z,zq, whereas the sign norm pairs z,-z. No two elements of the odd source subgroup can be negatives of one another. Adjoining the safe negative complements and squaring simply returns the squared-target length-2n query, with the displayed bases q^4 and q^2 correct. The higher 2-power root-of-unity identity is also correct in a splitting extension of the odd-characteristic fields; every nontrivial such root is outside the odd source subgroup. The report charges acquiring that extension/tower and does not treat this algebra as a free algorithm.

## Exact branch-packet floor

The global exponent difference between branch nodes is bounded by

4m^2+m^2(T-1)<=4m^4+3m^2<16m^4<D

for 1<=T<=4m^2 and m>=2. Thus equality modulo N lifts to zero integer exponent difference. The native offset_square_residue theorem implies delta_j=N(t^2-2t) modulo m for t=j^(-1). Because N is nonzero modulo prime m, each such low digit has at most two tags. At a fixed tag, integer exponent equality then forces equal branch indices. Consequently numerical branch values have multiplicity at most two and at least JT/2 distinct values. The proof does not assume root-count bounds over Z/N or unit pair differences.

After k time splits the offsets indeed range over r=0,...,2^k-1 at base q^(2^k). If a squaring/sign completion follows every split, direct induction gives nodes (z_j q^r)^(2^k) at base q^(4^k), exactly as written. The global gamma subgroup has odd order (the lcm of the two odd local orders), so raising to 2^k is injective; the distinctness floor persists.

At T comparable to m, an explicitly materialized whole target packet therefore has Omega(m^2) distinct entries. This is a valid acquisition/write floor for THAT packet interface. It is not a claim about implicit circuits, streaming identities without packet materialization, early stopping, or arbitrary norm algorithms. The report includes those limitations explicitly.

Native source premises were checked: seedOffset_bounds gives the integer span, offset_square_residue the quadratic low digit, and long_global_order_bound gives D>16m^4 on the actual certified long branch. The inherited prime-order supply supplies oddness and is not generalized to arbitrary even-order units.

## Carrier-sign argument

Over each hidden field all source roots are in the odd subgroup and every negative root is outside it. Thus H(X) and H(-X) have disjoint root multisets, and substitution X->-X does not descend to the original degree-J quotient. Completing the carrier to H(X)H(-X), made monic if necessary, has rank 2J. Its sign-invariant squared-root carrier has degree J, so this construction does not halve the original J-dimensional source state. Squaring is injective even when the original list has local repetitions; it preserves its distinct-root count. These are exact statements about the specified source and completed carrier, not nonexistence of every possible different norm representation.

## Primary Bernstein check

Independently read the saved primary title/abstract, pages 2--3 and tower discussion. It is D. J. Bernstein, Research in Number Theory (2023) 9:82, DOI 10.1007/s40993-022-00402-0. The PDF explicitly records online publication 10 November 2023. Its abstract treats integral elements in smooth-degree cyclotomic/Abelian number fields, with tower-compatible integral bases; the displayed n(log n)^(3+o(1)) bit bound is attached to the stated small-weight regime. Pages 2--3 explicitly compute g(X)g(-X), extract even coefficients, reduce in the known cyclotomic subfield and recurse by norm transitivity.

Thus the report correctly distinguishes that known tower/input representation from acquiring an implicit P_L modulo an arbitrary source H over Z/N. This primary result does not supply an uncharged canonical query oracle. I have not treated the unsuccessful eprint HTML response as a source.

The two other cited q-holonomic/cyclotomic-valuation references are supporting context; this review does not add fresh literature-completeness credit beyond the saved primary Bernstein inspection.

No issue was found in the exact algebra or stated explicit-versus-implicit scope. The long-query acquisition remains unpaid.
