# Independent review: recursive-products.md

26 October 2026. Bounded read-only paper review; no tests or repository edits. **PASS:** the common carry envelope is legal for the enlarged factoring predicate, the joint string kernel is genuinely initialized at the stated bound, and the pure Cartesian completion omits its tautological origin before evaluation. No target-rate gain follows.

## Envelope and all-leaf labels

For a=a_b+kt, canonical phase reduction gives exactly c(t)=ceil(jt/k-lambda_b/H) and x_(b,t)=x_b*R^t*q^c(t), with 0<=c(t)<=t. Therefore canonical clock n becomes unwrapped n-c(t), contained in [-Lmax+1,W]. Enlarging to this COMMON interval preserves coverage and is correctly not claimed as scalar equality.

For every added original leaf the exponent is

    bN+[a_b+lambda_b+k(1-j)t-Hv].

The bracket has magnitude less than 14k³+4H under the supplied loose bounds t<=4k and |v|<=10k+1. This is below N>256k⁴ for k>16. With b!=0 the exponent is nonzero. For transpose the exponent is

    aN+[b+lambda_b-kjt-Hv], a=a_b+kt!=0,

whose bracket is bounded by 14k³+2H+k<N. Thus every enlarged original/transposed leaf is independently licensed; no reconstruction of an old low-product leaf or numeric unit correction is needed. The phase carry is the same in both orientations, preserving the paired-prime coverage. This argument relies on the nonaxis difference refinement, as explicitly credited.

## Joint kernel and exact cost

The integer interval (-A,A) has fixed length, so its residue-class populations are two adjacent lengths. Partition the acquired b starts by that length. Within one part G_L(Z)=prod_(t<L)(1-R^t Z) is built by an actual degree-L product tree; no 1-R^t inverse or order premise occurs.

For a common q-clock block of d positions the kernel is prod_(i<d)G_L(q^-i Z), of degree Ld. Its translated evaluations are at x_b*q^(-v0), with O(B*K/d) actual starts. Product construction and monic multipoint evaluation cost soft(Ld+B*K/d+B+L). The partial tail has degree at most Ld and B starts, so it is included. Clipping d to [1,K] does not worsen soft(B+L+sqrt(LBK)): if the optimum falls below1 the L term pays the clipped cost, and if above K the B term pays it. The constant number of length groups is harmless.

With LB=O(k) and K=O(k), the full per-cell cost is soft k, without materializing BL root nodes before kernel construction. This improves the explicitly independent-string implementation, but not the already-known soft-k per-cell completion. Different cells still have soft-k total descriptors and no proved shared scalar readout.

Cost qualification: the displayed algebraic kernel costs describe continuing computation. A general terminating factor-or-value call also pays at most one inherited T_ext=soft N^(31/192), especially if a short prefix/subset would otherwise have smaller cost. Actual full per-cell soft k and whole-family soft k² absorb T_ext. It must not be called polylogarithmic merely because its annihilator label has O(log N) bits. No multiplicity in the number of cells/tests is needed because extraction terminates the algorithm.

## Pure Cartesian product

The finite polynomial H_cell includes every signed coefficient difference except (0,0), BEFORE specialization. Its leading coefficient is a product of known nonzero monomials and hence a unit. Its D=O(k) factors and product tree are genuinely acquired at soft k per selected cell. Evaluating its q^-h clock values at h=0,...,4k by the inherited block engine costs soft(D+sqrt(Dk))=soft k. Repeated numeric monomials do not invalidate monic remainder evaluation; their nonunit events retain the supplied nonzero exponent labels from the public filter.

The origin line must stay omitted: a complete-box formula includes the h=0 zero and cannot be divided numerically to recover H_cell. The report explicitly retains this finite omission when discussing corner/Nekrasov identities. Its degree-soft-k² combined polynomial, or the sum of per-cell completions, really costs soft k²; neither a descriptor nor recursive word is counted as its scalar value.

The direct kernel already proves the charged square-root-volume completion. The alternative multi-axis blocking sentence should be read as an equivalent choice of genuine finite kernels/tiles (the full D-factor kernel is one such choice), not a theorem that arbitrary recursive corner states are freely evaluable. The following section correctly states that a corner relation still needs initialized translated products and a collision-safe boundary proof.

## Conclusion

The new finite refinement is legal envelope removal and sharing G_L across b. The cleaner Cartesian family supplies an equally legal soft-k-per-cell scalar algorithm. Both preserve decodable zeros, and neither proves amortized soft-k whole-family acquisition. No additional coverage claim, root-of-unity closure, optional-unit bottleneck, or generic lower bound is inferred.
