# Independent review: colour-recurrence.md

26 October 2026. Read-only symbolic and primary-source check; no tests or repository edits. **PASS**, with the matrix-input-height qualification below. The conclusions are correctly restricted to the executed pointwise/slope specializations, not a general no-go.

## Lattice and phase compatibility

The kernels of the primitive surjective maps (a,b)->a*j²-bN mod k agree after an invertible integral M exactly when their row maps differ by a unit modulo k. This proves Eq. (1), including its unit multiplier. Substituting b=a*j²/N gives the inverse-square colour law Eq. (2), with the printed denominator and N factors. Without denominator invertibility only Eq. (1) is valid, as stated.

Expanding chi_j'(Mv)-chi_j(v) gives exactly d_a,d_b. The basis (k,0),(a0,1), a0=[N*j^-2]_k, has determinant k and spans Lambda_j, so k*d_a=0 and a0*d_a+d_b=0 modulo H are necessary and sufficient for WHOLE-LATTICE literal q-covariance. They do not prove finite-domain covariance or a scalar readout. The report preserves this distinction.

For T_c(a,b)=(a+cb,b), d_a=j-j'. Its first character condition forces j=j' among canonical representatives. Lattice compatibility then forces k|c; the second character condition becomes H|c*(1-j). Writing c=kt yields c a multiple of H/g, g=gcd(j-1,k), including j=1. For j=2 mod3, g=2 and the minimum is H/2. Half/quarter clock framing does not change the conclusion: modulo H/4, k*(j-j')=0 forces 3^e|(j-j'), and parity plus |j-j'|<2*3^e forces equality. With k|c the remaining 3-primary shear condition has the same H/g minimum.

This is a necessity result for the stated pointwise ordinary-baseline intertwiner. It does not rule out a transform with auxiliary states, a signed baseline, sums, or a different nonunit-preserving coverage theorem. A nonzero shear also cannot permute an entire finite integer set containing b!=0, though a partial edge/boundary construction remains possible.

## Primary DAHA specialization and actual native row

Checked Cherednik's primary PDF [arXiv:1406.3959](https://arxiv.org/pdf/1406.3959), Theorem 1.2(ii), Eqs. (1.28),(1.29). For A1, b=m*omega,c=n*omega, rho_k=κ*omega and the nontrivial reflection, pairing b+rho_k-w(rho_k)-w(c) with the positive root gives exactly m+n+2κ. Thus Q^(m+n+2κ)=1 and the choice κ=-k/2 with m=j,n=k-j are correct source conventions. Source Q is not silently the physical q. Polynomial identity at resonance does not import rational denominator inverses, efficient evaluation, or a native arithmetic interpretation.

For the B=2 auxiliary difference cell, a=[N*j^-2]_k is nonzero and a 3-unit. The row b=1 is admitted in that NEW auxiliary input, independently of old diagonal/low-product pruning. Its lambda satisfies lambda²=4aN mod H and is a 3-unit. Lift independence gives lambda_(k-j)=H-lambda. Therefore the node exponent difference is exactly H-2lambda, which is nonzero, not a multiple of H, and of magnitude below H. Since local ord(beta)>=ord(q)>16H, beta^(H-2lambda)-1 is nonzero at both primes; multiplying by the known monomial proves the asserted UNIT separation of the two actual nodes.

This refutes identifying those native node/kernel values directly under the source weight exchange. It is not a counterexample to a transformed whole-product invariant, a row permutation, or modular q-alias at a different shift. The source report explicitly leaves those possibilities open and claims no general DAHA obstruction.

## Costs and scope

All validation tests cost polylogarithmic bit work per colour PROVIDED the supplied M entries have O(log N) bits. For a longer supplied word/matrix, its entry/input height must be charged; “acquired matrix” cannot make arbitrarily long entries free. This minor condition should accompany any uniform soft-k validation claim. The short elementary shear case and actual B2 calculation already satisfy it.

Testing a lawful lattice/character map does not acquire the changed finite box, its origin omission, filter, or scalar boundary factors. The report correctly keeps all of these unpaid and retains the once-only T_ext=soft N^(31/192) factor branch. No complete query gain, adaptive selector, or general recurrence lower bound is inferred.
