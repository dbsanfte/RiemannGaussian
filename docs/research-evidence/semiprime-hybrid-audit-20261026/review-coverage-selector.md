# Cross-review: kernel cover and coverage/selector composition

26 October2026. Bounded paper audit, no tests or source/repository edits. **PASS for the mathematical construction and consumer, with the explicit Section4 premise correction below.** No new rate or free selector acquisition follows.

## Required kernel Section4 clarification

No k-roughening premise is needed to show r_P=ord_P(q) divides(P-1)/g. Since q=beta^H and g divides BOTH H and P-1,

    q^((P-1)/g)=beta^[(H/g)*(P-1)]=1 modP.

This directly proves the divisibility. The current roughness sentence is an unnecessary imported premise and should be replaced by this identity so the stated prepared-branch scope is transparent. Sections6-7 already use the exact Fermat gap and do not require that extra premise.

## Kernel integrality and complete cover

The kernel HNF and its determinant agree with the exact phase-index theorem. For v2=n(c,1), c=[Q]_k at the true colour, D=kg,delta=D*C-N-c, the index is explicitly

    I=C-((P-1)/g)*((Q-c)/k),

so it is integral and C-I is exactly the stated product. This also proves the printed formula(cP+Q+delta)/D with its correct sign.

For Section6 the inner lattice aP=bN modk is equivalent to a=c*b modk, because P is a unit modulo k. It has index k and weighted covolume kN. The Gauss norm bound supplies the nonzero existence vector without requiring its acquisition. D0=ceil sqrt(2kN), V=ceil sqrt(2k)+1 and T as given safely cover |b| and |t| for a=k*t+c*b: Q>=sqrtN, P>16H, |c|<k. D0<N follows with ample margin from N>256H², hence |a|<Q. The unwrapped exponent is EXACTLY H*(t+C*b), and the integer stationary index satisfies the displayed bound for h=I-t. The use of ceil(2D0/(kg)) rather than sqrt2*D0 is conservative.

The gap

    H*(C*b-h)=(P-1)*(k/g)*(bQ-a)

is exact and nonzero. If b!=0, |a|<Q excludes bQ=a; if b=0, nonzero vector implies a!=0. Thus the guaranteed hit is never one of the literal omissions. Negative t,b,h introduce no sign problem. Literal h=C*b is excluded by integer inspection BEFORE evaluation, including b=h=0; all other product leaves have their own nonzero short integer labels, even if they are accidental order aliases.

Section7 correctly uses the SUBKERNEL n0=k/2: it is an integer multiple of k/g because every g is even. Its generator phases are H/2 and(k/2)*(2k*C_j-N-c). C_j=C+epsilon,epsilon in{0,1}, and the shifted h=I-t-epsilon*b gives

    H*(C*b-h)=(P-1)*(k/2)*(bQ-a)

without an unknown-order reduction. This proves all-prepared-semiprime NONUNIT coverage at the smaller factor. It does not assert global zero. Origin removal, prefix localization and recovery therefore match the stated nonunit interface.

The exact sizes check: V=O(sqrtk), T=O(sqrtk), W_g=O(sqrtN/(g*sqrtk)+sqrtk), and W=O(sqrt(N/k)+sqrtk). The acquired starts in Section7 are only O(sqrtk), with logarithmic-bit exponents. Monic joint evaluation costs soft(sqrtk+sqrt(VW)), hence soft N^(1/4), before one possible terminating extractor. Its exact bound is T_ext=soft O(N^(31/192)), not polylogarithmic; this is absorbed by soft k and the stated slower fallback. All new annihilators have polynomial magnitude and logarithmic bit length, meeting the actual inherited extractor premise.

## Coverage-selector promised residue and cost

Its Section5 consumer is correct GIVEN one actual hit's h modk. Intersecting [-W,W] with that AP leaves O(W/k+1) positions for each of O(V) starts, so the total row-clock mass is O(sqrtN/k+sqrtk)=O(k²) under N<=k^6. Monic block evaluation, variable tails and at most one literal-index split per start cost soft k. Unit output may return bounded failure on a wrong residue; any nonunit still localizes to a valid nonzero-label factor or once-only T_ext. A polylogarithmic residue palette retains that rate. If b is also supplied, R>=ceil(W/k²) gives a one-row O(k²)-length AP and the same soft-k consumer; near N~k^6 this permits R=O(sqrtk).

This is a consumer theorem, not acquisition of rho. The construction does not identify its h with the earlier minus-row index, actual factor colour, or old tag polynomial. Selecting one universal row alone still leaves W~k^(5/2) in the hard regime and one-row cost k^(5/4); the audit correctly refuses the old shorter-horizon consumer at its old price.

## Promise mismatch and compositional scope

The torus substitution is algebraically correct: pi^lambda*barpi^sigma=(pi^H)^C*W^(-2sigma) when lambda+sigma=HC. The universal first HNF generator has lambda=sigma=H/2 and gives beta^H, not pi^H; the varying second generator retains its extra torus factor. Thus the old exact stationary/tag/unique-hit promise is not supplied together with the new common scalar starts by this direct substitution.

The scalar grids permit useful local aliases, but a located alias need not label the factor's residue. Conversely complete phase cosets and the actual sheared Gauss support are not interchangeable. The audit appropriately treats the literal support lower bound as specific to full explicit/union-support acquisition, not an implicit-algorithm lower bound or an exclusion of a smaller covered subset. No all-semiprime shift/residue selector is inferred from a conditional orientation promise.

The two reports therefore compose to a legitimate narrower hybrid TARGET: acquire one coarse residue of the universal kernel clock, then run the paid soft-k consumer. The current reports do not acquire that residue or a faster full kernel scalar. Subject to replacing the unnecessary roughness sentence, the guarantees and cost ledger are consistent.
