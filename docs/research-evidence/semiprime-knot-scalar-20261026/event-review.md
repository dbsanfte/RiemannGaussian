# Independent review: continuous-tag event-cover bound

2026-10-26. **PASS for the stated full continuous sigma-by-t covering problem.** No experiments, repo edits, novelty assessment, or lower bound for actual semiprime points. The proof's declaration must remain exactly at that scope.

## Normalization and arithmetic capacities

For h=gcd(|a|,|b|) and d=gcd(h,k), gcd(h/d,k/d)=1 prime by prime. Thus h(a0 N-b0 sigma²)=0 modk is equivalent to a0 N=b0 sigma² mod(k/d), exactly the congruence for the replacement (d a0,d b0). Its transverse absolute value is multiplied by d/h<=1. Replacing every descriptor therefore preserves full coverage while weakly reducing count after deduplication. This does not preserve arbitrary original leaf labels or other coefficient constraints, as the report explicitly says.

For n=k/d>1, a compatible primitive pair must have both a0,b0 units modulo n: at a prime dividing n, divisibility of one forces divisibility of the other. The resulting unit square-root equation has at most two roots modulo n, because n divides 2*3^e. There are at most d lifts of each root to a unit tag modulo k, giving <=2d compatible tags. The n=1 bound and the axis exclusion for delta<k are also correct.

For 0<a<=2delta, |b|<=4a+delta<=9delta, d<=2delta, and the integer-pair count O((delta/d)^2) is uniform even when delta/d lies in [1/2,1]. The measure contribution O(d) per pair and the bounded reciprocal-divisor sum over 2*3^e give O(delta²), with no logarithmic loss. Negative b and b=0 do not escape this enumeration.

For a>2delta, a/2<b<(9/2)a, so at primitive level a0 there are O(a0 tau(k)) normalized descriptors. Each has tag-times-interval measure <=(2d)*(2delta/(d a0))=4delta/a0. Sorting these capacities, or splitting at T~sqrt(R/tau(k)), gives O(delta sqrt(R tau(k))). The R<tau(k) case is correctly handled separately. No coefficient upper bound or independence assumption is used.

The domain measure is exactly 3 phi(k)=k. Combining the union bounds proves k<=C1 delta²+C2 delta sqrt(R tau(k)). Substituting delta=C sqrt(k/r), with r above an absolute threshold depending on C, gives R=Omega(kr/tau(k)). The step tau(2*3^e)=2(e+1)=Theta(log k) and the stated superlinearity for power-growing r are correct. The scaling from the original transverse inequality to delta=4sqrt(k/r) on 1<=t<=4 has the correct direction.

## Essential scope and a genuine discrete-scale opening

The result is a descriptor-count obstruction for covering **every** independent unit sigma and **every** real t in [1,4]. It is not a lower bound for the factorization goal. For a fixed semiprime N the two actual factor points are not this product domain, and finitely many points have zero Lebesgue measure. Requiring one actual witness, allowing a semiprime-specific tag/scale correlation, or computing an implicit norm without enumerating descriptors does not satisfy the theorem's premise.

A particularly explicit arithmetic warning/opportunity is available: for one specified rational scale t=u/v in lowest terms, the descriptor

    (a,b)=(k*v,k*u)

has content exactly k, satisfies the tag congruence for **every** sigma (both sides are 0 modk), and has at-b=0. Thus a finite known list of rational scales can be covered for this *relaxed event condition alone* with one descriptor per scale, regardless of r. For t=N/B² one may take u=N/g, v=B²/g with g=gcd(N,B²). This does not contradict the continuous theorem: each such descriptor covers a narrow interval, whose width shrinks with its potentially huge coefficients.

This observation is not a native-family or factoring construction. Those descriptors generally violate the native small-product/longitudinal coefficient bounds and can force an unaffordable clock or an unusable/trivial consumer. It nevertheless shows concretely why discreteness or a thinner semiprime-specific scale set could evade the measure argument; any proposed narrow cover must reprove those other bounds and acquisition costs rather than infer them from this relaxed congruence.

More generally a required subset of measure mu would yield only mu<=C1 delta²+C2 delta sqrt(R tau(k)), not the full k lower bound. For actual isolated arithmetic points this has no quantitative force. A useful next coverage theorem could exploit the known finite scales or the factor-residue relation while retaining the native coefficient budget; the reviewed theorem neither supplies nor excludes it.

No genuine gap found in the scoped continuous-cover proof. The distinction between that constructor obstruction and the unresolved semiprime acquisition problem is essential to every subsequent citation.
