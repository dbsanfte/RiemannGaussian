# Explicit N-dependent acquisition target from Lehman starts

This note gives an unconditional cover formula, with a remaining computational lemma. It does not assert a soft-O(N^(1/6)) algorithm.

Let N=P Q, P<Q, m=ceil(N^(1/6)), r=m^2. First perform deterministic Pollard--Strassen small-factor search through ceil(sqrt(N/r)); its cost is soft O((N/r)^(1/4))=soft O(m). If it returns no factor, P>sqrt(N/r).

For all positive u,v with uv<=r define

    c_uv = u N+v-ceil(2 sqrt(uvN)).

Let I={0,...,m-1} and let C be the multiset of these c_uv. Both formulas are explicit and use only N. For N above an absolute constant every c_uv exceeds m, so there are no zero crossdifferences. Small N can be handled by a fixed direct table.

Lehman's approximation lemma (in Harvey, arXiv:2010.05450, Lemma 3.3) supplies u,v with uv<=r and

    0<=u Q+v P-2sqrt(uvN)<sqrt(N)/(4r sqrt(uv))<=m/4.

The integer i=u Q+v P-ceil(2sqrt(uvN)) therefore lies in I. Since P=1 modulo d_P,

    c_uv-i = uN+v-uQ-vP = (P-1)(uQ-v)

is divisible by d_P. Thus this is an actual unconditional N-dependent individual-local-order cover; its cost issue is its volume, not a missing arithmetic coverage promise. The right-hand product is strictly positive: uQ>v is not automatic for all pairs but follows from P<Q and uv<=r<N for sufficiently large N; alternatively the checked hull c_uv>m already suffices.

For a supplied gamma form the succinct product functional

    H_N(X) = product_(uv<=m^2) (X-gamma^(c_uv))  modulo N.

Only the m evaluations H_N(gamma^i), 0<=i<m, and a witness nonunit factor are needed. If a proper gcd occurs, factor N. A saturated row can be localized with the standard balanced product tree; a saturated leaf gives the nonzero annihilator c_uv-i (O(log N) bits), accepted by the reviewed QRH decoder in soft O(N^(1/12)). One may also stream/localize by recursively restricting u,v domains if an accelerated restricted-product evaluator is available.

The smallest remaining algorithmic lemma is the following explicit restricted-product task: given N,gamma,m and an interval of the lexicographic hyperbolic index domain uv<=m^2, evaluate its H_N at the m consecutive gamma powers, and locate one nonunit leaf if there is one, in total soft O(m) bit work across the root call and localization. The ordinary product/remainder tree pays soft O(m^2), because the root count is Theta(m^2 log m). No method proving the stronger bound was obtained here. A root-only accelerated evaluator without charged localization would be insufficient.

A complete unconditional fallback is the known Harvey construction with r=M=ceil(N^(1/5)): the small-prime search costs soft O(N^(1/5)), and the shifted giant multiset has soft O(r+sqrt(N)/(sqrt(r)M))=soft O(N^(1/5)) entries. The supplied long-annihilator decoder can consume saturated leaves directly, so the reviewed group collision consumer applies without factorization of any exponent. This is a concrete N^(1/5) acquisition algorithm, not a new improvement on the literature.

## Why the actual coindices do not close the formula

Writing P=a d_P+1 and Q=b d_Q+1 gives ab<m^2/256, but the branch a=b=2 and distinct prime d_P,d_Q>16m^2 satisfies these inequalities. No short arithmetic interval for d_P or P follows. The derivation above handles that branch with the same explicit c_uv formula; only the restricted-product computation remains unproved. This does not establish a lower bound or rule out any different construction.

Primary source: https://arxiv.org/html/2010.05450 (Lemma 3.3; Algorithms 4.2--4.3; Remark 3.4 explicitly notes that a full square-root speedup for the original Lehman r=N^(1/3) would imply exponent one-sixth).
