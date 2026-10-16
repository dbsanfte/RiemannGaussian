# Independent review: actual genuine-pole count of the canonical mask contraction

2026-10-16. Verdict: PASS. The exact-rational-function scope is essential and is correctly retained.

Reviewed `/tmp/semiprime-syzygy-query-20261016/recurrence/pole-count.md`: 7738 bytes; SHA-256 `3ed29741ff7c06d962ef68e36d35c78c5145505e3743dade3daa87f185a63457`. The adjacent manifest SHA-256 is `cfdbee72073d8649d0d121cc7116f02cd77d67570757bd85f5d601ace391dd6f`. Its report entry and all FOUR source pins independently match their sizes and hashes. No original, repository file or frozen bundle was edited; no build was run.

## Negative-index recurrence and residues

The backward coefficient ratio is correct: c_(a-1)/c_a=q(q^a-1)/(q^a-q^(L+1)), and multiplying its h successive instances gives the displayed R_(-h)(X). For h>a its numerator contains X-q^a, while the denominator stays nonzero at X=q^a. Thus the low-coefficient identity with zero-padded negative coefficient indices is valid for every 0<=a<=L without dividing by an out-of-range c_a.

The available poles beta_t=q^(L+t) are distinct and simple, since R>L+M. Each rho_t is nonzero: every relevant exponent difference is nonzero with magnitude at most L+M. At beta_t, the regular quotient R_(-(t+u))/R_(-t) is exactly alpha^u c_u with alpha=q^(1-L); the reported signs and q powers agree with direct cancellation. In particular the alternative expression q^u(q^(-L);q)_u/(q;q)_u has the same normalization. The assumptions JB<=L imply M<L, so all c_u used here are in range.

The coefficient reversal c_(L-u)=c_L alpha^u c_u then proves the residue/high-tail correspondence, including its factor rho_t/c_L. All residues are formal simple-pole coefficients over the field; no characteristic-zero analytic step is needed.

## Mask reversal and forced blocks

The constant-one reversals have the stated normalizations: d_J e_M is the leading coefficient of D_B, so Dhat Ehat=Khat(x^B). For P=Ehat F(alpha x), the coefficient p_(M-t) is exactly e_M^(-1) sum_u e_(t+u)c_u alpha^u. This proves the residue correspondence rho_t e_M p_(M-t) with no missing reversal scalar.

In Q=Dhat P=Khat(x^B)F(alpha x), the first h+1 coefficients of block h have exactly the displayed convolution in k_0,...,k_h. Reversing the k-column order produces the contiguous q-binomial matrix c_(Ba+i), with only nonzero alpha row/column scalings. These indices lie strictly below M, as B>=J gives M-[B(J-2)+J-2]>=2. Thus all J-1 forced blocks counted are genuinely within the support range relevant to the poles.

## Actual unit minor

The cleared rational-Newton basis factorization is correct. Its seed and denominator exponents lie through L. At eta_k=q^(L-k), the basis matrix is lower triangular with the stated q^L, negative-q and L+u diagonal factors. The largest additional exponent is at most L+J-2<=L+M. The eta and X_a Vandermonde differences also use nonzero exponent differences within that unit range. Thus the coefficient matrix and its evaluation matrix are invertible over each field, and are unit-determinant matrices over Z/N under the stated unit-power promise. No generic determinant is specialized without proof.

Consequently all h+1 Q values in a forced block cannot vanish, since the corresponding coefficient vector has k_0=1. Different fields may select different nonzero coefficients in the same block; the report correctly makes no global-unit assertion about every counted coefficient.

## Support count and actual-source scope

Multiplication by degree-J Dhat lets a nonzero p_u influence only Q indices [u,u+J]. Since J<=B, such an interval meets at most two width-B blocks, including the inclusive boundary case J=B. Coefficients p_u with u>=M cannot influence Q indices below M. Covering J-1 forced nonzero blocks therefore needs at least ceil((J-1)/2) nonzero p_u for u<M, hence that many genuine poles. Cancellations can only remove an influence, so granting each full interval is a safe overcount.

For the native source, choosing J=m-1 and the least dyadic B>=J gives JB<2m^2<=L and L+M<6m^2<R_local. Distinctness of nodes is not needed by this proof, so any original source duplicates cause no missing hypothesis. This is an actual numerical-field conclusion with no additional deletion or random specialization.

The result excludes only exact representations of this SAME rational index function with polylogarithmically many total finite poles. It does not exclude an O(J)-size rational representation, a succinct denominator with many poles, an efficient construction/evaluation algorithm, a different representative modulo q-Ore relations, or finite-sample interpolation. In particular an Omega(J) pole count is compatible with the desired soft O(J) clock and gives no superlinear operation lower bound. The report states these limits explicitly and does not claim a whole-query acquisition algorithm.
