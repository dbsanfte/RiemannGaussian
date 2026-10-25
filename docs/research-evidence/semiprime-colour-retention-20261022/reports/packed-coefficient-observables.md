# Factor-producing observables of the packed C_N vector

22 October2026. Input N=P Q odd squarefree; public auxiliary prime ell, k|ell−1, gcd(N,ell k)=1. C=C_N in A_k=(Z/N)[X]/(X^k−1) is already acquired by the reviewed binary Jacobi-histogram algorithm, in soft O(ell+k) native bit work. This report gives two explicit factor-producing controllers with charged construction and exact sufficient conditions. No affordable public choice of ell,k making either condition universal has been proved. The original native long query remains unpaid.

Read the packed primitive, its independent review, and repository journal32089 onward before this continuation. No numerical examples, backend work, or repository edits were made.

## 1. All divisor restrictions and all monomial positions, in soft k

For each d|k, fold C into A_d:

    C_d(X)=C(X) mod(X^d−1)=sum_(r=0..d−1)c_(d,r) X^r.

For N odd, C_d(1)=1. Thus if C_d is monomial over either hidden field, its nonzero coefficient is necessarily1: it is exactly X^r. This normalization avoids an unknown scalar multiplier.

For every r compute

    g_(d,r)=gcd(N,{c_(d,s):s≠r}).                 (1)

All d values are acquired in O(d) gcd calls by prefix and suffix gcd arrays, initialized with N. No d-by-d coefficient comparison is needed. Return any 1<g_(d,r)<N.

**Exact guarantee.** If for some d|k the reduction of C_d at P is X^r and the reduction at Q is not the SAME X^r, then g_(d,r)=P. This includes the case where Q's vector is not monomial, or is a different monomial. The analogous statement holds with P,Q exchanged. Conversely a proper result of (1) certifies precisely such a locally monomial support: all coefficients outside r vanish at one factor and at least one does not vanish at the other, while their sum1 fixes the remaining coefficient.

**Full restriction cost.** The public factorization of k is available from factoring ell−1 in the initial construction. For each proper divisor d choose one prime p with dp|k and choose dp as its parent. Process from k downward; folding a length-dp parent to its child costs O(dp) coefficient additions. Each divisor is parent of at most omega(k) children, so total work is at most

    omega(k) sum_(d|k)d <= omega(k) k(1+log k).

The last inequality follows from sum_(d|k)d=k sum_(e|k)1/e<=k H_k. All arrays together also have at most k H_k entries. The prefix/suffix gcd work is O(sum_(d|k)d). Consequently the entire restriction-stable monomial test family costs soft O(k log N) bits and storage, including every divisor and every candidate support position. Added to the C_N construction this is soft O(ell+k), with logarithmic N factors suppressed. It never materializes k full Galois-conjugate vectors.

**Implementation-ready outputs and control.** Enumerate and sort the divisors of k in decreasing order. For each d<k fix parent(d)=d*p, using the smallest prime p dividing k/d; no search involving N is present. Initialize V[k] with the acquired vector. When processing d<k, zero a d-entry array and loop once over V[parent(d)], adding entry i to slot i mod d modulo N. Then:

1. If V[d] has exactly one nonzero coefficient and that coefficient is1, record `GLOBAL_MONOMIAL(d,r)`. This is a direct modular assertion, not a hidden-field decision.
2. Otherwise form prefix[0]=N, prefix[i+1]=gcd(prefix[i],c_i), suffix[d]=N, suffix[i]=gcd(suffix[i+1],c_i). Any proper scalar gcd already found here may be returned.
3. For each r compute gcd(prefix[r],suffix[r+1]); return `FACTOR(g,d,r)` when it is proper.
4. If no factor was returned and the vector was not globally monomial, record `BOTH_LOCALLY_NONMONOMIAL(d)`; this interpretation follows from the proved sufficiency, not from querying either hidden field.

For d=1 the vector is always1 and the first status is automatic. Local zero vectors cannot occur for any d: evaluating at X=1 gives1 in both hidden fields. If both local vectors were the same monomial, CRT would make the public vector exactly that monomial and step1 would record it. If exactly one was monomial or their monomial positions differed, step3 would return a factor. These cases exhaust the possible local monomial statuses. The controller returns the first factor, or the public list of statuses above; it does not output an uncertified local phase.

**Local meaning.** The exact hidden identity is

    C_N(X) = X^(−N log_g P) C_Q(X^P) mod P.        (2)

It commutes with reduction to every d|k. Since P is a unit modulo d, X→X^P permutes monomial positions, and multiplying by the displayed monomial preserves monomiality. Hence local monomiality of C_N at P is equivalent to monomiality of the unknown-index C_Q at P. The true local Frobenius identity makes C_P monomial, not C_N. Formula(2) is therefore an exact order/source boundary: this test does not silently replace C_N by C_P.

## 2. A coefficient correlation that can be evaluated exactly, and its limit

Let rho_−1 mean X→X^−1. For the Gauss pair G_a,G_−a define

    D_a=E_a+(1−E_a) ell X^(a log_g(−1)),
    G_a G_−a=D_a.

Multiplying G_1^N=C_NG_N by its rho_−1 conjugate gives

    C_N rho_−1(C_N)=D_1^N /D_N.

The slash here denotes an identity between units. Since gcd(N,k)=1, E_N=E_1. The monomial factors cancel, leaving the explicit identity

    C_N(X) C_N(X^−1)
       =E_1+(1−E_1)ell^(N−1).                    (3)

Thus the complete cyclic coefficient autocorrelation carries only the ordinary public Fermat value ell^(N−1), not an extra local Gauss phase. For A_d, its coefficient at0 is ell^(N−1)+(1−ell^(N−1))/d and every other coefficient is (1−ell^(N−1))/d.

This also places test1 accurately. If d>1 and C_d is monomial modulo P, (3) forces ell^(N−1)=1 mod P. Therefore first computing gcd(ell^(N−1)−1,N) is a cheap useful screen. A proper value already factors; if it is1, none of the nontrivial divisor monomial tests can succeed. The all-restriction controller supplies a potentially finer test in the globally saturated Fermat case, not a universal replacement for that missing branch.

## 3. A packed torsion/gcd test without choosing a monomial label

Acquire in A_k

    W=C_N^k−1

by binary powering. Let F=Phi_k(X); assume k>1. Reduce W modulo F, and run a guarded fast polynomial gcd with F over Z/N. Every attempted inverse of a leading coefficient is preceded by gcd(coefficient,N). A proper scalar gcd is returned immediately. A zero coefficient modulo N is deleted as a leading zero; a unit pivot permits the usual polynomial operation. No hidden field is an input.

Let

    delta_P=deg gcd(F mod P,W mod P),
    delta_Q=deg gcd(F mod Q,W mod Q).

**Exact guarantee.** If delta_P≠delta_Q the guarded computation must return a proper factor. Otherwise, if every needed pivot were a unit, every degree decision and Euclidean step would specialize identically to both fields, producing gcds of the same degree, a contradiction. It may also return a factor in additional cases; degree imbalance is a sufficient condition, not a claimed equivalence.

W is acquired in soft O(k) native bit work. F can be constructed in soft O(k) without a hidden factorization: the public factorization of k enumerates its divisors, and the cyclotomic product formula uses monic numerator/denominator products of total degree at most sum_(d|k)d<=k H_k. Monic exact division is valid modulo N.

The soft-linear gcd claim requires **guarded half-gcd**, not classical Euclid. The following transfer argument specifies that requirement. Use a characteristic-independent fast field half-gcd algorithm with O(M(n)log n) ring work, linear or soft-linear scalar divisions, and degree/zero decisions by inspecting coefficients. Use integer-packed polynomial multiplication over Z/N, rather than assuming roots of unity for a field FFT. Before each scalar inversion, or before accepting the first nonzero coefficient used to determine a degree or zero branch, compute its gcd with N. A coefficient zero modulo N is zero in both fields; a unit is nonzero in both; a proper nonunit returns a factor. Polynomial/matrix zero and degree tests are guarded in the same manner, not only the final Euclidean leading coefficient.

Until a proper factor is returned, the arithmetic, divisions and all branch decisions therefore specialize to exactly the same executions over F_P and F_Q. This proves both correctness and the complexity transfer: the executed prefix has the fast field algorithm's work bound. Integer packing gives soft-linear polynomial arithmetic; each required scalar guard or inverse costs only logarithmic factors in N. Coefficient inspections remain within the fast algorithm's soft-linear bound. Thus the guarded half-gcd controller has soft O(k log N) bit cost or returns a factor sooner. A plain quadratic Euclidean implementation would provide only O(k²) modular work and must NOT be cited for this soft-m claim. This is a paper-level guarded-algorithm specification, not a claim that such an implementation has been added or tested here.

A primary explicit general-half-gcd source is van der Hoeven, *Optimizing the half-gcd algorithm*, arXiv:2212.12389v1, Algorithm4 and Theorem15. Its generic multiplication model applies; the binary-FFT-only specialization is unnecessary. Thus this is another paper-level soft O(ell+k) controller, without evaluating one separate vector for each of k possible phases.

The interpretation at a primitive character is

    C_N(chi)^k=C_Q(chi^P)^k mod P,                 (4)

because the hidden factor chi(P)^(−N) has kth power1. Thus delta_P counts primitive-character components on which the unknown quotient C_Q has kth-power1, with the same count because chi→chi^P permutes primitive characters.

There is a useful base-field formulation, not an extra hidden oracle. Acquire the public unit

    U(X)=G_1^k=−C_k(X).

Then identically

    C_E(X)^k=U(X)^E/U(X^E).                       (5)

At P, ordinary Frobenius gives U(X)^P=U(X^P). Consequently (4) is exactly the compatibility condition U(chi)^Q=U(chi^Q), not an evaluation in a supplied hidden field. If Q=P^h mod k, this condition becomes the actual local-order condition

    ord(U(chi)) divides Q−P^h,

because U has rational integer coefficients and chi^Q=chi^(P^h). If Q is outside the subgroup generated by P modulo k, no such same-component simplification is assumed: the equation couples different character components. This states the order bridge explicitly while keeping those orders out of the algorithm's input.

## 4. Cocycle checks do not supply an unknown index

For all nonnegative a,b,

    C_(ab)=C_a^b rho_a(C_b)=C_b^a rho_b(C_a).

The equality follows directly from the defining Gauss-power identity; rho_a is a ring endomorphism even when a is not a unit modulo k. For fixed supplied indices it is cheaply checkable after acquiring the required vectors. Inserting a=P,b=Q retains unknown C_P,C_Q and does not construct either. Likewise fixed correlations

    C_N rho_s(C_N)
      =c_(1,s)^N c_(N,Ns)^(-1) rho_(1+s)(C_N)

are exact unit identities; the displayed inverse is justified algebraically but not required by either production controller above. This is another Gauss/Jacobi relation, not an index extractor. No k-by-k family of these correlations is charged as one operation.

## 5. Concrete remaining selection theorem

The two proved controllers would become a useful universal route if one could construct, with total soft m acquisition and controller work, public auxiliaries (ell,k) such that every prepared input forces either:

- an unequal local monomial restriction in test1; or
- a primitive torsion-gcd degree imbalance in test3.

For multiple auxiliaries, the total paid cost is soft O(sum ell), not soft O(max ell). Neither theorem is supplied by the native row collision. In particular a failed APR congruence may fail at both primes, yielding no pivot zero divisor and no degree imbalance. Completeness of a compositeness test is not completeness of either factor controller.

This is the exact missing selection statement; no universal coverage is asserted. The report supplies actual affordable scalar-factor tests, rather than an uncomputed full norm or a collection of successful examples. It does not assert that their sufficient conditions cover every input, shorten the native long index, or improve its all-input complexity.

## Primary reference

Schoof, Four primality testing algorithms, MSRI Publications44(2008), Section4, Proposition4.1 and Theorem4.2: https://reneschoof.github.io/05rene.pdf . Its conditional character congruences constrain prime divisors; the subsequent primality algorithm also uses enough checked auxiliary characters and candidate-divisor tests. It does not state a universal soft-m factor-producing coefficient imbalance theorem. Retained PDF schoof-four-tests.pdf SHA256 a5eb47de1dd06b5a0588478cb869bd13cc7dd9020ecf4472dac7ec47dac96d32.

The reviewed Gauss/Jacobi identities and packed-construction bit ledger are inherited from /tmp/semiprime-weighted-acquisition-20261022/gauss_literature/packed-gauss-quotient.md and its independent review. All new formulas here are direct algebraic derivations; no analytic assumption or arbitrary higher-character oracle is introduced.


Additional primary algorithm pin: van der Hoeven, *Optimizing the half-gcd algorithm*, arXiv:2212.12389v1, https://arxiv.org/abs/2212.12389v1 . Retained PDF van-der-hoeven-hgcd-2212.12389v1.pdf SHA256 4aa40faa8d128ab01b01e7bfcd36fe90bfe89690a7a5d4d828edf28b6412bd3e. The guarded composite-ring transfer above is separately proved; the source field theorem is not misquoted as a theorem about arbitrary composite coefficient rings.
