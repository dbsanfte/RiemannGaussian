# Independent audit: macro-FFT factor-count network and TheoremD.1

26October2026. Paper-implication study; factoring goal remains PAUSED. **Conditional PASS:** the proposed high-arity macro-FFT network satisfies the stated interface of the supplied paper's TheoremD.1. If that theorem is correct with its advertised succinct-entry model, the construction yields deterministic factoring in 2^{O(L/sqrt(logL))}=N^{o(1)} time and polynomial space. This is NOT derived from Sections3–5's sparse-F2 theorem, and is NOT an independent validation of TheoremD.1's proof or an implemented factorer.

The critical model permission is real: TheoremD.1, printedp.53, measures BIT EDGES, permits degree up to ceil(s^(9/10)), and permits tensors described by entry algorithms with the stated bounded time/space. It does not demand bounded-degree gates or an explicit truth table. The construction below uses polynomial-time, 0/1-valued entry algorithms. Internal arithmetic gates of a macro tensor therefore need not become extra network wires under THIS theorem.

## 1. Exact arithmetic parameters and Fourier validity

Let N>1 have L=ceil(log2(N+1)) bits (equivalently use its ordinary binary length; this harmless convention ensures N<2^L). Handle bounded small L separately. Choose n a power of two, n>=16 and n²>=16L, minimally so; thus n<=8sqrt(L) for L>=16. Put

b=n/4, R=2^b, d=ceil(L/b)<=n/4,
M=2^n+1, omega=4 modM.

Represent each candidate nonnegative factor by d base-R digits, padding the remaining n-d input slots with zero. Restrict any unused high bits of the top digit to zero, so each candidate has exactly L available bits. Ring words use w=n+1 BITS, not n: the canonical residue 2^n is legal in Z/M and needs that extra bit. This changes no asymptotic count.

The n-point Fourier transform is invertible over the COMPOSITE public Fermat ring Z/M. It is not enough merely to cite an element of order n; here omega is a principal n-th root. Indeed omega^(n/2)=2^n=-1 modM and omega^n=1. For 0<k<n, write k=2^t k_odd and a=n/2^(t+1). Then omega^(ka)=-1; partition the n-term geometric sum into alternating blocks of length a to obtain sum_(j<n)omega^(kj)=0. Since n is a power of two and M is odd, n has an inverse modM. Thus inverse DFT is n^-1 times the transform with omega^-1. No inverse of omega^k-1, primality of M or factorization of N is used.

The zero-padded polynomial product has degree<=2d-2<n, so cyclic convolution creates NO wrap. Every integer convolution coefficient satisfies

0<=C_i<=d(R-1)²<d 2^(2b)<2^n<M.

The last inequality follows from d<=n/4 and (n/4)2^(n/2)<2^n for n>=16. Consequently the canonical inverse-DFT residues are EXACT integer convolution coefficients, not just their reductions modulo M. This is essential to excluding spurious modular products.

## 2. Two macro stages per DFT, with actual ports

Write n=r t, r,t powers of two differing by at most a factor2; both are O(sqrt n). One exact Cooley–Tukey factorization, with input index j=j1+r j2 and output k=k2+t k1, is

Y_(j1,k2)=sum_(j2<t) omega^(r k2 j2) x_(j1+r j2),
X_(k2+t k1)=sum_(j1<r) omega^(t k1 j1) omega^(k2 j1)Y_(j1,k2).

Stage1 has r tensors, each receiving/emitting t ring words. Stage2 has t tensors, each receiving/emitting r words, with the known twiddle inside its entry predicate. This is TWO macro stages, not log(n) layers of separately charged butterflies. The inverse transform has the same two-stage layout, omega replaced by its inverse and n^-1 included in the final output relation.

Each macro tensor is the 0/1 predicate that all its word ports are canonical in [0,M), and that its output words equal the displayed modular linear transform of its input words. Its description contains the block indices and public arithmetic parameters. Direct evaluation of the predicate uses polynomially many bit operations in L, even with schoolbook arithmetic. There is no exponentially large table in the description and no unproved small-circuit claim.

Use TWO forward transforms, n pointwise multiplication tensors z_k=xhat_k*yhat_k modM (canonical outputs), and ONE inverse transform. Every intermediate word is a unique function of its canonical input words. Fan-out is absent: each intermediate word goes to its one next-stage block. The maximum degree of a Fourier macro tensor is at most2 max(r,t)(n+1)=O(n^(3/2))=O(L^(3/4)).

## 3. Integer carry chain and unique extension

Connect each inverse output C_i to an integer carry tensor, 0<=i<n. Supply N's base-R digit N_i as a CONSTANT (zero after its last digit), and impose

C_i+k_i=N_i+R k_(i+1), k_0=k_n=0.                  (F1)

These are INTEGER equalities on unsigned port words, not congruences modulo M. Use w-bit carry words and, if desired, explicitly restrict 0<=k_i<=d(R-1). Every genuine product has this bound: if k_i<=d(R-1), then C_i+k_i<=dR(R-1), so the next floor carry is again<=d(R-1). This fits well within w bits. The endpoint-zero constraints are separate fixed-word tensors.

Conversely, multiply(F1) by R^i and sum. The carry terms telescope EXACTLY because both boundary carries are zero, giving

sum_i C_i R^i=sum_i N_iR^i=N.

The left side is the ordinary product of the two encoded input integers by §1. Hence every accepted assignment represents a genuine factor pair, with no modular overflow, cyclic wrap or hidden signed carries. For given candidate inputs, Fourier intermediates and convolution outputs are unique, and the carry recurrence from k_0=0 determines every carry uniquely; if any digit constraint fails it has no extension. Thus valid input pairs have exactly ONE internal extension.

## 4. Count the BIT wires, not the unexpanded gates

Use one word-edge for each canonical intermediate and carry. The complete raw network has:

* 2n source-to-forward-stage1 word edges;
* 2n forward-stage1-to-stage2;
* 2n forward-output-to-pointwise;
* n pointwise-to-inverse-stage1;
* n inverse-stage1-to-stage2;
* n inverse-output-to-carry;
* n+1 carry-chain edges, including its two endpoint pins.

Total:10n+1 word edges, each at most w=n+1 bit edges. Subdivide EVERY bit edge by a binary equality tensor to make the graph bipartite. This doubles the edge count and preserves the unique extension. For n>=16 it is below22n²<=1408L. Raw vertices number O(n), and equality subdivisions add O(L), all polynomial.

Maximum degree is unchanged by subdivision and bounded, for example, by128L^(3/4) for L>=16; all other vertices have O(n) ports. Set the paper's size parameter s=4096L. Then the edge count is<=s, maximum degree<=ceil(s^(9/10)), and precision P0=2L+1<=s; take the paper's coefficient truncation ell=1. Larger fixed constants would work equally well. This explicit rescaling removes any reliance on a degree bound holding only after an unmentioned huge threshold. Bounded smaller L can be handled directly.

The graph/port descriptions take polynomially many bits (indeed a straightforward encoding is O(L logL) plus arithmetic constants). Tensor-entry predicates have polynomial bit time/space in L, hence satisfy TheoremD.1's more generous entry bound with FIXED constants. Its potentially large implicit truth tables are allowed by the theorem; they are not silently declared polynomial sized.

## 5. Exact count and factoring self-reduction

All tensor entries are0 or1 in the allowed coefficient ring Z/2^P0, with ell=1. The ordinary integer contraction counts ordered nonnegative L-bit pairs P,Q satisfying P Q=N, and the unique-extension proof prevents additional multiplicity. Since N>1, both factors in any accepted pair are positive, and the two trivial pairs (1,N),(N,1) are distinct. The count is at most2^(2L)<2^P0, so its least nonnegative residue is the EXACT integer count.

For any prescribed prefix pi of P's original bits, modify the appropriate digit-source predicates to enforce it. No new edges are needed; local descriptions remain polynomial and entries remain polynomial-time computable. Let C_pi be the exact contraction. The number of NONTRIVIAL completions is

C_pi -1_(1 has prefix pi)-1_(N has prefix pi).

For composite N the empty-prefix value is positive. Fix P's bits one at a time, choosing a branch with positive nontrivial count. At most L further contraction calls recover a proper P; set Q=N/P by ordinary exact arithmetic. This also handles square semiprimes. If the count is2 there is no nontrivial factor; a separate primality assumption is unnecessary for the conditional search argument.

Each call uses the same s=O(L), polynomial descriptions and precision. TheoremD.1 therefore gives total deterministic time

poly(L) 2^{O(L/sqrt(logL))}=N^{o(1)},

and polynomial space, since calls are sequential. It beats every fixed N^epsilon asymptotically, including N^(1/6), CONDITIONALLY ON THE SUPPLIED THEOREMD.1. Constants and finite-size fallbacks may be enormous; this is an asymptotic paper implication, not an implementation claim.

## 6. What this does and does not validate

The construction does not need a linear-variable bounded-degree sparse-F2 Tseitin encoding. Sections3–5's failure to directly accept one dense integer multiplication equation does not apply to this high-arity tensor interface. The macro tensors perform polynomial-time arithmetic checks internally, exactly as D.1 permits. Conversely, if D.1 were restricted to explicit tables, bounded degree, or gate-by-gate entry descriptions charged as wires, this argument would NOT establish the stated bound. The supplied statement has no such restriction.

I find no arithmetic, canonicality, carry, port-count or entry-oracle gap in this conditional reduction. The remaining foundational dependency is the correctness of D.1 itself under that broad succinct-entry hypothesis and its stated bit/space bounds. This review has not independently reconstructed its entire recursive proof. No goal resumption, factoring implementation, numerical campaign or repository mutation was performed.
