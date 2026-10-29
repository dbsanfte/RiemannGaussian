# ETH paper study: a conditional subexponential factoring reduction

26 October 2026. User-requested study of OpenAI's [*The Exponential Time Hypothesis Is False*](https://github.com/openai/math/blob/main/preprints%2FThe-Exponential-Time-Hypothesis-is-False-October-25-2026%2Fpaper.pdf), dated 17 October and revised 25 October 2026, 67 pages. The persistent factoring goal was paused and remains paused. This packet records the paper study and its mathematical implications, not a resumed autonomous research run.

## Main finding

**Conditional on the supplied paper's Theorem D.1 as stated, deterministic factoring has a polynomial-space algorithm with bit complexity**

\[
 T(N)=2^{O(L/\sqrt{\log L})}\operatorname{poly}(L)=N^{o(1)},
 \qquad L=\lceil\log_2(N+1)\rceil.
\]

We give an explicit uniform reduction: an exact multiplication relation becomes a Boolean tensor network with **O(L) actual bit edges**, maximum degree **O(L^(3/4))**, polynomial descriptions and polynomial-time local entry evaluation. Theorem D.1 permits that interface. Exact conditional counts recover a nontrivial factor with O(L) calls. This covers all composite inputs; square and distinct-prime semiprimes are included.

This is a substantive positive implication, not a collection of successful inputs or an obstruction. The reduction and its costs have received independent arithmetic and theorem-interface reviews. **The source theorem itself has not been independently certified in full, implemented, or formalized here.** Consequently this packet does not claim an unconditional resolution of the 1/6 goal. Its conditional rate is asymptotically stronger than N^(1/6), with no useful numerical crossover or practical speed claim established.

The construction is in [implications.md](implications.md); the independent proof audit is in [review-factor-network.md](review-factor-network.md). The second audit of the implicit tensor interface is §7 of [tensor-counting.md](tensor-counting.md).

## Why a generic SAT reduction was insufficient, and this interface works

The paper's sparse fixed-width SAT bound has exponent O(v/sqrt(log v)), where v includes **every** verifier variable. Even granting an O(L log L)-variable multiplication encoding gives only an O(L sqrt(log L)) exponent. Witness length alone cannot be substituted for verifier size. A sufficient generic sparse-SAT threshold is v=o(L sqrt(log L)).

Theorem D.1, printed p53, instead charges actual connecting bits and allows vertices of degree at most ceil(s^(9/10)), with succinct entry evaluators. A tensor can check an entire finite Fourier block without exposing every internal arithmetic gate as another network edge. Its local arithmetic is still paid by the entry-evaluation bound. This specific permission is what makes the reduction work.

## Arithmetic and size proof

For L>=2 choose n the least power of two with n>=4sqrt(L), set b=n/4, d=ceil(L/b), and work inside local predicates over the explicit auxiliary ring

\[
 R=\mathbb Z/(2^n+1)\mathbb Z,\qquad \omega=4.
\]

The transform has n words, each n+1 bits. Since omega^(n/2)=-1 and n is a power of two, the finite geometric sums vanish at every nonzero frequency; n is a unit in R. Thus the n-point DFT is exactly invertible over this possibly composite ring. Neither a prime search nor knowledge of a divisor of N is needed.

Write each candidate as d base-2^b digits and pad to n words. Ordinary convolution has degree at most 2d-2<n. Every coefficient is less than d*2^(2b)<2^n+1, so neither cyclic wrap nor reduction modulo the auxiliary ring can change it.

Factor n=r*t with r,t=Theta(sqrt(n)). Cooley–Tukey expresses each forward or inverse transform as two stages of r- or t-word transforms, with twiddles and inverse normalization folded into the local predicates. The two forward transforms, pointwise products and inverse transform have only a constant number of word interfaces. Each transform vertex has O(n^(3/2))=O(L^(3/4)) bit ports; direct evaluation of its defining finite sum is polynomial in L. No assertion about a linear-size Boolean multiplication circuit is required.

An integer carry chain then enforces

\[
 c_i+u_i=N_i+2^b u_{i+1},\qquad u_0=u_n=0.
\]

These are integer equalities, not congruences. They telescope to the exact equation PQ=N. All ring words are canonical, every transform relation is functional, and the initial carry determines all remaining carries uniquely. Hence each accepted factor pair has exactly one internal extension.

The primary construction uses local digit predicates and Boolean OR flags to require P,Q>=2. With flags integrated into the digit predicates and carry endpoints embedded as constants, the number of bit edges before bipartite subdivision is exactly

\[
 (10n-1)(n+1)+2(n-1).
\]

The seven word-interface counts are 2n, 2n, 2n, n, n, n and n-1, with n-1 carry words. The separate 2(n-1) bit term counts the two flag chains. Subdividing every bit edge with an equality vertex makes the network bipartite and doubles the count. It remains O(n²)=O(L). The independent reviewer gives an equivalent variant that permits the two trivial factor pairs and subtracts them from each prefix count, removing the flags. Its different fixed constants do not change the result.

Take s=1024L and count with coefficients in Z/2^(2L+1), with the theorem's truncation parameter ell=1. The actual edge count is below a fixed constant times s; the conservative degree bound 100L^(3/4) is below s^(9/10). Descriptions and vertex count are polynomial. All entries are 0 or 1; the auxiliary odd ring is used only inside their polynomial-time predicates and is **not** embedded into the counting ring. The count is below 2^(2L+1), so modular recovery is exact. Fixing one input factor bit at a time, retaining a prefix with positive count, recovers a factor with at most L additional contractions and polynomial space.

This proves the stated implication from Theorem D.1 with full reduction-size, precision, local computation and witness-recovery accounting. It does not prove that theorem's internal contraction algorithm correct.

## Techniques and identities worth retaining

The detailed reading is in [shared-summaries.md](shared-summaries.md) and [tensor-counting.md](tensor-counting.md). The most relevant mechanisms are:

| Mechanism | Exact content | Relevance and paid condition |
|---|---|---|
| Shared-summary fibres, §3 | Sum over shared measurement values, multiplying independent sums over each group's matching fibre | Preserves correlations while splitting a sum; measurement number and range must be small and charged. A rank-one binary-weighted clock can still have exponentially many values. |
| Diagonal recovery, Lemma 3.3 | For degree-q polynomial families, Boolean Möbius inversion recovers sum_x p_x(x) from restricted sums of p_x(1_U) | An actual method for recovering the correlated diagonal; it costs sum_(j<=q) 2^j binom(n,j), not just two fast linear actions. |
| Commuting involutions, §4 | A polynomial matching parity on a central spectral interval makes an operator exact on that interval, with exceptional modes retained as summaries | Simultaneously proves bounded replacement degree and shared-kernel structure. Its combinatorial spectrum and exceptional count are explicitly known. |
| One global truncation, Lemma 5.2 | Each factor uses the same formal V; total V-degree>=ell is discarded because its integer value is divisible by 2^ell | Preserves a final coefficient-sum readout without paying every factor's high degree separately. That readout is applied after multiplication; it is not a ring homomorphism. |
| Cauchy wire deformation, §D.4 | With C(T)=product_(t=-a)^(a-1)(T-t), W_xy(T)=C(T)/(C'(0)(T-y+x)) satisfies W(0)=I | Deforms exact equality into grouped contractions. Here a denotes the packet length, not the paper's logarithmic packet parameter. The divided linear factor cancels polynomially. |
| Weighted mode truncation and tapered Hermite data, §D.4 | A mode of weight j carries a factor 2^j. Only monomials with total weight below working precision survive; unequal interpolation multiplicities control precision loss | This is the main mechanism supporting D.1's recursive bound. It produces exact cancellation at finite precision; no analytic smallness assumption replaces exactness. |
| Fixed common denominators, Appendix B | Pad to one denominator before aggregating; numerator length grows only logarithmically with the number of summed terms | Useful bit accounting for rational identities; it does not itself reduce the number of terms acquired. |

For the native residue, the direct import still has a mismatch: 2 is a unit modulo odd N, so the paper's 2-adic truncation does not discard native terms. Its bounded-degree polynomial identities also do not automatically accept a rational long-query evaluator at replacement points. The positive route above uses exact Boolean factor counting to avoid those particular handoffs.

## Scope of the implications

If the supplied SAT theorem is correct, its exact subexponential fixed-width algorithm refutes the stated ETH, #ETH, SETH, Gap-ETH and NSETH hypotheses. It does not imply P=NP, polynomial-time factoring, or an automatic speedup for every problem once assigned an ETH-based lower bound. Reductions and parameter growth still matter. The paper separately derives a circuit lower bound for E^NP and subexponential inversion of constant-output-locality maps; ordinary multiplication bits do not meet that locality assumption.

Our tensor reduction supplies a separate, explicit factoring implication. Its conditional asymptotic guarantee does not supply practical RSA attack costs, nor refute polynomial-time one-wayness. The existing native long-query implementation and retained soft-O(K^(5/4)) acquisition bound are unchanged; no soft-O(K) native residue algorithm is claimed. If D.1 survives full audit, the multiplication-network route bypasses that query for the factoring objective.

## Source discrepancy, validation and next dependency

Two local printed degree bounds need correction: Appendix B.2 and **equation (D.1)** in §D.3 omit factors present in the correct main-text degree bound. In §D.3 the printed k*a+2(ell-1) should be k*(a+2(ell-1)). A nonzero retained incidence monomial exceeds the printed cap. The correction preserves the fixed-k asymptotic order; details and the explicit control appear in [tensor-counting.md](tensor-counting.md). This is **not Theorem D.1**: the direct tensor-contraction theorem is in §D.1 and proved in §D.4, and the factoring reduction does not use the flawed sparse-encoding cap.

[check_fft_bridge.py](check_fft_bridge.py) checks the transform indexing, inverse normalization, no-wrap convolution, integer carries and parameter inequalities on finite diagnostic inputs. [identity-checks.json](identity-checks.json) records PASS. These checks are not semiprime coverage experiments, an implementation of the paper's algorithm, or proof of its asymptotic theorem. The uniform reduction is established by the algebraic argument and independent reviews, conditional on the source theorem.

The next foundational task is a full audit of Theorem D.1's recursive deformation, precision recovery, implicit child evaluators, and bit complexity. That theorem now stands between this explicit reduction and a claimed deterministic all-semiprime rate; another native representation or larger success sample is not required to state this conditional result. An implementation and Lean certification remain separate work. No commit or push was performed.
