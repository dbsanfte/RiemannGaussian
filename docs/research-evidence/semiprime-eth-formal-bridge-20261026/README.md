# ETH formal bridge: two counting routes and an executable factor network

26 October 2026. The user resumed the scaling goal, then broadened its wording to
“pursue the 1/6 (or better!) scaling goal.” It remains active. The preceding paper
study was substantive progress: it supplied an explicit linear-wire reduction
from factoring to the source's tensor theorem. This checkpoint audits that
dependency, follows the user's Lean-source lead, and begins the actual formal
and executable connection. The final all-semiprime bit-complexity/Lean goal is
**not complete**.

## What changed

1. **The earlier counting mechanism also suffices mathematically.** Our network
   can be handled by Proposition 3.4 and Lemma 4.7 of the paper, with manually
   verified parameters and streamed multilinear evaluation. This avoids needing
   Appendix D's newer contraction algorithm. The resulting proposed factoring
   bound is
   \[
   2^{O(L(\log\log L)^2/\sqrt{\log L})}\operatorname{poly}(L)=N^{o(1)},
   \qquad L=\lceil\log_2(N+1)\rceil.
   \]
   This is an independently reviewed mathematical derivation from those generic
   lemmas, **not yet a compiled theorem for the complete factoring algorithm**.
2. **The published Lean result exists, with a narrower interface.** At pinned
   OpenAI commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, the catalogue names
   `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`.
   It proves the earlier rate for fixed-width CNF on an actual primitive machine.
   Its statement does not supply the high-arity tensor counter automatically.
   An isolated strict build of its 2,569-module source closure is running; see
   [external-build-snapshot.json](external-build-snapshot.json). Its full endpoint
   has **not** been reported locally verified.
3. **The local evaluator and its true degree bound now compile in Lean.**
   [SemiprimeStreamingTensor.lean](SemiprimeStreamingTensor.lean) is a snapshot of
   the new repository module. It proves exact multilinear evaluation, Boolean
   recovery, branch-attached leaf/depth counts, and the total-incidence degree
   bound. The strict build and standard-axiom reports are in
   [streaming-repo-build.log](streaming-repo-build.log).
4. **The factor network is now executable.** [factor_network.py](factor_network.py)
   emits actual Boolean edges, ordered ports and local entry predicates. It
   validates supplied witnesses and supports prefix restrictions. Independent
   review and structural controls pass. It does not implement a contraction
   solver or search for factors.

## The earlier route: why the large local tensors are affordable

Let n be the actual number of bit edges in the network, and w the maximum local
arity. Each edge occurs at its two endpoints, so the occurrence bound is b=2 and
the total incidence is 2n. A local Boolean predicate T_v has the genuine rational
multilinear extension

\[
 \Phi_v(X)=\sum_{a\in\{0,1\}^{w_v}}T_v(a)
       \prod_j\bigl(a_jX_j+(1-a_j)(1-X_j)\bigr).
\]

The product's degree in separate incidence variables is at most
\(\sum_v w_v=2n\). This avoids multiplying maximum arity by the number of
vertices. Substituting degree-R paths therefore gives degree at most 2nR.
The new compiled theorem
`RiemannGaussian.SemiprimeStreamingTensor.natDegree_sum_product_evaluate_le`
proves exactly this sum-of-arities degree estimate for the actual recursive
evaluator.

The paper's generic Lemma 4.7 permits growing w. With
\(\lambda=\lceil\log_2n\rceil\), \(\nu=\lceil\log_2\lambda\rceil\), reuse
the numerical choices r=floor(sqrt(lambda)/nu²), Q=floor(lambda/(128nu)),
R=4ceil(sqrt(lambda)), tau=1/(r lambda), D=r^(2Q). The relevant balance condition
is

\[
 2(b+w)D^2=O(n^{3/4+1/64})=O(n^{49/64})<2n.
\]

The binomial-tail condition depends on b, not w. The other balance condition is
polylogarithmic. Thus these parameters work for our w=O(n^(3/4)), after a finite
fallback. This is a direct verification of Lemma 4.7; Lemma 4.8's stated
polylogarithmic-scope premise is not silently reused.

Evaluate each Phi at the actual non-Boolean Taylor inputs by streaming its 2^w
Boolean table entries. This costs 2^w times polynomial bit work and needs only
polynomial working space. One common denominator per factor, and ultimately
`((R-1)! Q!)^(2n)` for the entire product, prevents denominator growth with the
number of summands. Coefficient heights and final interpolation are polynomial.
The overall bound is

\[
 \operatorname{poly}(n+\text{description length})
 2^{O(n\nu^2/\sqrt\lambda)+O(w)}.
\]

Since our compiler has n=Theta(L), w=O(L^(3/4)), and polynomial-time local entry
checks, this yields the displayed N^o(1) derivation with O(L) conditional counts
for witness recovery. Full details are in §9 of [complexity.md](complexity.md)
and the independent [older-route review](older-route-review.md). This supplies a
second mathematical route, with a slower exponent than D.1 but still stronger
asymptotically than every fixed N^epsilon. It leaves the old native long-query
acquisition algorithm unchanged.

## Formal coverage and the remaining work

The [source specification audit](lean-specification.md) verifies that the
published SAT statement really quantifies over one fixed finite primitive
machine before its inputs, counts satisfying assignments, writes the result,
and bounds every prefix's visited tape cells. The comparator challenge's
`sorry` is its expected-statement placeholder; the actual solution closure has
no textual `sorry`, custom axiom declarations or `native_decide`. Those scans
are preliminary evidence, not substitutes for the running build or axiom audit.

[formal-bridge.md](formal-bridge.md) identifies reusable generic source interfaces
and the new obligations. The old fixed-k SAT endpoint cannot simply be called
with growing tensor arity. The report's initial external-module degree proposal
has been superseded by the directly compiled Mathlib-only degree proof in the
new repository module, avoiding that dependency wait.

Locally compiled theorems include:

- `evaluateTracked_eq_sum`: exact multilinear value with 2^w leaf calls and depth w.
- `evaluateTracked_at_boolean`: exact original tensor value at Boolean inputs.
- `natDegree_evaluate_le`: local degree at most wR.
- `natDegree_sum_product_evaluate_le`: global degree at most `(sum arities)R`.

All are in namespace `RiemannGaussian.SemiprimeStreamingTensor`. They use only
`propext`, `Classical.choice` and `Quot.sound` as applicable. Their counters are
attached to the evaluator's recursive branches. They do **not** prove primitive
bit-time or physical workspace by treating a general table function as a free
oracle. Entry-verifier costs, rational coefficient bounds, the interpolation
schedule, layout guards, the counting-machine wrapper, and formal compilation
of the multiplication network must still be connected.

## Network implementation and Appendix D audit

The compiler uses the explicit ring Z/(2^nfft+1), principal root 4, two macro
Fourier stages per transform, canonical words, and integer carry checks. It has
explicit twiddle vertices, unlike the earlier mathematical version which folded
twiddles into adjacent predicates. Its exact pre-subdivision edge count is
`(13*nfft+1)*(nfft+1)+4*d-2`; subdivision doubles it. The same O(L) edge and
O(L^(3/4)) degree bounds hold. See [implementation notes](factor-network-notes.md)
and [independent code review](review-factor-network-code.md).

The [tests](test_factor_network.py) verify wiring, exact carry behavior,
canonical residues, prefix restrictions, invalid supplied witnesses and inversion
over a composite auxiliary ring. These are compiler controls, not a semiprime
success campaign or evidence for an asymptotic factoring rate.

The three assigned audits of D.1 found no essential gap in its stated
construction: [precision recovery](precision.md), [mode/child identities](modes.md)
and [packing/runtime](complexity.md). Exact finite controls accompany the first
two. This is a manual reconstruction, not Lean certification of Appendix D.
The earlier-route connection is now the primary formalization target because
it can reuse the published generic counting infrastructure.

## Continuation

Continue the existing external build handle recorded in the snapshot; do not
restart it merely because an observation times out. Then complete the generic
counter's evaluator/precision/resource connection and certify the network
compiler. The source proof checkout remains unmodified and is pinned with its
Apache-2.0 provenance. Previous research and concurrent files are preserved.
No complete factoring rate, finished goal, commit, push or comparator success is
claimed by this checkpoint.
