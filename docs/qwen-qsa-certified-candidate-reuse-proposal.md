# Research proposal: certified candidate reuse for Qwen Sparse Attention

Date: 2026-10-24.

Status: research proposal with an elementary real-arithmetic derivation.
There is no implementation, GPU benchmark, trained-model validation, or compiled
Lean proof accompanying this note. Historical novelty is not established.

## Objective

Reduce Qwen3.8-Flash-Next's sparse-attention indexing cost by avoiding most
historical query-key computations on decoding steps where a cheap certificate
proves that a retained candidate set contains the exact current top-k blocks.
Use the existing full-history scorer and DeepSelect when certification fails.

The proposed addition sits **before full-history scoring**. DeepSelect remains
the selection backend. The intended savings are fewer key-cache reads and fewer
dot products, not a replacement for DeepSelect's efficient selection algorithm.

The first target is autoregressive decode within one QSA layer. Extend to
speculative verification or prefill only after establishing the state invariant,
numerical contract, and performance of that simpler case. This is separate from
the [Gated DeltaNet leaf-elimination proposal](gated-deltanet-speculative-leaf-elimination-proposal.md).

## Baseline and prior work

Qwen3.8-Flash-Next alternates three Gated DeltaNet layers with one Qwen Sparse
Attention (QSA) layer. Its indexer uses four 128-dimensional query heads and one
shared key head. It averages groups of four raw index keys, normalizes them,
and applies positional rotation after pooling. It selects 512 complete blocks,
expands them into 2,048 original token positions, and includes the current
incomplete block separately. The main attention reads the original K/V entries.
See the [Qwen technical report, Section 2.1.2](https://arxiv.org/html/2608.30320v1#S2.SS1.SSS2)
and [SGLang's implementation description](https://www.lmsys.org/blog/2026-08-26-qwen-flash-next/).

The comparison baseline must already use the optimized index scorer and
DeepSelect, with the same weights, cache formats, block budget, and causal
semantics. If it already restricts candidates or reuses indices, measure the
incremental benefit against that configuration too.

DeepSelect scans supplied scores, filters them against a rising threshold, and
periodically compacts a small candidate buffer. Its analysis reduces expected
selection work, but every supplied score is still read. It does not itself avoid
producing those scores. See the [pinned algorithm and analysis](https://github.com/deepseek-ai/DeepSelect/blob/bfa4507d935f17ebfc3d0f00ff7d3c9a4d0e5c18/docs/DeepSelect-deep-dive.md).

The DeepInfer inspection used commit
`9bd9cf243fc53ef9afbf8f04d391d989117d6ab9`, its pinned DeepSelect commit above,
and DeepGEMM commit `1fc9c66975ee322d628b3288534ca0e9ce12a64d`.
That code already implements:

- Direct cross-layer reuse of top-k indices in
  [attention execution](https://github.com/deepseek-ai/DeepInfer/blob/9bd9cf243fc53ef9afbf8f04d391d989117d6ab9/deepinfer/model_executor/models/v4_modules/attn.py#L553).
- Source-layer candidate-block selection, followed by later-layer scoring only
  within those candidates, in the
  [indexer runtime](https://github.com/deepseek-ai/DeepInfer/blob/9bd9cf243fc53ef9afbf8f04d391d989117d6ab9/deepinfer/model_executor/models/v4_modules/index_attn.py#L202).
- A configured sharing topology and transient candidate state in
  [cross-layer runtime](https://github.com/deepseek-ai/DeepInfer/blob/9bd9cf243fc53ef9afbf8f04d391d989117d6ab9/deepinfer/model_executor/models/v4_modules/cross_layer.py#L198).

No query-movement certificate for excluded scores, or corresponding certified
fallback, was found in those inspected paths. Their configured restriction can
be part of the intended model architecture; it is not an implementation error.
This inspection establishes a comparison boundary, not absence from all public
or internal DeepSeek work.

Related retrieval reuse also appears in
[ReTopK](https://arxiv.org/abs/2607.27692v1) and
[IndexCache](https://arxiv.org/abs/2603.12201v1). Qwen's MTP path already reuses
indices. The proposed research contribution is therefore narrowly scoped:
**a cheap sufficient certificate for temporal candidate reuse that preserves
the original QSA selector, with an executable fallback and measured net benefit.**

## Score and input contract

Work at one layer and one request. Let $H=4$, $d=128$, and $K=512$.
For a current query $Q=(q_1,\ldots,q_H)$ and a visible complete block $b$, write

$$
s_Q(b)=\sum_{h=1}^{H}\operatorname{ReLU}(q_h^\top k_b).
$$

The positive common score scaling is omitted here because it does not change
rankings. Either omit it everywhere in the certificate or include it consistently
in scores and bounds. The vectors are the actual normalized and rotated index
operands, not hidden states or pre-RoPE projections. Quantization is addressed
separately below.

The initial contract assumes that completed historical block keys do not change
as the sequence grows. If the serving implementation rewrites, requantizes, or
re-rotates old keys, it must invalidate the anchor or include a proved key-change
error. Cache remapping is harmless only when it preserves logical key contents.

The incomplete causal tail is handled exactly as in the baseline; it is not
subject to the block-selection certificate. When at most $K$ complete blocks
are visible, retain the baseline's short-context path.

## Anchor state

At a full-history refresh with query $Q_0$, let $B_0$ be the set of visible
complete blocks. Retain:

1. The anchor query $Q_0$.
2. A candidate set $C_0\subseteq B_0$ of size $L\ge K$, normally the anchor's
   top-$L$ blocks.
3. An upper bound $u_0\ge\max_{b\in B_0\setminus C_0}s_{Q_0}(b)$.
4. A norm bound $R_0\ge\max_{b\in B_0}\|k_b\|_2$.
5. The anchor prefix boundary and the request/layer/cache identity needed to
   check that all these operands still refer to the same historical keys.

A top-$(L+1)$ selection at refresh can supply $C_0$ and the largest excluded
score when there are more than $L$ blocks. The larger selection, metadata
gathering, and storage must be charged. Key norms can be bounded as keys are
written, retaining a running maximum; that work must also be charged. RMS
normalization alone is not permission to assume unit-norm keys.

If no blocks are excluded, the excluded-set condition is vacuous.

For a later query $Q_t$, let $D_t$ contain **every complete block newly visible
since the anchor**, and evaluate the candidate universe

$$
C_t=C_0\cup D_t.
$$

Keeping only the newest block would be incorrect after several successful
reuse steps. Refresh when the growing $D_t$ makes the fast path unattractive.

## Certificate and proof

Define

$$
\Delta_t=R_0\sum_{h=1}^{H}\|q_{t,h}-q_{0,h}\|_2.
$$

For every historical block $b\in B_0$, ReLU is 1-Lipschitz and
Cauchy-Schwarz gives

$$
\begin{aligned}
|s_{Q_t}(b)-s_{Q_0}(b)|
&\le\sum_h |(q_{t,h}-q_{0,h})^\top k_b|\\
&\le\|k_b\|_2\sum_h\|q_{t,h}-q_{0,h}\|_2\\
&\le\Delta_t.
\end{aligned}
$$

Thus every omitted block has current score at most $u_0+\Delta_t$.
Score $C_t$ with the baseline scoring rule and let $\tau_t$ be its $K$th
largest score. The sufficient certificate is

$$
\boxed{\tau_t>u_0+\Delta_t.}
$$

There are at least $K$ evaluated blocks above every omitted score, so the global
top-$K$ is contained in $C_t$. Selecting within $C_t$ therefore returns the same
top-$K$ under a common deterministic tie rule. The strict inequality prevents
an omitted block from tying the selection boundary. Failure is inconclusive;
it does not imply that the candidate set is wrong.

Use the same global-block-ID tie rule in restricted and full selection.
If the chosen library does not provide that contract, separately specify what
set equivalence means and send ambiguous boundary ties to the reference path.
Changing the tie policy silently is not exact baseline preservation.

### Persistent invariant

After a successful fast step, keep $Q_0,u_0,R_0,B_0$ unchanged. They still refer
to the last full refresh. Replacing $Q_0$ by the latest query while retaining
$u_0$ would invalidate the proof. An alternative that updates the bound by a
proved accumulated drift is possible, but is not the initial design.

For speculative branches, the anchor must describe a common, still-valid
prefix; all branch-specific visible blocks belong to that branch's candidate
universe. A rejected branch cannot publish its anchor metadata to an accepted
branch. The first implementation can simply invalidate on unsupported rollback,
eviction, cache conversion, or positional-coordinate changes.

## Integration with DeepSelect

```text
select_blocks(query, visible_prefix, anchor):
    if anchor is absent, invalid, or due for refresh:
        return full_scan_select_and_refresh(query, visible_prefix)

    candidates = anchor.candidates union all_new_complete_blocks(anchor)
    candidate_scores = baseline_score(query, candidates)
    selected, kth_score = DeepSelect(candidate_scores, K)
    excluded_upper = certified_excluded_bound(query, anchor)

    if kth_score > excluded_upper and tie_contract_is_satisfied:
        return selected mapped to global block IDs

    return full_scan_select_and_refresh(query, visible_prefix)
```

Always preserve the baseline's forced tail and causal masking when expanding
blocks into attention token IDs. Compute main-attention probabilities and
outputs normally; no historical attention weights or outputs are reused.

The fallback may recompute candidate scores as part of its full scan. Avoiding
that duplication is optional, and must not cost more than it saves. In the
first measurement, count it explicitly. GPU implementation must also account
for the decision: a device flag, conditional graph, or host synchronization has
real cost. A fast mathematical test does not imply a cheap serving control path.

## Floating-point and quantization contract

The theorem above is over real arithmetic. It is insufficient by itself to
claim exact agreement with a BF16/FP16/FP4 GPU implementation.

Define the real reference score using the dequantized operands actually used
by the baseline kernel. For stored computed anchor scores $\widehat s_0$ and
computed current scores $\widehat s_t$, suppose valid uniform bounds satisfy

$$
|\widehat s_0(b)-s_{Q_0}(b)|\le E_0,\qquad
|\widehat s_t(b)-s_{Q_t}(b)|\le E_t.
$$

If the cached bound is on computed anchor scores, a sufficient computed-score
upper bound for omitted blocks is

$$
U_t=u_0+E_0+\Delta_t+E_t.
$$

The bound covers dot-product accumulation, intermediate conversions, ReLU,
head reduction, and any common scaling. Compute norms, sums, and the final
upper bound conservatively; rounding an upper bound downward is unsound.
The restricted scoring kernel must agree with the chosen baseline arithmetic,
or its own discrepancy must be handled explicitly. NaNs, overflow, unsupported
quantization, or an unverified error bound trigger the baseline path.

An initial FP32 reference study may measure the potential of the real-arithmetic
certificate. A production correctness claim requires a concrete error model for
the actual kernels and cache formats. Matching outputs within a tolerance is a
different claim from matching selected IDs or sampled token streams.

## Cost model and break-even condition

Let $B$ be the number of visible compressed blocks and $L_t=|C_t|$.

| Component | Full scan with DeepSelect | Certified fast attempt |
|---|---|---|
| Index scoring | $O(BHd)$ | $O(L_tHd)$ |
| Index-key reads | All visible keys | Candidate and new-block keys |
| Selection | DeepSelect over $B$ scores | DeepSelect over $L_t$ scores |
| Query-change bound | None | $O(Hd)$ plus retained metadata |
| Persistent extra state | None from this proposal | Anchor queries, candidate IDs, bound and validity metadata |

At one million tokens, four-token compression gives about 250,000 complete
blocks. Trying an anchor shortlist of 2,048 blocks illustrates the possible
reduction in score count; **2,048 candidate blocks are not Qwen's 2,048-token
attention budget**, and this example is not a predicted speedup.

Let $F$ be baseline full-scan time, $A$ the complete fast-attempt time including
restricted selection and the decision, and $p$ the probability of certification.
Let $R$ be the amortized additional refresh and metadata cost beyond the baseline.
Under the simple fallback that reruns the full scan,

$$
\mathbb E[T]=A+(1-p)F+R.
$$

Net benefit requires $pF>A+R$. Low certification rates can make the proposal
slower. This model must include cache gathers, launch overhead, synchronization,
GPU tile utilization, growing new-block sets, and the larger refresh selection.
Whole-model gains depend on how much time the indexer consumes.

## Implementation and evaluation plan

### 1. Reproducible reference and state tests

Implement a baseline selector and the anchored selector on identical supplied
operands. Check the certificate proof obligations and compare every certified
result against a full scan. Exercise ties, zero scores, near-boundary scores,
large query changes, high-norm keys, short prefixes, and newly completed blocks.
Test repeated successes without resetting the anchor, forced refreshes,
cache invalidation, and accepted-prefix rollback.

Small synthetic checks are correctness diagnostics only. They cannot establish
that learned Qwen queries change slowly enough for useful certification.

### 2. Measure the certificate on actual Qwen traces

Capture queries and index keys at their actual normalization, rotation, and
quantization boundaries. Begin with within-layer decode traces over several
context lengths and workloads, including retrieval-heavy and abrupt topic-change
cases. Sweep shortlist size and refresh policy.

Record per layer and request:

- Certification rate and duration of successful reuse runs.
- $\tau_t-u_0$, the drift bound $\Delta_t$, and rounding margins separately.
- Candidate count, newly visible block count, and refresh frequency.
- Exact selected-ID agreement with the full reference on every certified step.
- Whether rare high-norm keys make the global norm bound too loose.

Decide whether the elementary certificate is useful before building a GPU kernel.
If it rarely succeeds, possible follow-ups include several retained anchors or
per-group norm/score bounds, with their acquisition, memory, and query costs
charged. These are further experiments, not assumed improvements.

### 3. Matched GPU and serving benchmark

Compare against the same optimized full scorer plus DeepSelect, not
`torch.topk` or an unfused reference. Measure fast successes, failures, and
refreshes separately, then the full decode lifecycle. Include batch size,
context length, shortlist size, and cache format in the results.

Report indexer latency, bytes read, temporary and persistent memory, control-flow
overhead, and whole-model time per committed token. If testing an existing
candidate-restricted implementation, retain its intended semantics and identify
which additional scans this proposal actually removes.

### 4. Acceptance criteria

The proposal succeeds only if the chosen numerical contract is satisfied and
verification-plus-fallback-plus-refresh cost is lower on representative workloads.
Report workloads where it regresses. A higher certificate pass rate obtained by
loosening an unproved bound does not count as progress.

## Secondary idea: the 16-subset identity

For Qwen's unweighted four-head score, define $a_A=\sum_{h\in A}q_h$ for each
subset $A\subseteq\{1,2,3,4\}$. Then

$$
s_Q(b)=\max_A a_A^\top k_b.
$$

With consistent tie-breaking, the global top-$K$ is contained in the union of
the top-$K$ lists for these 16 linear scores. For a purported omitted winner,
choose a subset attaining its score. If $K$ blocks precede it under that linear
score, their QSA scores are at least as large, contradicting its global rank.
The empty subset handles the zero-score case.

This is a possible connection to
[exact maximum-inner-product search](https://arxiv.org/abs/1202.6101v1), not a
completed speedup: 16 exhaustive scans would be worse than the baseline.
Building and updating an index, shared traversal, causal filtering, exact
reranking, and worst-case failure of pruning all remain to be evaluated.

It is not the first implementation target of this proposal. DeepSeek's
[learned head weights](https://github.com/deepseek-ai/DeepInfer/blob/9bd9cf243fc53ef9afbf8f04d391d989117d6ab9/deepinfer/model_executor/models/v4_modules/mla_attn.py#L131)
are not constrained nonnegative in the inspected path, so the simple
maximum-over-subsets identity does not transfer unchanged to its general score.

## Relationship to the repository's mathematical work

The [recent recurrence investigation](semiprime-factorisation-investigation.md)
motivates computing only the observable actually consumed and accounting for
the residual when shared work is removed. Here that residual is an explicit
bound on omitted scores. The proof uses elementary Lipschitz and norm bounds;
it does not require the repository's geometric-grid recurrence identities,
arithmetic cancellation estimates, or any RH hypothesis.

Candidate reuse is established prior work. The certificate, its numerical
realization, and its practical usefulness are the scoped research questions.
This document makes no new RH, semiprime-factorization, or measured inference
performance claim.
