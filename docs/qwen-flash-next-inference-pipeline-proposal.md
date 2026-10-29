# Research proposal: further Qwen3.8-Flash-Next inference optimizations

Date: 2026-10-25. Source audit and reference checks: 2026-10-24.

Status: implementation proposals supported by source inspection, real-arithmetic
identities, scratch Lean checks, and synthetic reference diagnostics. No GPU
kernel, trained-model experiment, measured speedup, or production numerical
equivalence result is supplied. Historical novelty is not established. This
investigation makes no RH or semiprime-factorisation progress claim.

## Scope and priorities

This proposal covers the inference pipeline beyond the three attention/GDN
ideas already handed to implementation:

1. The tighter 16-subset QSA temporal certificate.
2. Backward-query evaluation of Gated DeltaNet outputs.
3. Page-level QSA pruning.

The related starting notes are the
[QSA candidate-reuse proposal](qwen-qsa-certified-candidate-reuse-proposal.md)
and [GDN leaf-elimination proposal](gated-deltanet-speculative-leaf-elimination-proposal.md).
Numbering below continues at 4 so implementation handoffs remain unambiguous.

| ID | Candidate | Intended benefit | Initial priority |
|---|---|---|---|
| 4 | Select rows before the terminal GR mixer | Remove unused prefill-row projections | First implementation batch |
| 5 | Cache the fixed MTP token transform | Replace a repeated projection with a lookup | First implementation batch |
| 6 | Cache or prefetch PLE projected context | Remove or overlap immutable PLE work | Measure locality and contention |
| 7 | Circular PLE convolution history | Remove history shifts and a temporary window | First implementation batch |
| 8 | Captured-scalar PLE history codec | Reduce history storage and reads | Follow the ring implementation |
| 9 | Compact vocabulary-shard summaries | Reduce logits communication | First implementation batch |
| 10 | Certified coarse LM-head screening | Avoid most original-head weight reads | Research; certificate usefulness unknown |
| 11 | Certified RoPE tile recurrence | Trade phase-table traffic for arithmetic | Lower-priority research |

All work counts below are component counts, not latency estimates. Real
identities do not by themselves preserve a particular floating-point kernel's
rounding, tie decisions, or sampled token stream.

## Inspected sources and model dimensions

The audit used these pinned sources:

- SGLang: `656331295619a4d0267b40b7da0b5cd5b549fcbc`.
- Transformers: `50e35cc0ca18ec19b80653690de553e6decf74f5`.
- Official BF16 checkpoint configuration:
  `de4b8e4d43b917e7706784d8bb445c9af86a3540`.

Primary references are the
[Qwen architecture report](https://arxiv.org/html/2608.30320v1),
[checkpoint configuration](https://huggingface.co/Qwen/Qwen3.8-Flash-Next/blob/de4b8e4d43b917e7706784d8bb445c9af86a3540/config.json),
[SGLang model](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp.py),
and [Transformers reference model](https://github.com/huggingface/transformers/blob/50e35cc0ca18ec19b80653690de553e6decf74f5/src/transformers/models/qwen4_exp/modeling_qwen4_exp.py).
The implementation calls this architecture `qwen4_exp`.

Relevant dimensions are hidden width \(d=2560\), four residual branches,
GR bottleneck rank 320, 48 decoder layers, 512 routed experts with top-10
routing, expert and shared-expert intermediate width 640, and vocabulary size
248,320. PLE uses four convolution taps at dilation three, giving a nine-token
history. There is one full-attention MTP draft layer, with PLE disabled.

## Pipeline equations

The following equations describe real-arithmetic operations. Explicit cast
boundaries are restored where essential to proposal 8. Stored zero-centered
RMSNorm parameters appear as \(1+\gamma\).

### Gated residual reads and writes

For residual branches \(R_i\in\mathbb R^d\),

\[
N_i=\frac{(1+\gamma_i)\odot R_i}
 {\sqrt{d^{-1}\|R_i\|_2^2+\epsilon}},
\qquad
G=\operatorname{unvec}\,\sigma\!\left(
 W_u\operatorname{SiLU}(W_d\operatorname{vec}(N)/4)\right),
\]
\[
x=\frac14\sum_iG_i\odot N_i,
\qquad
s=2\sigma(W_w\operatorname{vec}(N)/4),
\qquad
R'_i=R_i+s_iF(x).
\]

The read gate is channelwise; the write gate is scalar per branch. Each
attention and MoE sublayer has its own GR module. The read replaces the block's
pre-normalization. The final text operation is another GR read followed by
the vocabulary projection, with no additional final text RMSNorm.
See the [GR implementation](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/hyperconnection.py#L199).

### GDN projections, convolutions, and output gates

Input projections produce the query, key, value, output-gate, and two
recurrence-gate streams. Queries and keys pass through a four-tap depthwise
causal convolution, SiLU, and L2 normalization; values pass through convolution
and SiLU. The recurrence gates have the form

\[
\beta_t=\sigma(b_t),\qquad
\alpha_t=\exp[-\exp(A)\operatorname{softplus}(a_t+b_{\rm dt})].
\]

After the GDN core, each value head is normalized and multiplied by its sigmoid
output gate before concatenation and output projection. The different head
denominators cannot be replaced by one global output-projection scalar.
Supported backends already pack input projections.
See [the GDN peripheral implementation](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen3_5.py#L393).

### PLE n-gram injection

PLE concatenates sixteen 160-dimensional lookup rows: eight bigram heads and
eight trigram heads. For the resulting \(E\in\mathbb R^{2560}\),

\[
K=W_KE,\quad V=W_VE,\quad
a_i=\frac{\langle N_{K,i}(K_i),N_{Q,i}(R_i)\rangle}{\sqrt d},
\]
\[
g_i=\sigma\!\left(\operatorname{sign}(a_i)
       \sqrt{\max(|a_i|,10^{-6})}\right),\quad
U_i=g_iV,\quad X_i=N_{{\rm conv},i}(U_i).
\]

The gate includes the signed square-root transform, not just a sigmoid of
the dot product. The PLE output is

\[
C_t=w_0\odot X_{t-9}+w_1\odot X_{t-6}
       +w_2\odot X_{t-3}+w_3\odot X_t,
\qquad
\Delta_t=U_t+\operatorname{SiLU}(C_t).
\]

The widened residual receives \(R\leftarrow R+\Delta\) before the second
decoder layer. Actual gate and normalization kernels have intermediate casts.
See [PLE forward](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp.py#L1338).

### Routed and shared experts

With router logits \(r=W_rx\), selected set \(I=\operatorname{Top10}(r)\),
and top-k renormalization enabled,

\[
p_e=\frac{e^{r_e}}{\sum_{j\in I}e^{r_j}},\qquad
F_e(x)=D_e\!\left(\operatorname{SiLU}(G_ex)\odot U_ex\right),
\]
\[
F_{\rm MoE}(x)=\sum_{e\in I}p_eF_e(x)
 +\sigma(w_s^\top x)F_s(x).
\]

The shared expert is separate from routed-expert normalization. The checkpoint
omits `norm_topk_prob`, but its official configuration class defaults it to
`True`. See the [router and shared expert](https://github.com/huggingface/transformers/blob/50e35cc0ca18ec19b80653690de553e6decf74f5/src/transformers/models/qwen4_exp/modeling_qwen4_exp.py#L952)
and [configuration default](https://github.com/huggingface/transformers/blob/50e35cc0ca18ec19b80653690de553e6decf74f5/src/transformers/models/qwen4_exp/configuration_qwen4_exp.py#L162).

### Vocabulary output, sampling, and MTP

The target output is \(h=\operatorname{GRMix}_{\rm out}(R)\),
\(z=W_{\rm vocab}h\). Logit processing and the requested sampler follow.
The checkpoint's generation defaults are temperature 1, top-k 20, and top-p
0.95. The inspected SGLang path applies top-k and top-p jointly.

The MTP input fusion is

\[
u_i=F_h\bigl[N_{\rm flat}(R)\bigr]_i
       +F_eN_e(E[t]).
\]

Here the hidden-input normalization is over the full flattened four-branch
stream before reshaping it into branches. The text-token embedding transform
is broadcast across the four branches. See
[MTP input fusion](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp_mtp.py#L116).

### Optional vision input

The inherited vision path applies patch projection plus interpolated positional
embeddings, then 27 blocks of width 1152:

\[
X'=X+\operatorname{Attention}(\operatorname{LayerNorm}(X)),
\qquad
X''=X'+W_2\operatorname{GELU}(W_1\operatorname{LayerNorm}(X')+b_1)+b_2.
\]

The patch merger normalizes each patch, concatenates a spatial 2-by-2 group,
and applies a two-layer GELU projection to width 2560. These features replace
visual-token embeddings. No additional unconditional theorem-driven vision
speedup was established. See [vision blocks and merger](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen3_vl.py#L261).

## 4. Select consumed rows before the terminal GR mixer

The model applies its terminal mixer to every token row. For prefill without
input logprobs, the logits processor subsequently keeps only the final row of
each sequence. Because the mixer is token-local,

\[
\operatorname{Gather}_J(\operatorname{Mix}(R))
 =\operatorname{Mix}(\operatorname{Gather}_J R).
\]

This identity permits nonlinear row-local functions: no linearity of GR is
assumed. Moving selection earlier removes

\[
10240\cdot320+320\cdot10240=6{,}553{,}600
\]

down/up projection FMA per omitted terminal row, plus associated temporaries.
The prior layer may already have prepared normalization for all rows; that
work is not removed by this change alone.

Implementation requirements:

- Complete pending residual or `DeferredFinalize` work and required captures
  before selecting; do not index an opaque owed-state handle.
- Gather `normalized_input` with the same indices.
- Preserve full raw HC states where MTP or full-state capture consumes them.
- Handle context-parallel global/local row mappings and prevent double pruning.
- Retain all rows needed for requested input logprobs or other output modes.
- Check numerical differences when the smaller batch selects another kernel.

The insertion points are the
[terminal mixer call](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp.py#L2130)
and [later row pruning](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/logits_processor.py#L687).
Scratch `select_rowwise` and `select_rowwise_with_aux` check the composition
identity; they do not prove the serving integration.

## 5. Cache the immutable MTP token transform

Define the table or cache entry

\[
T[t]=F_eN_e(E[t]).
\]

For ordinary text tokens this is a fixed function of token ID and model
parameters. A lookup can replace its repeated normalization and projection.
No transformed-token cache was identified in the inspected MTP path.

| Component | Size or work |
|---|---:|
| Removed projection per cache hit | 6,553,600 FMA |
| Full transformed BF16 table | 1,271,398,400 bytes |
| 8,192-row BF16 cache | 41,943,040 bytes (40 MiB) |
| Projection work to initialize the full table | 1,627,389,952,000 FMA |

Retain the original embedding table for target-model consumers. Dynamic
multimodal embeddings bypass this cache. Key or invalidate entries by relevant
weight/adaptor generation, dtype, and arithmetic contract. Cache lookup,
misses, initialization, storage, and eviction costs belong in the benchmark.
Batch-dependent GEMM rounding means real-arithmetic tabulation alone does not
guarantee a bit-identical serving result.

Scratch `fixed_embedding_consumer_lookup` checks the fixed-function identity.
This is ordinary tabulation, with no special number-theoretic premise.

## 6. Cache or advance PLE's immutable projected context

The complete lookup-ID tuple determines

\[
(\widehat K,V)=\bigl(N_K(W_KE),W_VE\bigr)
\]

before the query-dependent gate reads the residual. The current prefetch path
gathers embeddings; projections and key normalization occur later in forward.

A bounded cache can retain this pair, keyed by all sixteen lookup IDs plus the
model/arithmetic generation. A hit avoids both projections and key
normalization. It also avoids the host gather if the cache is checked before
prefetch; a lookup only at forward may already have paid that gather. Its
BF16 entry has 12,800 values, or 25,600 bytes.
The two projections require 32,768,000 FMA per token.

An alternative is to advance the projections and key normalization onto the
existing prefetch stream. Combining the two linear projections into one GEMM
is another scheduling option, subject to supported quantization layouts.
Count resource contention with preceding-layer work, larger buffers, cache
lookup/misses, and any changed arithmetic.

Do not preproject every individual table row into the full output space without
paying the storage expansion: mapping a 160-wide row to 12,800 outputs expands
that representation by 80 times. The proposed context cache is bounded and
stores results only for contexts actually acquired.

See [prefetch](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp.py#L1275)
and [projection placement](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp.py#L1340).

## 7. Circular PLE convolution history

The four-tap, dilation-three convolution consumes only the history at offsets
9, 6, and 3, plus the current input. The inspected decode implementation
materializes a ten-column window and shifts all nine history columns. Its
fused state kernel still copies the complete history.

Maintain nine slots and an oldest-slot cursor \(p\). Read slots
\(p,p+3,p+6\pmod9\), combine them with the current input, overwrite slot
\(p\), then advance the cursor. This removes the full shift and temporary
window, requiring three historical vector reads and one history-vector write.

Preserve tap accumulation order, output casts, SiLU, request indexing, and
padding-slot behavior. The cursor belongs to the recurrent state: copy,
prefix-cache, checkpoint, rollback, and export operations must preserve it.
Start with decode; verification's intermediate snapshots need a separate
integration audit.

See [the current decode path](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/models/qwen4_exp.py#L1126)
and [state-copy kernel](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/kernels/ops/mamba/qwen4_short_conv.py#L12).
Scratch `circular_write_eq_shift` proves the representation invariant for
arbitrary payloads and every positive ring length. It does not certify a GPU
kernel or its serving lifecycle.

## 8. Captured-scalar PLE history codec

The four PLE branches share one value vector. Exploit that structure while
retaining the actual intermediate rounding, rather than replacing four
normalization reductions by an idealized shared norm.

For the inspected BF16 decode path, let \(g_i\) denote the actual rounded
activated gate and let \(r_i\) be the actual FP32 reciprocal produced by
normalizing the rounded branch input. Then

\[
U_{i,j}=\operatorname{BF16}(g_iV_j),
\]
\[
X_{i,j}=\operatorname{BF16}\!\left(
  (\operatorname{FP32}(U_{i,j})r_i)
  (1+\operatorname{FP32}(\gamma_{i,j}))\right).
\]

Store \(V\), four activated gates, and four captured reciprocals. Reconstruct
\(X\) on convolution reads using the same multiplication and cast sequence.
The normalization gains remain fixed model state. Capture \(r_i\) from the
original reduction; recomputing it in another order does not preserve the
same numerical contract.

| Default BF16 representation | Per token | Nine-token history |
|---|---:|---:|
| Four full normalized branches | 20,480 bytes | 184,320 bytes |
| Value vector, gates, reciprocals | 5,144 bytes | 46,296 bytes |

These counts exclude alignment and cursor metadata. The convolution cache
dtype is configurable; the table assumes its default BF16 representation.
The tradeoff is extra reconstruction arithmetic and static gain reads at each
tap. Capturing scalars and integrating the new state format are also paid work.

See [gate casts](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/kernels/ops/elementwise/qwen4_gate.py#L24)
and [normalization arithmetic](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/kernels/jit/csrc/elementwise/grouped_gemma_rmsnorm.cuh#L95).
Actual GPU equivalence requires matching compiler/FMA/cast behavior for the
supported backend. Other gate kernels, verification paths, and cache dtypes
need their own reconstruction contract or a fallback.

## 9. Compact vocabulary-shard output summaries

Under a common score/token-ID tie order, global top-k is contained in the union
of shard-local top-k. Keep local LM projection, but communicate candidates and
partition statistics instead of all vocabulary logits. For shard \(V_r\),

\[
m_r=\max_{v\in V_r}z_v,\qquad
S_r=\sum_{v\in V_r}e^{z_v-m_r},
\]
\[
M=\max_rm_r,\qquad Z_M=\sum_re^{m_r-M}S_r.
\]

The combined candidates contain the exact global top-k, and \(Z_M\) supplies
the full-vocabulary normalization. At TP8 and top-k 20, FP32-score/INT32-ID
pairs plus two FP32 statistics per rank contain 1,344 bytes per output row,
compared with 993,280 bytes for a full FP32 vocabulary row. These are logical
payload sizes, not total collective wire traffic. All local LM projection
FMA and weight reads remain.

The inspected sampler uses joint top-k/top-p. Applying top-p after normalizing
only the top-k changes support. For example, probabilities
\((0.5,0.25,0.15,0.1)\), top-k 2, and top-p 0.6 retain the first two entries
under the inspected joint semantics; top-k-first renormalization retains only
the first. Preserve the full partition or a sufficient certificate for the
same support decision.

Apply penalties, grammar masks, and temperature before constructing summaries.
Specify ties, empty/all-masked cases, requested logprobs, speculative
probabilities, and RNG behavior. Full-output requests need an explicit path.
The existing deferred-argmax machinery is an implementation precedent, but
its shard-return guard depends on softcapping absent from the official Qwen
configuration; it does not establish that Qwen already avoids the gather.

See [logits processing](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/logits_processor.py#L938)
and [joint sampler invocation](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/sampler.py#L435).
Scratch certificates cover rank containment, exponential reanchoring, and
normalization cancellation, not the full sampling implementation.

## 10. Certified coarse LM-head screening

This is a research extension with unknown practical certification rates.
Evaluate a cheaper proxy head \(\widetilde W\), retain original weights for
refinement, and obtain conservative intervals using

\[
|W_jh-\widetilde W_jh|
 \le\|W_j-\widetilde W_j\|_2\|h\|_2+\epsilon_{\rm arithmetic}.
\]

Refine promising rows until every omitted upper bound is strictly below the
kth exact selected score. Preserving selected IDs alone is insufficient:
selected logits and downstream support/weights must meet the numerical
contract too.

For joint nucleus sampling, obtain partition bounds
\(Z_{\rm lo}\le Z\le Z_{\rm hi}\) on a common exponent scale. With exact
selected weights in descending order and preceding mass \(C_r\),

\[
C_r\le pZ_{\rm lo}\ \Longrightarrow\ \text{include rank }r,
\qquad
C_r>pZ_{\rm hi}\ \Longrightarrow\ \text{exclude rank }r.
\]

Refine ambiguous cases or run the reference path. Once the support is
certified, the full partition cancels when normalizing the surviving exact
weights. Requests for original full-model logprobs still require the full
partition.

For scale, the BF16 vocabulary head contains about 1.271 GB. An INT4 proxy
contains about 318 MB before scales; one FP32 row-error bound per vocabulary
item adds about 0.993 MB. Twenty exact BF16 rows contain 102.4 KB. Count the
proxy scan, additional resident storage, candidate gathers, interval
evaluation, refinement, and failures. Loose norm bounds may eliminate any
benefit. No useful learned-weight certificate has been supplied.

The same idea applies to the 512-row router, with a smaller optimization
ceiling. Router weights must still be computed accurately after selecting
experts.

## 11. RoPE tile recurrence with an explicit error budget

The existing project theorem
[`ComplexApproximateOrbit.error_le`](../RiemannGaussian/ComplexApproximateOrbit.lean)
and its trigonometric specialization prove

\[
\|v_n-u^n\|\le n(\varepsilon B+\delta)
\]

given a unit exact rotation \(u\), an approximate rotation base within
\(\varepsilon\), a computed-orbit norm bound \(B\), and a per-step residual
bound \(\delta\). This can support periodically reanchored phase recurrence
within bounded prefill tiles.

The actual arithmetic must independently supply the error budgets. Respect
MRoPE's coordinate runs and the partial rotary dimension: only 64 of the
configured 256 attention-head coordinates rotate. This trades phase-table
traffic or trigonometric evaluation for arithmetic; cached phase tables may
already be cheaper. No bitwise-equivalence or performance claim is made.

## Existing theorem connections and rejected shortcuts

| Source | Transfer supported | Remaining obligation |
|---|---|---|
| Mathlib `Function.comp_assoc` | Row selection through arbitrary row-local functions; fixed-function tabulation | Actual consumer/capture and numerical contracts |
| Mathlib `Matrix.mulVec_smul`, finite-sum identities | Scalar transport and distributed reduction | Preserve group axes, bias placement, and arithmetic |
| [ComplexApproximateOrbit](../RiemannGaussian/ComplexApproximateOrbit.lean) | Quantitative approximate rotation recurrence | Supply actual base/step errors and orbit bound |
| [CertifiedQuadraticForm](../RiemannGaussian/CertifiedQuadraticForm.lean), `posSemidef_of_gram_residual` | Offline PSD certificates from a supplied Gram factor and residual | Acquire a useful certificate for the actual weight error |
| [ProjectionHeatLeakage](../RiemannGaussian/Hybrid/ProjectionHeatLeakage.lean), `compressedMatrix_mul_compressedMatrix` | Exact missing term under projected matrix composition | Eliminate or bound the complementary transition |
| [FiniteAbelVariation](../RiemannGaussian/FiniteAbelVariation.lean) | Transport supplied prefix-error bounds through weighted sums | Supply the original prefix bounds; learned cancellation is not automatic |

For example, for \(\tau\ge0\), a certificate
\(\tau^2I-(W-\widetilde W)^\top(W-\widetilde W)\succeq0\)
would bound projection error by \(\tau\|x\|\). The project theorem is
certificate infrastructure, not an acquired useful approximation to Qwen's
weights. The practical cache and ring ideas use ordinary function and finite
index algebra; they do not depend on RH or arithmetic cancellation estimates.

Several apparent opportunities are already implemented or fail their premises:

- GR Combine plus next RMSNorm fusion and write-gate overlap already exist.
- Supported GDN input projection packing already exists.
- Raw-logit top-k/router normalization and shared-expert finalization already
  have optimized paths. Weighted down-projection linearity does not remove
  expert matrices or commute through SwiGLU.
- PLE query normalization consumes \(R\); the following GR consumes
  \(R+\Delta_{\rm PLE}\). Their normalization statistics cannot be reused.
- The real polarization identity for \(\|R_i+s_iy\|^2\) omits the intermediate
  rounded residual if applied directly to the serving path. It also requires
  cross products whose acquisition is not free.
- Replacing PLE branch norms by one norm of \(V\) ignores rounded gated values.
  Proposal 8 instead captures the original reciprocals.
- Per-value-head GDN output norms cannot become one output-GEMM scalar.
- Static vision LayerNorm folding obeys
  \(W\operatorname{LN}(x)+b=WD_\gamma Px/r(x)+W\beta+b\),
  where \(P=I-\mathbf1\mathbf1^\top/d\). However, folded GEMM can suffer
  severe cancellation on nearly constant inputs. Stable consumer fusion is a
  safer initial experiment; pre-shuffle patch normalization also has separate
  denominators for the four patches.
- Muon and training scaling laws add no inference operations to optimize.

## Validation and implementation acceptance

Scratch Lean files were checked with the repository's pinned toolchain and
`-DwarningAsError=true`. Audited dependencies are only the standard logical
axioms. The row-selection and fixed-function lookup identities require no
axioms. These are component proofs, not end-to-end serving proofs.

The retained reference diagnostics report:

- 81,920 reconstructed normalized PLE cells and 81,920 FIR output cells exactly
  matching a scalar FP32/BF16 model, including ring wrap and checkpoint rollback.
- 14,873 mismatched cells for the invalid shared-norm shortcut, demonstrating
  why its rounding assumption matters.
- 433 distributed-output cases, including a 248,320-token vocabulary across
  eight shards, ties, and large common logit shifts. Tested supports and
  distributions matched the reference under its specified tie/threshold rules.

These are synthetic checks. They do not validate a GPU reduction, compiler
fusion, cuDNN convolution, RNG stream, trained-model behavior, or latency.

The scratch audit packet is outside the repository at
`/tmp/qwen-rest-pipeline-audit-20261024/`. Relevant files are:

| Artifact | Scope |
|---|---|
| `pipeline-and-proposals.json`, `manifest.json` | Equation map, source pins, counts, and artifact hashes |
| `inventory/SelectedRows.lean` | Row-selection and fixed-function identities |
| `inventory/RingBuffer.lean` | Arbitrary-length circular-write invariant |
| `inventory/RestMicroops.lean` | Scalar transport, convolution partition, softmax merge ingredients |
| `residual_ple/ResidualPLE.lean` | Specialized ring/FIR and real norm identities |
| `residual_ple/results.json` | PLE reconstruction and rounding diagnostics |
| `moe_output/OutputCertificates.lean` | Selection, partition, interval, and nucleus certificates |
| `moe_output/check_output.py`, `check-output-results.json` | Distributed output reference and results |

For each implementation, compare against the pinned optimized path using the
same model, cache formats, requested outputs, and sampling configuration.
Measure the complete lifecycle, including initialization, misses, fallback,
commit/rollback, and collectives. Report output/state errors, selection and
support agreement, temporary and persistent bytes, and end-to-end latency.
Component arithmetic reductions count as implementation opportunities until
those measurements establish a net benefit.

The recommended first implementation batch is 4, 5, 7, and 9. Measure context
cache locality for 6, then evaluate 8's reconstruction cost on top of the ring.
Treat 10 and 11 as trace-driven research experiments.

The [softmax exact-result follow-up](qwen-softmax-exact-result-proposal.md)
adds proposals 12 and 13: reuse repeated exponential arguments while
preserving the original reduction, and certify rounded outputs through
adaptive interval bounds. It includes retained Lean proofs and synthetic
experiments, with mathematical rounding and existing-kernel equality kept
as separate contracts.
