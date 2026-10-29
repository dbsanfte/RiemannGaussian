# Llaminar Qwen Flash Next: applying the softmax identities to CUDA and ROCm

Date: 2026-10-25. Audited branch `feat/qwen-flash-next` at
[`f609b409b599ebdfbc48d60e6a77a782127ab3cd`](https://github.com/Llaminar/llaminar/tree/f609b409b599ebdfbc48d60e6a77a782127ab3cd).
The isolated checkout was read only. This is a source audit, new algebraic
proof, and CPU scalar experiment; no CUDA/HIP kernel was changed or timed.

This audit qualifies the earlier
[softmax proposal](qwen-softmax-exact-result-proposal.md). Its SGLang-specific
BF16-origin vocabulary premise does not transfer to Llaminar. The strongest
new exact-arithmetic candidate is eliminating unit rescaling exponentials in
ROCm's explicitly selected FP16 attention program. A larger MoE reduction is
mathematically valid but does not preserve the existing floating-point program.

## Actual execution, including prefill and decode

| Surface | Prefill | Decode and retained MTP target rows |
|---|---|---|
| CUDA selected attention | Fixed FP32, eight partitions of at most 257 selected tokens | Same per-row program and reduction order |
| ROCm default attention | Same shared FixedFP32 program | Same shared FixedFP32 program |
| ROCm explicit `fp16_tile`, uniform schedule | Eight interleaved 64-token tile streams | Same eight-stream program |
| ROCm explicit `prefill8_decode33` schedule | Eight tile streams | 33 fixed parts, at most one 64-token tile per live part |
| Ordinary vocabulary head | Last requested prompt row, not every prompt position | One ordinary row; grouped verifier heads cover their required rows |
| Stochastic vocabulary sampling | Select adjusted top K, then K exponentials | Same compact distribution math per live target row |
| Greedy vocabulary selection | Argmax, no softmax exponentials | Argmax; production MTP drafts also use greedy one-hot proposals |

Sources: [CUDA launcher](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/cuda/attention/CUDAQwenSparseAttention.cu#L70),
[ROCm launcher](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/rocm/attention/ROCmQwenSparseAttention.hip#L71),
[typed phase resolver](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/execution/compute_stages/stages/qwen4exp/Qwen4ExpSparseAttentionBuilder.cpp#L165),
and [LM-head row selection](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/execution/compute_stages/stages/LMHeadStage.cpp#L128).

`M > 1` does not identify prefill: grouped MTP verification is Decode. The
33-part selection is explicit and resolved before capture. It is restricted
to the admitted ROCm/native-FP16, single-request family. CUDA rejects the FP16
attention experiments. The current ROCm implementation targets wave64 gfx906;
this audit establishes no wave32 portability claim.

## Default attention already shares its exponentials

For each row, query head, and partition p, the installed kernel computes:

\[
z_{pj}=\operatorname{FP32QK}(q,k_j)/16,\quad
m_p=\max_j z_{pj},\quad w_{pj}=E(z_{pj}-m_p),
\]

\[
L_p=\operatorname{FixedTreeSum}_j w_{pj},\qquad
O_{pd}=\operatorname{AscendingFMA}_j(w_{pj},v_{jd}).
\]

Here E is the compiled backend exponential, not an assumed correctly rounded
real exponential. The shared `logits` array is overwritten with each weight
once, then reused by all 256 output-coordinate owners. The reducer computes
\(s_p=E(m_p-\max_r m_r)\) once per nonempty partition, and preserves ascending
FMA folds for numerator and denominator before the final division. Optional
TQ inverse rotation and sigmoid gating follow. See
[weight production and PV](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/qwen4exp/QwenSparseGPU.cuh#L823)
and [ordered merge](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/qwen4exp/QwenSparseGPU.cuh#L1042).

With S selected tokens and P=ceil(S/257) nonempty parts, the default path uses
S+P attention exponentials. At S=2051 this is 2059 per row/head, excluding the
256 optional gate exponentials. There is no repeated softmax exponential per
value coordinate to eliminate.

Identical-argument memoization remains valid around `QwenSparseGPU.cuh:836`,
provided it uses the actual shifted FP32 argument bits, identical evaluator,
and unchanged sum/FMA consumers. However, native BF16/FP16 KV does not imply
BF16/FP16 attention scores: QK accumulation and reduction produce FP32 scores.
No useful repetition rate is established. A table/ballot/hash implementation
would have to beat the current one-evaluation-per-token program on at most
257 arguments per partition.

CUDA's build adds `--use_fast_math --ftz=true --prec-div=false
--prec-sqrt=false`; see
[compiler flags](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/CMakeLists.txt#L283).
Changing exponentials, division, or rounding points therefore requires a
reference to the actual compiled program. A real-arithmetic proof alone is
insufficient for its byte-equivalence contract.

## Best candidate: omit the unit exponential in ROCm's online update

The explicit FP16 producer currently computes

\[
m'=\max(m,t),\qquad a=e^{m-m'},\qquad b=e^{t-m'},
\]

with a=0 on an empty prior stream. It then updates each FP32 total using the
existing multiplication/FMA expressions. See
[the exact update](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/rocm/attention/ROCmQwenSparseFP16Attention.cuh#L1046).

For finite maxima, the maximum is one of the two operands. Consequently,

\[
(a,b)=
\begin{cases}
(e^{m-t},1),&m<t,\\
(1,e^{t-m}),&t<m,\\
(1,1),&m=t.
\end{cases}
\]

The first live tile has previous scale 0 and tile scale 1. This removes an
entire wave-uniform exponential evaluation, rather than merely electing one
lane to execute the same vector instruction.

A proposed finite-state implementation keeps the original `nextMaximum`,
products, FMAs, and publication boundaries:

```cpp
const float nextMaximum = fmaxf(maximum, tileMaximum);
const float previousScale = denominator == 0.0f ? 0.0f :
    (maximum == nextMaximum ? 1.0f : expf(maximum - nextMaximum));
const float tileScale = tileMaximum == nextMaximum ? 1.0f :
    expf(tileMaximum - nextMaximum);
// Retain all original value * tileScale and fmaf expressions below.
```

This is a proposal for finite live tile maxima and a finite prior maximum
whenever the denominator is nonzero; the initial prior maximum is deliberately
negative infinity. It is not an installed patch. Native qualification must
establish `expf(+0)==expf(-0)==1` for the
loaded compiler/runtime and retain the original nonfinite behavior. Keep the
neutral first-tile FMAs and signed-zero/subnormal treatment; simplifying the
entire first recurrence would be a separate transformation. Inspect ISA first:
the compiler may already eliminate some source-level work.

The compiled evidence theorem `max_rebase_evaluator` establishes the max
identity for any evaluator with value 1 at zero. `max_rebase_exp` specializes
it to the real exponential. Neither theorem formalizes the GPU evaluator or
IEEE subtraction. Those native premises remain explicit.

### Distinct payoff by phase

Let T=ceil(S/64) be the live tile count and A=min(T,8) the number of nonempty
streams in the eight-stream program. Counts below exclude the merge and gate.

| Program | Current scale-exp calls per head, counted per wave | After unit-scale elimination |
|---|---:|---:|
| Eight streams | 2T−A | At most T−A |
| 33 single-tile parts | T | 0 |

At S=2051, T=33. Eight streams go from 58 scale calls to at most 25; the
33-part program goes from 33 to zero. Each call currently has 64 active
lanes. Including the S per-token exponentials, source scalar evaluation
counts become 5763→at most3651 for eight streams, and 4163→2051 for33 parts.
These are source counts, not instruction counts or predicted speedups.

Under `prefill8_decode33`, the first row applies to prefill and the second to
ordinary/grouped decode. Under uniform FP16 setup, both phases use the first
row. Default FixedFP32 uses neither online producer and cannot receive these
savings by this edit.

Merely broadcasting one of the current identical scale results across64 lanes
is a weaker proposal: a masked AMD vector exponential may cost the same issue
slot, plus a shuffle. Unit-scale elimination instead targets a whole wave's
unnecessary call. A further duplicate part32 scale in the33-part reducer may
already be removed as dead lane work by the compiler; it is not a claimed win.

## Vocabulary and routed MoE change the earlier priorities

### Vocabulary: FP32 results, and only K live exponentials

Llaminar's native16-weight projection consumes FP32 hidden states and produces
FP32 accumulated logits. It does not narrow the projection result to BF16
before widening it. See the
[CUDA contract](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/cuda/gemm/CUDAFloatingPointGemmKernel.cpp#L464)
and [ROCm contract](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/rocm/gemm/ROCmFloatingPointGemmKernel.cpp#L477).
The earlier 248320→3020 BF16-origin synthetic example is not evidence for
Llaminar's logits.

The production stochastic sampler already selects adjusted top K logits,
then calls the shared
[`build_topk_topp_distribution_from_sorted`](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/common/SamplingMath.h#L2270).
K is bounded by256; the QFN model policy recommends20. The helper computes
each selected exponential once, keeps its weight, accumulates in order,
determines the top-p prefix using individual divisions, recomputes the prefix
sum in the same order, and normalizes retained weights. Its top-p is applied
after top-k normalization; the earlier SGLang joint-filter description is not
this implementation's contract.

An inexpensive exact-reuse experiment would compare adjacent actual argument
bit patterns in that sorted list and reuse a previous exponential for equal
arguments. Preserve every ordered addition, division, tie rule, and stored
probability. Its benefit is bounded by K and requires measured repetitions.
No large vocabulary histogram or dense BF16 table is justified here.

Production MTP drafts currently use greedy proposals with q=one-hot; see
[the orchestrator](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/execution/local_execution/orchestrators/DeviceGraphOrchestrator.cpp#L57699).
Target verifier distributions use compact top-k/top-p rows. Available backend
full-temperature primitives do contain duplicate full-vocabulary exponential
passes, but their current callers are tests/performance harnesses, not this
production QFN draft path. Removing their second pass would not accelerate
today's greedy draft lane.

### MoE: 512→10 is available mathematically, with a rounding-contract change

Llaminar does compute all512 router exponentials, normalizes the full row,
then renormalizes the selected10 expert weights. CUDA uses divisions; ROCm
has reciprocal/multiply paths. Relevant sources are
[CUDA full normalization](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/cuda/moe/CUDAMoEKernels.cu#L14250)
and [ROCm decode routing](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/rocm/moe/ROCmMoEKernels.hip#L14867).

The previously checked normalization cancellation gives

\[
\frac{e^{r_i}/Z}{\sum_{j\in I}e^{r_j}/Z}
=\frac{e^{r_i}}{\sum_{j\in I}e^{r_j}}.
\]

It suggests selecting raw top10 and exponentiating only those. Unlike the
audited SGLang backend, this saving is not already installed in Llaminar.
However, rounded full probabilities, their selected sum, and final
renormalization do not cancel exactly in floating arithmetic. In live decode
paths, selection itself is performed on rounded probabilities; distinct raw
logits can collapse to ties. Full probability rows are also written back, so
their consumers and snapshots must be accounted for.

The retained CPU counterexample uses512 FP32 logits `-i/100` and the CUDA
source's256-thread sum layout. Even with the same selected IDs0..9, the two
normalization programs differ in four selected weights. This is a scalar
model counterexample, not a CUDA device result. Thus512→10 is a candidate
explicit arithmetic redesign or a reference-result certification project,
not an exact drop-in rewrite. Serial/grouped agreement must be established
within any new program on both backends.

## Why the earlier BF16 rounding certificate is not enough

Default attention returns256 FP32 weighted outputs, not BF16 probabilities.
In the explicit FP16 path, the producer stores

\[
h_j=\operatorname{RN}_{16}(E(a_j)2^{-7}),
\]

but its denominator sums the **unrounded FP32 E(a_j)** before applying the
power-of-two scale. See
[probability and denominator boundaries](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/src/v2/kernels/rocm/attention/ROCmQwenSparseFP16Attention.cuh#L999).
Matching every half probability therefore does not establish the same
denominator or output. The1/128 factor also interacts with half rounding and
underflow; real common-factor cancellation does not remove those boundaries.

The relevant real identity for a weighted output is

\[
\frac{N+\Delta N}{Z+\Delta Z}-\frac NZ
=\frac{\Delta N-(N/Z)\Delta Z}{Z+\Delta Z},
\]

proved in `weighted_quotient_difference`. A useful certificate must bound
both numerator and denominator. Signed V and cancellation mean a tail-mass
bound alone is insufficient. Matching the existing program additionally
requires its QK, exponential, half/FP32 PV, partition merge, divide, FTZ,
rotation, and gate error behavior. The existing real-softmax BF16 certificate
does not supply those bounds. Stored sampler/router probabilities are also
FP32, with much narrower rounding cells and decision thresholds to certify.

## Integration and validation required before implementation promotion

Use the repository's
[CUDA guidance](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/.agents/cuda-tuning/SKILL.md)
and [ROCm guidance](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/.agents/rocm-tuning/SKILL.md).
An implementation must retain explicit streams, admitted persistent storage,
device-owned live masks, and complete capture identity. New lookup storage
must enter the existing PhysicalMemoryAuthority BOM; the immutable embedding
lookup API is not an existing exponential-table interface.

The root [architecture rules](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/AGENTS.md#L5)
forbid automatic fallback modes. The earlier generic certificate proposal's
fallback wording cannot be imported as a host/eager/old-kernel escape path.
Any refinement must be part of a complete, preselected captured program with
admitted storage and defined failure behavior. No such production certifier
was found in this audit.

For the unit-scale candidate, validate against the frozen existing program,
not merely against a serial version modified in the same way. Compare every
output and numerical partial byte for both8/33 programs, prefill and Decode
including grouped verification, dirty replay, native pre/post-RoPE layouts,
head shards, and selected counts around64/257/512/768/1024/2048/2051. Include
finite extremes, ties, signed zero, subnormals, and original nonfinite failure
behavior. Retain gate and observation cases.

Inspect the exact loaded ISA for actual exponential instructions and branches,
VGPR/SGPR/LDS use and spills. Then run the captured component comparison and
matched unprofiled whole-model prefill/decode measurements. Existing notes
already document that a qualified merge improvement did not improve total
model throughput; see
[the169 result](https://github.com/Llaminar/llaminar/blob/f609b409b599ebdfbc48d60e6a77a782127ab3cd/docs/v2/projects/2026-10/QFN_ATTENTION_STRUCTURE_COMPARISON.md#L1023).
Source operation counts alone are not a speed verdict.

## Retained evidence and disposition

The [evidence packet](research-evidence/llaminar-softmax-20261025/) contains
`RebaseScales.lean`, its strict compile/axiom log, a CPU scalar recurrence
comparison, detailed ROCm/sampling source notes, the MoE counterexample, and
a source/artifact hash manifest. Five Lean endpoints compile with only
`propext`, `Classical.choice`, and `Quot.sound`. The CPU recurrence experiment
passed100242 cases and1102662 bit comparisons, including finite extremes and
signed zero. It uses CPU `std::exp` and unchanged FP32 products/FMA; it does
not validate CUDA/HIP lowering or provide GPU performance evidence.

Priority: first inspect and prototype ROCm unit-scale exponential elimination
within the existing8/33 programs. Measure sorted-K duplicate arguments before
adding sampler memoization. Treat selected-only MoE normalization as a
separate arithmetic proposal. Do not carry the large BF16 vocabulary-cache
benefit or the BF16 probability certificate over to these FP32 contracts.
