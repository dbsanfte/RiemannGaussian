# Softmax with fewer evaluations and certified rounding

Date: 2026-10-25. Continuation of proposals 4–11 in the
[inference pipeline proposal](qwen-flash-next-inference-pipeline-proposal.md).

The subsequent [Llaminar CUDA/ROCm audit](llaminar-qwen-softmax-kernel-audit.md)
changes the implementation priority for that engine: its vocabulary logits
are FP32 accumulated outputs and ordinary sampling already exponentiates
only top-K candidates. The BF16-origin vocabulary example below is a
SGLang-path hypothesis and synthetic result, not evidence of Llaminar savings.
The audit identifies unit rescaling exponentials in ROCm attention as a more
direct exact-arithmetic candidate.

Two concrete routes emerged. Proposal 12 reuses evaluations at identical
arguments and can preserve a specified floating-point kernel's output bits.
Proposal 13 uses rigorous bounds to determine the correctly rounded real
softmax output, refining when a bound crosses a rounding boundary. Neither
has a GPU implementation or a measured Qwen latency result in this audit.

## What “the same result” means

These are separate contracts:

1. The same exact real distribution.
2. The exact real distribution rounded once to BF16, FP16, or FP32.
3. The same bits as a particular existing implementation, including its
   exponential approximation, reduction tree, reciprocal, casts, and FTZ.

Real-algebra identities establish the first contract. They do not automatically
establish the third. Floating-point variants of softmax can differ despite
real equality, as analyzed by
[Blanchard, Higham, and Higham](https://arxiv.org/abs/1909.03469).

The compiled theorem `SoftmaxAlgebraAudit.full_softmax_rigidity` proves, for a
nonempty finite vector of finite real logits,

\[
\operatorname{softmax}(x)=\operatorname{softmax}(y)
\quad\Longleftrightarrow\quad
\exists c\;\forall i,\;x_i=y_i+c.
\]

Consequently, independently rounding logits generally changes the exact
distribution. For example, BF16 rounding maps both 256 and 256.5 to 256;
softmax changes from approximately (0.37754, 0.62246) to (0.5, 0.5).
Matching rounded outputs is a different, certifiable possibility.

## 12. Reuse identical exponential arguments, preserving the reduction

Let the existing implementation produce shifted exponential arguments
\(a_i\), and let \(U\) be the number of distinct argument bit patterns in a
row of length \(N\). Compute the existing exponential evaluator once per
distinct argument:

\[
E[b]=\operatorname{Exp}_{\mathrm{ref}}(b),\qquad
w_i=E[\operatorname{bits}(a_i)].
\]

Feed the original ordered sequence \((w_1,\ldots,w_N)\) to the **unchanged
reference reduction**. After obtaining the same denominator or reciprocal,
reuse the reference normalization operation once per distinct argument and
scatter its result to the original positions.

For the reference model tested here, the expensive-operation counts become:

| Work | Original | Reuse |
|---|---:|---:|
| Exponential evaluations | N | U |
| Final normalization multiplications | N | U |
| Ordered denominator additions | N−1 | N−1 |
| Input/output positions visited | N | N |

The implementation also pays grouping, lookup, storage, and synchronization.
The theorem `memoized_evaluation_preserves_ordered_consumer` proves the
underlying transport for arbitrary deterministic evaluators and consumers.
It does not prove a particular GPU cache implementation. Preserve argument
bits, masks, exceptional-value handling, scalar evaluator, reduction layout,
operation order, and casts. Replacing a GPU exponential instruction with a
different library's exponential would break this contract.

### Where Qwen can supply repeated arguments

The pinned SGLang source has a path that computes the vocabulary projection
in the LM-head dtype, then converts its result to FP32. If that projection
produces BF16, the FP32 buffer retains the original small alphabet; it has
not acquired new precision. Explicit FP32-output options take a different
branch. See
[projection output dtype](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/logits_processor.py#L1129)
and [conversion to FP32](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/logits_processor.py#L1289).

A uniform temperature transform preserves equality between identical logits.
Token-dependent penalties or biases can split groups. Group the actual
post-transform argument bits, or explicitly track these exceptions. Do not
cast an FP32 projection to BF16 to manufacture repetitions. Attention scores
accumulated in FP32 do not inherit a BF16 alphabet merely because Q and K are
BF16. The vocabulary softmax is the first target to investigate.

### Exact histogram identity, with a separate arithmetic contract

For distinct original logit values \(v_u\), multiplicities \(c_u\), and a
common anchor \(m\), finite-fibre regrouping gives

\[
Z=\sum_i e^{z_i-m}=\sum_{u=1}^{U}c_u e^{v_u-m},
\qquad p_i=\frac{e^{v_{g(i)}-m}}Z.
\]

This can reduce denominator work too. The repository already uses this
finite-fibre identity in
[`sum_pairedEtaInverseProductCoefficient_mul`](../RiemannGaussian/EtaInverseProductCoefficients.lean).
The new `partition_by_equal_logits` and `softmax_histogram_denominator`
specialize the underlying identity to softmax.

Replacing repeated additions by multiplicity multiplication changes floating
rounding. For instance, sequential FP32 accumulation of
\(1,2^{-24},2^{-24}\) gives 1, while \(1+2\cdot2^{-24}\) gives
\(1+2^{-23}\). Use histogram normalization with a correctly rounded real
target or a separate reduction certificate; preserve the original tree for
the direct bit-preserving route.

### Evidence and cost limit

The executable reference uses FP32-rounded `math.exp`, a fixed pairwise FP32
sum, one FP32 reciprocal, and FP32 products. Across 24 synthetic cases,
1,503,036 output-bit comparisons matched. One Gaussian vocabulary-sized row
gave these counts after a uniform temperature transform:

| Source values | N | Distinct shifted FP32 arguments U |
|---|---:|---:|
| BF16-origin | 248,320 | 3,020 |
| FP32-origin | 248,320 | 244,782 |

The first row removes about 98.8% of exponential evaluations with global
reuse. This is **not** an 82-fold softmax speed claim. Restricting reuse to
tiles of 32, 128, or 1,024 entries requires respectively 244,887, 234,811, or
167,150 evaluations on that same BF16-origin row. Exploiting global repetition
requires paying for global organization; a warp-local shortcut obtains much
less benefit. A dense table of 65,536 FP32 values alone costs 256 KiB per
active row, before validity metadata. Compact tables have their own indexing
cost. Measure both against the existing fused kernel.

## 13. Certify rounded outputs using inexpensive bounds

Keep the original logits. For \(w_i=e^{z_i-m}\), obtain certified enclosures
\(0\le l_i\le w_i\le u_i\). Define

\[
L=\sum_i l_i>0,\qquad U=\sum_i u_i.
\]

Then the compiled `probability_enclosure` establishes

\[
\frac{l_i}{U}\le p_i\le\frac{u_i}{L}.
\]

Let \((a_i,b_i)\) be the interior of the rounding cell for a candidate output
\(q_i\). The division-free sufficient check is

\[
\boxed{a_i U<l_i\quad\text{and}\quad u_i<b_i L.}
\]

`cell_of_cross_products` proves that this implies \(a_i<p_i<b_i\).
Thus the output is exactly \(q_i\) under the specified rounding map.
The strict check deliberately rejects midpoint ties. Dyadic bounds and
midpoints permit exact integer cross-products; hardware implementations must
pay their widths or use proven outward rounding.

A tighter bound retains the numerator's participation in its own denominator:

\[
\frac{l_i}{l_i+\sum_{j\ne i}u_j}
\le p_i\le
\frac{u_i}{u_i+\sum_{j\ne i}l_j}.
\]

`dependent_interval` proves this with explicit positivity hypotheses. Share
the two total sums instead of reevaluating all exponentials for each output.
Outward error in subtracting a component from a computed total must remain
covered.

### Proposed execution

1. Generate a cheap candidate and proven exponential bounds, using a table
   or a short polynomial. Bound evaluation rounding as well as approximation
   error; an empirical error maximum is insufficient.
2. Accumulate shared lower and upper partition bounds.
3. Test output rounding cells with cross-products.
4. Refine uncertain bounds, including the shared denominator when necessary.
   Emit only certified outputs. At a practical refinement limit, fall back
   to an implementation satisfying the chosen contract.

For a correctly rounded real target, an arbitrary FP32 softmax is not a
correct fallback by definition. For matching an existing kernel, the bounds
must enclose that kernel's actual pre-cast result, including all intermediate
errors, or fall back directly to that kernel. Correct rounding of the real
answer alone does not establish agreement with its output bits.

This adapts the established rounding-cell principle used by
[RLIBM](https://people.cs.rutgers.edu/~sn349/rlibm/) to a normalized vector,
using the repository's checked interval machinery. It is a proposed softmax
application, not a claim that this principle is new.

### Why common error can be cheaper than independent error

For approximate weights \(\widehat w_i=w_i(1+\delta_i)\), let
\(\bar\delta=\sum_j p_j\delta_j\). The compiled
`weighted_relative_error_identity` gives, when denominators are nonzero,

\[
\widehat p_i-p_i
=p_i\frac{\delta_i-\bar\delta}{1+\bar\delta}.
\]

A common multiplicative error cancels exactly. The quantity to certify is
the deviation from that common error, rather than just each exponential's
isolated error. This follows the repository's existing practice of retaining
shared-input cancellation before taking absolute values in
[`CorrelationLinearEnclosure`](../RiemannGaussian/CorrelationLinearEnclosure.lean).
It does not make arbitrary FP16 exponentials exact, and accumulation and
final division errors still require bounds.

For a tail of M logits satisfying \(z_j-m\le-A\), `omitted_tail_bound` gives
\(T\le M e^{-A}\). Carry this as denominator uncertainty. A tiny individual
probability can round to zero while its mass still changes another output;
discard a tail only after certifying every required output.

### What is actually checked

The new Lean file calls the pinned LeanCert theorem
`IntervalRat.mem_expPointComputable`, rather than assuming a Taylor-error
oracle. Exact kernel checks at Taylor depth 5 prove that softmax(0, −1) lies
strictly inside the BF16 cells for

\[
\left(\frac{187}{256},\frac{69}{256}\right)
=(0.73046875,\;0.26953125).
\]

The terminal theorems are `example_high_bf16_cell`, `example_low_bf16_cell`,
and `example_nearest_local_codes`. The last proves the local binade codes;
it is not a formalization of a global hardware BF16 conversion routine.
The proof uses exact rational Taylor arithmetic. It demonstrates that a
bounded calculation suffices, not that a hardware FP16/FP8 implementation
has already been certified or accelerated.

A separate Python interval prototype tested 116 rows representing 1,845,560
logits, including all-equal rows, subnormals, extreme tails, and full
vocabulary sizes. All rounded outputs agreed with its higher-budget interval
reference. It uses documented correctly rounded
[`Decimal.exp`](https://docs.python.org/3/library/decimal.html#decimal.Decimal.exp)
with neighboring decimal bounds, plus exact integer/fraction arithmetic.
Its nominal precision budgets select decimal precision with guard digits;
they are not hardware FP16 or FP32 arithmetic measurements. These Python
results are evidence, not Lean proofs of the Python implementation.

For 16 tested rows, that real-answer reference differed from the specified
serial-FP32 model in 74 output positions. This confirms why the two output
contracts must be kept separate. Longer rows also create more opportunities
for rounding-boundary ambiguity; a high per-coordinate success rate does
not guarantee a cheap whole-row pass. No uniform low-precision bound,
whole-row hit rate on Qwen traces, or speedup is established.

## Baselines and rejected shortcuts

- The pinned routed-MoE backend already has a raw-logit top-k path followed
  by softmax only over the selected entries. The 512-to-10 exponential
  reduction is an existing baseline there; see
  [`fused_topk_softmax_torch_raw_logits`](https://github.com/sgl-project/sglang/blob/656331295619a4d0267b40b7da0b5cd5b549fcbc/python/sglang/srt/layers/moe/topk.py#L1147).
- The pinned LeanCert package already proves `softmax_algebraic_identity`
  and `mem_softmax`. Its full interval evaluator evaluates a separate
  shifted denominator for each component: useful as a correctness baseline,
  but N squared exponential evaluations do not accelerate ordinary softmax.
- Finite Abel transport can reduce a weighted attention numerator to
  differences of weights times value prefixes. The new
  `numerator_via_value_prefixes` compiles this transfer from
  [`FiniteAbelVariation.weighted_sum_eq`](../RiemannGaussian/FiniteAbelVariation.lean).
  Savings require few contiguous weight plateaus and already available
  prefixes. No such structure is established for Qwen scores here.
- Digit-factor exponential tables and exact integer accumulation are valid
  design options, but table products still need error bounds, and exact
  accumulation changes a rounded reduction tree. No superior kernel follows
  from these identities alone.
- Directly storing exponential results in FP16 caused 101 BF16-output
  differences in the tested 2,048-entry row; BF16 storage caused 510.
  Low precision without a certificate did not preserve the result.

## Proofs, reproduction, and implementation priority

The retained [evidence packet](research-evidence/qwen-softmax-20261025/) contains:

| Artifact | Purpose |
|---|---|
| [Algebra.lean](research-evidence/qwen-softmax-20261025/Algebra.lean) | Rigidity, grouping, ordered-consumer reuse, sparse updates, Abel transport |
| [SoftmaxCertificates.lean](research-evidence/qwen-softmax-20261025/SoftmaxCertificates.lean) | Interval and cross-product checks, common-error identity, tail bound, concrete BF16 cells |
| [Histogram.lean](research-evidence/qwen-softmax-20261025/Histogram.lean) | Finite-alphabet sum and exponential-factor identities |
| [check_reference.py](research-evidence/qwen-softmax-20261025/check_reference.py) | Exact-bit memoization experiment and counterexamples |
| [reference-results.json](research-evidence/qwen-softmax-20261025/reference-results.json) | Operation counts, tile limits, output-bit comparisons |
| [check_lut.py](research-evidence/qwen-softmax-20261025/check_lut.py) | Adaptive interval/histogram prototype |
| [interval-results.json](research-evidence/qwen-softmax-20261025/interval-results.json) | Interval prototype results |
| [manifest.json](research-evidence/qwen-softmax-20261025/manifest.json) | Toolchain, dependency pins, hashes, and check scope |

All three Lean evidence files were compiled individually with
`lake env lean -DwarningAsError=true`. Terminal axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. They are standalone evidence
files, not newly registered modules in the root mathematical library.
No full repository rebuild or GPU test is claimed.

Start with proposal 12: collect actual post-transform argument cardinalities
and benchmark exact reuse against the existing vocabulary kernel. Preserve
its reduction to keep the bitwise target simple. Pursue proposal 13 as a
separate correctly rounded kernel or as a certified accelerator for a named
reference, paying all enclosure and fallback costs. The mathematical pieces
are checked; practical performance remains an implementation experiment.
