# Research proposal: leaf elimination for Gated DeltaNet speculative verification

Date: 2026-10-24.

Status: research proposal with a handwritten algebraic derivation and small
floating-point reference checks. No GPU kernel, measured speedup, trained-model
validation, or compiled Lean theorem is supplied. Novelty has not been
established. This note records a side investigation; it does not advance the
repository's RH or guaranteed one-sixth semiprime-factorisation claims.

## Proposal

Compute the outputs of speculative-tree leaves without computing their
state-update correction vectors. Solve corrections only for internal nodes,
whose descendants require them. If the accepted path ends at a leaf, retain its
raw update operands and resolve that one pending correction during the next
verification round.

The intended benefit is less checkpoint-projection arithmetic and a smaller
correction system, while retaining every candidate output and the exact
accepted-path state in real arithmetic. The opportunity is strongest for trees
with many leaves. For a chain, the previous round's pending correction cancels
the single-leaf projection saving in steady state.

This applies the output-only/adjoint perspective explored in the
[semiprime recurrence investigation](semiprime-factorisation-investigation.md):
identify the observable that is actually consumed, move the contraction through
the update, and defer information needed only by a later consumer. It does not
transfer the factoring recurrence's commutativity or geometric-grid structure.

## Existing methods and comparison boundary

- [Gated DeltaNet, Section 3](https://arxiv.org/html/2412.06464v3#S3)
  supplies the recurrence and its chunkwise WY formulation.
- [TreeWY, Section 3](https://arxiv.org/html/2608.20961v1#S3)
  solves a tree-wide system of correction vectors and reconstructs the accepted
  state instead of storing a full recurrent state at every candidate.
- [Bole, Section IV](https://arxiv.org/html/2608.01651v1#S4)
  gives a tree correction system, a finite inverse polynomial bounded by tree
  depth, and a GPU implementation using value tiles. Its depth-based
  cancellation is prior work, not a contribution of this proposal.
- [ReplaySSM, Section 5 and Appendix B](https://arxiv.org/html/2610.13778v1)
  keeps a checkpoint plus a bounded buffer of update records. It separates
  output computation from periodic state materialization and supports cheap
  speculative rollback.

The inspected TreeWY/Bole formulations compute corrections for all candidate
nodes. The inspected
[ReplaySSM speculative GDN kernel](https://github.com/Johnny-Liou/ReplaySSM/blob/main/vllm/third_party/flash_linear_attention/ops/gdn_replayssm_spec_decode.py)
also computes and stores every draft correction. That source was inspected on
2026-10-24; the linked main branch is mutable. No leaf-specific elimination was
identified in these inspected sources. This is a limited literature/code
comparison, not a priority claim.

The relevant performance baseline is an optimized output-only verifier with
compact update storage. Beating a token loop or full-state snapshotting alone
would not establish an improvement over these methods.

## Recurrence and supplied inputs

Work per GDN state head with column vectors
\(q_i,k_i\in\mathbb R^{d_k}\), \(v_i\in\mathbb R^{d_v}\), and
\(S_i\in\mathbb R^{d_v\times d_k}\). Some implementations store \(S_i^\top\).
For parent \(p(i)\), define

\[
u_i=\beta_i\bigl(v_i-\alpha_i S_{p(i)}k_i\bigr),
\qquad
S_i=\alpha_iS_{p(i)}+u_i k_i^\top,
\qquad
o_i=S_iq_i.
\tag{1}
\]

The tree topology, checkpoint, and per-node operands are supplied to the GDN
core. Keys, queries, values, and gates are assumed to have been produced using
the correct branch-local convolution history. The query includes whatever
normalization and head scaling the implementation requires.

The identities below do not require key normalization or division by a decay
gate. They remain algebraically valid at zero decay or endpoint write gates.
They concern the core readout before output normalization, gating, projection,
and the rest of the model.

## Leaf-output identity

Set

\[
\eta_i=\beta_i k_i^\top q_i,
\qquad
\widehat q_i=\alpha_i(q_i-\eta_i k_i).
\tag{2}
\]

Substituting the correction from (1) gives

\[
\begin{aligned}
o_i
&=\alpha_iS_{p(i)}q_i+
  \beta_i\bigl(v_i-\alpha_iS_{p(i)}k_i\bigr)(k_i^\top q_i)\\
&=S_{p(i)}\widehat q_i+\eta_i v_i.
\end{aligned}
\tag{3}
\]

Thus one parent-state action on the adjusted query replaces separate actions
on the key and query. It produces the entire output vector without acquiring
\(u_i\). This identity holds for every node, but an internal node still needs
its correction for its descendants. A leaf has no such consumer during the
current verification pass.

The parent state need not be materialized. If \(S_0\) is the state before the
tree and \(g_p\) is the product of gates on the path to parent \(p\), then

\[
S_p x=g_p S_0x+
  \sum_{j\preceq p}\delta_{j,p}\,u_j(k_j^\top x),
\tag{4}
\]

where \(\delta_{j,p}\) is the product of gates strictly after \(j\) through
\(p\), and \(\delta_{p,p}=1\). Every \(j\) in this sum is an internal node of
the current tree. Equation (4) uses path products, not ratios of cumulative
gates, so zero gates introduce no singularity.

For a ReplaySSM-style checkpoint plus resolved history, expand \(S_0x\) in the
same way using the buffered history. This remains an action on a vector and
does not require rebuilding the logical current state matrix.

## Eliminating leaf rows from the tree system

Let \(I\) be the internal nodes and \(L\) the leaves. Internal nodes form an
ancestor-closed set. Ordering internal nodes before leaves preserves all
ancestry constraints.

In the usual tree formulation, stack corrections and outputs as row matrices:

\[
(I_{\!N}+G)U=R,\qquad O=B+CU.
\tag{5}
\]

Here, with \(\delta_{j,i}\) defined as in (4),

\[
\begin{aligned}
G_{ij}&=\beta_i\delta_{j,i}(k_i^\top k_j)
  &&\text{if }j\text{ is a strict ancestor of }i,\text{ else }0,\\
C_{ij}&=\delta_{j,i}(q_i^\top k_j)
  &&\text{if }j\preceq i,\text{ else }0,\\
R_i&=\bigl[\beta_i(v_i-g_iS_0k_i)\bigr]^\top,
&B_i&=(g_iS_0q_i)^\top.
\end{aligned}
\]

No leaf is an ancestor of another node. Consequently,

\[
\begin{pmatrix}
I+G_{II}&0\\
G_{LI}&I
\end{pmatrix}
\begin{pmatrix}U_I\\U_L\end{pmatrix}
=
\begin{pmatrix}R_I\\R_L\end{pmatrix}.
\tag{6}
\]

Only the smaller internal system must be solved:

\[
U_I=(I+G_{II})^{-1}R_I.
\tag{7}
\]

The leaf readout can be written without forming \(U_L\):

\[
O_L=B_L+C_{LL}R_L+
  (C_{LI}-C_{LL}G_{LI})U_I.
\tag{8}
\]

\(C_{LL}\) is diagonal, with entry \(q_i^\top k_i\). Combining its terms
before evaluation gives exactly the adjusted query in (2)-(3). In particular,
an implementation should not first construct \(R_L\) and then eliminate it:
that would already have paid for the leaf key projections we want to avoid.

This is a row-elimination identity with an explicit cheap realization, rather
than an assumption that a smaller observable is automatically cheaper.

## Accepted-state continuation and the pending-update invariant

A verifier eventually needs the state at the accepted endpoint. Returning only
the leaf output is insufficient for continued generation. The proposed buffer
representation addresses that obligation explicitly.

For each request and each GDN layer/head, retain:

1. A checkpoint matrix.
2. A bounded accepted history of resolved additive updates
   \((\alpha_j,u_j,k_j)\).
3. Optionally one unresolved final update
   \((\alpha_*,\beta_*,k_*,v_*)\).

If the accepted endpoint is internal, its correction is already available.
Append its accepted path's resolved records. If the endpoint is a leaf,
append the resolved strict ancestors and keep the leaf as the single pending
update. Retain the raw leaf operands until acceptance selects or discards them.

In the next round, include a pending update as a virtual common ancestor of
all new candidate roots. Compute its correction along with the new internal
corrections, using the checkpoint and resolved buffer. Its output was already
computed in the previous round and need not be evaluated again.

The state invariant is:

> Applying the resolved buffer to the checkpoint and then applying the optional
> pending update yields the ordinary recurrent state of the accepted,
> already-processed token prefix, in exact arithmetic.

Inductively, resolving the old pending record changes only its representation.
Equations (1)-(8) compute the new candidate outputs on the correct paths.
Keeping only the selected path then restores the invariant with at most one
new pending record. Rejected siblings never enter the accepted history.

An actual dense-state consumer or a buffer flush must resolve the pending
record before materialization. It cannot silently drop that work. For normal
continuation, the intended kernel fuses resolution into the next verification
pass so that it does not cause a separate checkpoint read.

This invariant assumes ordinary speculation commits a single path. Beam
search or multiple retained branches require one such representation per
retained branch. Convolution caches, softmax KV caches, token positions, bonus
token handling, and acceptance sampling must separately follow the same
accepted-prefix boundary.

## Arithmetic accounting

Let \(N\) be the number of candidate nodes, \(F\) the leaves,
\(I=N-F\) the internal nodes, and \(p\in\{0,1\}\) indicate a previous pending
update.

An all-node correction formulation computes checkpoint actions on \(N\) keys
and \(N\) queries. The proposed formulation needs:

- \(N\) output-query actions, using adjusted queries where needed;
- \(I\) current internal-key actions;
- \(p\) pending-key actions.

The corresponding projection-vector counts are

\[
2N\quad\longrightarrow\quad N+I+p=2N-F+p.
\tag{9}
\]

Each dense checkpoint action costs \(O(d_kd_v)\) arithmetic before batching.
Constructing each adjusted query costs \(O(d_k)\). The correction system has
\(I+p\) unknown rows instead of \(N\) current-node rows. All \(N\) output
vectors are still required.

| Candidate tree | \(N\) | \(I\) | \(F\) | Baseline projection vectors | Proposed, \(p=0\) | Proposed, \(p=1\) |
|---|---:|---:|---:|---:|---:|---:|
| Chain of 9 nodes | 9 | 8 | 1 | 18 | 17 | 18 |
| Star of 19 nodes | 19 | 0 | 19 | 38 | 19 | 20 |
| Ternary tree with 3 draft levels | 39 | 12 | 27 | 78 | 51 | 52 |

For the ternary example, the steady-state count decreases from 78 to 52,
one third of this projection arithmetic, and the correction system decreases
from 39 to 13 rows.

These are component-level arithmetic counts, not measured latency, total
FLOP savings, or memory-bandwidth savings. They do not include buffered-history
interactions, tree coefficient construction, output accumulation, flushes,
other neural-network operators, or runtime scheduling.

An optimized all-node verifier can already reuse a single checkpoint load
across many projections. Reducing its projection count need not reduce
checkpoint bytes read. GPU tile padding can also hide smaller dimensions.
The smaller solve and reduced projection work must be measured with the
complete verification/commit lifecycle.

## Preliminary reference checks

An in-memory JavaScript reference check was run during the side conversation
on 2026-10-24. It compared ordinary per-node matrix recurrence against
ancestor-correction vector actions and adjusted-query outputs.

The check used key dimension 7, value dimension 5, normalized random keys,
nonzero random initial checkpoints, and a deterministic linear-congruential
generator initialized with seed 20261024. The shapes were a 9-node chain,
a 19-node star, a 39-node ternary tree, and 27-node irregular trees.

Three gate regimes covered ordinary decays/write strengths, selected zero
decays, and unit decay with write strengths alternating between zero and one.
Each shape/regime ran four successive rounds. Every candidate endpoint was
checked for accepted-state reconstruction; one selected leaf was carried as a
pending update into the next round. Resolved accepted histories remained
factored in the candidate evaluator.

Observed results:

| Observation | Value |
|---|---:|
| Candidate outputs compared | 1,128 |
| Maximum absolute output discrepancy | \(8.881784197001252\times10^{-16}\) |
| Maximum absolute accepted-state discrepancy | \(5.551115123125783\times10^{-16}\) |

The checked variant used adjusted queries for every output and solved
corrections only for internal nodes, including any pending virtual ancestor.
The dense reference constructed branch states independently.

These are recorded exploratory floating-point observations, not formal
certificates. The original harness ran in conversation memory and is not a
tracked repository artifact. This note preserves the setup and observations;
it does not claim that the numerical experiment is independently reproducible
from a checked-in executable. A retained reference harness is a first
implementation deliverable.

## Proposed implementation and evaluation

### 1. Retained reference implementation

Implement an ordinary tree recurrence, an all-node correction verifier, and
the internal-node/adjusted-query verifier with the same input contract.
Preserve a reproducible harness and inputs.

Check every output and accepted endpoint on chains, stars, shallow wide trees,
irregular trees, and trees with early leaves. Exercise consecutive rounds,
acceptance ending at internal nodes, no accepted draft extension, pending
updates, buffer boundaries, flushes, and subsequent continuation. Include
nearly parallel keys and small gates.

### 2. Fused verification kernel

Evaluate checkpoint projections for current outputs, current internal keys,
and the optional pending key in the same pass over each checkpoint tile.
Solve only the internal/pending system and form all outputs.

Keep raw leaf operands available for accepted-path commit. Resolve the old
pending record within the verification launch; avoid adding a separate
full-checkpoint read. Preserve fixed launch shapes and CUDA-graph compatibility
where possible. Internal-node packing, ancestor masks, padding, and grouped
query/key heads all need explicit accounting.

### 3. Compare matched implementations

Use the same model weights, candidate tree, supplied operands, precision,
accepted path, and batching configuration for the all-node and proposed
verifiers. Compare against the relevant Bole/TreeWY-style formulation and an
optimized ReplaySSM-style buffer, not only full-state snapshots.

Measure:

- Verification latency and accepted-state commit/flush latency, including
  pending resolution over several rounds.
- Checkpoint and update-record bytes read/written, temporary storage, register
  pressure, occupancy, and tensor-core utilization.
- Behavior as leaf fraction, depth, batch size, head dimensions, and buffered
  history length vary.
- Kernel-level performance and whole-model time per committed token
  separately.

Use chain-shaped trees as a control: equation (9) predicts no steady-state
projection-count saving there.

### 4. Numerical and serving equivalence

The derivation is exact over real arithmetic. Reassociation, adjusted-query
rounding, and lower-precision cached corrections can change floating-point
outputs. Check FP32 before BF16/FP16 kernels, quantify output and continued-state
errors, and examine model logits and acceptance decisions against the chosen
serving reference.

Matching a small numerical tolerance is not by itself a proof of identical
sampled token streams or target distributions. The acceptance procedure must
remain correct for the probabilities actually computed, and every layer must
publish only the accepted branch's recurrent and convolution state.

## Decision criterion and open questions

The useful result would be lower verification-plus-continuation cost on
representative wide trees at matched correctness and precision, without
recovering the savings as an extra pending-resolution or flush cost.

Open questions include whether checkpoint bandwidth already dominates the
saved arithmetic, whether smaller internal systems survive GPU tile padding,
whether adjusted-query rounding is acceptable, and whether pending records fit
existing cache and graph-capture interfaces.

The algebra identifies a concrete candidate optimization. A historical novelty
claim and a practical speedup claim remain open.
