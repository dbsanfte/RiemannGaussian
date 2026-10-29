# ECDLP paper review and factoring comparison

This packet preserves the completed review of the pinned
[ECDLP paper](https://github.com/bochum-crypto/subexponential-ecdl/blob/252d44eb1c3ec92a2ce6a7dc5dc17ce49a5a22ee/subexponential-ecdl.pdf).
The [manifest](manifest.json) records its source hash, the review's scope and
hashes of the unchanged scratch reports. The paper and its full extracted
text are not redistributed here.

The reviewers found no blocking flaw in the arithmetic and randomized
reduction they examined, conditional on the assumed OpenAI D.1 theorem.
They did not independently certify that assumption. Read the
[arithmetic review](arithmetic-tensor-owner-audit.txt),
[probability and cost review](probability-and-cost-review.txt), and
[transfer assessment](transfer-audit-vertex.json) for the precise limits.
The paper's randomized expected-time rate does not improve the project's
deterministic worst-case target.

The [literature comparison](literature-comparison.json) records the bounded
search and pinned external theorem statements. In particular, the reported
Rudich--Rousseau qualitative subexponential result is separate from the
sharper quantitative rate sought here; this review did not rebuild their
Lean repository. No external factoring implementation was integrated.

The current project's acquisition algorithm is already specified. Its
remaining implementation and complete primitive bit-cost obligations are
shown in the [algorithm explorer](https://dbsanfte.github.io/RiemannGaussian/semiprime-proof/)
and [publication progress record](../semiprime-publication-20261029/progress.json).
The full target-rate theorem remains open.
