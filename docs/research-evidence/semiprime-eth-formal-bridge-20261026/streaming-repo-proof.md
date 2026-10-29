# Direct total-incidence degree proof: compiled

Sole authorized source edited: `/home/dbsanfte/riemann/formal/RiemannGaussian/SemiprimeStreamingTensor.lean`.

Added `natDegree_evaluate_le`: for arbitrary Boolean tensor `T : (Fin w → Bool) → C` over any commutative ring C and polynomial port paths of degrees at most r, the actual recursive evaluator with constant-polynomial table entries has degree at most `w*r`. Proof is induction on the evaluator's two branches, using the bounds on `1-path(0)`, multiplication and addition. No external counting-polynomial module is imported.

Added `natDegree_sum_product_evaluate_le`: for a finite assignment index X and tensor vertices E with arbitrary arities, the sum over X of products of those evaluated tensors has degree at most `(sum_e arity(e))*r`. This directly yields `2*n*r` when total port incidence equals `2*n`. There is no maximum-arity-times-number-of-tensors loss.

Strict compilation PASS with Lean 4.34.1, `-DautoImplicit=false -DwarningAsError=true`. Output is isolated at `/tmp/semiprime-d1-audit-20261026/SemiprimeStreamingTensor.olean`; log at `streaming-repo-build.log`. Both new theorem axiom reports are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axioms.

Replay from formal repository:

```sh
TASK_LEAN_PATH=$(find /home/dbsanfte/riemann/formal/.lake/packages -path '*/.lake/build/lib/lean' -type d | paste -sd:)
LEAN_PATH="$TASK_LEAN_PATH" /home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -DautoImplicit=false -DwarningAsError=true -o /tmp/semiprime-d1-audit-20261026/SemiprimeStreamingTensor.olean RiemannGaussian/SemiprimeStreamingTensor.lean
```

This is an unconditional algebraic degree bound for the executable recursive definition, together with the previously compiled interpolation and attached call/depth counts. Generic counting-machine compilation, coefficient heights, precision scheduling, arbitrary table-entry cost and global workspace remain separate obligations. No factoring runtime theorem is claimed here; the root's external closure build was not touched.
