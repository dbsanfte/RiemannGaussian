# Actual streamed Möbius enumeration

New module `RiemannGaussian/SemiprimeCounterEnumeration.lean` strictly compiles. Scoped root-import 15-linter gate PASS; every generated declaration audit PASS: 82 declarations, 48 theorem constants, standard axioms only. Logs are `enumeration-build.log` and `enumeration-audit.log`; replay auditor is `CheckEnumeration.lean`.

## Actual recursion and correctness

`stream todo q f` traverses three possibilities for each original coordinate: absent from S, in S but absent from U, or in both S and U. At support budget zero it takes only the first branch. The leaf immediately evaluates `f ∅ ∅` under the composed insertion callbacks; no mask family or output list is produced. Arbitrary `AddCommMonoid` outputs are supported, so the actual Möbius sign and jet/group computation may already be inside f.

`stream_eq_menu` proves for any duplicate-free input list that the value is exactly

`sum_(S⊆todo, |S|≤q) sum_(U⊆S) f(S,U)`.

The proof establishes the two powerset insertion cases and the actual three-branch recurrence; it does not assume a menu identity. Empty support, zero budget, and budget larger than the number of variables are all covered uniformly.

`tracked` is the same actual recursion with value, callback-count, node-count and maximum-depth fields. `tracked_menu` proves jointly:

* value equals the finite subset-pair menu;
* callbacks equal `Cq(n)=sum_(j=0..q) 2^j choose(n,j)`;
* traversal nodes are at most `(n+1)Cq(n)`;
* maximum recursive depth is n.

The node count is attached to the same recursive calls that produce the value. `strict_width_callbacks` states the exact `range(q+1)` count: the counter's Taylor precision is J=q+1, not q.

## Weighted entropy

`weightedCount_le_entropy` proves

`Cq(n) <= (q+1)(8n/u)^u`, for `0<u<=n` and `q<=u`.

The standalone real-cutoff binomial estimate is adapted and explicitly attributed in the module to OpenAI Math, Apache-2.0, commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, `BranchTree.choose_le_rpow_real`. The weighted extension explicitly charges all 2^j sub-support choices. No full SAT module or fixed-arity endpoint is imported; only Mathlib is needed. The already established schedule/jet-order inequalities must still be instantiated to turn this finite bound into the final asymptotic budget.

## Resource scope

This is an executable traversal and uniform algebraic refinement, not just a cardinality bound on a separately supplied mask family. It retains the input list and recursive callback closures, with a depth-n stack and at most a constant number of accumulated A-values at each frame. Each insertion-built S/U contains at most n original indices. Hence for bounded-size callback states/accumulator values the natural implementation has polynomial retained state; the theorem here formally records depth and traversal nodes, **not** a Lean/Turing-machine bit-space theorem for arbitrary A or arbitrary f. Callback work, Finset insertion/index encoding, closure allocation, accumulated rational heights, and primitive arithmetic remain separately charged. The preceding jet-height results are relevant to those accumulator sizes but are not silently imported as a universal A-size premise.

No existing module or frozen evidence file was modified.
