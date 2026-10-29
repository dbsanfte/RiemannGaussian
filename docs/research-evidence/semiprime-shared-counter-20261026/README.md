# Executable shared-summary factoring route and global jet bounds

26 October 2026. The active objective is still **pursue the 1/6 (or better!)
scaling goal**. The preceding goal turn made substantive progress; this turn
implements the proposed counter and recovery path and strengthens its compiled
coefficient bounds. The complete kernel-checked factoring/rate theorem remains
open. No finite test is treated as asymptotic evidence.

## What is now concrete

- [shared_layout.py](shared_layout.py) deterministically constructs the actual
  replacement rows and integral measurements from the original scopes. It uses
  exact conditional expectations, commuting-swap spectral rows, and copy
  embeddings. The construction pays for its polynomial-size matrices.
- [shared_counter.py](shared_counter.py) executes the shared-summary fibre sums,
  Boolean Möbius correction of Taylor jets, and exact Hermite recovery. It
  streams assignments and never constructs full local truth tables or fibre
  lists. Non-Boolean inputs use the genuine multilinear extension of each
  supplied Boolean entry predicate.
- [shared_parameters.py](shared_parameters.py) checks the actual numerical
  hypotheses, including the exact binomial tail, with integer arithmetic.
  [factor_solver.py](factor_solver.py) connects the existing macro-FFT network
  to this counter and recovers a factor in at most L+1 conditional counts.
  Inputs failing the schedule use an explicitly reported exact divisor-scan
  fallback. The asymptotic argument shows only finitely many lengths fail;
  it makes no practical threshold claim.
- [SemiprimeStreamingTensorHeight.lean](SemiprimeStreamingTensorHeight.lean)
  snapshots the new repository proof module. Its strict build and scoped
  root-import lint passed, with only the three standard axioms.

The all-input [resource derivation](resource-derivation.md) and
[independent integration review](review-counter-integration.md) support the
proposed ordinary-bit-model bound

\[
 \operatorname{poly}(L)\,2^{O(L(\log\log L)^2/\sqrt{\log L})}=N^{o(1)},
 \qquad L=\lceil\log_2(N+1)\rceil.
\]

This is an algorithm-level derivation using the paper's main counting and row
identities, **not a compiled end-to-end runtime theorem**. The source's Appendix
D is not needed for this route. The old native long-query acquisition bound
remains unchanged; this alternative tackles factoring directly.

## What Lean proves here

The new module is in namespace `RiemannGaussian.SemiprimeStreamingTensorHeight`.
It connects an integer numerator recurrence to the earlier actual evaluator:

- `polynomialNumerator_map` proves the exact polynomial denominator `d^w`.
- `abs_coeff_polynomialNumerator_le` bounds every retained coefficient of a
  local factor, charging local arity rather than the number of assignments.
- `sum_product_polynomialNumerator_map` proves one shared denominator
  `d^(sum arities)` for the entire assignment sum of products.
- `abs_coeff_sum_product_polynomialNumerator_le` bounds its retained coefficient
  by `card(X) * J^card(E) * [J*(|d|+2B)]^(sum arities)` for J>=1, entry magnitude
  at most one, signed weights of magnitude at most one, and retained input
  numerator coefficients bounded by B. Empty products are included.

Consequently exponentially many summands add their logarithmic count to the
coefficient bit bound; they do not force a separate denominator per summand.
See [proof notes](streaming-height-proof.md), [strict build](height-build.log),
and [scoped audit](height-root-audit.log). The polynomial model verifies algebra
and coefficients. It is not yet a primitive-machine implementation of Python's
truncated arrays, its entry verifiers, or the complete counting loops.

## External Lean baseline

The pinned OpenAI source is commit
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, under Apache-2.0; full attribution,
toolchain and license provenance are in the
[preceding source checkpoint](../semiprime-eth-formal-bridge-20261026/sources.json).

We now locally audited six reusable algebra theorems from `GlobalPolynomial`,
`Separation`, and `SqrtLog.LayoutExactBuckets`. Their entire 14-module external
dependency closure had already passed the ongoing strict build; source and
object hashes were rechecked. The six theorem axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. See
[audit result](external-generic-audit.json) and [audit log](external-generic-audit.log).
This is an **external baseline**, not original project mathematics or a proof
that the new counter already instantiates those theorems.

The full published SAT endpoint build remains separate and live as recorded in
[external-build-snapshot.json](external-build-snapshot.json). Re-poll its existing
exec session 85099. A timeout is not completion or failure. No full endpoint or
comparator success is claimed here.

## Controls and replay

The final source checkpoint has 30 passing focused tests: 11 for layout algebra,
10 for the counter, and 9 for parameter/recovery integration. These include
nonconstant rows, nonlinear tensors, higher Taylor coefficients, Möbius signs,
forced-bit fibres, Hermite normalization, invalid-design rejection, and a live
counter-to-recovery adapter control. Independent controls and a code review
accompany the tests. Their purpose is implementation validation, not a semiprime
coverage campaign or runtime extrapolation.

From this directory:

```sh
python3 -m unittest -v test_shared_counter test_parameters_solver
python3 -m unittest discover -v -s tests
```

The generic counter also supports exact rational callbacks algebraically.
Polynomial-space guarantees require Boolean entries, as in our actual network,
or a supplied common polynomial-bit denominator and height bound. Separate
polynomial-bit rational answers can otherwise accumulate an enormous lcm.
The API and review keep that distinction explicit.

## Remaining obligations

1. Formalize correctness of the actual uniform macro-FFT compiler, including
   canonical residues, integer carries, unique extensions and prefix restrictions.
2. Instantiate the generic counting identities with these constructed rows,
   finite jets and streamed Boolean predicates. The code is implemented and
   reviewed; this composition is not yet kernel checked.
3. Formalize eventual parameter acceptance and all bit/space costs of row
   construction, entry evaluation, enumeration and Hermite recovery, then attach
   them to a deterministic machine and the L+1-query factor recovery.
4. Finish the pinned external theorem build/audit for whatever external baseline
   the final proof uses. An earlier fixed-width SAT theorem alone cannot be
   applied as a growing-arity tensor theorem.

The full 1/6 guarantee is therefore still unproved in the repository. All prior
research is preserved. No commit, push or completion is claimed.
