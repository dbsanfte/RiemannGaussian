# Physical bit execution and original-input factor recovery

27 October 2026. **PROGRESS; the full guaranteed factoring bit-time theorem is
open.** This packet extends the source-acquired counter and records concrete
reuse opportunities in the published Lean proof. It does not improve the older
native long-residue query's soft-K^(5/4) bound.

The user's Lean-source lead is confirmed by the pinned
[fixed-width counting/SAT machine theorem](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean).
Its endpoint and complete source closure were audited in earlier packets.
It proves the square-root-logarithmic rate for fixed-width CNF; it does not
automatically furnish the newer manuscript's sharper rate or a growing-scope
factoring machine. That external audit is preserved, with no new rebuild here.

## What is now connected

**Original integer to acquired count to a proper factor.** The new public
algorithm reindexes the actual ordered equality-subdivided multiplication graph,
uses its paid original entry checkers, acquires the source arrays and measurement
designs internally for every prefix count, and performs actual false-first
witness recovery. Restricting a prefix changes table entries, not scopes, so
the exact occurrence bound remains two. Every chosen bit belongs to one common
accepted witness. A literal binary decoder returns an ordinary proper integer
divisor, including for square inputs.

`ScheduledFactorExecution.run` takes only N. It computes the schedule and exact
precision, tests a decidable integer/rational guard, and uses complete trial
division when the guard is not met. Lean proves soundness and completeness for
every natural input, including zero, one and primes. It also proves that the
actual guard passes eventually, so this same execution eventually selects the
source-counter branch. Recovery uses at most wireCount+1 acquired queries.
Each query currently reacquires its source/design data; no cross-prefix cache
is assumed. See the [public execution review](review-public-acquired-execution.md).

These are whole-input semantic and branch theorems, not a time theorem. The
fallback's finite exceptional range has no small explicit threshold here.
Small fallback controls therefore say nothing about fast-branch performance.

**Actual coefficient arithmetic.** The new jet routines operate on signed
Boolean numerators and Boolean denominators, using actual rational-word
addition, scaling and convolution. The expression compiler accepts original
physical-word constants. Its structural capacity calculation derives every
intermediate fit and an initialized width; it assumes no coefficient answer or
output-fit oracle. See [compiler details](physical-jet-compiler-proof.md) and
the [independent review](review-physical-jet-compiler.md).

**Actual local interpolation.** The physical local evaluator executes both
restricted truth branches and caches their outputs. Input representations
derive all intermediate widths and exact agreement with the frozen rational
evaluator. From initial bounds J,d,B<=2^b, the sufficient word width is

```
Wbits = (2*b+3)*(w+1)+3.
```

Its actual arithmetic/cell ledger is at most
`2^w*(E+(w+1)*nodeBudget(J,Wbits))`, where E bounds the actual entry callback.
See [local execution](local-bit-execution.md) and
[independent review](review-local-physical.md).

**Actual measurement tests.** Signed-word dots, subtraction and zero scans
preserve the exact previous false-first representative, including signed-zero
encodings and empty fibres. Every visited measurement leaf has a polynomial
arithmetic bound. Matrix and target acquisition, listing and the outer
control/address implementation remain separate.

**Literal support count.** For the actual integer schedule and cutoff
q=floor(2nR/Q), Lean proves

\[
\text{for every }\epsilon>0,\quad
\sum_{j=0}^{q}2^j\binom nj\le e^{\epsilon n}
\quad\text{eventually}.
\]

The proof keeps the rounded definitions of R and Q and avoids the previously
unpinned constant 16435. The public incidence identity is exactly 2*wireCount,
and the public precision computes this same cutoff plus one. This counts the
actual support menu, not the cost of executing each callback. See
[measurement and rate details](measurement-and-support-proof.md) and their
[independent review](review-measurement-rate.md).

## Reusable machinery found in the upstream proof

The [read-only source audit](upstream-source-reuse.md) found actual primitive
programs for arbitrary finite scope lists, beyond the fixed-k SAT interface:

- Packing has a fixed-polynomial bound in a scalar size that includes the
  explicit scopes, incidences, r^Q and r^(2Q), without a hidden 2^n term.
- An executed integer cache and count-based numerator recurrence already
  generate the required integer data. `scalarEntry_eq_entry` connects that
  recurrence to the semantic numerator our source construction uses.
- A generic opaque-byte emitter constructs source row expressions from
  materialized scalar tables.

These components can avoid reimplementing substantial preprocessing. Reuse
still requires exact scope/order, reciprocal tolerance, namespace and signed
word/byte encoding bridges, plus paid rational constant tables. The existing
fixed-width finite-ring backend cannot simply be declared an unconditional
exact-rational ring: our rational capacity proofs are essential.

A second positive route deserves investigation: the upstream backend already
computes in an unramified extension of Z/(3^t), and its exact count decoder can
recover a Boolean count below 3^t. Taking t=n+1 provides enough count range.
Residue-distinct interpolation nodes can be supplied in extension degree
O(log Q). This could avoid much of the remaining rational-machine assembly,
but it requires rebuilding the source/interpolation instance over that ring.
Reducing our current rational coefficients or integer nodes modulo 3^t would
not suffice, because denominators divisible by three are not units. The
growing-scope local evaluator and complete controller still need to be joined.

This alternative has a generic algebraic starting point:
`GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial` permits arbitrary
factor systems over a commutative ring, and `Counting.explicitRecoveredValue_eq_count`
supplies generic finite-alphabet reconstruction. The current concrete leaf
program still assumes SAT clauses. One candidate adapter uses the engine's
ternary alphabet, rejects symbol 2 in every local predicate, and otherwise
runs our Boolean checker. Coverage would then force every accepted global
assignment to be Boolean, without changing scopes or the occurrence bound.
Local traversal becomes 3^w, still subexponential at our scope bound; polynomial
degree doubles and the precision/guard constants must be re-established.
This is a proposed connection, not a proved factoring-machine instantiation.

## Remaining acceptance condition

The reviewed candidate envelope remains
`poly(n)*Cq*Y*2^h*2^w`, with n proportional to bitLength(N). Its scheduled
nonpolynomial factors suggest the earlier candidate N^o(1) rate. **No theorem
in this packet bounds the complete public run by that expression.**

The next work is to join the upstream source programs through exact adapters,
acquire physical source/corrected-port words, and connect the physical group,
fibre, support and Hermite computations. The same run must pay all source and
width initialization, finite-list/closure access, control, binary address and
storage costs. Array access and some immutable-word copies currently carry
conservative flat-cell charges; they are not yet a compiled tape execution.
Natural-number report bookkeeping is also not a free primitive instruction.

Only that complete execution/resource composition, followed by the schedule
estimate, can establish the 1/6-or-better scaling goal. Correct all-input
factor recovery and component clocks do not substitute for it.

## Verification and preservation

Eleven new Lean modules pass with autoImplicit disabled, warnings as errors,
ordinary root imports and all 15 scoped linters. The axiom audit covers all
490 generated declarations, including 328 theorem constants, allowing only
propext, Classical.choice and Quot.sound. Independent isolated objects match
the canonical objects, with the source-resolved dependency checkpoint unchanged.
Exact counts and hashes are in `verification.json` and `manifest.json`.

Execution diagnostics cover signed cancellation and inconsistent measurements,
actual acquired conditional counts, initialized/overflow coefficient arithmetic,
a rational two-port local tensor, and the input-only fallback wrapper. These
are structural controls, not a semiprime success campaign or rate evidence.
All preceding evidence, concurrent work and append-only journal prefixes are
preserved. No commit or push was performed.
