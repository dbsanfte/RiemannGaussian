# Formal counter identities, arithmetic network, and scheduled rate bounds

26 October 2026. Active objective: **pursue the 1/6 (or better!) scaling goal**.
The preceding turn implemented a complete reference algorithm and was progress.
This turn proves central identities for that actual route. The full all-input
factoring bit-complexity theorem is still open; the goal remains active.

The implementation being formalized is preserved in the
[shared-counter checkpoint](../semiprime-shared-counter-20261026/README.md).
No finite example or successful test is used to infer coverage or an exponent.

## Newly compiled pieces

| Component | Compiled result | Remaining connection |
|---|---|---|
| Boolean diagonal | `SemiprimeBooleanDiagonal.boolean_diagonal` proves the full degree-truncated Möbius identity, signs and forced-coordinate sum | Connect concrete row forms and original assignments to the counter's global polynomial |
| Taylor degree | `SemiprimeCounterFiltration.correctedProduct_taylor_diagonal` derives the required filtration for actual scalar bases, positive-degree linear correction ports and streamed tensor products | Prove these ports are exactly the shifted native rows and identify the executed coefficients |
| Measurement fibres | `SemiprimeSharedSummary.shared_summary_contraction` proves arbitrary-group separated sums, with unforced representatives and empty fibres included | Derive its invariance from the constructed rows and refine the scanning loops |
| Hermite recovery | `SemiprimeHermiteRecovery.explicit_hermite_at_zero` proves the explicit formula from retained Taylor packets, using a constructed finite inverse | Relate the code's inverse recurrence/truncated arrays to this polynomial construction and account for bit work |
| Multiplication arithmetic | `SemiprimeMacroFermatNetwork.arithmetic_network_iff` proves canonical Fourier/carry stages exist exactly for integer digit multiplication | Connect the Boolean bit-port graph, nontrivial-factor flags, parameter selection and wire counts |
| Prefix recovery | `SemiprimeCountRecovery.search_some_sound` and `search_queries_le` prove a common original witness and at most L+1 actual conditional-count calls | Supply correctness/cost of the original network's prefix counter and decode its factor bits |
| Rate and guards | `SemiprimeCounterRate.eventually_non_tail_schedule_checks` proves the actual integer schedule's non-tail guards, including growing arity | The exact binomial-tail guard and full machine runtime remain open |

All theorem names above have prefix `RiemannGaussian`. These are separate
components with explicit interfaces; no single theorem yet composes the complete
counter or factoring machine. [Independent integration review](proof-integration-review.md)
records the precise boundary.

## The counting algebra now proved

The Boolean diagonal theorem starts from arbitrary multivariate polynomials and
their genuine total-degree bound. It proves cancellation outside the monomial
support, derives the cutoff, and then sums over arbitrary assignment-dependent
polynomials. The actual corrected product is proved to satisfy
`degree_X(coeff_z^j G_x) <= j`; this condition is not supplied as a new hypothesis.
All retained coefficients share the implemented menu `|E|<=J-1`.

The Hermite module constructs the local inverse rather than assuming matching
output jets. For

\[
 L_t(T)=\prod_{s\ne t}\left(\frac{T-s}{t-s}\right)^J,
\]

its shifted constant is one. A finite geometric inverse modulo `z^J` supplies
the local quotient. The resulting sum of cardinal factors has the required
degree and Taylor packets, so the proved multiplicity/divisibility argument
identifies it with H. Its value at zero is the formula used by the reference
counter, with the quotient evaluated at `-t`. Only retained input packets enter.

See [diagonal notes](boolean-diagonal-proof.md),
[filtration notes](counter-filtration-proof.md),
[Hermite notes](hermite-explicit-proof.md), and
[recovery/separation notes](recovery-summary-proof.md).

## Arithmetic and real size bounds

The macro-Fermat module uses the literal composite ring `ZMod(2^n+1)` and root
4, with n a power of two. It proves the principal character sum, invertible
normalization, compiler-indexed two-stage transform with twiddle, finite ordinary
convolution, canonical inverse recovery, integer carry existence and uniqueness.
The final equivalence is about actual integer digit multiplication. The strict
quarter-radix bound also proves coefficients and carries fit below `2^n`, matching
the physical carry-word restriction. It does not yet prove correctness of the
Python Boolean graph or uniqueness of every encoded internal bit extension.
See [arithmetic notes](macro-arithmetic-notes.md).

The rate module formalizes the actual integer-floor schedule, not merely an
assumed small auxiliary dimension. In particular, its scheduled D satisfies
`D^128 < 2n`, hence `D^2 <= 2*n^(1/64)`. This proves eventual incidence balance
for every arity `w<=C*n^(3/4)`. Group balance has an explicit sufficient threshold.
It also proves eventual positivity/concentration range and centered-interval
containment for the actual r,Q,R choices. The exact binomial tail is the remaining
numeric guard. See [rate notes](rate-proof.md).

The analytic envelope, including a fixed multiplicative constant, polynomial
prefactor, and the local `exp(B*L^(3/4))` work, is proved subpower after the
logarithmic substitution. This is a theorem about that envelope, **not yet a
running-time theorem for the factoring code**. Its connection to actual binary
length, linear wire count and primitive bit operations must be proved.

## Verification and continuation

Seven new modules compile strictly against the pinned repository toolchain.
[CombinedCounterAudit.lean](CombinedCounterAudit.lean) imports the ordinary root
and every new module, runs scoped lint, and audits every generated declaration
for custom or disallowed transitive axioms. See its
[output](combined-audit.log) and [review record](review.json).
Independent reviews check theorem scope against the actual code, rather than
treating compilation as evidence that the intended algorithm was modeled.

The full external SAT theorem build is still tracked separately in
[external-build-snapshot.json](external-build-snapshot.json), using live exec
session 85099. Continue that handle; do not restart on an observation timeout.
These seven new modules import Mathlib and existing project modules, not the
external SAT endpoint. Its completion alone would not close this new route.

The next substantive proof should compose the constructed forms, global H,
concrete corrected ports, measurement invariance and Hermite expression into one
counter-correctness theorem. The Boolean graph/compiler refinement, remaining
binomial-tail test, and primitive bit-time/space proofs remain necessary for the
full 1/6 guarantee. Previous evidence is preserved. No commit, push, or goal
completion is claimed.
