# The remaining coprime/count cancellation test

The numerical `-79/1000` floor remains open. This pass proves no further
source-scale saving for the main signed aggregate. The preceding
`ZetaRieszSmallGcdPayment` comparison and its independent target
`remainingEnergy <= 3/(320*(N+1))` remain unchanged.

## The checked common channel

For a squarefree label `n != 1`, a positive cutoff `k<n`, and the strict
reflected endpoint `(n-1)/k < minFac n`, the original divisor prefix is

\[
\operatorname{sharp}(k,n)=-\mu(n).
\]

Consequently, on any population sharing this late-prefix geometry, the
ACTUAL joined correlation is

\[
\sum_n w_n\operatorname{sharp}(k,n)=-\sum_n\mu(n)w_n.
\]

The weight `w_n` can contain the original phase, factorial kernel,
allocation and all masks. No count or bin is averaged away. The energy
on such cutoffs is exactly the square of this signed Möbius moment times
their reciprocal-cutoff mass. The one-sided pairing is exactly that
moment times the nonnegative corrected-profile increment. Its favorable
sign is left uncharged in `signed_plateau_floor`.

These statements concern a selected population with the stated geometry;
they do not assert that the whole core has one common plateau. The
moment itself has no new arithmetic bound. In particular, a lower bound
on a comparison energy is not a lower bound on the carrier's deficit.

`coprime_three_prime_regression` checks the genuine squarefree labels
`1001=7*11*13` and `7429=17*19*23`. They are coprime, and both have prefix
one at the active post-hinge cutoff 500 for length `log 499`.
`coprime_cutoff_cross_positive` shows that after deleting the diagonal,
their ordered cross contribution is still `1/250`. The test weights are
one. This is not a native core example with the carrier's phase weights,
and not a counterexample to a fixed-height cofinal arithmetic estimate.
It does rule out inferring cutoff orthogonality from coprimality alone.

## Quantitative finite test

The optional `scripts/probe_riesz_joined_count_correlation.py` exhausts
every squarefree subset of each of two disjoint twelve-prime universes.
It checks the original core predicates, moving length, physical support,
factorial allocation and phase at the native orders 256 and 640. All
counts selected by these predicates stay joined. This improves the
incidence coverage of the earlier one-label-per-count diagnostic, but
does not supply a population or density approximation.

Each chosen universe has total logarithm less than `3.9N`. Any two core
labels in one universe therefore share a prime. Every such shared prime
has logarithm above `N/4096`; across the universes every pair is coprime.
The script computes the remaining small-gcd matrix after removing the
old relative-nearness and phase-alignment masks, using the SAME adverse
cutoff selection made on the entire chosen population. It retains every
ordered-pair sign and reports both the before-mask and after-mask count
matrices. Signed masked matrices need not be positive semidefinite.

The twelve height/seed/order tests give:

| Quantity in the constructed finite populations | Observation |
| --- | --- |
| Selected labels | 273, 283, 352, 360 |
| Counts present | 3–7 at order 256; 3–9 at order 640 |
| Cross-count terms in the COMPLETE adverse energy | reinforce in 7 cases, cancel in 5 |
| Joined / separate-count COMPLETE energy | about 0.476–1.395 |
| Cross-count terms in the REMAINING small-gcd aggregate | reinforce in 8 cases, cancel in 4 |
| Remaining same-count contribution | negative in 11 cases |
| Remaining all-count aggregate | positive in 4 cases, negative in 8 |
| Cutoff-period cost reduction | about 0.034%–0.228% of this subset's atomic price |

The same-count contributions above exclude individual-label diagonals.
They are signed entries of the masked cross matrix, not independently
proved payments. They cannot be discarded or used as credits for the full
core. In particular, counting the complete matrix's large-shared-factor
terms as progress on the remaining coprime problem would be incorrect.

The numerical values use a COMMON amplitude rescaling with log scale
roughly `-503` or `-1253`. They cannot be compared to the actual
`3/(320*(N+1))` budget. The original count cutoff is used at these small
orders: the eventual `K/864` payment must not be applied prematurely.
No order 65536+, count 56+, many-bin or cofinal population is certified.
Prime tests and profile integration are floating diagnostics, without
Lean primality certificates or interval arithmetic. The report is
`.lake/riesz-joined-count-probe.json`; it is outside ordinary builds/CI.

## Consequence for the next estimate

Neither coprimality nor joining all counts in a finite universe forces a
small result. The actual signed Möbius/phase moments, and especially their
cross-count terms AFTER the paid masks, still need an independent bound.
The checked plateau identities explain why cutoff-period grouping can
leave a coherent contribution unchanged: the phase belongs to the label,
not to the varying divisor cutoff.

Preserve the whole original population and adverse set in that next
estimate. Do not split the reinforcing mixed counts into positive
allowances, treat the observed same-count negatives as free credits, or
claim that these tests refute a cofinal cancellation mechanism. No new
carrier, floor, ceiling or zero exclusion is introduced in this pass.

## Local verification

Eight public theorems have direct/targeted warnings-as-errors checks,
ordinary-root import, namespace lint and all-public standard-axiom audits.
See `docs/riesz-coprime-plateau-audit.json`. Earlier mathematical sources,
the unrelated staged files, README and published endpoints are preserved.
Work remains local; no commit, push or wider publication gate is requested.
