# Running investigation: semiprime factor location

Started: 2026-10-01. Last updated: 2026-10-03.
Scope: side investigation; independent of the active RH proof campaign.
Repository reference when this note was written:
`ec0473dfab685561c2fdca7f08ff449684bcca07`.

## Publication registration (2026-10-02)

The ten `Semiprime*` proof modules are now imported by the ordinary Lean
library and checked by its build, declaration lint and axiom audit. The
numerical factorisation probes and benchmarks remain optional and separate
from the RH campaign. Historical entries below describe their earlier local
validation and import status; this registration supersedes statements that
the published proof modules are outside the umbrella or ordinary CI. It
supplies no new generic factoring exponent or RH estimate.

## Current conclusion

We now have a cheap classical modular encoding of the unknown factor sum:
for `N=p*q`, `S=p+q` and `gcd(a,N)=1`, `a^(N+1)=a^S (mod N)`.
A sparse residue-colour decoder searches this encoding without a zeta
coefficient grid. Adaptive interval growth and prime-power residue masks
give a measured speed advantage over the installed GNU `factor` 8.32 on
fresh balanced semiprimes with the public promise `q/p<=2`.
The saved implementation and complete 108-input replay are linked in the
dated modular-signal entry below. At 79–96 input bits that replay was
approximately 3.4–6.8 times faster than this baseline.

This is a practical result in a specified regime, not a new asymptotic
factoring theorem or a claim to beat the best classical software.
The collision search remains approximately `N^(1/4)` in size, with
additional collision work possible for small multiplicative orders.
Broader factor ratios reversed the earlier prototype's advantage.
Tuned quadratic-sieve and number-field-sieve implementations have not
been benchmarked.

Earlier numerical zeta extraction remains useful evidence about exact
support filters: the local-support/Euler-filter pass reduced medians from
0.125 s to 0.0197 s at 323, and from 1.661 s to 0.0653 s at 2021.
These small-input extractors did not beat conventional factorisation.

The scaling audit below still rules out an anticipated large-input
crossover for the present fixed-cutoff, fixed-local-window parameter
strategy: its grid grows at least linearly in the numerical product
magnitude, hence exponentially in input bit length. Improving the
arithmetic cost per sample or these fixed filters does not remove this
dependence.

The October 2 investigation adds an experimental weighted collision search
at the one-fifth target scale, with exact order certificates and batched
GCD/vector operations. Its saved replay improves our own baseline by about
10% at nominal 64 and 80 bits, but fixed-base low-order failures remain.
It does not prove a new unconditional exponent.

An exact sparse Frobenius identity also exposes `p+q` through a truncated
polynomial or one binomial residue. Cheap extraction remains unresolved.
Independent prime-prefix tables do improve large-batch throughput: a
fresh 1,024-input, 32-bit replay took about 11.0 microseconds per input,
including cache construction, versus 44.1 for our prime-power decoder.
That is a standard shared-precomputation regime, not a single-input
one-sixth factoring result. Source and replay data are saved below.

The latest single-input investigation implements an order-separation pass
with `~O(N^(1/6))` charged work and an explicit coverage condition. It uses
`N-1` to make the hidden local orders coprime before a batched order search.
Adding it before our own weighted prototype gives total-corpus speedups of
about 1.1–1.9 times at nominal 64 bits and 1.8–2.3 times at nominal 80 bits
in two fresh replays. These comparisons are against our Python prototype.
The pass fails explicitly on long remaining periods; it is not a generic
one-sixth algorithm.

Quadratic Jacobi colour supplies another exact order separator using
`N-Jacobi(D,N)`. An exact common phase rotation reduces its geometric
evaluation from three scalar convolutions to two, with approximately 2%
runtime savings in the larger tested inputs. Both ideas have checked Lean
algebraic lemmas and exact finite regressions. Colour solved the five
safe-prime controls that defeated the scalar pass, but adding it to the
hybrid increased total runtime in the fresh 72-input corpus. Three new
controls, including 64- and 80-bit inputs, defeat all 16 tested colours:
all four `p±1,q±1` rough periods are too long. The dated entry below records
the successful extraction, the phase-tilt derivation and this sharper gap.

The subsequent long-period investigation gets past two of those controls
with a degree-six Dickson map, including a remaining period about 95 times
larger than the old linear cover. Exact trace folding, multiplicative
finite differences and monic remainder trees supply public-input recovery
without a quadratic grid. Classical ECM supplies another bounded pass that
solves all three controls on its first public curve. On 48 fresh inputs,
the Dickson pass adds five hits over the same-colour linear pass but costs
more time; one curve succeeds on 44/48. Staged target evaluation improves
the curve pass's total runtime by 1.67–1.93 times over full-cover evaluation.
These are partial algorithms and comparisons within our prototype, not
a generic exponent theorem or a speed claim against tuned ECM software.

The complex-correction follow-up adds two more public-input covers. A phase
rotation before scalar projection recovers two of four saved Dickson
failures; exponentially spaced order aliases recover a third. Their points
are generated by repeated group powering, without writing enormous integer
exponents. The larger four-rough control still defeats all tested phase
and small-base orbit covers. Lean also proves that applying the RH-style
perpendicular null correction to our coherent collision detector erases
the factor-bearing amplitude entirely. This distinguishes useful rotation
from an exact cancellation which destroys the observable.

The user-confirmed terminal target is now a **guaranteed bound on every
run**: factor every semiprime in `~O(N^(1/6))` bit operations, where `N`
is the numerical input, including all input-specific construction. It is
not an expected-time target. This theorem is **not proved**. A bounded-work
attempt, a coverage hypothesis, and a finite successful corpus do not
establish it. The checked Lean files now certify signal algebra, a universal
classical arithmetic cover and complete correctness of an explicit public
factorizer. They do not certify a one-sixth implementation cost model.

The latest row audit proves an exact shared-prefix cancellation and a
root-preserving paired product/reciprocal-trace identity. Raw signed row
cancellation can erase an original factor hit; the root-preserving version
retains the coupled weighted centre. Sharing those centres saved about 6.7%
of centre evaluations on the fresh 80-bit cohort, with no exponent change.
The dated row-structure entry records the proofs and complete replay.

The Cartesian follow-up computes the exact root-preserving product of a
4,096-by-4,096 **constant-centre model** from 8,192 residues without visiting
the individual pairs. It is about 10 times faster than explicit pair
multiplication in the tested 79–80-bit inputs. This is a bulk-detector
benchmark, not a factoring speedup: the literal rounded square-root centres
are different. Lean now proves the mixed-curvature formula and a lower
bound on the integer correction width needed to flatten them. The dated
Cartesian entry below records both the working batch kernel and that gap.

The immediate open problem is processing an exact, complete collision cover
within a linear-width budget while preserving its proper factor hits. The
literal-centre construction must retain its integer square-root correction;
the October 3 centre-free construction below replaces that construction
with a longer exponent interval. All input-specific construction is charged.
The full classical cover has checked universal coverage and proper-factor
recovery. A faster proposed cover must preserve those guarantees and supply
the complete bit-operation bound.
These experiments do not establish independence of prime gaps and factors,
or impossibility of other zeta-based algorithms.

The recovery follow-up now proves that every supplied proper pair hit can
be recovered with at most one GCD per target plus one per distinct root,
including globally shared and repeated roots. It reuses the existing
shared-root derivative lemma and retains all literal integer centres in
its row replay. The exact workload audit also proves a quadratic lower
bound for the replay's explicit weight enumeration. This advances recovery
for supplied lists; exact implicit construction and the complete every-run
one-sixth bit bound remain open. The dated recovery
entry below records the proofs and executable replay.

The universal-coverage continuation formalizes the complete Lehman window
with literal rounded centres and gives a factorizer receiving only N.
`SemiprimeLehmanCoverage.factor_semiprime` proves that it returns a proper
factor for every product of two primes, including equal primes and arbitrary
factor ratios. `candidatePairs_length_ge` also proves that its explicit
candidate list has at least B² entries at B=ceil(N^(1/6)). The gap is now
an exact fast search and its every-run bit cost, not correctness of this
full classical cover. This baseline is not a one-sixth algorithm.

The next construction test shares exact centres by square classes:
k=d*m². `SemiprimeSquareProductCover.square_class_centre` proves the
literal formula `ceil(2*m*sqrt(d*N))`. A short fixed class menu gives
small centre caches, but loses universal coverage. Lean now verifies
a semiprime with no sharp-window hit in any class through 16, and a
second semiprime with no hit even in the full width-B interval. Exact
non-square rows outside the menu succeed on both controls. These are
coverage obstructions for the specified menus, not impossibility
theorems for other batching methods or modular aliases. The every-run
one-sixth bit bound remains open.

The RH-cancellation search now transfers the finite signed-subset/Euler
identity to the original row differences. `SemiprimeRHCancellation`
proves that this product keeps every prime-field collision, and that
unit phase/target normalization preserves the exact GCD for every modulus.
It also exposes the centre-power companion in a mixed row difference.
Verified literal controls lose their proper factors under this signed
sum and under a complete common-centre divisor-orbit ratio, while their
original collision products retain the factors. The dated entry below
records the seven RH source references, 19 compiled public theorems and
exact replay. The full product's fast construction remains unresolved.

The additive-prefix continuation now specifies one degree-B polynomial
evaluated at B public points, with at most one lazy block scan. The compiled
`SemiprimeStrassenPrefix.prefix_none_iff_clear` connects this result exactly
to the complete Lehman complement, and `factor_semiprime` proves universal
correctness of the updated full specification. The recovery query bound is
2B, including whole-modulus columns. This is classical Strassen batching;
the Lean specification does not implement the GMP polynomial engine or prove
its bit cost. The centre-coupled complement remains quadratic and the full
one-sixth guarantee remains open.

The centre-free continuation now proves a complete prime-field collision
cover with B geometric roots and an exponent interval of length 3B²+1.
`SemiprimeCentreFreeCover.recoverShifted_after_failed_short` discharges
its hidden-period premises from the public prefix, projected GCD and failed
short-search certificates. `explicit_reshape_input_bound` proves that the
standard baby/giant reshape still uses more than sqrt(12B³) inputs. The
next compression target is this exact interval search. Public projection
kernels and a Lean total bit-cost theorem also remain open; the full
one-sixth guarantee has not been achieved.

The interval-derivative continuation retains three row scalars: the original
product and its derivatives with respect to the target and base. The compiled
`SemiprimeIntervalJet.exists_recoverable_projected_row` proves that a proper
hit survives through these scalars after the public prefix and short-period
checks. Even a product zero over the whole modulus can reveal different
exponent indices in the two prime fields. A blocked executable evaluator
constructs one row without the full exponent interval or a pair matrix.
Searching every row still exceeds the linear-width budget; its exact
construction and the remaining search cost are recorded below.

The shared-block follow-up now proves the exact three-channel circuit,
including the block-offset and normalized-point derivative terms.
`SemiprimeSharedIntervalJet.sharedBlockedJet_exact` identifies its output
with the original padded interval scalars, and
`exists_recoverable_padded_row` retains a proper hit from the complete
centre-free cover. One shared polynomial and point tree reduce the explicit
all-row input construction to the earlier B^(3/2) reshape scale. A checked
two-row control also shows why their first jets cannot simply be pooled:
all three channels vanish. The every-run one-sixth bit bound is still open.

Higher deformation coefficients now retain the information that pooling
first jets erases. `SemiprimeTaggedPooling.unequal_zero_counts_gcd`
separates different local collision counts; `different_zero_labels_gcd`
separates equal counts with different row labels; and
`decodedHead_original_distinct_index_gcd` retains different exponent
indices even when the same rows collide in both fields. The final tagged
heads have linear degree bounds, but obtaining them cheaply is still open.
The tagged prototype computes all original row jets first and retains a
dense coefficient prefix. This identifies a sufficient information payload
for a future shared construction, rather than achieving the requested cost.

The original-source follow-up now removes that dense prefix after public
row classification. `SemiprimeSourceHead.fullSource_head_eq_tagged` and
`fullMarked_head_eq_tagged` connect the heads to complete original
collision deformations. `publicHeadProduct_eq_coeff` and
`publicHeadMarked_eq_coeff` obtain them from a homogeneous marked product
tree, with no deformation prefix. The executable source pass computes
residuals first and defers derivative channels to saturated rows. The
shared residual construction still has the B^(3/2) input scale; neither
that cost nor deterministic base selection has been reduced to the
required every-run sixth-root bound.

The deterministic seed continuation now removes a successful-seed-menu
premise from a universal factor-or-large-order reduction.
`SemiprimeSeedLcm.publicRoute_semiprime` proves that the N-only procedure
returns a proper divisor or an explicit unit whose order exceeds 4B^2.
Small known orders are accumulated by LCM until their common modulus
reaches B; a degree bound guarantees each intervening small-integer seed
scan succeeds. Its lookup-source and candidate-power budgets are at most
4B*clog(2,B) and B*clog(2,B). This does not factor the above-cap population.
Large kernel/nonkernel extraction and the complete bit backend remain
open; no universal one-sixth factorization theorem is claimed.

The local-order continuation now refines the selected large-order seed
with the existing distinct-root polynomial batch, before any projection.
`SemiprimeLocalOrderRouting.recoverShort_of_unequal` needs only unequal
local periods and a small minimum; a failed batch on an above-cap seed
certifies that both local periods are large. Its N-only
`publicRoute_semiprime` returns a proper factor, a large-kernel certificate,
or a projected unit with two large, coprime, B-rough local periods.
The added source lists have length 2B on each axis and polynomial degree
at most 2B. `refineBaseGcdCount_le` charges at most 9B+2 GCD queries,
including the base-unit check. The fresh frozen-input replay now returns
19 factors and two projected-long certificates; a separate checked kernel
control is retained. These are stronger reductions, not the every-run
one-sixth bit bound. Both remaining extraction branches and that backend
are still open.

The kernel continuation now constructs one additive prefix for N-1 and
reuses its labelled columns at every retained residual divisor.
`SemiprimeKernelResidual.splitSmall_complete` proves that logarithmic
prime-removal fuel leaves an exact smooth/rough split, with every rough
prime above B^2. `orderFromPrimes_eq_order` derives the smooth case's order
from the extracted prime list. A nontrivial active channel has prime
common order; `kernelRoute_semiprime` either factors N or retains a
semiprime R with 2R<N and a certified child route.
`residual_transport` proves that a factor of R recovers a proper factor
of N using the retained active unit. The N-only `publicRoute_semiprime`
eliminates original-input kernel outputs, while retaining projected-long
outputs and pending smaller tasks. The new replay factors two saved
kernel controls, including 3542303047=29759*119033, and preserves an
explicit pending-child control. Recursive completion, projected-long
extraction at linear source width, and the full every-run bit bound
remain OPEN.

The subsequent complete kernel descent reuses every actual child route.
`SemiprimeKernelDescent.publicTrace_cases` proves that the N-only trace
terminates at a recovered original factor or a projected-long certificate
on a semiprime no larger than N. Every parent unit, active unit and prime
list stays available for factor transport. Public logarithmic fuel bounds
the entire chain; `publicTrace_routing_width_budget` reserves at most
3B*clog(2,N+1) in base-width slots, including an immediately successful
child call, and `publicTrace_prefix_budget` pays the small-prime GCD
allowances at every level. Kernel descent is now complete under these
correctness and width contracts. The projected-long extractor at linear
source width and the complete classical bit backend remain OPEN.

The long-power continuation retains that entire descent and adds two
degree-at-most-2B batches at public powers N and N+1. In
`SemiprimeLongPowerRouting`, `publicPacket_cases` proves original-factor
recovery or a strengthened long leaf; `publicPacket_refinement_queries_le`
charges at most 8B+3 added GCDs at the ORIGINAL input's width.
`projected_predecessor_coprime` proves the surviving global period coprime
to N-1 without an added query. Failed N and N+1 batches certify global
coprimality to N and smaller-field coprimality to N+1, respectively.
`recoverKnownOrder_of_long` proves that acquiring the actual global order
would determine the exact factor sum via (N+1) mod M and factor directly.
That order is not supplied to the public routine. Two selected former
long controls now factor; all three previous long leaves still survive.
Order acquisition or another universal linear-source extractor and the
full every-run bit backend remain OPEN.

The retained global-collision continuation now recovers all three of those
previous long leaves. `SemiprimeTotientWindow.quarter_totient_properties`
proves that the cached projected unit is annihilated by the quarter
totient T, without acquiring its actual order. The public centre
C=(N+1-2*sqrt(N))/4 equals T plus the literal quarter factor-sum offset d.
`recoverQuarter_complete` recovers a factor when d<(2B)^2 by retaining
the global equality's exponent labels. `publicPacket_source_budget`
uses two lists of at most 2B entries and at most 4B merge comparisons at
the ORIGINAL input's width, preserving every preceding descent frame.
`publicPacket_cases` proves factor recovery or a remaining semiprime leaf
with p+q-2*sqrt(N)>=16B^2. A new selected 61-bit control remains in that
large-gap population. Universal coverage and the complete every-run bit
backend remain OPEN.

The cached residue continuation now also recovers offsets that wrap to
a short remainder in either hidden prime field. In
`SemiprimeTotientResidues`, `residue_source_of_left_offset` and
`residue_source_of_right_offset` prove recovery when d mod Dp or d mod Dq
is below (2B)^2 after the global decoder fails. The same cached lists
supply one degree-at-most-2B polynomial batch with at most 4B GCD queries;
no new window or powers are constructed. `publicPacket_cases` retains
the whole preceding packet and proves original-factor recovery or both
reduced offsets at least (2B)^2 on the actual semiprime leaf. A selected
63-bit wrapped-offset input now factors. The preceding 61-bit negative
still survives both orientations. Universal coverage and the complete
every-run bit backend remain OPEN.

The source-construction continuation now supplies executable natural-number
binary powers and geometric walks, with retained arithmetic counters.
`SemiprimeWindowConstruction.windowCertified_reconstruction` proves that
the actual constructed sorted records, global collision and decoded factor
equal the preceding certified window. `publicWindow_construction_budget`
charges at most 4B+4L+2 residue multiplications and 8B+6L+5 modulus-N
reductions at the ORIGINAL input's width, where L=clog(2,N+1).
Temporary products have at most 2L bits. This closes the recurrence/source
equivalence and exposes the raw arithmetic construction cost; inverse
acquisition, square roots, sorting, polynomial work, transport and their
complete implemented bit bounds remain separate requirements. All previous
outcomes persist, including the surviving 61-bit negative. Universal
coverage and the full guaranteed one-sixth bit theorem remain OPEN.

The inverse continuation now computes the modular inverse from the public
scalar with Euclid, retaining every actual step and bounded temporary.
`SemiprimeWindowInverse.countedInverse_correct` proves its gcd-coefficient
equation; `countedInverse_unit` identifies the canonical unit inverse.
`windowCertified_initialisation` reconstructs the exact preceding rows,
collision and factor without a supplied inverse. At original-input width,
`publicWindow_initialisation_budget` includes at most 4B+6L+2
multiplications, 8B+12L+7 reductions, 2L Euclidean quotients and 2L+1
power halvings. This closes inverse acquisition's arithmetic implementation
and operand bounds. Its primitive bit implementation, other backend costs
and universal coverage remain OPEN; all earlier outcomes persist.

The square-root continuation now supplies a restoring base-four algorithm
for the public centre and the optional quadratic decoder. In
`SemiprimeWindowSqrt`, `countedSqrt_correct` proves the exact integer root;
`countedSqrt_counts` charges its fixed shifts, digit extraction, comparisons,
additions and subtractions. The optional decoder gcd also uses counted
Euclid. `windowCertified_rooted_initialisation` retains every preceding row,
collision and factor. `publicWindow_rooted_initialisation_budget` includes
at most 4B+8L+4 variable products, 8B+18L+10 general reductions, 4L Euclidean
quotients, 3L restoring digit pairs and 2L+1 power halvings at the ORIGINAL
input's width. Primitive bit implementations and universal recovery still
remain required; the saved 61-bit negative persists.

The Boolean-backend continuation now implements ripple addition and
shift-and-add multiplication directly on little-endian bit lists. In
`SemiprimeBitArithmetic`, `addBits_correct` and `mulBits_correct` prove
their actual output values. The charged gate/read/write/branch model gives
at most 11L+4 primitive charges for addition and 24(L+1)^2+1 for a product
of physical L-bit inputs; `multiplyBatch_cost` composes actual product
reports with traversal and retention charges. A raw-row replay uses this
multiplier for both powers and walks and preserves every outcome. Native
remainder, legacy integer conversion, the rest of the arithmetic backend
and universal recovery remain required. This is a local primitive-model
price, not the whole factorizer's bit or machine-execution certificate.

The division continuation now implements ripple subtraction, paid
fixed-width copying, Boolean zero detection and restoring quotient/remainder.
`SemiprimeBitDivision.divideBits_correct` proves both computed outputs for
all input words, including zero divisors. `bounded_modMulBits` composes the
actual product and division with clock at most 96(L+1)^2+2 for physical
L-bit inputs. The replay now computes every raw residue update with that
Boolean backend and preserves all prior outcomes. Legacy conversions,
exponent and label interfaces, the other pipeline operations and universal
recovery remain required. The complete one-sixth guarantee is still open.

The bit-only loop continuation now keeps intermediate residues in Boolean
words throughout both setup powers and both geometric walks.
`SemiprimeBitPowerWalk.constructBitRows_raw_values` identifies their
residues with the earlier raw arrays at the actual encoded public centre
and block. `constructBitRows_cost` composes their complete local clocks
in the supplied exponent lengths and template length. Public-input and
template encoding, final labels/conversions, the other pipeline stages
and universal coverage remain required for the full guarantee.

The signed-multiplier continuation now closes the coverage gap on every
remaining projected-long quarter-window leaf. In
`SemiprimeTotientMultipliers`, `exists_multiplier_proper_pair` derives a
proper collision from a bounded signed multiple of the cached public
centre; no hidden order or offset enters the detector.
`publicPacket_complete` proves universal original-input recovery, including
squares and arbitrary factor ratios, with every descent frame retained.
The compact source reuses one degree-at-most-2B baby polynomial and three
2B-entry caches. Its full family still has exactly 4B² evaluation points
and at most 8B² streamed GCD queries. Fast implicit evaluation, the other
unpaid bit interfaces and the guaranteed one-sixth bound remain OPEN.

The exact-norm continuation now replaces that expanded multiplier stream
with shared full blocks and one separately shared short tail.
`SemiprimeMultiplierNorm.publicPacket_complete` proves universal recovery
through this N-only route. Each signed centre is read through its interval
product and two derivatives; a saturated norm retains a recoverable CRT
exponent index. The interval is exact, with no unproved simple-root padding.
The explicit degree/point budget has B^(3/2) scale, with a checked matching
scale obstruction for this representation. This improves the construction
frontier; it still does not meet the required linear B budget or complete
every-run one-sixth bit theorem.

The first-nonunit continuation now removes derivatives from the complete
norm cache. `SemiprimeFirstNorm.publicPacket_complete` proves that the
first public norm with GCD greater than one is always recoverable on
every actual remaining certified core. A proper product GCD skips
derivatives; only a saturated selected row constructs them. The scalar
recurrence contains no jet or derivative construction and is proved equal
to the richer carrier. `buildFirstSource_gcd_bound` proves at most 6B+2
GCD queries for this new source. Its main explicit norm input budget is
still B^(3/2); the full every-run one-sixth bit theorem remains OPEN.

The bulk continuation also removes per-row norm outputs and unit phase
construction from the detector. `SemiprimeBulkNorm.publicPacket_complete`
proves universal recovery with a concrete phase-free aggregate forest.
Saturation triggers a balanced left-first search; a unit left product
lets the source infer a zero right product without constructing it.
The actual forest uses at most 2D bulk GCD queries, where
D=log2(2B)+1, followed by at most one original late-jet consumer with
4B+2 queries. The explicit shared evaluation-point layout remains
B^(3/2), and the complete one-sixth bit theorem remains OPEN.

The scalar q-recurrence audit now proves why transposition alone does
not remove this price. `SemiprimeQAggregate.recurrenceCoeff_natDegree`
gives coefficient degree r, and `normalizedBlock_natDegree` gives
baby degree r*s. `qInputs_full_floor` proves the same strict 32B³
squared-input floor for every positive transposed block width.
The known-residue polynomial audit also checks a claimed one-sixth
literature lead: `SemiprimeKnownBitsBudget.originalForm_not_irreducible`
proves its unscaled integer polynomial has a nonunit content factor.
The correctly cleared idealised height budget requires N<B^4.
Neither audit is a lower bound on all possible factoring algorithms;
the requested every-run one-sixth bit theorem remains OPEN.

The quotient-row continuation now constructs an alternative informative
quadratic family through public Euclidean division, after removing the
trivial linear direction from its coefficient lattice.
`SemiprimeQuotientRows.publicRow_correct` proves its nonzero quadratic
coefficient and square-root-sized quotient coordinates.
`publicRow_balanced_power_coverage` connects that executable constructor
to an actual hidden-prime-field collision and a complete quadratic
candidate list for p≤q≤2p. `fifth_layout_budget` gives a linear row/point
input budget at fifth-root modulus scale. The native source evaluates
one polynomial on one baby axis and recovers a saturated aggregate from
one selected column, without constructing a pair matrix. Its certified
search-axis envelope at sixth-root modulus scale still has quarter-root
size. Arbitrary-ratio coverage, saturated local-period setup, full machine
refinement and the requested every-run one-sixth bit theorem remain OPEN.

The latest quotient packet now applies a public, target-preserving center
shift. `SemiprimeQuotientCentering.shiftRow_residual_gcd` preserves the
complete original GCD signal, and `publicPacket_balanced_power_coverage`
keeps the actual bounded collision and factor candidate. The shorter
shared baby axis uses the width of the public balanced factor box rather
than the full factor sum. On the saved hard input it reduces sixth-root
points from 98,775 to 11,642 and the paired native time from 6,403.50 ms
to 884.31 ms, including all new centering work. This changes the interval
constant, not its asymptotic exponent; the universal one-sixth bit theorem
remains OPEN. Original rows, signed indices and frozen parents survive.

The broader Euclidean-family audit now retains every convergent and
intermediate quadratic, plus both public factor orientations.
`SemiprimeEuclidRowFamily.intermediate_row_correct` proves their actual
quotient relations. Its literal balanced-semiprime control has
`control_column_gcd_one` for every signed index |i|<=269: expanding this
family does not justify the proposed m-sized window. Reference-only
index-growth data further challenge a small uniform constant; they are
not asymptotic lower bounds or complete detector failures at larger sizes.
The every-run one-sixth bit theorem remains OPEN.

The row-to-row continuation now forks the retained giant values into a
distinct-root polynomial and evaluates its derivative on those roots.
`SemiprimeRowDerivative.rowDerivative_eq_product` preserves every
off-diagonal difference exactly, and `recoverRows_none_iff` proves the
complete proper-pair hit union and saturated recovery. Its compiled
`control_derivative_recovers` theorem recovers on the earlier full-family
short baby-window counterexample. This removes the pair matrix from that
observable, but does not guarantee a local row collision or a one-sixth
bit budget. A separate timed native stress input exhausts all 394,276
original row derivatives; an inverse row axis has additional reference
hits. The fixed original-axis coverage and universal scaling questions
must therefore remain distinct.

The reciprocal continuation now retains cross-products of original row
values through coefficient reversal of the same monic polynomial.
`SemiprimeReciprocalRows.reciprocalPolynomial_eq_reverse` and its exact
value/derivative unit-phase GCD theorems connect that channel to complete
deflated inverse-root recovery. `control_reciprocal_recovers` proves
recovery on the larger native ordinary-axis failure. Its full paid native
source returns 39,167,077,933 using the original 394,276 giant powers and
one root tree, with no extra giant powers or pair matrix. Universal
coverage of the combined channels and their complete bit budget remain
OPEN; the larger ordinary-axis failure itself remains native-only after
the attempted monolithic kernel certificate exceeded 50 GB of memory.

The guarded trace continuation now combines both original pair channels
in one distinct-trace polynomial. `SemiprimeTraceRows.trace_difference_gcd`
retains their exact product GCD, and
`SemiprimeGuardedTrace.guardedTraceRows_succeeds_of_pair` proves complete
supplied-hit preservation through raw endpoints, checked whole-trace
compression and saturated derivative recovery.
`guardedTraceRows_none_iff` proves the exact original pair/endpoint hit union,
so compression creates no extra coverage.
`guardedTraceGcdCount_le` bounds these recovery stages by five GCD queries
per original unit; construction, lookup and polynomial bit costs are outside
that bound. A wider reference corpus has a 90-bit combined-channel miss,
including both raw endpoints. The complete timed N-only source now also
returns none after evaluating all 4,894,754 trace derivatives, without a
pair matrix; this exhaustive fixed-family failure remains native-only.
Its replay is recorded in the dated continuation below. None of these
results supplies universal
arbitrary-ratio one-sixth bit coverage.

## Mathematical observables and existing Lean work

Throughout the factor-reconstruction identities, let `N = p*q` for distinct
primes `p < q`, and define

$$
\eta=\frac{\log q-\log p}{2},
\qquad p=\sqrt N\,e^{-\eta},
\qquad q=\sqrt N\,e^\eta.
$$

The local scratch file is
`.lake/SemiprimeImbalanceScratch.lean`, in namespace
`RiemannGaussian.SemiprimeImbalanceScratch`. It is outside ordinary builds
and is not a portable, tracked library artifact. Its existing declarations
include:

| Observable or audit | Scratch theorem |
| --- | --- |
| Reconstruction from imbalance | `small_factor_log`, `small_factor_eq` |
| Noisy imbalance gives a factor interval | `factor_interval_of_imbalance_error` |
| Midpoint Riesz response equals `log p` | `riesz_midpoint_eq_small_log` |
| Noisy Riesz measurement gives a factor interval | `factor_interval_of_riesz_error` |
| Total-log phase depends only on the product | `total_phase_product` |
| Factor-sensitive pair spectrum equals `2*cos(2*t*eta)` | `pairSpectrum_semiprime` |
| Nonaliased noisy phase gives a factor interval | `factor_interval_of_phase_measurement` |
| Cosine sensitivity is quadratic near equal factors | `phase_defect_quadratic_bounds` |
| Positive product-Gaussian resolution requirement | `productGaussian_resolution_requirement` |
| Low-sensitivity estimator obstruction at 33 and 35 | `low_sensitivity_two_semiprime_obstruction` |

These declarations were inspected, not recompiled during this side
investigation. Accurate measurement is an explicit premise in the
reconstruction statements; an efficient evaluator is not supplied by them.

Relevant tracked building blocks:

- [ZetaPrimeQuadraticArithmetic.lean](../RiemannGaussian/ZetaPrimeQuadraticArithmetic.lean):
  `zetaPrimePairArithmetic` is the Dirichlet convolution
  `vonMangoldt * vonMangoldt`, and
  `LSeriesHasSum_zetaPrimePairArithmetic` identifies its convergent series.
- [SuzukiLogarithmicConvolution.lean](../RiemannGaussian/SuzukiLogarithmicConvolution.lean):
  `vonMangoldt_logWeight_add_self_convolution` and
  `sum_moebius_log_square_eq_vonMangoldt_log_add_pair` retain the pair
  coefficient in exact arithmetic identities.
- [GaussianMellinVertical.lean](../RiemannGaussian/GaussianMellinVertical.lean):
  `integral_gaussianMellin_vertical` evaluates the full complex Gaussian
  Mellin integral while retaining its phase.

The scratch comments also record earlier finite-spectrum probes:
a precomputed 225-prime universe and all 25,200 distinct prime-pair
products showed improved localization only when the positive product
filter became extremely narrow. That experiment already knew every
prime pair, so it was not a blind factoring algorithm. A separate
4,000-semiprime phase-feature regression gave mean log-factor error
0.12538505 versus 0.12537949 for its prior alone. These are historical
scratch diagnostics, not newly rerun results.

## 2026-10-01: neighboring primes and factor correlation

Write the nearest surrounding primes as

$$
r_-=N-d_-,\qquad r_+=N+d_+,\qquad g=r_+-r_-=d_-+d_+.
$$

Their distances describe the local prime gap around the product. They
do not directly identify a divisor of the product.

Numerical protocol:

- Sample 36,000 distinct-prime semiprimes with both factors greater than
  100: 18,000 from each product band
  `[2^19,2^20)` and `[2^21,2^22)`.
- Seed: `20261001`. Predict `eta`.
- Control for product size using eight logarithmic bins in each band,
  and for residue class using `N mod 210`.
- Assign complete surrounding prime gaps to the same split using a
  deterministic hash of the lower neighboring prime. The split contained
  21,606 training, 7,201 validation and 7,193 test observations.
- Select ridge/shallow boosting models using validation only.
- Test gap sizes/asymmetry, neighboring Legendre symbols, their combinations,
  and features formed by division/multiplication with the neighbors.

The improvement statistic is
`100*(baseline_MSE-feature_MSE)/baseline_MSE`;
negative values mean slightly worse held-out prediction.

| Feature family | Test MSE improvement |
| --- | ---: |
| Neighboring-gap features | -0.0021% |
| Neighboring Legendre-symbol features | -0.0314% |
| Gap and character features together | -0.0361% |
| Direct ratio/operation features | -0.0731% |

A 6,500-input follow-up also searched for primes surrounding
`N*r_-` and `N*r_+`. The combined model improved test MSE by
-0.1728%, with approximate gap-clustered 95% interval
[-0.525%, +0.179%].

Decision: no useful extra predictive signal was established by these
feature families and models. This is a finite statistical result, not a
proof that every correlation is absent.

## 2026-10-01: successive multiplication and division

The cross operations have exact algebraic identities:

$$
Nr_-=(N-g)r_+ + d_+g,
\qquad
Nr_+=(N+g)r_- + d_-g.
$$

Consequently the remainders are respectively
`(d_+*g) mod r_+` and `(d_-*g) mod r_-`.
If these products are smaller than the corresponding moduli, and
`gcd(N,d_-)=gcd(N,d_+)=1`, their gcds with `N` reduce to
`gcd(N,g)`. The apparent factor information is then the prime-gap
width's common factor with `N`.

Example: `N=119=7*17` lies between 113 and 127. Its gap width is 14,
and `119*113 mod 127 = 112`, so `gcd(119,112)=7`.
This illustrates a genuine factor extraction, but the same factor is
already found by `gcd(119,14)`.

Across the 36,000 sampled semiprimes with factors greater than 100,
the cross-operation gcd tests and gap-width gcd tests found no
nontrivial factors.

A separate modular-power test tried each of `d_-` and `d_+` as a
base, with exponents `(N-1)//2` and `N-1`, and tested gcds of
the resulting residues minus one with `N`. On 6,500 inputs:

| Base selection | Inputs with a factor found |
| --- | ---: |
| The input's own neighboring gaps | 5.338% |
| Gap bases from matched size/residue controls | 5.163% |
| Fixed bases 4 and 6 | 5.385% |

Matched controls used eight peer draws per input. No special advantage
for neighboring-prime bases was established. These are finite success
rates under this trial budget, not end-to-end factoring complexity
benchmarks.

## 2026-10-01: blind zeta coefficient extraction

Let

$$
Z(s)=-\frac{\zeta'(s)}{\zeta(s)},\qquad
Z(s)^2=\sum_{n\ge1}M(n)n^{-s},\qquad M=\Lambda*\Lambda.
$$

For a distinct-prime semiprime,

$$
M(N)=2\log p\log q,\qquad
\eta=\sqrt{\frac{(\log N)^2}{4}-\frac{M(N)}2}.
$$

Thus a sufficiently accurate estimate of `M(N)` determines the factor
imbalance, with the smaller factor recovered by `sqrt(N)*exp(-eta)`.
This observable uses the full von Mangoldt series, including prime powers;
the semiprime coefficient itself has exactly the two ordered prime pairs.

The experiment evaluated actual numerical values of zeta and its derivative,
rather than constructing a prime-pair table:

$$
\widehat M_H(N)=
\frac{N^\sigma}{\sqrt{2\pi}H}
\int_{\mathbb R} Z(\sigma+it)^2
e^{it\log N}e^{-t^2/(2H^2)}\,dt.
$$

Its exact smoothed-series interpretation is

$$
\widehat M_H(N)=
\sum_{n\ge1}M(n)(N/n)^\sigma
e^{-H^2\log^2(N/n)/2}.
$$

### Numerical recipe and evidence limits

- `sigma=3`; working coefficient-error allowance `eps=0.0002`.
- Zeta and its derivative evaluated by analytically differentiated
  Euler–Maclaurin summation with 16 Bernoulli correction terms.
- At each 64-point block, the integer-series endpoint was
  `max(32,ceil(max(t)/2))`. No factor labels or primality information
  were used in these integer sums.
- Positive frequencies were computed explicitly and negative frequencies
  supplied by conjugate symmetry.
- One thread: `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`.
- Environment: the existing `../.venv/bin/python`, NumPy 2.2.6,
  SymPy 1.14.0, mpmath 1.3.0.
- Point evaluations were compared with mpmath at 40 decimal digits at
  `t=0,0.125,10,100,1000,10000`. Observed absolute discrepancies were
  at most approximately `7.2e-14` for zeta and `5.4e-14` for its
  derivative at those points.
- Analytic leakage, quadrature-aliasing, truncation and Euler–Maclaurin
  bounds were used to select parameters. They do not bound all IEEE
  floating-point roundoff, so the resulting factor intervals are
  experimental rather than formally certified.
- Each recovered integer factor was subsequently verified by exact
  divisibility. Independent factorization labels were introduced only
  after zeta extraction and timing.

For reproducing the conservative Gaussian grid, let
`e=eps/8`, `a=3/2`, and use

$$
H=\frac{\sqrt{2\log(4N^3/e)}}{\log(1+1/N)},
$$

$$
h=\frac{2\pi a}{
\log\!\left(1+
\frac{(36N^{3-a}+4N^{3+a})e^{a^2/(2H^2)}}{e}
\right)},
$$

$$
T=h\left\lceil
\frac{H\sqrt{2\log(4N^3/e)}}h
\right\rceil.
$$

Here `h` is frequency-grid spacing and `T` is its upper endpoint.
These are this prototype's conservative parameter choices, not universal
requirements for every coefficient-extraction algorithm.

### Measured extraction results and fresh-factor baselines

| N | Factors recovered | Zeta time | Positive grid nodes | Fresh-factor SymPy time | GNU factor time |
| --- | --- | ---: | ---: | ---: | ---: |
| 35 | 5 × 7 | 0.095302 s | 4,776 | 4.679 µs | 0.980 ms |
| 77 | 7 × 11 | 0.563619 s | 12,972 | 4.819 µs | 0.967 ms |
| 143 | 11 × 13 | 2.252019 s | 28,081 | 5.238 µs | 0.848 ms |
| 323 | 17 × 19 | 13.367284 s | 76,441 | 5.657 µs | 1.231 ms |

SymPy timings are medians of 31 calls with
`sympy.ntheory.factor_.factor_cache.cache_clear()` before each timed call.
Earlier repeated-call timings used a populated factor cache and were
superseded by these measurements. Library imports remain warm.

GNU timings are medians of seven fresh `factor` subprocesses and include
process startup. The installed coreutils version was 8.32.

Zeta timings exclude imports, Bernoulli-coefficient preparation and the
post-hoc independent factorization check. They include extraction and a
six-width diagnostic scan sharing the same zeta evaluations. Fresh
imports of NumPy/SymPy/mpmath took about 0.223 s, and preparation of the
16 Bernoulli coefficients took about 0.0053 s. This is an exploratory
prototype comparison, not an optimized implementation shootout.

| N | Observed absolute coefficient error | Experimental smaller-factor interval |
| --- | ---: | --- |
| 35 | 3.11e-10 | [4.99852, 5.00149] |
| 77 | 6.84e-12 | [6.99845, 7.00155] |
| 143 | 6.92e-11 | [10.99344, 11.00661] |
| 323 | 1.74e-9 | [16.98484, 17.01542] |

Every interval contained exactly one integer, the correct smaller factor.

A width scan used `H/N` equal to
`0.125,0.25,0.5,1,2,4`. Broader, cheaper filters mixed in neighboring
coefficients; several estimates even made the reconstruction's square-root
radicand negative. At `H/N=4`, the estimate for `N=323` gave a smaller
factor near 17.0406, but without the selected conservative error allowance.
The final conservative widths had `H/N` between approximately 6.83 and
7.67.

### Larger conventional baselines and scaling forecast

Deterministic seed `20261001` supplied balanced, non-close prime factors
for four larger input examples. These are a handful of examples, not a
representative distribution benchmark.

| Input N | Bits | SymPy fresh-factor median | Projected zeta grid nodes |
| --- | ---: | ---: | ---: |
| 16,363,499 | 24 | 0.206 ms | 1.86e10 |
| 5,141,575,211 | 33 | 0.769 ms | 9.71e12 |
| 789,103,629,247 | 40 | 0.792 ms | 2.13e15 |
| 208,812,600,117,463 | 48 | 0.794 ms | 7.88e17 |

The node counts are forecasts from the same parameter rule, not measured
zeta runs or lower bounds on all possible zeta methods.

SymPy's self-initializing quadratic sieve, using `prime_bound=1000` and
`M=5000`, factored the 40-bit example in 0.0919 s and the 48-bit example
in 0.0785 s. The returned factors were verified. GNFS and ECM were not
benchmarked here.

Decision: the tested zeta extractor has no speed advantage, even over
basic conventional methods on tiny inputs. For a positive Gaussian
isolating individual integers, the log separation near `N` is about
`1/N`; this implementation therefore uses frequency width on the scale
of `N`, with logarithmic accuracy costs. Its straightforward
Euler–Maclaurin evaluation adds substantial further work. The scratch
Gaussian theorem audits this filter class, not all signed or arithmetic
factor-localization methods.

## 2026-10-01: first extractor optimization

This version preserves the same coefficient observable and the working
error allowance `eps=0.0002`. It changes parameter selection and the
numerical evaluator; it supplies no new Lean theorem.

### Sharper leakage estimate

For `n>=1`, the elementary divisor identity gives

$$
0\le M(n)=\sum_{d\mid n}\Lambda(d)\Lambda(n/d)
\le \log n\sum_{d\mid n}\Lambda(d)=(\log n)^2.
$$

Let `B(sigma)=1+1/(sigma-1)^2`. Bounding the unimodal function
`log(x)*x^(-sigma)` by its integral plus its maximum gives
`|Z(sigma+it)|<=B(sigma)` for `sigma>1`.
For the 24 nearest integer offsets on each side of `N`, bound each
coefficient individually. Only the more distant tail receives the
whole-series bound. The resulting leakage bound is

$$
E_D(N,H)\le
\sum_{\substack{0<|d|\le D\\N+d\ge2}}
(\log(N+d))^2\left(\frac{N}{N+d}\right)^\sigma
e^{-H^2\log^2((N+d)/N)/2}
+N^\sigma B(\sigma)^2
e^{-H^2\log^2(1+(D+1)/N)/2}.
$$

Here `D=24`; no neighboring coefficient is factored or supplied as an
oracle. Choose `H` by solving for the bound to equal `eps/8`. At
`N=323,sigma=3`, this reduces `H/N` from approximately 7.669 to 5.440.
Selecting the analytic quadrature strip from four candidate widths also
reduces the frequency count from 76,441 to 45,022.

### Faster finite zeta evaluation

Use 20 Euler–Maclaurin corrections and select the integer-series endpoint
for each block by its explicit analytic remainder bound, rather than
setting it to half the frequency. At the largest frequency for `N=323`,
the new endpoint is 3,010 instead of roughly 9,484 in the first prototype.

For consecutive frequencies, reuse the exact identity

$$
e^{-i(t+h)\log n}=e^{-it\log n}e^{-ih\log n}.
$$

Evaluate blocks of 128 samples by multiplicative phase recurrence,
reinitializing the phase at each block. This replaces most complex
exponential evaluations by complex multiplications. An identical-grid
ablation at `N=323` took 2.539 s with direct exponentials and 0.731 s
with recurrence. These are individual measured runs, not universal
speed ratios.

### First optimized run

| N | Original zeta time | Optimized zeta time | Approximate improvement |
| --- | ---: | ---: | ---: |
| 35 | 0.095302 s | 0.016275 s | 5.9× |
| 77 | 0.563619 s | 0.052467 s | 10.7× |
| 143 | 2.252019 s | 0.157133 s | 14.3× |
| 323 | 13.367284 s | 1.126942 s | 11.9× |

All four factors were recovered from single-integer experimental
intervals and checked by exact division. Observed coefficient errors
were between about `5.9e-7` and `4.7e-6`, below the working allowance.
The narrower filter intentionally uses more of the error allowance than
the original over-precise run.

The same method recovered `899=29*31` in 7.881 s. A later run took
6.676 s; runtime depends on system load. It also recovered independent
test inputs `221=13*17`, `437=19*23`, `667=23*29` and `1147=31*37`
using `sigma=2`. Lowering `sigma` reduces numerical amplification but
requires more quadrature nodes, so it did not improve runtime on these
small inputs. The `sigma=2` run recovered `2021=43*47` in 48.531 s.
A first `sigma=3` run on that input stopped at a 30-second execution
cap before completing its grid; that is an execution limit, not a
failed factor estimate.

Independent 40-digit checks of the optimized evaluator covered
`sigma=2,3`, four frequencies near each of `0,10,100,1000,10000`.
Maximum observed discrepancies were approximately `3.4e-13` for zeta
and `3.7e-13` for its derivative. Analytic approximation bounds still
do not certify floating-point roundoff.

Decision: meaningful implementation improvement, but the repeated
finite-series evaluations still scale poorly. The next test is to
evaluate the entire equally spaced frequency grid together, using
FFT gridding plus a controlled Taylor correction for the nonuniform
frequencies `h*log(n)`. No prime-pair table is needed for this test.

## 2026-10-01: FFT evaluation of the whole frequency grid

The next version replaces repeated finite zeta sums by a batched
nonuniform Fourier evaluation. It keeps the sharper leakage estimate,
the coefficient error allowance `eps=0.0002`, and analytically
differentiated Euler–Maclaurin corrections. Its test contour is
`sigma=2`, which limits numerical amplification by `N^sigma`.

### Exact expansion behind the acceleration

For a fixed finite integer endpoint `m`, both the finite zeta sum and
its derivative have the form

$$
S_j=\sum_{1\le n<m}a_n e^{-ijh\log n},\qquad 0\le j<K.
$$

Use `a_n=n^(-sigma)` for zeta and `a_n=-log(n)*n^(-sigma)` for its
derivative. The coefficients are real. No prime-factor table occurs.

Choose an FFT length `L>=2K`, round `h*log(n)` to the nearest grid angle,
and set

$$
b_n=\operatorname{round}\!\left(\frac{Lh\log n}{2\pi}\right),
\qquad
\delta_n=h\log n-\frac{2\pi b_n}{L}.
$$

For each Taylor order, bin the real coefficients as

$$
C_r[b]=\sum_{b_n\equiv b\pmod L}
a_n\frac{(K\delta_n)^r}{r!}.
$$

The exponential expansion then gives

$$
S_j=\sum_{r=0}^{P}
\left(-i\frac jK\right)^r\operatorname{FFT}_L(C_r)[j]+E_j.
$$

Since `|delta_n|<=pi/L` and `j<K`, every Taylor argument has magnitude
at most `pi/2`. In exact arithmetic,

$$
|E_j|\le
e^{\pi/2}\frac{(\pi/2)^{P+1}}{(P+1)!}\sum_{n<m}|a_n|.
$$

At `P=24`, the scalar tail factor is approximately `2.481e-20`.
This bounds Taylor truncation only; frequency rounding and FFT
floating-point errors are separate. No formal certification of those
errors is claimed.

The implementation uses `scipy.fft.next_fast_len(2*K, real=True)` and
single-worker `scipy.fft.rfft`. Because every `C_r` is real and
`j<K<=L/2`, the real FFT contains all required output frequencies.
The finite-series endpoint is chosen once for the largest frequency,
and the ordinary Euler–Maclaurin tail and derivative are then added
at every sample.

The batched finite-sum work is roughly `O(P*(m+K*log K))`, instead
of `O(m*K)` individual finite-series work. Euler–Maclaurin corrections
add linear work in the sample count for fixed correction order.
This is an improvement in evaluation cost; the coefficient isolation
still requires a large frequency grid.

### Results

| N | Recovered factors | FFT extractor time | Observed coefficient error magnitude |
| --- | --- | ---: | ---: |
| 35 | 5 × 7 | 0.02251 s | 4.58e-6 |
| 77 | 7 × 11 | 0.01466 s | 2.28e-6 |
| 143 | 11 × 13 | 0.03167 s | 3.58e-6 |
| 221 | 13 × 17 | 0.06293 s | 2.53e-10 |
| 323 | 17 × 19 | 0.12689 s | 5.93e-7 |
| 437 | 19 × 23 | 0.22613 s | 2.13e-6 |
| 667 | 23 × 29 | 0.41275 s | 2.14e-6 |
| 899 | 29 × 31 | 0.65844 s | 2.25e-6 |
| 1147 | 31 × 37 | 0.88028 s | 2.45e-10 |
| 2021 | 43 × 47 | 1.69671 s | 3.92e-10 |

All ten experimental intervals contained exactly one integer, and
exact division verified the factor. Factorization labels were introduced
only after extraction and timing. The first FFT run at `N=35` includes
first-call FFT overhead; the results show that FFT is not always the
fastest evaluator on the smallest grids.

Three-repeat timings for the larger examples were:

| N | FFT times, seconds | Median | Fresh-factor SymPy median |
| --- | --- | ---: | ---: |
| 323 | 0.10455, 0.10315, 0.10223 | 0.10315 s | 5.727 µs |
| 899 | 0.52977, 0.53107, 0.53549 | 0.53107 s | 6.635 µs |
| 2021 | 1.70454, 1.70931, 1.71134 | 1.70931 s | 7.682 µs |

The `N=323` median is about 130× faster than the original 13.367 s
prototype. The `N=2021` median is about 28× faster than the previous
48.531 s recurrence run on the same `sigma=2` quadrature grid. Library
imports, Bernoulli-coefficient preparation and independent reference
factorization are excluded from the extractor times. The SymPy timing
used 31 calls with its factor cache cleared before each timed call.

Independent 40-digit comparisons at nine points each on the `N=323`
and `N=2021` grids observed discrepancies of at most approximately
`1.8e-12` for zeta and `2.7e-12` for its derivative. The larger grid
extends to frequency approximately 82,598. These sampled checks and
the small observed coefficient errors are numerical evidence, not
interval-arithmetic or Lean certification.

### Interpretation and remaining obstruction

The improvement is real, but conventional factoring still wins by
roughly four to five orders of magnitude on these tiny inputs. The
FFT accelerates access to the same observable; it does not remove
the product-resolution problem. In particular, `N=2021` still uses
484,433 frequency samples despite having only 11 input bits.

The next mathematical improvement would need to reduce coefficient
isolation cost or extract factor-sensitive information without isolating
the coefficient. Possible computational follow-ups are a cheaper signed
filter, adaptive measurement precision with a bounded candidate budget,
and reuse of a common spectral grid across many inputs. These are
untested options, not achieved speedups. Any batch comparison must
include preprocessing and compare against batch arithmetic/sieving
methods, rather than only isolated calls to a factorization library.

## 2026-10-01: scaling audit

Question: could the zeta extractor lose on small semiprimes but eventually
win on huge ones? That is a valid criterion for a new algorithm, but the
current extractor has unfavorable asymptotic scaling.

Let `b=ceil(log2(N))`. Resolving nearby product coefficients requires
separating logarithms whose spacing is about `1/N`. The current positive
Gaussian therefore uses `H` proportional to `N`, with accuracy factors.
Its truncation endpoint is `T=H*sqrt(2*log(N^sigma*B(sigma)^2/e))`, and
the analyticity-based grid spacing decreases on a `1/log(N)` scale.
The grid count `K=ceil(T/h)+1` thus grows at least on the scale of `N`,
with additional logarithmic factors.

In particular, even an idealized evaluator costing roughly one operation
per sample would require exponentially many operations in `b`, since
`N` is approximately `2^b`. FFT batching improves the finite-sum evaluation
to `O(P*(m+K*log K))`; it does not reduce `K`.

This is an audit of this implementation and its parameter strategy,
not a lower bound on every possible zeta-based factoring method.

### Comparison with established methods

For generic balanced semiprimes, suppressing polynomial costs of
big-integer arithmetic, the usual scaling comparison is:

| Method | Growth with input bit length b |
| --- | --- |
| Current zeta extractor's sample processing | At least on the `2^b` scale, with additional costs |
| Trial division | Approximately `2^(b/2)` candidate divisions |
| Pollard rho | Heuristic expected `2^(b/4)` modular-operation scale |
| Quadratic sieve | Heuristic `exp(O(sqrt(b*log b)))` |
| General number field sieve | Heuristic `exp(O(b^(1/3)*(log b)^(2/3)))` |

Pollard rho's `O(sqrt(p))` scale comes from its collision model; for a
balanced semiprime the smaller prime is on the `sqrt(N)` scale.
See [Pollard's original paper](https://pages.cs.wisc.edu/~cs812-1/pollardrho.pdf).
The sieve estimates are heuristic subexponential bounds, not certified
runtime limits for every input; see
[Pomerance, A Tale of Two Sieves](https://math.dartmouth.edu/~carlp/PDF/paper109.pdf).
These comparisons do not use quantum algorithms.

Adding ten input bits multiplies the current grid's leading `N`
dependence by approximately 1,024, before logarithmic costs. The
corresponding leading factor for Pollard rho is approximately 5.66.
The sieve algorithms have slower asymptotic growth still.

### Parameter-only projections

Evaluate the improved leakage/grid formulas at magnitude `N` near
`2^b`, `sigma=2`, `D=24`, and the original fixed `eps=0.0002`.
The evaluation uses logarithmic arithmetic and mpmath to avoid overflow
and the loss of `N+1` in floating-point calculations. No large zeta
grid is allocated and no large semiprime is factored in this forecast.

| Product magnitude | Projected frequency samples |
| --- | ---: |
| Near 16 bits | 2.35e7 |
| Near 24 bits | 9.74e9 |
| Near 32 bits | 3.60e12 |
| Near 64 bits | 3.97e22 |
| Near 128 bits | 2.00e42 |

These are predictions for the chosen parameter rule, not measured
runtime or universal requirements for coefficient extraction.

### Accuracy adds further costs

Holding the coefficient tolerance fixed does not maintain a fixed-width
factor interval as `N` grows. For the continuous reconstruction formula,

$$
M=2\log p\log(N/p),\qquad
\frac{dM}{dp}=\frac{4\eta}{p}.
$$

Consequently the local factor sensitivity is `dp/dM=p/(4*eta)`.
When the imbalance `eta` stays a fixed positive constant and `p` is on
the `sqrt(N)` scale, a constant-width factor interval needs coefficient
error on the `N^(-1/2)` scale. Very close factors can require finer
accuracy. This is a sensitivity calculation, not a replacement for the
scratch theorem's explicit interval/error hypotheses.

As an illustrative calibration, setting `eps=1/(4*sqrt(N))` instead
predicts approximately `4.34e12` grid samples near 32 bits and
`6.33e22` near 64 bits. That calibration is not a universal certificate
for every possible factor imbalance.

The current double-precision implementation and fixed Taylor degree
24 cannot simply be used at those large sizes. The analytic Taylor
error is amplified by `N^sigma`; the degree and arithmetic precision
must grow to keep the extraction allowance. A fixed 20-term
Euler–Maclaurin choice also gives extra growth in the integer-series
endpoint. Therefore the grid forecasts already omit further costs
needed for a reliable large-input implementation.

Decision: the 130× small-input improvement is useful computationally,
but it does not create an eventual advantage over conventional
factorization. The next competitive mechanism needs to change the
dependence on product magnitude, through a different observable,
a substantially different isolation strategy, or an arithmetic
localization identity. Further FFT tuning alone leaves the dominant
scaling obstruction intact.

## 2026-10-01: repository audit for a different scaling mechanism

This audit inspected local Lean source; it did not recompile the declarations
or alter the main RH campaign. The specializations and numerical mask test
below are side-investigation deductions, not newly checked Lean theorems.
The search covered the finite divisibility/Fourier, prime-count, coprime
Euler, factorial-filter, prime-colour, semiprime Riesz and convolution files.

### Factor-sensitive identities worth retaining

1. **Exact semiprime cutoff profile.**
   `riesz_semiprime_eq_tent` in
   [ZetaRieszSemiprimePrefixDecay.lean](../RiemannGaussian/ZetaRieszSemiprimePrefixDecay.lean)
   keeps the complete two-prime tent. For distinct `p<q`, its specialization is

   $$
   \mathcal R_L(pq)=L_+-(L-\log p)_+-(L-\log q)_+
     +(L-\log N)_+.
   $$

   In particular, at `L=log(N)/2` the response is exactly `log(p)`, as
   already stated in the scratch theorem. Its breakpoints also identify
   both factors. The missing algorithm is an evaluator from `N,L` that
   avoids enumerating unknown divisors; the tent identity itself does not
   supply one.

2. **Finite coprime Euler factor contains the factor sum.**
   `CoprimeEulerPhase.coprimeEuler_eq_product` in
   [ZetaCoprimeEulerPhase.lean](../RiemannGaussian/ZetaCoprimeEulerPhase.lean)
   gives, for this squarefree semiprime,

   $$
   E_N(s)=\sum_{d\mid N}\mu(d)d^{-s}
     =(1-p^{-s})(1-q^{-s}).
   $$

   Specializing the finite expression at `s=-1` gives
   `E_N(-1)=N+1-(p+q)=(p-1)(q-1)`. Knowing this integer would determine
   `p+q`, hence the roots of `X^2-(p+q)X+N`. This is an exact alternative
   to measuring a log-product coefficient, but `zetaCoprimeEulerFactor`
   is defined through `N.divisors`. Evaluating that definition is not a
   blind fast algorithm. Its convergent infinite-series representation
   is only established for `Re(s)>1`; it must not be evaluated at `-1`
   by an unsupported series continuation.

3. **Opposite phases retain the split; ordinary multiplicative phase does not.**
   The scratch `pairSpectrum_semiprime` is `2*cos(2*t*eta)`.
   `total_phase_product` instead gives only `exp(i*t*log(N))`.
   The latter is already known from the input. The exact pair moment and
   Suzuki convolution identities preserve genuinely factor-sensitive
   coefficients, but the existing coefficient-isolation cost remains.

4. **Newton identities remove repeated-prime contamination.**
   `PrimeNewtonThree.newton_two` in
   [PrimeNewtonThree.lean](../RiemannGaussian/PrimeNewtonThree.lean) proves
   `2*pairPrefix = (sum f)^2 - sum(f^2)` for a finite prime universe.
   This is a precise signed diagonal deletion. It can clean a prime-pair
   observable without approximating the diagonal, but it does not select
   the unknown product's coefficient or bound its evaluation cost.

### Masks with an evaluator from the input alone

`sum_divisors_moebius_dvd_eq_coprime` in
[EtaMoebiusCoprimeProduct.lean](../RiemannGaussian/EtaMoebiusCoprimeProduct.lean)
identifies the whole signed common-divisor sum with `1[gcd(N,a)=1]`.
The right side is directly computable without factoring `N`. This is
an important computational distinction from a generic divisor sum.

The finite union and prime-pattern identities in
[FiniteDivisibilitySieve.lean](../RiemannGaussian/FiniteDivisibilitySieve.lean)
and [FinitePrimePatternSieve.lean](../RiemannGaussian/FinitePrimePatternSieve.lean)
retain signed overlaps exactly. They motivate testing a block of candidate
integers using `gcd(N, product(block) mod N)`, followed by subdividing a
successful block. This is a batched arithmetic search, not a new zeta
oracle. Product construction, collisions where both factors are present,
and the full candidate-range cost must all be counted. No new asymptotic
factoring bound follows from these source identities.

For example, before reaching the smaller factor, every positive candidate
`a<p` has `gcd(N,a)=1`. An unweighted initial coprimality scan therefore
has no early factor signal. Batching can change evaluation cost, not this
exact arithmetic fact.

### Exact Fourier residue masks: numerical cost audit

`sum_range_finiteCircleWave` and
`sum_range_finiteCircleWave_mul_conj` in
[FiniteCircleFourier.lean](../RiemannGaussian/FiniteCircleFourier.lean)
provide the orthogonality needed for an exact product-index mask:

$$
\frac1Q\sum_{a=0}^{Q-1}
   e^{2\pi i a(n-N)/Q}=\mathbf 1_{n\equiv N\pmod Q}.
$$

Applying this to the Gaussian extractor leaves aliases at `N+d*Q`,
rather than every neighboring integer. We tested the resulting *analytic
leakage envelope*, without factoring or building a prime-pair table:
`N=2021`, `sigma=2`, `D=24`, leakage budget `0.0002/8`.
For each modulus, solve `E_Q(H)=budget`, where

$$
\begin{aligned}
E_Q(H)={}&\sum_{0<|d|\le D,\,N+dQ\ge2}
  \log^2(N+dQ)\left(\frac N{N+dQ}\right)^\sigma
  e^{-H^2\log^2((N+dQ)/N)/2}\\
&+N^\sigma B(\sigma)^2
  e^{-H^2\log^2(1+(D+1)Q/N)/2}.
\end{aligned}
$$

The far term deliberately bounds the remaining mass by the same
unmasked absolute-series bound used earlier. This is a floating parameter
calculation, not an interval-certified implementation of masked L-series.

| Modulus `Q` | Required `H` | Bandwidth reduction | `Q*H` / unmasked `H` |
| ---: | ---: | ---: | ---: |
| 1 | 11197.537166 | 1.000000 | 1.000000 |
| 7 | 1599.696790 | 6.999787 | 1.000030 |
| 31 | 361.429361 | 30.981260 | 1.000605 |
| 127 | 88.998094 | 125.817719 | 1.009397 |
| 509 | 23.778766 | 470.904894 | 1.080898 |

The numerical finite-circle selector agreed with its exact integer mask
to residuals below `4.5e-14` for `Q=7,31,127`.

Decision: congruence filtering genuinely improves isolation, but a direct
`Q`-channel evaluation gives essentially the same channel-times-bandwidth
cost. `Q*H` is a diagnostic work proxy, not measured runtime or a lower
bound for all implementations. A useful speedup would require a shared
evaluation of the masked series that saves the channel cost as well.
The additive twist acts on the product index `n`; it is not obtained just
by changing the vertical ordinate in an ordinary zeta evaluation.

### Relevant exclusions and next computational target

- The prime-count Euler series has coefficient `mu(N)*z^omega(N)=z^2`
  for a distinct-prime semiprime. Count information alone is already known.
- `zetaPrimeDivisorCoefficient_eq` and `squarefree_log_eq_prime_sum`
  reduce the complete sum of distinct-prime logarithms to `log(N)`.
  That common colour weight does not distinguish the split.
- Independent fourth-root colour averaging in
  [Zeta23FourthMomentPhaseColour.lean](../RiemannGaussian/External/Zeta23FourthMomentPhaseColour.lean)
  removes unbalanced labelled monomials, but requires the labelled finite
  family and does not supply the missing factors or a cheap product mask.
- The exposed-zero prime filters require a specified hypothetical zero
  and exposure hypotheses. They are spectral tools for the RH campaign,
  not unconditional factor-location estimators for an input semiprime.
- `eventually_zetaFactorialLocalAmplitude_near_one` in
  [ZetaFactorialFilterLocalization.lean](../RiemannGaussian/ZetaFactorialFilterLocalization.lean)
  shows that a fixed normalized filter remains near one on its affine
  logarithmic window. It is not a universal obstruction to all moving
  filters, but rules out attributing sharp localization to that fixed
  normalization alone.
- `sum_pairedEtaInverseOuterDivisible_mul_eq` exactly isolates `f(q)`
  from a finite inverse hyperbola when `q` is supplied. It does not find
  an unknown factor; evaluating its signed hyperbolic sum still has a cost.

The most immediately executable avenue is input-only batched divisibility
and interval localization. For a specifically zeta-based improvement,
the focused open task is shared evaluation of a signed residue-masked,
opposite-phase pair observable. It must demonstrate an end-to-end saving
in channel count and coefficient isolation, not just a narrower kernel.
None of the inspected theorems yet supplies that algorithm.

## 2026-10-01: prime anchors and a cheap rough-prime Euler filter

The user correctly emphasized that the available preprocessing includes
the nearest surrounding primes. These supply a logarithmic bracket and
exact arithmetic calibration values, even though they are computable
from the input rather than independent external data.

For `N=2021`, the nearest primes are `r_-=2017` and `r_+=2027`, at
distances 4 and 6. In the Dirichlet-series coordinate this gives

$$
\log(2017)<\log(2021)<\log(2027).
$$

For the full von Mangoldt coefficient the endpoint values are
`Lambda(r_±)=log(r_±)`. For our pair coefficient `M=Lambda*Lambda`,
both endpoint values are exactly zero. An interior composite can still
have nonzero `M`; a prime gap is not a gap in the pair spectrum.

### Exact filtering with known small primes

Choose a *known* small-prime set `S_B={ell prime: ell<=B}` and put
`P_B=product(S_B)`. First compute `gcd(N,P_B)`. A nontrivial gcd already
finds a divisor; if it equals 1, the target pair coefficient is preserved.
Use the single modified zeta response

$$
Z_B(s)=Z(s)-\sum_{\ell\in S_B}\frac{\log\ell}{\ell^s-1}
      =-\frac{d}{ds}\log\left(\zeta(s)
                 \prod_{\ell\in S_B}(1-\ell^{-s})\right).
$$

On `Re(s)>1`, its coefficients are exactly the von Mangoldt coefficients
with the selected prime powers removed. Squaring gives

$$
Z_B(s)^2=\sum_{n\ge1}M_B(n)n^{-s},\qquad
M_B(n)=M(n)\mathbf 1_{\gcd(n,P_B)=1}.
$$

This follows because a nonzero von Mangoldt leg is a prime power, and
coprimality of a product with `P_B` is equivalent to coprimality of both
legs. It is an exact derived identity; it has not been added as a new
Lean theorem in this side investigation. The finite coprime Euler and
convolution files supply the underlying identities.

This differs computationally from a direct `Q`-channel residue selector:
there is one zeta/derivative evaluation per frequency, with a finite
explicit correction for the selected primes. No unknown divisor of `N`
enters that correction.

For `B=7`, exclude the known primes `2,3,5,7`. Only 2021 survives these
coprimality tests among the composite integers strictly between 2017 and
2027. The nearest other integers that *could* have nonzero filtered pair
coefficient are 1991 and 2033. A survivor is not asserted to have nonzero
pair coefficient; using its `log^2(n)` bound is conservative.

### Parameter and extractor tests

Use `sigma=2`, `eps=0.0002`, and scan offsets `|d|<=128` around the
target. Delete an alias from the near leakage bound if it has a selected
small prime factor (by gcd) or is itself prime. Keep the same unfiltered
absolute-series bound for the entire far tail. The algorithm counts the
small-prime generation, neighboring-prime search, local gcd/primality
checks, parameter selection and extraction in its timing. Imports and
the already-prepared Bernoulli coefficients are excluded consistently
with the earlier FFT comparison.

For 2021, the bandwidth calculations gave:

| Known small-prime cutoff | Number of selected primes | Required `H` | Reduction from unmasked `H` |
| ---: | ---: | ---: | ---: |
| None | 0 | 11197.537166 | 1.000000 |
| 2 | 1 | 5598.779222 | 1.999996 |
| 7 | 4 | 914.197989 | 12.248482 |
| 19 | 8 | 423.217719 | 26.458101 |

With no Euler deletion, removing the known prime aliases alone did not
change the bandwidth materially in this example: the adjacent composite
aliases still controlled the bound. The strong gain is from the known
small-prime filter and local support checks together; it must not be
attributed to the two prime endpoints alone.

We then ran the actual zeta/derivative FFT extractor, replacing `Z^2`
by `Z_B^2`. This was not a prime-pair coefficient-table evaluation.
The following are three-run medians in the same comparison process,
using `B=7` for all three inputs:

| N | Surrounding primes | Unfiltered FFT | Filtered FFT | Speedup | Exact division result |
| ---: | --- | ---: | ---: | ---: | --- |
| 323 | 317, 331 | 0.124627 s | 0.019693 s | 6.33× | 17 × 19 |
| 899 | 887, 907 | 0.641987 s | 0.231736 s | 2.77× | 29 × 31 |
| 2021 | 2017, 2027 | 1.661500 s | 0.065348 s | 25.43× | 43 × 47 |

All runs produced a single-integer smaller-factor interval and verified
it by exact division. Observed coefficient errors were approximately
`1.19e-5` to `1.22e-5`, within the working `0.0002` allowance. Independent
factorization labels were not used in the filter, parameter selection,
zeta evaluation or candidate recovery.

A single additional `B=19` run at 2021 took `0.026232 s`, used 18,311
frequency nodes and an Euler–Maclaurin integer endpoint of 870, and
recovered 43 and 47. Four independent 40-digit mpmath checks of the
filtered logarithmic derivative had discrepancies at most `8.8e-14`.
This last timing is a single run, not a median.

These are floating numerical experiments with exact final divisibility
verification. There is still no interval bound for all accumulated
floating-point error and no new Lean-certified numerical extractor.
The test scripts ran in memory, as in the earlier experiments.

Decision: preprocessing supplies useful exact coefficient zeros and a
substantial practical improvement on these small inputs. The earlier
negative gap-feature regression did not test this filtering mechanism.
There is still no demonstrated asymptotic factoring advantage: with a
fixed small-prime cutoff and a fixed 128-offset support scan, the far-tail
parameter retains bandwidth proportional to the product magnitude up
to logarithmic factors. Scaling the cutoff or scan must account for the
cost of finding and applying every additional zero.

## 2026-10-01: modular factor-sum signal and stronger residue colours

### Exact signal, decoder and scaling

For distinct primes `N=p*q`, write `S=p+q`. Euler's theorem and
`phi(N)=N+1-S` give

$$
\boxed{a^{N+1}\equiv a^S\pmod N,\qquad \gcd(a,N)=1.}
$$

This is a modular encoding, not an ordinary complex phase readable by an
argument operation. Acquisition needs one modular exponentiation; repeated
squaring costs `O(b*M(b))` bit operations for `b=bit_length(N)`.
It requires no zeta coefficient extraction, factor-pair table, neighbouring
factorisation or Fourier grid.

Under the public promise `p<=q<=R*p`,

$$
2\sqrt N\le S\le(R+1)\sqrt{N/R}.
$$

For `R=2`, the exact integer endpoints are `L=ceil(sqrt(4N))` and
`U=floor(sqrt(9N/2))`. Compute `h=2^(N+1-L) mod N` and decode
`h=2^(S-L) mod N` inside this interval. Known small prime divisors and
perfect squares are checked first.

Every collision candidate must have square discriminant `S^2-4N`, correct
parity, and a proper divisor verified by exact division. Duplicate modular
values retain ALL associated exponents. The saved regression exercises
`N=2047`, where base 2 has order 11, and rejects a false collision before
recovering `23*89`.

Since the interval width is approximately `(3/sqrt(2)-2)*sqrt(N)`, the
usual baby-step/giant-step search-size heuristic is `O(N^(1/4))`, or
`O(2^(b/4))`. It is not an unconditional runtime theorem for this
implementation: small multiplicative order can create extra candidates.
No input-bit-length `O(b log b)` factorisation has been obtained.

### Cheap colour and prime-power correlations

For a known small modulus `m` coprime to `N`, every valid factor sum lies in

$$
A_m(N)=\{t+Nt^{-1}\bmod m:\ t\in(\mathbb Z/m\mathbb Z)^\times\}.
$$

At odd prime moduli this is equivalent to requiring the discriminant to
be a quadratic residue. The decoder joins permitted residues by CRT
directly; it does not scan the full product wheel. Each giant stride is
a multiple of that wheel. Precomputed modular jumps visit only permitted
baby exponents.

With permitted density `rho` and stride `m`, approximate work is
`rho*m+(U-L)/m`, minimized near `m=sqrt((U-L)/rho)`. This improves
constants and memory, not the `N^(1/4)` exponent. Adaptive decoding first
searches a smaller interval and reuses the baby table as the stride grows.
The actual factor sum and factor ratio never enter the policy.

Prime-power lifts preserve additional exact correlations:

- If `N=1 mod 3`, both factors have the same residue modulo 3. Hence
  `p-q` is divisible by 3 and the discriminant vanishes modulo 9.
  At `N=3337` the modulo-3 mask admits six lifts modulo 9, while the
  exact mask admits only `{1,8}`.
- If `N=1 mod 4`, moving from modulus 8 to 16 halves the unit
  factor-sum mask's density. At `N=2021`, the four lifts admitted by
  the modulo-8 mask reduce to `{6,10}` modulo 16.
- Stationary-residue lifts modulo 25 are used when `N` is a quadratic
  residue modulo 5.

The frozen input-only policy uses 8 or 16, 3 or 9, 5 or 25, and selected
primes 7, 11, 13 and 17. Larger wheels are used only at larger bit lengths.
Every input's wheel construction is included in its timing.

### Benchmark progression

The initial decoder recovered all 210 generated semiprimes through
63–64 input bits. A sparse CRT decoder recovered all 120 subsequent
fresh cases; at 63–64 bits its median was 1.10 ms versus 5.63 ms without
colours. Comparing to a stronger native baseline then erased the apparent
large advantage over Python Pollard–Brent: GNU `factor` was approximately
level with the fixed-wheel decoder at 64–80 nominal bits and faster at 88.

Adaptive interval growth and prime-power masks produced the following
in-memory result on a fresh corpus, with seed `2026100900+nominalBits`.
Settings were frozen before the sample. Times are median three-run
batch-average milliseconds per input, with method order shuffled
deterministically:

| Actual input bits | Inputs | Prime-power prototype | GNU `factor` 8.32 |
| ---: | ---: | ---: | ---: |
| 63–64 | 48 | 0.50196 ms | 0.97367 ms |
| 79–80 | 32 | 5.35771 ms | 21.11880 ms |
| 87–88 | 20 | 12.08723 ms | 99.13121 ms |
| 95–96 | 8 | 54.58630 ms | 442.08379 ms |

All 108 factors passed exact checks. Imports, prime generation and
reference labels were outside the timing regions. Decoders received only
`N`, the public `q/p<=2` promise and public settings. Native timing includes
one process startup and captured output per batch. GNU performs general
factorisation; this decoder uses the balance promise.

The saved implementation has structured counters and an explicit resource
cap. Its fresh replay of the same seeded corpus is recorded in
[semiprime-modular-signal-audit.json](semiprime-modular-signal-audit.json),
including every input/reference pair, decoder statistics, all timing
repetitions, environment/baseline versions and the source SHA-256:

| Actual input bits | Inputs | Saved decoder | GNU `factor` 8.32 | Speedup |
| ---: | ---: | ---: | ---: | ---: |
| 63–64 | 48 | 0.58213 ms | 0.98113 ms | 1.69× |
| 79–80 | 32 | 6.24033 ms | 21.17065 ms | 3.39× |
| 87–88 | 20 | 14.59621 ms | 99.10359 ms | 6.79× |
| 95–96 | 8 | 66.01737 ms | 441.49579 ms | 6.69× |

Every replay input factored exactly. The source also passes 601 small
semiprime/perfect-square checks, 16 independently enumerated CRT masks,
a low-order alias regression and an explicit table-cap regression.
A pure-Python fallback recovered
`24514908557095695328929618289 = 151488737100313 * 161826608540953`.

The balance restriction matters. An earlier adaptive-prototype audit used
12 inputs per population, seed `2026100780`, and a public ratio ceiling
large enough for each population:

| Nominal bits | Factor bit lengths | Ratio ceiling | Adaptive prototype | GNU `factor` |
| ---: | --- | ---: | ---: | ---: |
| 80 | 40,40 | 2 | 9.30631 ms | 29.66532 ms |
| 80 | 39,41 | 8 | 52.44166 ms | 21.24412 ms |
| 80 | 38,42 | 32 | 94.14567 ms | 10.41097 ms |

Thus this is a measured win in a specified regime and baseline version.
There is no claim of a record, superiority over current GNU versions,
tuned quadratic sieve or NFS, or improved asymptotic complexity.
Published deterministic `N^(1/5)` methods already improve the exponent
through shared weighted-factor-sum collisions and lattice constructions.
Those methods are the relevant scaling comparison.

### Other colour and signal gates

These exploratory probes ran in memory. Their aggregate results are
preserved without claiming complete executable reproduction:

- Quartic colour can distinguish factor splits with the same product
  colour. Independent fourth-root averaging kills the pair amplitude
  while preserving balanced pair energy. It does not cheaply select the
  unknown semiprime coefficient; phase-colour identities are not themselves
  factorisation oracles.
- The unit-restricted Gauss sum
  `U_N=sum_(x mod N, gcd(x,N)=1) exp(2*pi*i*x^2/N)` is factor-sensitive.
  Put `F=epsilon_N*sqrt(N)+1-U_N`, where `epsilon_N=1` for `N=1 mod 4`
  and `i` for `N=3 mod 4`. The derived reconstruction is `S=abs(F)^2`
  in the second case and `S=abs(F^2-2*sqrt(N))` in the first.
  Ten small-semiprime checks agreed within `5.14e-12`. No cheap evaluator
  of the unit restriction was found: the discarded nonunits carry the
  factor-sensitive correction, and sampling a nonunit already finds a factor.
- A Lucas parameter with `Jacobi(P^2-4,N)=-1` guarantees opposite
  local quadratic colours. A 1,800-input audit compared this variant with
  fixed Lucas and ordinary `p-1` at smoothness bounds 32, 128 and 512,
  seed `2026100521`. Returned-factor checks passed, but no consistent
  advantage over fixed Lucas was found. This is classical Williams
  `p+1` machinery, not a near-linear algorithm.

### Saved source and replay commands

The optional decoder is
[probe_semiprime_modular_signal.py](../scripts/probe_semiprime_modular_signal.py).
It is not integrated into ordinary builds or CI. From `formal/`, using
the existing research virtual environment:

~~~bash
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_modular_signal.py validate
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_modular_signal.py factor 24514908557095695328929618289
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_modular_signal.py benchmark --output docs/semiprime-modular-signal-audit.json
~~~

The benchmark is explicit and optional. Its defaults are
`--bits 64 80 88 96 --counts 48 32 20 8 --seed-base 2026100900 --repeats 3`.
GMP is optional for individual decoding (`factor --no-gmp`); generated
experiments require SymPy and a GNU-compatible `factor` executable.
The two-million-entry table cap reports resource exhaustion rather than
treating an unfinished search as evidence.

The older source
[probe_semiprime_partial_information.py](../scripts/probe_semiprime_partial_information.py)
is preserved too. Its Euler–Maclaurin correction had an extra integer-
endpoint factor previously removed only in memory. The saved source now
contains that correction. Nine independent 45-digit mpmath checks of its
small zeta grid had maximum zeta/derivative discrepancies below `5e-16`.
This is a numerical regression, not a floating-error certificate.

## 2026-10-02: weighted batching, sparse signals and independent tables

This entry preserves the later in-memory investigation as executable source
and a fresh replay in
[semiprime-sparse-batch-audit.json](semiprime-sparse-batch-audit.json).
The artifact separates historical measurements from saved-source results
and records source hashes, seeds, dependency versions and corpus information.
The algebra below has exact Python regression checks; it has not been
formalised in Lean in this slice.

### Cheaper shared collision work

[probe_semiprime_weighted_batch.py](../scripts/probe_semiprime_weighted_batch.py)
preserves the weighted factor-sum prototype. It joins primitive balanced
rows `a*b<=r`, with `r` proportional to `N^(1/5)`, using centres
`ceil(2*sqrt(a*b*N))` and anchors `2^(a*N+b-centre) mod N`.
The implementation combines an exact Kronecker product tree, geometric
evaluation by a Bluestein convolution, blocked GCD extraction, and a
NumPy Montgomery accelerator for sufficiently many anchors. Small batches
retain the simpler GMP exponentiation path.

The new order gate tests geometric products in approximately square-root
many evaluations. A proper GCD returns a factor; unit products certify
that neither prime sees order at most the requested cutoff. A global
low-order collision is reported as a failure rather than silently treated
as a certificate. A general large-order base finder is still missing.
The public promise is an odd balanced semiprime with `p<q<=2p`.

The saved replay checks 220 order-certificate outcomes and 108 factoring
runs on six inputs in each nominal size, seed `2026100447`. Method order
is shuffled, each input is repeated twice, and times include the full
factor call. The table is the median across input mean times:

| Nominal bits | Baseline, ms | Batched GCD, ms | Joint batching, ms |
| --- | ---: | ---: | ---: |
| 48 | 1.6705 | 1.8048 | 2.0287 |
| 64 | 19.9638 | 18.0510 | 17.8604 |
| 80 | 206.5784 | 196.3529 | 186.8431 |

These are modest practical savings against our own prototype. Smaller
inputs favour the baseline. The number of materialised rows remains at
the one-fifth target scale, so batching alone supplies no exponent change.
The factor calls receive only `N`; generated factors are used for the
final exact assertions. Fixed base 2 is not an unconditional algorithm.

### An exact sparse polynomial signal

For distinct odd primes `p<q<2p`, put `N=p*q` and `m=floor(sqrt(2N))`.
Then `q<=m<2p`, and coefficientwise reduction gives

$$
(1+X)^N\equiv 1+qX^p+pX^q
\pmod{N,\ X^{m+1}}.
$$

Modulo `p`, Frobenius gives `(1+X)^N=(1+X^p)^q`; below degree `2p`,
only `1+qX^p` survives. Modulo `q`, the corresponding truncation is
`1+pX^q`. The displayed identity follows by CRT. Thus the unknown prime
locations really are encoded sparsely. The alternating binomial prefix
then yields a single scalar observable:

$$
p+q\equiv 1-(-1)^m\binom{N-1}{m}\pmod N.
$$

Since `0<p+q<N`, its least nonnegative residue is the exact factor sum.
For `N=323`, `m=25` and the binomial residue is `35`, giving sum `36`
and factors `17,19`. The source
[probe_semiprime_sparse_signal.py](../scripts/probe_semiprime_sparse_signal.py)
checks the polynomial coefficients, scalar identity and formal derivative
on all 423 eligible odd-prime pairs below 200.

This has two exact extraction obstructions. First, the nonconstant
formal derivative is zero modulo `N`, because its coefficients are
`p*q=N`. Differentiation erases the sparse factor signal. Second,
ordinary scalar modular exponentiation includes the high-degree tail;
it does not evaluate the truncated polynomial. At `N=323`, evaluating
the truncation at `X=2` gives `73`, whereas `3^323 mod 323` is `146`.
The quotient's nilpotent variable cannot be evaluated at an ordinary
unit by a ring homomorphism. The saved naive convolution probe also
finds fully dense intermediate polynomials. Final sparsity does not
itself provide cheap construction.

### Factorial value/derivative extraction

A second exact access route keeps a product and its derivative together.
Let `F_m(X)=prod_(i=1..m)(X+i)`, `B=m!`, and `D=F'_m(0)`.
On the same balanced support, `B` contains each prime exactly once, so
`b=B/N` is a unit modulo `N`. All derivative summands except the two
prime locations vanish modulo `N`, giving

$$
D\equiv b(p+q)\pmod N.
$$

Recover `b mod N` from `B mod N^2` by exact division by `N`, then
recover the factor sum from `D*b^(-1) mod N`. A product tree of dual
numbers `(B,D)`, with multiplication `(a,b)(c,d)=(ac,ad+bc)`, evaluates
these two quantities jointly. It never divides by `B mod N`, which
is exactly the nonunit where the factor information lives.

The source
[probe_semiprime_factorial_jet.py](../scripts/probe_semiprime_factorial_jet.py)
checks 1,035 odd semiprimes with primes below 200, including squares and
unbalanced pairs: 612 use a proper factorial GCD and 423 use the trace
identity. The factor recovery does not receive the reference factors.
The batched derivative cache works, but is slower than the prime-prefix
cache below; it is an identity/extraction audit rather than the preferred
routine. This mirrors the repository's useful practice of retaining
joined product/derivative information before division, for example in
[ZetaRieszOrderedWard.lean](../RiemannGaussian/ZetaRieszOrderedWard.lean).
It does not establish that the RH identities supply a factoring oracle.

### Independent prime tables and accumulating remainders

[probe_semiprime_prime_prefix_batch.py](../scripts/probe_semiprime_prime_prefix_batch.py)
builds an independent Eratosthenes list and exact prime-product tree
through `floor(sqrt(X))`, where `X` is the public input bound.
For a query `N=p*q`, the primorial prefix through `floor(sqrt(N))`
contains the smaller prime and excludes the larger one; its GCD with
`N` gives the factor. A square also gives its prime factor.
A sparse accumulating remainder tree shares the large integer reductions
across many distinct queries. These are standard remainder-tree ideas;
see [Harvey's notes, sections 7.1 and 7.4](https://swc-math.github.io/aws/2026/2026HarveyNotes.pdf).

The saved replay checks 1,081 small semiprimes, including even inputs,
squares and unbalanced pairs, plus duplicate queries, an empty batch
and rejection of queries outside the cache bound. The timing corpus
contains 1,024 distinct 32-bit semiprimes with disjoint factors. It uses
seed `6897333`, a common public bound, shuffled method order and the
median of three repetitions. The cache is target-independent.

| Batch size | Cached query, microseconds/input | Cache plus query, microseconds/input | Existing prime-power decoder, microseconds/input |
| --- | ---: | ---: | ---: |
| 1 | 27.6570 | 5580.9550 | 48.5390 |
| 64 | 9.6074 | 96.3777 | 44.9445 |
| 256 | 7.6999 | 29.3925 | 43.8225 |
| 1024 | 5.6134 | 11.0365 | 44.1333 |

Construction took `5.5533 ms`. Stored product integers total `165,723`
bytes; that excludes Python object overhead and the sieve. The largest
batch is about four times faster than our decoder with precomputation
charged. This is not a benchmark against the fastest native factoring
software, and the small prototypes do not establish large-input scaling.

With logarithmic factors suppressed, the natural total batch cost is
`~O(sqrt(X)+B)` for `B` queries, and the amortized cost is
`~O(sqrt(X)/B+1)` per input. Reaching `X^(1/6)` this way requires roughly
`B>=X^(1/3)` inputs sharing the public bound. A single input still pays
the square-root construction/reduction cost. Storage and preparation
remain exponential in input bit length and are infeasible for RSA-size
universal tables. No generic single-input `N^(1/6)` improvement was found.

### What sparse centres and colour tables did not yet provide

[probe_semiprime_centre_compression.py](../scripts/probe_semiprime_centre_compression.py)
preserves the numerical Taylor-block experiment for
`ceil(2*sqrt(N*k))`, `r<=k<2r`, with `r=floor(N^(1/3))`, seed `600193`.
Cubic blocks of length about `2*r^(2/5)` and quartic blocks of length
about `2*sqrt(r)` need few correction descriptors in the tested inputs.
At 47 bits the quartic pass used 110 blocks and 15 exceptions instead
of 47,947 literal centres.

Those exceptions were discovered by scanning every centre. Rounding
also destroys the polynomial's exact higher-difference cancellation:
about 87% of next-order differences were nonzero in the largest quartic
probe. Neither cheap exception generation nor an implicit modular
collision-product evaluator has been proved. A heuristic one-sixth
descriptor count therefore remains a representation observation.

The same source audits precomputed unit-residue factor-sum masks.
For the tested `W=2^t`, `t=4,6,...,16`, the residue class `N=-1 mod W`
still permits exactly `W/8` sum residues. Larger tables do not remove
that density on this class. This is a result about unit residues, not
an impossibility theorem about prime pairs in a bounded input range.
Mixed wheels can improve individual classes at a larger table cost.
No cheap zeta/eta table has supplied an additional independent factor
signal; the repository's eta here is Dirichlet eta, not Dedekind eta.

### Replaying the preserved source

These five scripts are optional, guarded on import, and are not wired
into ordinary builds or CI. From `formal/`, run any of:

~~~bash
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_sparse_signal.py
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_centre_compression.py
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_factorial_jet.py
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_prime_prefix_batch.py
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_weighted_batch.py
~~~

The replay environment uses Python 3.10.12, gmpy2 2.3.1, NumPy 2.2.6,
SymPy 1.14.0 and mpmath 1.3.0. Timings are indicative: no CPU affinity
was imposed, and the initial independent replay jobs overlapped.
Use sequential repeats for a controlled timing comparison. All checks
reported above passed; no source edit or staging in this side project
changes the active RH work.

## 2026-10-02: cheap individual extraction and exact phase tilt

This pass charges the construction and evaluation costs to each input.
No square-root-sized universal table, known factor, totient, private local
order or separate Legendre sign is an input to the extraction functions.
Write `N=p*q` with distinct odd primes. The exponent in `N^(1/6)` refers
to numerical `N`: for a `b`-bit input it is about `2^(b/6)`, not polynomial
time in `b`. The one-fifth comparison is to the deterministic exponent
framework, rather than a claim to beat heuristic NFS or tuned native code.

### A public exponent separates the hidden local periods

For an ordinary modular unit, let

\[
g=\gcd(p-1,q-1).
\]

The identities

\[
\gcd(p-1,N-1)=\gcd(q-1,N-1)=g
\]

imply that raising the unit to `N-1` makes its two local orders divide
`(p-1)/g` and `(q-1)/g`. Those quotients are coprime. Subsequent common
prime-power projections preserve that coprimality. Neither `g` nor either
local order needs to be known to execute the projection.

This pays a concrete weakness of the previous low-order search: distinct
nontrivial local periods cannot coincide after separation. If one local
period closes before the other, the GCD is a proper factor. If both close
within the same geometric block, the product-tree descent recovers a
separating leaf. The implementation inspects the first nonunit block,
rather than accepting a shared collapse as a factor. A bounded search over
32 bases can still return `kernel-unresolved`; it does not assume a small
nontrivial witness always exists.

[SemiprimeOrderSeparation.lean](../RiemannGaussian/SemiprimeOrderSeparation.lean)
now proves the cardinality/GCD identities, coprime projected orders, their
preservation under further powers, a bounded separating witness, its GCD
consequence and the exact geometric-cover indexing. This optional module
is outside the RH umbrella. It does not formally verify the whole Python
program or its bit complexity.

The public budget is

\[
B=\lceil N^{1/6}\rceil,\qquad
D=\max(1,\lfloor B^2/c\rfloor).
\]

The pass builds its own primes through `B`. For each prime `ell<=B`, it
projects by the largest power of `ell` at most `floor(sqrt(N))`, not just
the largest power below `B`. Thus it removes all small-prime powers from
the smaller factor's remaining order. Checking the GCD after every power
preserves a factor found during the projection.

The final polynomial has about `sqrt(D)` roots and is evaluated at about
`sqrt(D)` geometric points. Their differences cover every positive period
through `D` (with a slightly larger exact block endpoint). With fast integer
and polynomial arithmetic, construction, projection, evaluation and GCD
descent have soft `O(B)` bit work, with logarithmic factors in `N` suppressed.
This operation analysis is separate from the Lean structural proof.
Success is guaranteed for a nontrivial separated witness when at least one
remaining private period lies in that cover. Otherwise the pass reports
`certified-large-order`: both private periods exceed the covered endpoint.
It does not hide failure inside an unproved coverage hypothesis.

[probe_semiprime_single_extraction.py](../scripts/probe_semiprime_single_extraction.py)
implements the partial pass and a hybrid using our earlier weighted search
as fallback. The fallback keeps its balanced-input and fixed-base
limitations; this is not an unconditional factoring library.

### Fresh single-input timing, with failure and fallback charged

[semiprime-single-extraction-audit.json](semiprime-single-extraction-audit.json)
contains 32 fresh balanced inputs at each nominal size, seed `2026100331`.
The fixed divisor `c=16` was chosen after a separate small exploratory
budget scan with seed `2026100251`. Complete method calls, including each
input's sieve, are timed in shuffled order for three repetitions. There
is no cross-input cache. Known factors construct and verify the corpus;
they are not passed to recovery. Every returned factor was verified.

| Nominal bits | Partial pass successes | Weighted total, ms | Hybrid total, ms | Total speedup |
| --- | ---: | ---: | ---: | ---: |
| 48 | 13/32 | 60.3940 | 54.7768 | 1.103x |
| 64 | 19/32 | 732.3646 | 390.6287 | 1.875x |
| 80 | 20/32 | 8145.0112 | 3600.2575 | 2.262x |

At 48 bits the hybrid median was worse, `2.0994` versus `1.8120` ms, even
though its total was slightly better. Median improvements at the larger
sizes are strongly affected by the partial pass solving over half the
inputs, so the total-corpus comparison is the clearer aggregate measure.

A second fresh corpus, seed `2026100461`, contains 24 inputs per size.
Its scalar-hybrid total speedups were `1.032x`, `1.107x`, `1.781x` at
48, 64, 80 bits respectively. Hit rates and benefits vary materially by
corpus. Neither replay establishes a limiting success probability or a
generic exponent improvement. These are API timings against our own
Python weighted prototype, not the best classical factoring software;
startup is excluded, and no CPU affinity was imposed.

### Quadratic colour: use the public product of the private signs

In the quadratic algebra `(Z/NZ)[sqrt(D)]`, use a norm-one unit. Its local
orders divide

\[
A=p-\epsilon_p,\qquad B_q=q-\epsilon_q,
\qquad \epsilon_p=\left(\frac Dp\right),\quad
\epsilon_q=\left(\frac Dq\right).
\]

Only their product is needed by the separator:

\[
\sigma=\operatorname{Jacobi}(D,N)=\epsilon_p\epsilon_q,
\qquad E=N-\sigma.
\]

For all four sign patterns, exactly

\[
\gcd(A,E)=\gcd(B_q,E)=\gcd(A,B_q).
\]

Raising the norm-one unit to `E` therefore makes its private local orders
coprime too. `colour_gcd_separator` and
`coloured_projected_orders_coprime` formalize the signed cardinality
arithmetic and the group conclusion, assuming the local order divisibility.
The identification of those cardinalities with the quadratic Legendre
cases uses the standard finite-field fact; it is checked in the exact
reference probes, not separately formalized here.

The norm-one starting element is the input-specific Cayley quotient

\[
\frac{a+\sqrt D}{a-\sqrt D}
=\frac{a^2+D}{a^2-D}+\frac{2a}{a^2-D}\sqrt D.
\]

A nonunit denominator supplies a GCD factor. The code checks parameter
values `1..32` and reports failure if they all lie in the separator kernel.
Its default colour scan selects `Jacobi=-1` and therefore `E=N+1`; an
explicit public discriminant also tests the `Jacobi=+1`, `E=N-1` case.
Equal mixed-sign cardinalities force twin factors; their product plus one
is a square, which the public preliminary square test pays exactly.

[probe_semiprime_quadratic_extraction.py](../scripts/probe_semiprime_quadratic_extraction.py)
implements both split and nonsplit quadratic arithmetic with exact modular
products and a geometric order cover. `quadratic_norm_one_collision`
proves that the norm detects equality between norm-one elements over either
local quadratic algebra, including the split case. This restriction matters:
zero norm does not mean zero for arbitrary elements of a split algebra.

Five safe-prime controls, from `59*83` through a nominal 80-bit input,
all fail the scalar full-budget pass but are factored by colour at the
same `c=1` budget. This is additional coverage, not a universal guarantee.
On the fresh 72-input timing corpus the cheaper colour pass (`c=256`)
added only one hybrid success per size, and increased total hybrid runtime.
It remains optional rather than becoming a recommended default.

### Exact phase tilt removes a convolution channel

The new RH theorem in
[ZetaRieszComplexProjection.lean](../RiemannGaussian/ZetaRieszComplexProjection.lean)
motivated a specific extraction question: can a common known phase be
removed before projecting the entire collision product? The factoring
analogue is algebraic; a real one-sided inequality from the RH theorem
cannot itself be used as a modular divisibility detector.

Let `beta` be the projected norm-one element, `alpha=beta^2`, and choose
an even baby width `b`. With

\[
P(X)=\prod_{i=0}^{b-1}(X-\alpha^i),
\]

the whole geometric evaluation has the exact known phase

\[
P(\alpha^{bj})
=\beta^{b^2j+b(b-1)/2}\,c_j,
\qquad \overline{c_j}=c_j.
\]

Indeed each difference factors as

\[
\beta^{2e}-\beta^{2i}
=\beta^{e+i}
  (\beta^{e-i}-\beta^{i-e}).
\]

The parenthesized factor is anti-selfadjoint; an even product is
selfadjoint. This preserves every collision and its cross terms. The
Lean lemmas `squared_collision_phase`,
`inverse_difference_anti_selfadjoint`,
`even_collision_product_selfadjoint`, `product_collision_phase`,
`quadratic_selfadjoint_im_zero` and `quadratic_phase_recover` check the
algebra underlying the projection.

The Bluestein convolution also has a known phase. We compute only its
real coordinate, using two scalar convolutions instead of three, and
recover the real scalar by dividing out that phase coordinate. All
divisions are charged using one input-specific batch inversion. A nonunit
coordinate gives a proper GCD factor; an exceptional zero coordinate has
an exact full-coordinate fallback. Thus the optimization does not silently
project away a factor or use a floating-point phase.

This is a useful implementation connection to the repo's phase-preservation
principle. Reciprocal symmetry and two-convolution `p+1` evaluation already
appear in [Montgomery–Kruppa's primary stage-two presentation](https://antsmath.org/ANTSVIII/files/kruppa.pdf).
We are not claiming a first-ever phase-based factoring algorithm.

[semiprime-quadratic-extraction-audit.json](semiprime-quadratic-extraction-audit.json)
records the comparison on the same fresh 72-input corpus:

| Nominal bits | Quadratic total, ms | Tilted quadratic total, ms | Runtime reduction |
| --- | ---: | ---: | ---: |
| 48 | 34.5341 | 34.5653 | -0.091% |
| 64 | 264.5777 | 260.0765 | 1.701% |
| 80 | 1592.7923 | 1557.4320 | 2.220% |

These small differences need larger controlled repeats before a robust
runtime claim. The exact convolution-count reduction is stronger evidence
than a small timing difference. The total complexity remains soft `N^(1/6)`
for the partial pass; this does not change the coverage exponent.

### Exact controls identify the remaining information gap

[probe_semiprime_order_controls.py](../scripts/probe_semiprime_order_controls.py)
and [semiprime-order-separation-audit.json](semiprime-order-separation-audit.json)
preserve the regressions, larger controls, dependency hashes and focused
Lean compilation. The scalar checks include 3,828 local-order comparisons,
1,035 semiprime projection cases, 220 geometric-cover tests, and 567 exact
folded-Frobenius identities. Quadratic checks include naive-convolution and
Horner comparisons, 108 exact real-tilt regressions, and 990 distinct odd
semiprime cases for both the original and tilted/same-colour variants.

Two more cheap signal candidates failed their intended extraction test:

- For `0<k<min(p,q)`, every `binomial(N,k)` is zero modulo `N`.
  `low_choose_dvd_semiprime` proves this exactly. A shorter nilpotent
  binomial prefix therefore has no factor-sensitive nonconstant residue.
- The reciprocal folded-Frobenius scalar can be evaluated in `O(log N)`
  modular operations and satisfies its exact Laurent identity. The tested
  fixed values `t=2..14` factored none of the 96 fresh inputs. This is a
  finite negative probe, not an impossibility theorem for all Frobenius
  tests or all parameters.

The more decisive coverage counterexample is

\[
N=6827\cdot7187=49065649,\quad B=20,\quad D=400.
\]

Its four cardinalities are

\[
p-1=2\cdot3413,\quad p+1=12\cdot569,\qquad
q-1=2\cdot3593,\quad q+1=12\cdot599.
\]

All four displayed rough factors are prime and exceed `400`. The scalar
pass and all 16 explicit colours return `certified-large-order` at the
full `c=1` budget. Reference exponentiation verifies the exact private
orders after projection. `four_rough_period_control` checks the prime,
factorization and budget arithmetic in Lean. Its statement is deliberately
a finite structural control, not a lower bound for arbitrary algorithms.

The same pattern survives on larger independently generated controls,
seed `2026100541`:

| Input | Public `B` | Covered `D=B²` | Colour outcomes |
| --- | ---: | ---: | --- |
| `2346272483 * 3649327547` | 1431 | 2047761 | All 16 private-order covers fail |
| `661911275027 * 720957498683` | 8840 | 78145600 | All 16 private-order covers fail |

Here both primes are of the form `12r-1` with `r` and `6r-1` prime.
Consequently changing colour merely selects between two long private
prime periods on each leg; it does not create a short period. Generating
these controls uses known reference factors, but recovery receives only
their product. No claim about infinitely many such prime patterns is made.

The next scaling improvement must extract something from long rough
periods, or provide a new cheaply constructed cover of them. Improving the
phase projection alone cannot turn this bounded cover into a generic
one-sixth algorithm. If a remaining order has two rough factors, the
ordinary GCD equality detector only sees closure of their product, not
closure of one private order factor; those factors also need a new signal
or a cheap joined evaluation. This is the sharply defined open target.

The literature's [conditional one-sixth framework](https://arxiv.org/html/2511.10851v1)
requires efficiently prefactored structured difference covers. Our colour
signal and phase projection do not establish that hypothesis.
[The arithmetic-progression obstruction](https://arxiv.org/html/2608.06681)
rules out a particular one-dimensional proposal, not every higher-rank
cover. There is no justified generic one-sixth result here yet.

### Optional replay commands

From `formal/`, the focused validation and exact controls are:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_order_controls.py --check-lean
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_single_extraction.py hybrid 4897
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_quadratic_extraction.py factor 4897 --order-divisor 1 --tilt
~~~

The saved timing replays are reproducible with:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_single_extraction.py benchmark --bits 48 64 80 --cases 32 --repeats 3 --seed 2026100331 --order-divisor 16
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_quadratic_extraction.py benchmark --bits 48 64 80 --cases 24 --repeats 3 --seed 2026100461
~~~

All new scripts are guarded and optional, with no CI or RH-build integration.
Only the side-project sources, note and audits are staged for preservation.

## 2026-10-02: extracting from long periods without a quadratic grid

Artifacts:

- [Public-input extractor and fast multipoint implementation](../scripts/probe_semiprime_long_period.py).
- [Reference-only signal probes and focused proof replay](../scripts/probe_semiprime_long_period_signals.py).
- [Control recovery audit](semiprime-long-period-audit.json),
  [fresh timing corpus](semiprime-long-period-benchmark.json), and
  [signal/validation audit](semiprime-long-period-signals.json).
- [Checked Lean algebra/witness lemmas](../RiemannGaussian/SemiprimeLongPeriodExtraction.lean),
  outside the RH umbrella.

### A signal beyond the linear order cover

Take the same public quadratic colour `D=-1`, Jacobi separator and smooth
projection used by the earlier pass. Write the resulting norm-one element
as `alpha`, and set `B=ceil(N^(1/6))`. The new pass compares the scalar
traces of

$$
\alpha^{D_6(i,1)},\quad 0\le i<B,
\qquad
\alpha^{D_6(Bj,1)},\quad 1\le j\le B,
$$

where `D_6(x,1)=x^6-6x^4+9x^2-2`. Equal traces detect equal **or inverse**
norm-one elements. This remains valid on both split and nonsplit local
quadratic algebras; no hidden Legendre symbol enters recovery.

The exact identity, now checked in Lean, is

$$
D_6(x,1)-D_6(y,1)
=(x-y)(x+y)(x^2-xy+y^2-3)(x^2+xy+y^2-3).
$$

On the 64-bit control the public algorithm finds `j=477`, `i=1427`,
`B=1431`. Its recovered factor is `2346272483`. **After recovery**, the
reference check identifies the local order as `195522707`, while the old
cover reaches only `2047761`. Put `x=477*1431`, `y=1427`. Then

$$
x^2-xy+y^2-3=2378\cdot195522707,
\qquad x+y<195522707.
$$

The quadratic factor supplies a multiple of the private period; neither
linear gap does. The algorithm never receives that period. Its actual
trace residues give the directly verified certificate

$$
\gcd(6820094445240089472-237621801882584593,\,
8562316804979989201)=2346272483.
$$

This is extraction before enumerating the long period, not an order oracle.
The earlier smallest rough control is also recovered. The 80-bit control
still defeats this particular degree-six map.

### Paying for the nonlinear points

For a fixed-degree integer polynomial `f`, generate `alpha^f(i)` using its
finite-difference table. The update

$$
\alpha^{v_i}\alpha^{v_{i+1}-v_i}=\alpha^{v_{i+1}}
$$

uses only a fixed number of group multiplications per new point. All initial
differences and their powers are computed for the input. Negative exponents
use norm-one conjugation. The implementation reduces each quadratic point
to one scalar trace **before** constructing the collision polynomial.

Geometric chirp evaluation no longer applies to these points. The new
monic product/remainder tree evaluates them using exact GMP polynomial
products and Newton reciprocal iteration. A monic reversed polynomial has
constant coefficient one, so this needs no division by an unknown nonunit
in `Z/NZ`. The algorithm materializes `O(B)` points, not `B^2` comparisons;
the polynomial work is softly linear in `B`. Its logged convolution and
coefficient counts include the full query-specific construction.

These techniques have classical precedents: the
[Brent–Kruppa–Zimmermann account](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf)
describes fast polynomial continuation, power/Dickson maps and ECM. The
contribution here is their concrete integration with our local-order
separator, scalar trace folding and audited controls. We do not claim to
have invented Dickson continuation or ECM.

### Cheaply replacing a resistant group

`curve_extract` constructs a public Suyama Montgomery curve, starting at
`sigma=6`, and projects away primes through `B`. It compares x-coordinates
of `[i]Q` and `[Bj]Q`: equality means `[Bj-i]Q` or `[Bj+i]Q` is zero locally.
The same monic multipoint evaluator batches the test. Coordinate inversions
are batched, with nonunit GCDs checked first. Curve construction, projection,
coordinates, products and factor descent are charged to the input.

This changes the local group; it does **not** decode the original long
`p±1` periods. On all three controls the first public curve succeeds:

| Input | Old linear cover | Dickson-six result | Curve factor | Verified local annihilator |
| --- | ---: | --- | ---: | ---: |
| `6827*7187` | 400 | factor 6827 | 6827 | 191 |
| `2346272483*3649327547` | 2047761 | factor 2346272483 | 3649327547 | 1357673 |
| `661911275027*720957498683` | 78145600 | no collision | 661911275027 | 20873 |

The last column is verified only after GCD recovery, not supplied to the
search. No curve-order oracle, factor-indexed table, or list of all primes
through `B^2` is used.

The target batches grow as `1,2,4,8,...`, reusing the baby product. This
allows an early hit while retaining only logarithmically many degree-`B`
reductions in the worst case. Fixed-size repeated batches would silently
restore quadratic cost and are deliberately avoided. The 80-bit control
needs only three target coordinates in two batches; its exploratory time
drops from about 0.97 s for the full target cover to 0.24 s. That single
timing motivated, but does not replace, the fresh corpus below.

### Fresh corpus and negative probes

Seed `2026100663`; 16 fresh balanced inputs per nominal size; three
repetitions in randomized method order. Each timing includes the complete
input-specific call. Imports, sample generation, reference verification
outside the call, and JSON are excluded. Every returned factor is checked
by exact divisibility. The one-curve test uses the same public `sigma=6`
on every input. There are no retained cross-input prime or curve tables.

| Nominal bits | Same-colour linear hits | Dickson-six hits | One-curve hits | Linear total ms | Dickson total ms | Staged curve total ms | Full curve total ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 48 | 14/16 | 16/16 | 14/16 | 155.5 | 197.8 | 99.4 | 171.6 |
| 64 | 12/16 | 14/16 | 15/16 | 1261.5 | 1793.8 | 896.4 | 1499.5 |
| 80 | 13/16 | 14/16 | 15/16 | 10058.6 | 15870.9 | 7373.4 | 14264.2 |

The nonlinear map adds five hits but is slower in total than the linear
pass. Staging improves the curve totals by `1.727x`, `1.673x`, `1.935x`,
with unchanged hit counts. No tuned native ECM comparison was performed.
Single-input failure is explicit; a fixed curve or fixed map is not
guaranteed to factor every semiprime.

Public exponents `N^d-1` for `1<=d<=64` produce no factors on these controls.
Reference-only alias probes find no power-map hits through tested degree
60 on the two larger controls; the Dickson-six quadratic hit distinguishes
the 64-bit case. Neither power nor tested Dickson maps hit the 80-bit
control. The diagnostic tables contain private periods for explanation;
the separate recovery algorithms never consult them.

There is also an exact inexpensive gap encoding for every unit `a`:

$$
a^{N-1}+a^{-(N-1)}
\equiv a^{q-p}+a^{-(q-p)}\pmod N.
$$

Lean proves the two local exponent identities behind it. The trace is cheap
to obtain, but decoding a generic large gap remains expensive. A short-gap
promise also benefits classical Fermat factoring, so this alone is not a
new generic speedup.

Validation independently compares 175 monic remainders with elementary
division, 625 multipoint values with Horner evaluation, 3335 finite-
difference powers with direct powers, 638 local trace collisions, and 948
Montgomery multiples with an independent affine group law. All pass.
The focused Lean file compiles without warnings or admissions. Its lemmas prove
the algebra and integer witnesses, not the entire Python implementation,
its bit complexity, a hit-rate theorem, or generic one-sixth factoring.

### What is still missing

The quadratic alias is real information that the original linear cover
missed. A universal cheap cover of long periods is still unproved. Fixed
nonlinear maps can fail; increasing their number must be charged. Changing
curves is a useful classical escape, but a bounded curve pass likewise
has no unconditional one-sixth coverage guarantee. The research target
remains a provable improvement in coverage per unit of extraction work,
rather than another cheaply encoded quantity with an expensive decoder.

Optional replay, from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period_signals.py --check-lean
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period.py controls
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period.py benchmark --bits 48 64 80 --cases 16 --repeats 3 --seed 2026100663
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period.py factor 8562316804979989201
~~~

## 2026-10-02: complex null corrections and cheap exponential orbits

Artifacts:

- [Public-input phase/orbit extraction](../scripts/probe_semiprime_complex_extraction.py).
- [Exact checks and selected challenge replay](semiprime-complex-extraction-audit.json).
- [33 checked algebra/witness theorems](../RiemannGaussian/SemiprimeLongPeriodExtraction.lean),
  including the new correction and orbit identities, outside the RH build.

### What transfers from the RH null correction

The RH theorem `ZetaRieszComplexNullFloor.increment_coherent_zero` cancels
a flat contribution when its phase is collinear with a common moment.
Its cross-phase algebra transfers to modular quadratic rings. For a known
norm-one phase `phi` and a scalar collision value `v`, write `F=phi*v`.
Then exactly

$$
\phi_{\rm im}F_{\rm re}-\phi_{\rm re}F_{\rm im}=0,
\qquad
\phi_{\rm re}F_{\rm re}+\phi_{\rm im}F_{\rm im}=v
$$

in the Gaussian modular ring. The first identity holds without a norm
assumption; the second uses `norm(phi)=1`. Thus a perpendicular correction
annihilates **every** scalar amplitude, including the amplitude whose GCD
would reveal a factor. `coherent_null_gcd_is_full` proves its GCD is always
the entire modulus. It is not an additional separating signal. No ordered
real inequality from the RH floor is applied to `Z/NZ`.

Rotating **before** projecting changes the collision itself. For norm-one
`kappa,x,y` over either split or nonsplit local quadratic algebras,

$$
\operatorname{Re}(\kappa x)=\operatorname{Re}(\kappa y)
\iff x=y\ \text{or}\ \kappa^2xy=1.
$$

When `kappa=alpha^c`, the second channel is

$$
f(i)+f(Bj)+2c\equiv0\pmod{\operatorname{ord}(\alpha)}.
$$

The equal channel is unchanged. The implementation constructs and tests
the rotated scalar points without knowing either local order. Each added
phase pays for its additional polynomial tree and evaluation; it is not a
free new search dimension. The fixed phases `-13,+15` were calibrated on
a previous control, and the replay identifies that calibration explicitly.

Pure imaginary rotation is less useful here: after removing the 2-part,
the projected local order is odd. Its subgroup cannot contain `-1`.
`imaginary_rotation_odd_order_inverse_impossible` proves that a phase
`i*alpha^c` cannot provide the inverse channel on that subgroup. Imaginary
projection alone consequently loses the existing folded channel rather
than extending it on that odd-order leg.

A second exact limitation concerns choosing an apparently optimal phase.
Both degree-six exponents `e,f` are even, so the public choice
`c=-(e+f)/2` forces `kappa^2*alpha^e*alpha^f=1` globally. The rotated traces
then agree modulo both prime factors, and their GCD is `N`. The new replay
checks this on every challenge. `global_inverse_alignment_gcd_is_full`
proves it over the composite modular ring. A separating phase must expose
a relation on one hidden leg without enforcing the same relation globally.

### Exponentially large exponents with linear point-generation work

Compare traces of `alpha^(a^i)` and `alpha^(b^j)`, with `1<=i,j<=B` and
public distinct integers `a,b>=2`. Each point is generated from the
previous point by the exact recurrence

$$
\bigl(\alpha^{a^i}\bigr)^a=\alpha^{a^{i+1}}.
$$

There is no need to construct the integer `a^i` or to perform a fresh
powering using its exponentially large value. Constant bases need `O(B)`
group multiplications; the public bases `N,N+1` need `O(B log N)`.
One baby product and doubling target batches keep polynomial evaluation
softly linear in `B`. Indices zero are excluded to avoid the vacuous
identity `a^0=b^0=1`. Shared full-modulus collisions are skipped so they
cannot hide a later separating target.

On the 64-bit four-rough control, the public bases `N,N+1` recover factor
`3649327547` with baby index `121`, target index `34`. Only after recovery
can the private-period diagnostic describe this as

$$
N^{121}\equiv(N+1)^{34}\pmod{304110629}.
$$

The actual algorithm computes group points and a GCD; it does not receive
this modulus. This extracts a new collision from a long period at bounded
work. It is not a deterministic cover of every period.

### General structure behind the recoveries

The new `dickson_collision_lift` theorem applies to **every degree**, not
just the degree-six example. For nonzero lifted units `v,w`,

$$
D_d(v+v^{-1},1)=v^d+v^{-d},
$$

and exactly

$$
D_d(v+v^{-1},1)=D_d(w+w^{-1},1)
\iff (v/w)^d=1\ \text{or}\ (vw)^d=1.
$$

Thus the map is a power operation followed by reciprocal identification.
For a **prime** remaining period `r`, a trace lift lies in either the
split torus of size `r-1` or the nonsplit norm-one torus of size `r+1`.
Roots of unity in both tori create the extra fibres, explaining why both
`gcd(d,r-1)` and `gcd(d,r+1)` enter. Classical
[Dickson value-set work](https://doi.org/10.1016/0022-314X(88)90006-6)
studies this structure; the contribution here is a checked connection to
our actual collision extraction. The hidden period `r` is not supplied
to the algorithm.

The finite-field probe enumerates 143 complete small prime fields and
checks 74,924 lift identities. For primes `r=5 (mod 6)`, degree-six
Dickson folding has about twice the full-field collision probability of
the ordinary sixth-power map. For `r=1 (mod 6)`, it has about two-thirds.
The successful 64-bit control has period `195522707=5 (mod 6)`, where the
nonsplit torus supplies a channel the power map misses. These are exact
full-field counts, not a coverage theorem for the short structured grids.
The actual same-sign witness has quadratic characters `-1,-1` for its
two trace lifts, recorded separately in the reference-only audit.

There is an important scaling limit. `dickson6_fiber_card_le` proves that
each degree-six output has at most six preimages over any field.
`dickson_nested_fold` proves that nesting degrees `a,b` is just degree
`a*b`. Nesting does not supply independent free layers. In the current
finite-difference point generator, degree `d` takes `d` group updates per
point. Any proposal for a growing fold must reduce this charged cost or
exploit additional arithmetic structure, rather than infer a new exponent
from one unusually long-period hit.

There is also a universal restriction on the remaining order geometry.
For the smaller factor `p<=q` and `B=ceil(N^(1/6))`,

$$
p+1\le B^3+1.
$$

After removing every prime through `B`, the remaining local order has
**at most two prime factors, counted with multiplicity**: three factors
greater than `B` would have product at least `(B+1)^3>B^3+1`.
`smaller_factor_group_budget` and `rough_order_prime_count_le_two`
formalize these arithmetic bounds. They assume the stated roughness of
the residual order; they do not make the hidden order readable.

Consequently the unresolved smaller-prime orders have only two shapes:

1. One prime `r>B^2`.
2. Two rough primes `r1,r2>B`, including a repeated prime, whose product
   exceeds `B^2`. Each individual factor is below `B^2`, as proved by
   `two_rough_factors_lt_square`.

This is a concrete commonality to exploit. In the second case, finding
closure of one order factor is insufficient: the current GCD needs the
whole local element to close. A new partial-order extraction identity
would have to bridge that difference at charged one-sixth cost.

The reference-only audit of the smaller `p-1,p+1` cardinality envelopes
in the saved 48-input corpus finds 41 single-long-prime envelopes, 10
two-rough-factor envelopes, 41 inside the old cover and 4 completely
cleared. There are no rough-square envelopes in that corpus. Actual
element orders can be proper divisors of these envelopes. Recovery does
not consult the reference factorizations.

### Selected challenges and their cost

The four challenges below are the Dickson failures already present in the
saved 48-input corpus. This is a selected regression, not a fresh unbiased
benchmark. Recovery receives only `N` and fixed public parameters.

| Input `N` | Phases `0,-13,+15` | Orbits `2,3` | Orbits `N,N+1` |
| --- | --- | --- | --- |
| `6015700395832288409` | no hit | no hit | factor `2278586117` |
| `10457652412285181353` | factor `2755464161` at `c=15` | factor `2755464161` | no hit |
| `681744979629536288452009` | no hit | no hit | not tested |
| `387911014119558410533909` | factor `588556368311` at `c=-13` | no hit | not tested |

The new scalar trace tests verify their equal/inverse channels after
factor recovery. Exact single-call observations were about 320 ms for
the adjacent-base recovery in the first row, 87 ms for the small-base
orbit recovery in the second, and 1.71 s for the phase recovery in the
fourth. They include setup, projection, points and polynomial work. These
are not timing guarantees or comparisons with tuned classical software.

The 80-bit four-rough control still defeats all three phases and both
small-base orbit pairs `2,3` and `2,5`. Reference-only probes also found
no inverse-channel hit among 63 predetermined phase exponents, and no
small/adjacent-base orbit hit on either of its two nonsplit rough periods.
Neither reference test is used by recovery. We do not infer an infinite
family or a lower bound for arbitrary factoring algorithms.

Independent exhaustive local checks cover 33,256 rotated trace identities,
including split quadratic algebras. A shared-target regression confirms
the full-modulus collision is skipped before a later GCD of 5 is recovered
modulo 35. Together with the long-period validations, these check the
implemented algebra. The 33 Lean theorems compile without admissions;
they do not yet verify the full Python execution or bit-operation cost.

### The guaranteed one-sixth proof obligation

For every pair of primes, including equal primes, the desired algorithm
must return `1<d<N`, `d|N`, and have charged bit-operation cost at most

$$
C N^{1/6}(\log N)^e
$$

for fixed constants `C,e`, apart from finitely many small inputs. There
must be no assumption about short orders, prime smoothness, a lucky
curve, or a factor-sensitive lookup table. A randomized formulation with
this guarantee on **every run** must cover every allowed random choice;
an expected success probability is insufficient.

The present covers have bounded work but explicit budget exhaustion.
Further numerical successes would not discharge the universal coverage
quantifier. The next theorem must control all possible remaining local
orders with a cheaply constructible cover and guarantee a separating
collision, then tie the cost bound to the actual execution. Enlarging the
phase/map budget is valid only when that enlarged cost is charged.

The literature offers relevant infrastructure, but not a supplied proof
of this target. [Harvey–Hittmeir (2026)](https://arxiv.org/abs/2601.11131)
deterministically produce an element of order greater than `D`, or a
factor, in roughly `sqrt(D)` work without the older lower restriction on
`D`. At `D=N^(1/3)`, that is compatible with a one-sixth budget. It removes
base construction as an asymptotic bottleneck; it does not decode a long
local order. This subroutine is not implemented here yet.

[Umans–Wang](https://arxiv.org/abs/2511.10851) give a conditional
one-sixth route using a structured, efficiently prefactored divisor cover.
The missing cover cannot be inserted as an assumption and called our
desired universal theorem. Our exponential orbits illustrate cheap access
to large exponents, but their observed misses leave the covering theorem
open. Their success cases alone do not establish the conjectured structure.

Optional replay, from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_complex_extraction.py probe
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_complex_extraction.py factor 10457652412285181353 --algorithm orbit --bases 2 3
/home/dbsanfte/.elan/bin/lake env lean RiemannGaussian/SemiprimeLongPeriodExtraction.lean
~~~

## October 2, 2026: partial rough-order projection and indexed Lucas maps

This pass tests the two remaining extraction targets: one long prime
period, and a period with two rough factors. The implementation is
[probe_semiprime_rough_projection.py](../scripts/probe_semiprime_rough_projection.py),
the complete replay is
[semiprime-rough-projection-audit.json](semiprime-rough-projection-audit.json),
and the class-specific proofs are in
[SemiprimeRoughProjection.lean](../RiemannGaussian/SemiprimeRoughProjection.lean).
Recovery receives only `N` and fixed public parameters. Private factors
and periods occur only in reference diagnostics or explicitly structured
corpus generation.

### Closing one component, without waiting for the product

Write `B=ceil(N^(1/6))`. Form the public exponent

$$
M_2=\prod_{i=1}^B(i^2+1)|i^2-2||i^2-3||i^2-5|.
$$

For a prepared local element whose order divides `r*t`, the exact
group identity is

$$
r\mid M_2\quad\Longrightarrow\quad
\operatorname{ord}(a^{M_2})\mid t.
$$

Thus removing one component can bring the remaining order into the
linear collision cover even when the original order was outside it.
This includes repeated factors `r=t`; the method does not need the
period to be squarefree. The Lean class theorem retains the explicit
small-root condition `r | i^2+1`, `1<=i<=B`, coprimality of the prepared
local orders, and a nontrivial surviving other leg. It does not assume
that every rough prime has such a root.

There are `4B` positive leaves, and Lean proves

$$
M_2\le(B^2+5)^{4B}.
$$

Its complete exponent therefore has `O(B log B)` bits. The implementation
builds a balanced integer product and charges its construction and the
entire modular exponentiation. In split colour `D=1`, an exact character
identity permits native scalar modular powering; both coordinate
recovery and the required inverses are explicit in the proof. If both
local legs close, a balanced prefix descent attempts to separate them;
a shared closing leaf is reported rather than called a factor.

Two additional saved recoveries illustrate actual partial extraction:

| Input `N` | Recovered factor | Initial local order | Order after projection |
| --- | --- | --- | --- |
| `6327961582282610561` | `2228299919` | `3413*25111` | `3413` |
| `513699397734689750848799` | `552807545971` | `18869*976571` | `976571` |

The first uses `924^2-2`, which contains `25111`; the second uses
`5647^2+1`, which contains `18869`. These private order explanations are
computed after recovery. On the structured repeated-order control
`N=232567537276409921`, the local order `8101^2` reduces to `8101` because
`90^2+1=8101`. The original linear attempt misses it.

A cubic continuation uses the fixed leaves `|i^3-2|`, `|i^3-3|`,
`|i^3-5|`, and `i^3+2`. Lean proves closure on the explicit cubic-root
class. It neither asserts a root for arbitrary primes nor conceals a
larger grid. A fresh additional recovery is
`N=9609119139727769923`: the linear, quadratic, and default Lucas attempts
miss, but the cubic projector factors out `2523901547`. The reference
local order is `11093*113761`; `1345^3-5` removes `11093`, leaving `113761`
inside the linear cover. The other local order remains the prime
`475906001`.

### Cheap growing indices and coherent-root extraction

For a fixed seed `s`, let `e_i=D_i(s,1)` be the Dickson/Lucas sequence.
Instead of materializing its exponentially large integer values, generate
the group sequence by

$$
g_0=a^2,\qquad g_1=a^s,\qquad
g_{i+2}=g_{i+1}^{s}g_i^{-1}.
$$

Lean proves `g_i=a^(e_i)`. With fixed seeds, generating each next point
requires a bounded number of group operations. This supplies cheap
access to large exponents, but not universal collision coverage. The
default pair is `5,7`; the identity `D_i(7,1)=D_(2i)(3,1)` also demonstrates
why some apparent aliases are globally coherent and yield no factor.

The saved nominal 64-bit control
`N=8562316804979989201` is recovered using this recurrence. Its recovered
factor `3649327547` has actual projected prime period `1824663773`, about
891 times the old `B^2` cover. This is an individual long-prime recovery,
not a general 891-fold speedup.

Two exact extraction improvements preserve information lost by scalar
trace folding. If a shared trace combines equality on one local leg
with inversion on the other, imaginary differences or sums can still
yield a proper GCD. Globally identical scalar roots are deduplicated;
at most four distinct norm-one representatives share a trace for an odd
squarefree semiprime. When a target equals one global root, evaluate

$$
F'(t)=\prod_{r\ne t}(t-r)
$$

to remove that coherent factor while retaining additional local
collisions. Lean proves the polynomial identity over a commutative ring,
without a field assumption. This avoids repeatedly scanning an entire
list of coherent roots.

### Replay and limitations

The final replay uses fresh seed `2026100273`, with eight balanced inputs
of each exact size 48, 64 and 80 bits. Map constants and default Lucas
seeds were fixed before generating that corpus. The combined stopping
policy was assembled after the individual-method replay, so its result
is not an independently held-out portfolio evaluation. Each actual
combined run charges all attempted preparation and extraction work,
stopping at the first proper factor.

| Population | Cases | Linear | Quadratic projection | Lucas `5,7` | Actual combined |
| --- | --- | --- | --- | --- | --- |
| Structured declared classes | 9 | 0 | 6 | 1 | 9 |
| Saved two-rough cardinality envelopes | 10 | 7 | 9 | 6 | 9 |
| Saved four-rough controls | 3 | 0 | 0 | 1 | 1 |
| Fresh balanced inputs | 24 | 18 | 20 | 13 | 23 |

The combined order is linear, quadratic, Lucas, cubic. Standalone cubic
attempts recover all three constructed cubic controls. Other combined
recoveries may stop before cubic; standalone cubic hit rates are not
inferred for those rows. The remaining fresh miss is
`N=9710106156230271983`, whose two actual projected periods are the primes
`442912871` and `913470307`. The saved two-factor population also retains
one miss, `N=380307690410407004392769`, with actual local orders
`95971*1012513` and `65229376777`.

Timings are single full calls with warm imports in a shared environment,
including setup, projection, points and polynomial work. Across the 24
fresh inputs, the combined calls total about 8.82 seconds, compared with
7.86 seconds for linear alone: the added recoveries do not establish an
overall runtime improvement. There is no tuned classical comparison.
The JSON preserves corpus, outcomes, counters, timing protocol and
source hashes.

### Why the nominal 80-bit control defeats these maps

The deliberately four-rough control is

$$
N=477209897193541203289441
 =661911275027\cdot720957498683.
$$

Its factors each have 40 bits; the product has 79 bits despite the
historical nominal 80-bit label. Both factors are safe primes, both are
`11 mod 24`, and their ratio is about `1.0892`. All four natural group
cardinalities have a tiny smooth part followed by just one large prime:

| Cardinality | Exact factorization | Prime residual / `B^2` |
| --- | --- | --- |
| `p-1` | `2*330955637513` | about 4235 |
| `p+1` | `12*55159272919` | about 706 |
| `q-1` | `2*360478749341` | about 4613 |
| `q+1` | `12*60079791557` | about 769 |

Here `B=8840` and `B^2=78145600`. All four residuals are prime. The
cross-cardinality GCDs are only `2,2,2,12`; preprocessing removes the
small shared structure and leaves distinct long prime periods. The
saved 16-colour diagnostic therefore has no short-period choice.
For the current split-colour base, the actual projected orders are
`330955637513` and `360478749341`.

This is a proved obstruction to quadratic partial extraction on these
orders: every leaf is positive and at most `B^2+5`, so its product is
coprime to each long prime period. The Lean theorem
`long_prime_order_survives_quadratic_projection` says the order remains
unchanged. The fixed cubic and Lucas attempts also miss this control.
A reference-only enlargement to 528 seed pairs on each of the four
private periods finds no noncoherent equal/inverse alias at this width;
globally coherent aliases are excluded. That finite experiment is not
a lower bound for other maps or all factoring algorithms.

The existing
[long-period audit](semiprime-long-period-audit.json) records a useful
contrast: the first Suyama elliptic curve, `sigma=6`, factors out
`661911275027`, with projected local point annihilator `20873`, well
inside `B^2`. The four-rough property constrains the current multiplicative
and norm-one groups; it does not constrain every elliptic-curve order.
This control is therefore diagnostic of our chosen group families, not
evidence of intrinsic factoring hardness. The private factorizations in
this diagnosis are not cheaply available input to recovery.

Power/Dickson continuation and fast product/remainder factoring are
classical; see
[Brent–Kruppa–Zimmermann](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf).
The present contribution is the explicit partial-order classes, exact
orientation/coherent-root handling, implementation and replay. Universal
coverage is still missing. A bound on attempted work with budget
exhaustion does not prove factoring every semiprime in one-sixth time.

Scoped validation passes: 528 recurrence identities, shared-prefix
descent, imaginary orientation, a repeated-coherent-root cost regression,
and two derivative-stripping controls. The 23 new Lean theorems build
with warnings as errors, and the scoped 14-linter pass reports no errors.
The checked critical declarations use only standard Lean axioms; there
are no admissions or computation axioms. This does not yet verify the
whole Python program or its bit-operation complexity. The optional
module is not imported by the RH umbrella and the probe is not run in
ordinary CI.

Optional replay, from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_rough_projection.py validate
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_rough_projection.py factor 477209897193541203289441
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_rough_projection.py probe --output docs/semiprime-rough-projection-audit.json
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeRoughProjection --wfail
~~~

## October 2, 2026: public-input group selection with a dyadic tournament

The new optional
[group-selection implementation](../scripts/probe_semiprime_group_selection.py)
chooses a useful elliptic-curve probe from the input `N`, without consulting
the reference factors or hidden group orders. The reproducible
[53-input audit](semiprime-group-selection-audit.json) includes the source
hashes, every attempted curve/width, operation counters, factor certificates,
timing samples and independent single-curve reference replays.

Here “best group” has a precise, limited meaning: the first certified factor
at the smallest successful probe width in the fixed menu
`sigma=(6,11,7,8)`. It does not mean the elliptic curve with the smallest
group cardinality, the cheapest runtime, or the optimum among all curves.
The selector discovers a useful group during recovery; it does not obtain
the hidden order as free preprocessing.

### Public algorithm and the formal guarantee

At each width `W=16,32,64,...`, followed by the exact one-sixth-budget cap
if necessary, try every menu curve before increasing the width. Construct
the Suyama point and Montgomery parameter from the public sigma. Setup
denominators and the discriminant are GCD-tested, so an early failure may
itself expose a factor. Incrementally project by prime powers for newly
admitted primes `ell<=W`, taking each power up to the public bound
`N+2*isqrt(N)+3`. Baby/giant cover collisions are then batched with the
existing polynomial product/remainder machinery. Full-GCD coherent roots
are handled using the earlier derivative-stripping recovery. Setup,
projection, failed curves, repeated covers and recovery are all charged.

[SemiprimeGroupSelection.lean](../RiemannGaussian/SemiprimeGroupSelection.lean)
proves the reusable finite-menu policy:

- `tournament_sound`: every returned checked GCD is a proper divisor.
- `search_minimum_scale`: an ordered search chooses a width no larger
  than any successful candidate's width in the tested menu.
- `dyadic_tournament_guarantee`: if a menu candidate has a successful
  checked residue at `W=b*2^k`, the tournament returns a proper divisor at
  width at most `W`, and its sum of visited cover widths is at most
  `2*m*W`, where `m` is the menu size.
- `capped_coverWidth_bound`: appending a final truncated cap costs at
  most `3*m*cap` in the same cover-width measure.

The successful-probe premise is explicit. These are guaranteed policy and
certificate statements, not an assertion that every semiprime has a useful
curve in the menu. Cover width is a work proxy, not the complete program's
bit-operation count. The module also proves that the projective collision
signal and polynomial Montgomery addition/doubling formulas commute with
ring homomorphisms, and checks the hard control's concrete GCD certificate.
It does not yet verify the full Python implementation or the elliptic-curve
group-law interpretation of every recurrence.

### Same-menu benchmark and held-out results

The exploratory sample has eight balanced semiprimes at each of 48, 64 and
80 exact input bits, seed `2026100281`. The separate held-out sample uses
the same sizes with seed `2026100287`. The curve menu and initial width
were fixed before exploratory generation. A capped-pilot variant was
selected on exploration and frozen before generating the held-out sample:
try the menu through width 128, give sigma 6 an extra width-256 probe, then
fall back to the old staged sigma-6 pass.

The stronger comparison is against the previous staged ECM on precisely
the same four curves, sequentially. Its isolated function namespace makes
one recorded substitution, `sigma=curve_index+6` to
`sigma=curve_index+curve_start`, leaving the old arithmetic, projection
bound, staged target batches and recovery unchanged. This baseline was
added after the initial analysis; the recovery menu and pilot parameters
were not retuned. It is distinct from the new implementation's full-cover
fixed-menu control, which is also saved in the audit.

Each table time is the sum of per-input median full-call timings from
three calls, rotating method order with imports warmed. All algorithm
setup and failed probes are included. Reference generation, validation
replays and JSON writing are excluded. A budget-exhausted run contributes
to the total work but is not reported as a successful factor time.

| Sample | Method | Factors recovered | Sum of medians |
| --- | --- | --- | --- |
| Exploratory, 24 | Old staged sigma 6 | 21/24 | 4493.31 ms |
| Exploratory, 24 | Old staged same menu | 24/24 | 4601.24 ms |
| Exploratory, 24 | Adaptive tournament | 24/24 | 6060.06 ms |
| Exploratory, 24 | Capped pilot + sigma-6 fallback | 23/24 | 5043.18 ms |
| Held-out, 24 | Old staged sigma 6 | 23/24 | 3234.06 ms |
| Held-out, 24 | Old staged same menu | 24/24 | 5051.39 ms |
| Held-out, 24 | Adaptive tournament | 24/24 | 1727.31 ms |
| Held-out, 24 | Capped pilot + sigma-6 fallback | 24/24 | 1982.79 ms |

The tournament is about **2.92 times faster on the held-out same-menu
comparison**, with equal coverage. It is about **31.7% slower on
exploration**, again with equal coverage. On the 23 held-out inputs that
old sigma 6 already factors, the aggregate comparison is almost equal:
1668.72 ms for that baseline versus 1660.05 ms for the tournament. Much of
the held-out benefit is avoiding an expensive failed group before finding
a useful one. This is evidence for useful online group selection, not a
universal speedup or a new factoring exponent. The capped pilot does not
uniformly remove the tournament overhead, and can miss a curve found by
the full tournament.

The five saved regressions give a more concrete picture:

| Input `N` | Old staged same menu | Tournament | Chosen sigma / width |
| --- | --- | --- | --- |
| `49065649` | 0.57 ms | 0.65 ms | 6 / 16 |
| `8562316804979989201` | 129.48 ms | 95.66 ms | 11 / 256 |
| `477209897193541203289441` | 247.72 ms | 87.28 ms | 6 / 256 |
| `9710106156230271983` | 69.57 ms | 10.22 ms | 11 / 32 |
| `380307690410407004392769` | 6.72 ms | 42.84 ms | 6 / 128 |

The four-rough control is about **2.84 times faster** than the old same-menu
pass. The earlier rough-projection miss `9710106156230271983` is about
**6.81 times faster**. The last row is a substantial slowdown and must be
kept when assessing whether the selector is reliably useful.

On the four-rough control, independent public-input single-curve replays
give first successful widths 256, 512, 8192 and 4096 for sigmas 6, 11, 7
and 8 respectively. The selector visits cover widths totaling 1216,
below the formal bound `2*4*256=2048`. The successful x-coordinate alias
has baby multiplier 137 and giant multiplier `81*256`. On the public
projected point, the difference multiplier 20599 yields GCD 1, while
the sum multiplier 20873 yields factor `661911275027`. The saved signal
`474427418761119040057631` has that exact GCD with `N`; Lean checks this
certificate. A first successful width is an observed cover scale with
changing smooth projection, not a claim about the exact group order.

### What cheap colour does and does not reveal

A supplementary in-memory probe on the same control holds `A24` fixed
and tries affine x-coordinates 2, 3, 5, 7 and 11. For the corresponding
curve/twist choice, compute the public unit
`B_x=x*(x^2+(4*A24-2)*x+1)` and its Jacobi sign modulo `N`. The signs are
`+1,-1,+1,+1,-1`; first successful widths are respectively
`256,4096,256,256,256`. Thus x=3 and x=11 have the same cheap Jacobi colour
but very different useful scales in this example. This exploratory
diagnostic is not a formal impossibility theorem. It says that this colour
alone does not identify the best tested point for this input; the public
collision probes provide substantially more information.

The menu remains grounded in classical ECM. Suyama sigma 11 has useful
torsion statistics for certain prime congruence classes, as studied in
[Barbulescu–Bos–Bouvier–Kleinjung–Montgomery, Finding ECM-Friendly Curves](https://eprint.iacr.org/2012/070.pdf).
That is a curve-selection prior, not a pointwise optimality theorem.
The x-only arithmetic follows the framework described by
[Costello–Smith, Montgomery curves and their arithmetic](https://arxiv.org/abs/1703.01863),
and polynomial continuation is classical; see
[Brent–Kruppa–Zimmermann](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf).
The present result is an implementation, a controlled comparison and a
formal search-policy guarantee over these group choices.

### Validation and the next mathematical gap

The audit checks 10 curve setups, 230 scalar-ladder recurrences against
the previous implementation, six small proper-factor cases, 1098 width
schedules and two shared-root regressions. All four saved source hashes
match the final files. The new optional Lean module has 23 theorems and
builds with warnings as errors; its scoped 14-linter pass reports no
errors. The audited critical proofs use only standard Lean axioms. The
module is outside the RH umbrella and the numerical replay is not part
of ordinary CI.

Optional commands from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py validate
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py factor 477209897193541203289441
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py factor 477209897193541203289441 --hybrid
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py probe --repeats 3 --output docs/semiprime-group-selection-audit.json
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeGroupSelection --wfail
~~~

The target of guaranteed one-sixth factoring for every semiprime remains
open. The immediate gap is a useful-group existence or prediction theorem:
why should a cheaply searched menu contain a separating probe within the
budget on every input? A minimum-width theorem conditional on such a hit
does not supply it. Also outstanding is complete bit-complexity accounting
for smooth projection, polynomial batches and shared-root recovery.
Further experiments should test input-derived ranking signals against
this same-menu baseline, retain failed and slow inputs, and keep ranking
cost inside the recovery budget. The current small shared-environment
timings are not a comparison with a tuned production GMP-ECM build.

## October 2, 2026: useful-group coverage, exact counterexamples and a guaranteed prefix

The next requirement is coverage on **every run for every semiprime**, with
numeric-input budget `B=ceil(N^(1/6))`. Successful samples alone cannot
provide that guarantee. The new
[coverage module](../RiemannGaussian/SemiprimeGroupCoverage.lean),
[public-input probe](../scripts/probe_semiprime_group_coverage.py) and
[coverage audit](semiprime-group-coverage-audit.json) separate a sufficient
period criterion, exact failures of the current menu, an unconditional
small-factor population and the remaining curve-generation problem.

### Exact menu failures, including a separated control

The four-curve menu `(6,11,7,8)` passes an additional 599 balanced examples
at 24, 32, 40 and 48 bits, generated with seed `2026100293`. That exploratory
scan ran in memory. A targeted known-prime diagnostic then found actual
menu failures; its deterministic generation and public replay are saved.

| Control `N` | Reference primes | Width cap | Original four curves | B-step Fermat | Extended menu |
| --- | --- | --- | --- | --- | --- |
| `62108022589` | `248909`, `249521` | 63 | exhausted | first test recovers `248909` | sigma 13, width 16 |
| `46840800959` | `203653`, `230003` | 61 | exhausted | all 61 tests exhausted | sigma 12, width 16 |

Both controls also exhaust the complete quadratic integer prefix because
their factors are above `B^2`. The first control is near a square, so it is
not a difficult factoring example for Fermat. The second has first Fermat
centre `216428` and factor-pair centre `216828`, 400 increments apart. It
therefore remains outside the **current B-step** near-square window.
These finite examples are failures of the specified budget/menu, not
asymptotic lower bounds for arbitrary factoring methods or larger constants.

On the first control the reference residual point periods are:

| Sigma | Modulo `248909` | Modulo `249521` |
| --- | --- | --- |
| 6 | 5189 | 20719 |
| 11 | 20789 | 20873 |
| 7 | 20773 | 5189 |
| 8 | 20753 | 6949 |

Every period is above `63^2+63=4032`; neither equality nor inverse cover
leaves can reach them. Reference orders are computed only after supplying
the known prime to a separate finite-field diagnostic. They never enter
recovery. For both controls, the audit also computes the actual public
projective leaf products at every original curve/width and checks GCD 1,
with all coordinate denominators units. Thus these are exact replayed
implementation failures rather than noisy estimates of smoothness.

The first reference search checks 1174 distinct primes in
`[3*64^3/4,64^3)`, seed `2026100299`; the second checks 1708, seed
`2026100311`, and additionally requires failure of the public B-step
Fermat test. Both deliberately construct adversarial inputs. Their private
prime inspection is diagnostic work, not an available algorithmic signal.
The extended menu `(6,11,7,8,9,10,12,13)` was chosen after inspecting the
first control. It fixes these two examples but has no universal coverage
theorem. The original selector and its previous benchmark remain unchanged.

### The useful-period criterion is weaker than coprimality

For the two projected local point periods `r_p` and `r_q`, a sufficient
target is

$$
\min(r_p,r_q)\le B^2,
\qquad r_p\ne r_q.
$$

`smaller_period_separates` and `unequal_small_periods_have_cover` prove
that a smaller positive period supplies a separating power; coprimality
of the two periods is unnecessary. Crucially,
`smaller_period_has_two_orientation_cover` retains both x-coordinate
orientations. If the smaller period is below `B`, a baby identity
separates. Otherwise write it as `B*j+i`, with `1<=j<=B`, `0<=i<B`.
The selected group closes in the inverse orientation, while the other
group closes in neither orientation: its possible difference exponent
`B*j-i` is positive and below its period, and the sum exponent is the
smaller period. For `i=0` this is a separating giant identity.

Conversely, `same_period_coherent_aliases` proves that equal periods make
all integer-exponent aliases coherent, including inverse channels. Thus
finding a small period alone is insufficient; the other component must
separate. These are generic group theorems. The full elliptic-curve
group-law interpretation of the Python formulas remains outside this
formal module, as in the earlier selector work.

### A population with unconditional coverage

The new public `prefix` command constructs the degree-B polynomial

$$
P_B(X)=\prod_{i=0}^{B-1}(X-i)
$$

and evaluates it at `B,2B,...,B^2` with the existing product/remainder-tree
code. These B evaluations jointly cover all positive integers through
`B^2`. It constructs neither the length-`B^2` factorial nor a factor table.
This is classical Strassen-style batching, not a new algorithmic exponent.

`descending_block_eq_polynomial`, `prefix_rows_eq_factorial` and
`prefixProduct_eq_factorial` prove the exact joined polynomial identity.
`polynomial_prefix_recovers_under_sixth_budget` proves that for every
semiprime `N=p*q`, `p<=q`, with `B>=4`,

$$
(B-1)^6<N,\qquad p\le B^2
\quad\Longrightarrow\quad
\gcd\!\left(N,\prod_{j=1}^{B}P_B(Bj)\right)=p.
$$

The larger prime is automatically above the covered prefix at this budget,
so the separating condition has no additional arithmetic hypothesis.
`failed_prefix_excludes_small_prime` proves that a coprime complete prefix
rules out every prime factor at most `B^2`. Consequently the group search
only needs to handle the remaining larger-factor population.

Twelve fresh samples, seed `2026100307`, use 12-, 16- and 20-bit smaller
primes with a larger prime chosen above `p^2`. All twelve are recovered by
the public prefix at their computed width, on inputs of 36–61 bits. The
reference factors only verify the mathematical coverage premise afterward.
Polynomial work and setup are included in the recorded time and counters.
The formal proof gives exact coverage and GCD soundness; it does not yet
verify the whole Python implementation or its bit-operation complexity.

### Universal arithmetic order targets exist; cheap realisation is missing

`smaller_factor_le_cubic_width` proves `p<=B^3` from `p<=q` and
`p*q<=B^6`. For the remaining range `B^2<=p<=B^3`, set

$$
D=2^{\lceil\log_2 B\rceil},\qquad
c=\lfloor p/D\rfloor+1,\qquad M=Dc.
$$

`dyadic_hasse_order_target` proves

$$
B\le D<2B,\qquad
0<c\le B^2+1,\qquad
p+1\le M\le p+1+2\lfloor\sqrt p\rfloor.
$$

`semiprime_hasse_order_target` supplies a small-cofactor Hasse candidate
for every smaller factor under the sixth-root budget; small factors can
use trace zero. `projected_candidate_order_bound` proves that an actual
point order dividing `M`, after an exponent containing `D`, fits a padded
width-`B+1` cover. The useful-order target is thus precise rather than an
unspecified smoothness wish.

For the first control, the candidate orders are `248960=64*3890` and
`249536=64*3899`, with traces `-50` and `-14`. Classical finite-field order
realisation is described by Deuring–Waterhouse; see Theorem 6.8 of
[Kowalski, Analytic problems for elliptic curves](https://people.math.ethz.ch/~kowalski/analytic-pbs.pdf)
and [Waterhouse's original classification](https://numdam.org/articles/10.24033/asens.1183/).
That curve-realisation theorem is **not formalised or imported here**.
In particular, the Lean Hasse-target theorem is arithmetic existence, not
a claim to have constructed a useful public curve.

The obstacle is algorithmic access: the expression uses the unknown `p`.
A curve or CRT lift designed with private prime knowledge is circular for
factoring. Prescribed-order construction literature also has a different
input specification; for example
[Bröker–Stevenhagen](https://arxiv.org/abs/0712.2022) constructs a field and
curve from a given prime target order. It does not provide a cheap public
constructor over our unknown factor field.

`fixed_divisor_cubic_gap` makes the scaling issue explicit: a fixed
guaranteed torsion divisor does not by itself bound the residual by `B^2`
when the original order is on the cubic scale. Growing smooth structure,
or a guarantee of hitting it, is required. Also,
`period_preserved_by_coprime_kernel` proves that a group homomorphism with
kernel killed by an exponent coprime to the point period preserves that
period exactly. Isogeny-like changes satisfying this condition cannot
shorten the obstructive rough period. This does not exclude genuine
changes of curve or twist that alter the local order.

### Exact frontier and checks

The remaining universal target is an input-derived public family, of at
most polylogarithmically many affordable candidates, guaranteed to produce
unequal projected local periods with a minimum inside the cover for every
remaining semiprime. The dyadic tournament already controls selection
overhead once such a candidate exists. Its existence and cheap construction
are still open. No universal one-sixth claim follows from these examples,
from expected ECM smoothness, or from the Hasse candidate alone. Compare
the explicit conjectural one-sixth framework of
[Umans–Wang](https://arxiv.org/abs/2511.10851); its structured difference-cover
premise is also a genuine additional requirement.

The new module's focused warning-as-error build, 14 namespace linters and
all-public standard-axiom audit pass. The numerical replay checks both
menu failures, the expanded-menu recovery certificates, every recorded
public projective cover, reference-period reductions and all twelve
guaranteed-prefix cases. The optional code and Lean module remain outside
the RH umbrella and ordinary CI. No source from the RH proof campaign or
the previous group selector is changed.

Optional commands from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py prefix 46840800959
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py fermat 46840800959
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py curve 46840800959
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py probe --output docs/semiprime-group-coverage-audit.json
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeGroupCoverage --wfail
~~~

## October 2, 2026: public point rotation and a cheap product-colour selector

The new [point-rotation module](../RiemannGaussian/SemiprimePointRotation.lean),
[optional implementation](../scripts/probe_semiprime_point_rotation.py) and
[replay audit](semiprime-point-rotation-audit.json) test a cheaper change of
local group before constructing another Montgomery curve. Curve setup is
shared across starting points. Each point still pays its own smooth
projection and polynomial collision batches. Hidden factors and local
orders never enter recovery.

The target remains a deterministic, every-run guarantee for **every**
semiprime at numeric-input cost `Õ(N^(1/6))`. A bounded search that can
return exhaustion is not that theorem. This scaling would improve the
published deterministic one-fifth benchmark on semiprimes; it would not
asymptotically beat GNFS's standard heuristic subexponential scaling. See
[Harvey–Hittmeir](https://arxiv.org/abs/2105.11105) and
[Bernstein–Lenstra's GNFS analysis](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf).

### Point rotation fixes both existing menu failures

The existing Montgomery x-only formulas work with a different starting
point on the corresponding curve/twist without changing `A24`; see
[Costello–Smith](https://arxiv.org/abs/1703.01863). The public point fixes are:

| Input | Sigma | Affine x | Successful width | Factor | Exact GCD signal |
| --- | --- | --- | --- | --- | --- |
| `62108022589` | 11 | 3 | 16 | `248909` | `2497552906` |
| `46840800959` | 6 | 2 | 16 | `203653` | `21203535748` |

`first_control_point_signal` and `separated_control_point_signal` check
these proper-divisor certificates in Lean. The optional implementation
first keeps the original four Suyama points and then tries the three
additional public points `(6,2)`, `(11,2)`, `(11,3)`. Its default policy
exhausts the original menu before using this fallback.

The exact finite-field diagnostics explain why the points matter. On the
first input the sigma-eleven curve has projected cardinality quotients
`199` and `10357` over the two reference primes, while its twists have
quotients `20789` and `20873`. The original Suyama point selects the two
twists. On the second input the sigma-six curve at the smaller prime has
quotient `227`, while its twist has `16993`. An alternative point exposes
the small channel. These cardinalities are computed by finite-field
enumeration with **known reference primes**, solely for diagnosis. The
elliptic group-order interpretation is not yet a Lean-verified certificate.

### Preserve the successful baseline instead of interleaving blindly

The fixed point menu was chosen on those two failures before a fresh
32-input sample, seed `2026100323`, with input sizes 23–48 bits. Every call
uses three repeats; totals below sum per-input median times in this shared
development environment.

| Policy | Fresh successes | Total median time | Additional-point hits |
| --- | --- | --- | --- |
| Original four-point tournament | 32/32 | 104.36 ms | — |
| Original pass, then fixed-point fallback | 32/32 | 104.62 ms | 0 |
| Interleaved seven-point tournament | 32/32 | 123.19 ms | 1 |
| Original pass, then colour-selected fallback | 32/32 | 104.56 ms | 0 |

Interleaving costs about 18% more overall. Its one improvement reduces
the observed width from 64 to 32 on `137894683731943`, but the additional
work on the other inputs outweighs that saving. This is retained as a
negative result. The fallback policies preserve every original operation
counter, selected sigma and successful width whenever the baseline succeeds;
the audit asserts this. Small wall-time differences between those policies
are measurement noise, not a claimed speedup. The colour policy was designed
after the adversarial control below; these 32 already-successful inputs
do not test its rescue rate on unseen menu failures.

### A new exact palette failure

The private-prime diagnostic finds

$$
N=71739148259=252983\cdot283573,
\qquad B=\lceil N^{1/6}\rceil=65.
$$

`point_menu_miss_semiprime_and_budget` checks both primes, the product,
`64^6<N<=65^6`, and that both factors exceed `65^2`. The public replay
exhausts the original four points and all three additional points. All
28 actual projective cover products have GCD one, and every sampled
coordinate denominator is a unit. These products and projected starting
coordinates are saved; they are computational trajectory checks rather
than a formal verification of the entire Python program.

The complete `1..65^2` additive prefix and all 65 bounded Fermat tests
also miss. Fermat starts at 267842, whereas the factor-pair centre is
268278. This is a failure of these specified menus and budgets, not an
asymptotic lower bound. The eight-curve extension recovers `283573` at
sigma 9, width 16.

Generation is reproducible: the first reference search uses seed
`2026100337`, width 64, and finds `252983` after 2772 distinct primes.
The second uses seed `2026100351`, width 72, and finds `283573` after 427.
Reference-only searches are never counted as affordable algorithmic input.

### Product colour supplies a cheap, useful selection bit

For a projective point `(X:Z)` and `A=4*A24-2`, evaluate

$$
Q_A(X,Z)=XZ(X^2+AXZ+Z^2).
$$

`homogeneousColour_eq_scaled_rhs` proves exactly, for nonzero `Z` in a
field,

$$
Q_A(X,Z)=Z^4\big[(X/Z)^3+A(X/Z)^2+X/Z\big].
$$

Thus its quadratic colour agrees with the affine RHS colour without
performing a coordinate inversion. `homogeneousColour_character` checks
the multiplicative-character statement with its square-unit premise.

The public Jacobi colour is the product of the two unavailable local
Legendre colours. `product_colour_flip_exactly_one` proves that reversing
this product flips **exactly one** local sign. This makes a curve/twist
change accessible using only `N`; it does not reveal which prime changed,
nor does it assert a shorter order. An unchanged product colour can also
hide changes to both local signs, so opposite-colour selection is not a
complete substitute for the original point palette.

The optional `--colour-flip` policy first runs the original four-point
pass. After exhaustion it scans at most 32 small x-values per curve,
retaining up to two with product colour opposite to that curve's original
point. Every scan, rejected point, GCD and subsequent projection is charged.
Failure to find a requested colour within the cap stays explicit. This
policy recovers all three recorded controls. On the new palette miss it
selects sigma 7, x=2, width 32, with exact signal `38765850005` and factor
`252983`; `colour_selected_new_control_signal` checks that GCD in Lean.

The colour fallback is additional coverage, not an established performance
advantage. It takes about 45 ms on the new control after paying the failed
original pass; the sigma-nine curve extension recovers the same input
earlier. The policy remains optional and does not change the old selector.

### A uniform limitation on changing points

`projected_prime_dichotomy` and `projected_prime_order_of_ne_one` prove:
if a point order divides `h*ell`, `h` divides the public projection exponent,
and `ell` is prime, then the projected point is either the identity or has
order exactly `ell`. If `ell>B^2+B`,
`projected_prime_no_two_orientation_cover` proves both orientations of every
B-by-B cover leaf miss for every nonidentity projected point. This is
uniform across starting points, rather than a finding about a few examples.

For instance, the two sigma-seven cardinality channels at reference prime
`203653` are `8*25469` and `12*16963`, both with large prime quotients;
`separated_rough_channels` checks those primes and the numerical cover gap.
Changing a point within either projected population cannot produce a
shorter **nonidentity** period. It can still hit the identity and separate
the other component, or switch to a different local group. Neither event
is guaranteed by its public colour alone.

This is the remaining mathematical coverage target: guarantee an
affordable candidate whose actual local periods separate and fit the
cover, or provide a genuinely different structured extraction for the
remaining long-prime population. Colour gives cheap access to one bit of
local group selection. It does not supply the missing every-semiprime
order bound, and these results do not establish universal one-sixth time.

### Validation and optional replay

The twelve public theorems have a focused warning-as-error build, scoped
declaration lint and standard-axiom audit. The optional replay checks
the three control certificates, all 28 new-failure cover products, both
reference generators, all fresh successes and preservation of the original
cost counters. Four recorded source hashes match the final files. Full
Montgomery group-law correctness and whole-program bit-complexity remain
outside these certificates. The module stays outside the RH umbrella and
ordinary CI.

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_point_rotation.py factor 62108022589
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_point_rotation.py factor 71739148259 --colour-flip
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_point_rotation.py probe --repeats 3
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimePointRotation --wfail
~~~

## Open questions and next experiment criteria

1. Decode the available modular factor-sum signal with better scaling.
   Explore shared collision work across weighted sums and factor-ratio
   windows, comparing with published deterministic `N^(1/5)` methods.
   The sparse binomial observable now gives an exact target: find a cheap
   evaluator that does not materialise a square-root-length truncation.
   Compact rounded-centre descriptors need both cheap exception generation
   and an exact shared collision-product evaluator before an exponent claim.
   The new order-separation pass supplies actual one-sixth-budget extraction
   on an explicit population; the remaining target is cheap information
   from long rough periods. The new Dickson/quadratic alias reaches two
   four-rough controls; its coverage beyond the linear interval needs a
   quantitative theorem. Compare any expanded map family with the newly
   implemented one-curve pass, charging all finite-difference and polynomial
   work. More colours or a constant-factor phase saving alone do not pay
   the generic gap.
2. Test whether a signed or multiscale filter can cancel unwanted
   coefficients while preserving a measurable factor-imbalance signal.
   Specify its evaluation cost and leakage control before calling it a
   factoring algorithm.
3. If revisiting nearby-prime operations, compare the same trial budget
   against matched gap bases and standard modular-factor methods. Include
   the cost of locating all auxiliary primes.
4. Any promising numerical result needs held-out inputs, no hidden factor
   tables, an explicit factor interval and exact divisibility verification.
   A formal measurement theorem and a cheap measurement algorithm are
   separate requirements.
5. Benchmark any improved method against suitable conventional methods at
   meaningful input sizes. Account for cache state, precomputation,
   precision, failure rate and total runtime.

## October 2, 2026: both hidden colour branches and lazy acquisition

The next investigation tested the selector on inputs deliberately built
from original-point misses, rather than relying only on fresh cases that
the original menu already solves. It found a specific information loss:
unchanged public product colour can hide reversal of **both** private local
curve/twist choices. A useful point can consequently be excluded by an
opposite-colour-only policy.

The new optional
[public implementation](../scripts/probe_semiprime_colour_coverage.py),
[exact replay audit](semiprime-colour-coverage-audit.json) and
[focused Lean module](../RiemannGaussian/SemiprimeColourCoverage.lean)
preserve the earlier prototypes. They supply a colour-diverse fallback
and cheaper acquisition of the same opposite-colour menu. They do not
establish an all-input sixth-root factoring bound.

### A same-colour point recovers the excluded branch

The finite control is

\[
N=494041\cdot494191=244150615831,
\qquad B=\lceil N^{1/6}\rceil=80.
\]

The original four-point menu and its opposite-colour fallback both exhaust
their full budgets. The existing fixed-point fallback succeeds on sigma
eleven at affine `x=3`, width 32, with certificate

\[
\gcd(244150615831,10273242508)=494191.
\]

On this curve, the original point has private RHS colours `(-1,+1)` while
the successful point has `(+1,-1)`. Both public Jacobi products are `-1`.
The opposite-colour selector instead chooses `x=2,4`, both with private
colours `(+1,+1)`. Private Legendre evaluations appear only in the labelled
known-prime explanation; the public algorithms receive only N.

`product_colour_same_both_or_neither` proves the exact sign classification:

\[
\epsilon_p\epsilon_q=\epsilon'_p\epsilon'_q
\Longrightarrow
(\epsilon'_p,\epsilon'_q)=(\epsilon_p,\epsilon_q)
\quad\text{or}\quad
(\epsilon'_p,\epsilon'_q)=(-\epsilon_p,-\epsilon_q).
\]

Together with the earlier `product_colour_flip_exactly_one`, this accounts
for every hidden branch. It does **not** mean that acquiring both public
colours guarantees acquiring both local sides: two points with colours
`(+1,+1)` and `(+1,-1)` already cover both public products while leaving
the first field's side unchanged. Nor does any colour bit determine a
projected period.

`same_colour_control_signal` checks the proper-divisor certificate in Lean;
`same_colour_control_semiprime` checks the primes and budget arithmetic.
This control is near a square: the first Fermat centre is 494116 and
`494116^2-N=75^2`. Thus it also has an exceptionally cheap classical
solution. The control establishes a selector failure and its repair,
not superiority over Fermat or intrinsic factoring difficulty.

### Two public policies, with every attempted point charged

Both new policies run the original four points over the complete dyadic
width schedule first. On failure, they acquire each curve's new menu only
when that curve is reached. A successful early probe therefore avoids
scanning later curves. Immutable curve setup is reused, with a separate
smooth-projection history for every point.

The lazy opposite policy retains the first two opposite-colour affine
points found in `x=2..33`, exactly the previous menu. The optional
`--diverse` policy retains those same two points plus the first same-colour
point, in scan order. It handles the new control without a factor, private
character, or group-order oracle. A same-colour point need not reverse
both local signs, so a fixed scan still has explicit failure cases.

Every setup, rejected candidate, GCD, Jacobi test, projection and polynomial
batch is charged. Each policy still has only a fixed number of curves and
points, with maximum width B. This preserves the earlier partial-pass
operation scale; it does not prove that a successful group exists for every
input. The diverse option is not made the default.

### Adversarial replay and fresh controls

The explicitly private generator first tests known primes against the
four original points at a reference width. Seed `2026100367`, width 80,
finds 11 misses among 8051 distinct primes in `[2^18,2^19)`. Seed
`2026100383`, width 112, finds 16 among 15766 primes in `[2^19,2^20)`.
The implementation records the seeds, random-draw limits, exact survivor
lists and diagnostic exponents, and its regeneration replay passes.

All within-cohort and cross-cohort pairs give `55+120+176=351` distinct
semiprimes, at 36--40 bits. Actual recovery uses each product's own B.
Some cross-cohort products raise B above the first reference width and
are therefore solved by the original menu. This construction deliberately
biases the corpus toward failures; it is not a random-input success-rate
estimate.

| Public policy | Factors recovered | Candidate-colour scans | Jacobi tests | Scalar bits |
| --- | ---: | ---: | ---: | ---: |
| Original four points | 60/351 | 0 | 0 | 1222502 |
| Eager opposite-colour fallback | 350/351 | 4611 | 7238 | 1706985 |
| Lazy opposite-colour fallback | 350/351 | 3078 | 5319 | 1706985 |
| Lazy diverse-colour fallback | 351/351 | 3323 | 6119 | 1848211 |

Lazy acquisition reduces candidate scans by 33.25% and Jacobi tests by
26.51%, with **identical** aggregate group and polynomial-operation
counters to the eager opposite-colour policy on this corpus. It does not
demonstrate a meaningful whole-call runtime gain: on the first 24
adversarial pairs, rotating method order over three repetitions, sums of
per-input median times are 947.887 ms eager, 948.512 ms lazy opposite and
1006.262 ms lazy diverse. The diverse option is about 6.16% slower here
and performs 8.27% more scalar bits over the full corpus. Additional
coverage is not a claimed general speedup. These are comparisons with our
own Python prototypes, not GNFS or the best available classical software.

All 32 fresh controls, seed `2026100413`, remain successful in the original
pass with identical original operation counters under both new policies.
Separate small-input checks cover 465 semiprimes with factors at most 113
under both policies, plus 16 finite scan-cap regressions. Every returned
factor is checked by exact divisibility and, where supplied, its GCD signal.

The four new Lean declarations compile with warnings treated as errors,
pass all 14 scoped declaration linters and use only `propext`,
`Classical.choice` and `Quot.sound`. The sign identities are generic;
the concrete GCD and prime assertions are kernel-checked arithmetic.
This does not certify the whole Python control flow or the elliptic group
law. Source hashes tie the replay to the new implementation, previous
rotation/selection implementations and Lean module. No RH source,
umbrella import, default CI target or repository publication artifact changes.

### The universal group guarantee is still the missing exponent step

The sufficient criterion remains unequal local projected periods with
minimum at most `B^2`. The previous
`projected_prime_no_two_orientation_cover` already proves that a nonidentity
point in a residual prime-order population with `ell>B^2+B` cannot close
either orientation in the cover, regardless of which starting point is
chosen. Colour selection helps only when another local curve/twist side or
an identity projection is useful; it does not shorten a long prime period
inside the same group.

Both a curve and its twist can have almost-prime group orders. This is
also the deliberately constructed regime called twist security in
[Costello--Smith's Montgomery-curve survey](https://eprint.iacr.org/2017/212.pdf).
The survey's curve/twist observation supplies context, not a coverage
theorem for our parameter menu. The more recent
[even-order ECM approach](https://arxiv.org/html/2503.00950) explicitly uses
GRH and a distribution conjecture in its complexity analysis; it does not
give the guaranteed every-run sixth-root estimate requested here.

The new sign theorem repairs information loss in the cheap selector; it
does not reduce the universal coverage gap. The next exponent-changing
result must either construct a small separating period at affordable cost
from N alone, or extract useful information from a long rough period without
enumerating it. Enlarging a fixed point palette and reproducing successful
samples are not substitutes for either theorem.

Focused replay, outside normal builds and CI:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_colour_coverage.py factor 244150615831 --diverse
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_colour_coverage.py probe --regenerate-cohorts --repeats 3
lake build RiemannGaussian.SemiprimeColourCoverage --wfail
~~~

## October 2, 2026: cheap high-degree evaluation and its collision partition

This investigation tested an inexpensive way to access large polynomial
degrees directly, rather than constructing another group-point menu.
The optional
[public probe](../scripts/probe_semiprime_fast_dickson.py),
[complete replay](semiprime-fast-dickson-audit.json),
[Lean proofs](../RiemannGaussian/SemiprimeFastDickson.lean) and
[scoped checker](../scripts/CheckSemiprimeFastDickson.lean)
are separate from the existing factoring policies and ordinary CI.

For the direct Dickson map `D_d(x,1)`, the exact binary updates are

\[
D_{2k}(x)=D_k(x)^2-2,
\qquad D_{2k+1}(x)=D_k(x)D_{k+1}(x)-x.
\]

They evaluate a degree with millions or trillions of terms without
expanding its coefficients: each point uses two modular multiplications
per degree bit. The generic Lean theorem `dicksonOfBits_correct` proves
both outputs of the binary circuit over every commutative ring, including
composite residue rings. This is different from the earlier experiment
`alpha^(D_d(i,1))`: here the polynomial is evaluated **directly modulo N**,
with no intermediate group exponent.

### Large degree is not the missing coverage signal

The exact fibre theorem is

\[
D_d(x)=D_d(y)\text{ in }\mathbb F_p
\iff
D_{\gcd(d,p^2-1)}(x)=D_{\gcd(d,p^2-1)}(y)\text{ in }\mathbb F_p.
\]

`dickson_prime_field_collision_gcd` proves it for every prime and all field
elements. The proof lifts a trace to reciprocal roots in an algebraic
closure, proves their exponent divides `p^2-1`, and compares the two exact
power kernels. The GCD is a reference explanation; recovery never reads
the unknown prime or this hidden field exponent. The underlying Dickson
theory is classical; see
[Bluher's primary paper](https://arxiv.org/html/1707.06877), which states the
permutation criterion. This pass does not claim to have invented Dickson
folding.

For **every** ordered odd semiprime `N=p*q`, `p<q`,

\[
\gcd(N,p^2-1)=1.
\]

Consequently degree N permutes the smaller prime field. It cannot create
new smaller-prime collisions, even though its evaluation is inexpensive.
`semiprime_degree_short_grid_no_collision` proves that the concrete
`B`-by-`B` integer grid still misses whenever `B^2<p`. This closes the
degree-N candidate for extracting information beyond that smaller-factor
prefix; it is not a lower bound for other maps or factoring algorithms.

The 5940 composite/prime-ring recurrence checks pass. All 990 ordered
odd-prime pairs below 200 reproduce the smaller-field permutation; 875
also permute the larger field. Every larger-field exception has
`p | q-1` or `p | q+1`. There are 1980 full-field collision-partition
comparisons and 336 additional cover-partition comparisons on the saved
and fresh factoring inputs; all agree with the exact GCD compression.

### A real nearby-degree recovery, but sparse coverage

The fixed public degree menu is `1,6,24,N,N-1,N+1`. Each method receives
only N, evaluates B babies and B giants, and uses the existing monic
product/remainder batch, coherent-root stripping and GCD descent.
Every fold update and batch operation is charged; an unsuccessful batch
returns explicit budget exhaustion rather than an alleged factor.

| Direct fold | Four saved controls | 24 fresh inputs |
| --- | ---: | ---: |
| Degree 1 | 0/4 | 0/24 |
| Degree 6 | 0/4 | 1/24 |
| Degree 24 | 2/4 | 1/24 |
| Degree N | 0/4 | 0/24 |
| Degree N-1 | 1/4 | 1/24 |
| Degree N+1 | 1/4 | 1/24 |

The fresh corpus uses seed `2026100441`, with eight balanced inputs at
each exact size 40, 48 and 64 bits. Degree N+1 gives a distinct fresh
recovery missed by the direct degree-1/6/24 batches:

\[
N=171033372116459=12108181\cdot14125439,
\qquad B=236,
\]

\[
\gcd(N,95291626633620)=12108181.
\]

This uses baby 207 and giant `236*41`, with 472 evaluated points and
45312 fold modular multiplications. `fresh_nearby_degree_signal` checks
the proper-divisor certificate in Lean. The private explanatory GCDs
are 420 in both fields, whereas degree N has GCD one. This demonstrates
cheap individual access to a genuine extra collision, not a guaranteed
degree selector or superiority over the existing elliptic algorithms.

Neither nearby degree recovers the saved nominal 64/80-bit four-rough
controls. Their degree N-1 collision partitions are exactly those of
degree 24; their degree N+1 partitions are exactly those of degree 2.
Thus making the degree enormous buys no extra collision pattern there.
One recovery occurs only on the small saved control, and the other on
the previously documented near-square control that Fermat solves
immediately. Those are not new hard-input milestones.

Single full-call exploratory totals on the fresh corpus are about
0.92 seconds for the direct linear batch, 0.98 for degree 24, and 1.90
for degree N+1. They include setup and polynomial work, with warm imports
in a shared environment. There is no tuned classical benchmark, timing
distribution or claimed practical speedup. The complete output retains
per-input results, proper-GCD witnesses, operation counters, private
diagnostics and source hashes. The Lean circuit and algebraic theorems
do not certify the full Python control flow or its bit complexity.

All 11 public theorems compile with warnings treated as errors. The
scoped declaration check passes all 14 linters, and the transitive-axiom
audit covers all 47 module declarations, including 37 proof declarations
with generated equations: only `propext`, `Classical.choice` and
`Quot.sound` are used. The exact finite recovery certificates and
operation-budget checks pass on all 28 saved/fresh inputs.

The remaining exponent step is precise: cheap evaluation is available,
but an input-dependent degree or other map must guarantee a **separating
collision** from N alone. A large formal degree, a hidden large GCD, or a
few successful examples does not prove such coverage. The requested
every-run, every-semiprime `Õ(N^(1/6))` theorem remains open.

Focused replay, outside normal builds and CI:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_fast_dickson.py factor 171033372116459 --degree N+1
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_fast_dickson.py probe
lake build RiemannGaussian.SemiprimeFastDickson --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeFastDickson.lean
~~~

## October 2, 2026: row batching and cancellation transferred from the RH toolbox

The new optional
[Lean module](../RiemannGaussian/SemiprimeRowStructure.lean),
[public-input implementation](../scripts/probe_semiprime_row_structure.py),
[complete replay](semiprime-row-structure-audit.json) and
[scoped checker](../scripts/CheckSemiprimeRowStructure.lean)
test whether common phases and joined cancellation can remove the cost of
constructing the weighted collision rows. The universal, every-run
`Õ(N^(1/6))` factoring guarantee remains **unproved**.

### What is shared exactly

For a unit `g`, weights `a,b`, and the literal centre
`c(a,b)=ceil(2*sqrt(N*a*b))`, write

\[
V_{a,b}=g^{aN+b-c(a,b)}
       =(g^N)^a g^b(g^{-1})^{c(a,b)}.
\]

`rowAnchor_factor` proves the shared-axis identity in any commutative
group. The centre depends only on `a*b`, so the implementation caches it
and its modular power once per distinct product. All caches are rebuilt
from public N inside the timed call; no private factors or lookup table
are supplied to the algorithm. Every literal row is still materialized.

For a rectangular four-corner test, `rowAnchor_cross_ratio` cancels the
large axis powers exactly, leaving

\[
\frac{V_{a,b}V_{a',b'}}{V_{a,b'}V_{a',b}}
  =g^{c_{01}+c_{10}-c_{00}-c_{11}}.
\]

`rowAnchor_cross_eq_iff_order_dvd` identifies exact separability with
divisibility of this centre defect by the local group order. This does
not assume that rounded centres admit an outer-product representation.
The 1402 tested admissible four-corner signals `g^defect-1` were all
units, so none yielded a factor or an exact separable block.
This finite negative audit does not rule out a different low-rank or
structured construction.

### A cheap signed collapse, and its lost hit

The strongest directly transferable RH idea was to keep a common prefix
until the cancellation is exact. Swapped weights have the same centre:

\[
\frac{V_{a,b}}{V_{b,a}}=g^{(a-b)(N-1)}.
\]

`rowAnchor_swap_ratio`, `rowAnchor_swap_difference` and
`rowAnchor_swap_sum` prove the ratio and both ring channels. If the weight
indices lie in a B-by-B grid, all normalized swapped channels depend on
only O(B) differences. The implementation tests them using one setup power
`g^(N-1)`, B repeated multiplications and 2B GCDs. No quadratic row list is
required for **these particular channels**.

However, this is exactly the already-known N-1 projected-period signal.
It removes the centre information that aligns an original row with the
target one. `swap_cancellation_does_not_preserve_hit` checks the literal
counterexample N=77, weights 1 and 2, centre 25: the anchors are 71 and 23.
The first anchor minus one gives factor 7, while both their sum and their
difference are coprime to 77. The B=`ceil(N^(1/6))` signed-collapse probes
also returned no proper factor on any of the 20 saved/fresh inputs.
This disproves replacement of the original hits by those channels, not
the possibility of a different joint cancellation.

### Retaining the boundary preserves roots

The RH masked-convolution principle is more useful here than a signed
norm saving: retain the target-one terms before joining the rows. Put
`Y=V_(b,a)` and `beta=g^((a-b)*(N-1))`. The checked theorem
`rowAnchor_swap_target_product` gives

\[
(V_{a,b}-1)(V_{b,a}-1)
  =Y^2\beta-Y(\beta+1)+1.
\]

The constant and linear boundary terms are indispensable. This is an
exact collision product, but Y still contains the coupled weighted centre.

There is also a root-preserving reciprocal fold. For any units x,y in a
commutative ring, `unit_trace_collision_factorization` proves

\[
(x^2-1)(y^2-1)
 =xy\left[xy+(xy)^{-1}-x/y-y/x\right].
\]

`unit_trace_collision_iff` proves that in each hidden prime field the
bracket vanishes exactly when `x^2=1` or `y^2=1`. It therefore retains all
target-one hits and also the target-minus-one hits. No unknown field
order or division by a nonunit is used. If both prime components hit,
the joined GCD is N and the original factors must be inspected by descent;
this is visible in the N=77 regression, where the other row reveals 11.
Reciprocal Laurent/trace folding is classical, rather than an invented
new factoring mechanism; see
[Montgomery–Kruppa's stage-two construction](https://antsmath.org/ANTSVIII/files/kruppa.pdf).

The new small-ring replay checks all these identities, unit-prefix GCD
invariance and preservation of original hits on 1860 swapped pairs.
That does not give a universal separating-hit coverage theorem or certify
the complexity of the complete Python factoring control flow.

### Which RH results carry over

- `ZetaRieszComplexNullFloor.increment_coherent_zero` motivates cancelling
  a shared prefix exactly. The row-swap lemmas implement that idea, but
  the counterexample shows why the factor target cannot be discarded.
- `ZetaRieszOrderedWard.masked_logarithmic_convolution` retains the signed
  complement of an order mask. Its lesson here is the target boundary
  in the paired product. A literal logarithmic derivative cannot be
  divided by the collision product at a factor hit: it is then a nonunit.
  Product/derivative jets must be retained without that division.
- `ZetaRieszCrossingOrbitCancellation.crossing_literal_sum_eq_zero` uses
  complete divisor orbits and affine saturated hinges. Those hypotheses
  do not hold for `g^(-ceil(2*sqrt(N*a*b)))`; unknown divisors are also not
  a cheaply supplied factoring input.
- `ZetaRieszComplexProjection.native_floor_with_credit` improves a real
  one-sided allowance. A reduced real allowance does not itself establish
  a modular collision or a proper GCD.

Thus exact product identities and retained mask boundaries are useful
transfers. Generic real-valued sign savings are not sufficient coverage
signals for factoring.

### Quantitative anchor replay

Seed `2026100463` generates four fresh balanced products at each exact
size 40, 48, 64 and 80 bits, plus four previously saved controls.
Reference prime labels come from `gmpy2.next_prime` and are used only for
generation and post-GCD validation. Every method receives only public N.
The four anchor implementations agree on all 675408 compared residues.
Each input/method is timed three times in shuffled order, after imports
are warm. Timings include geometry, centre and axis powers, and output
construction; they do **not** measure a full factorisation.

| Input bits | Native powers, ms | Shared axes, ms | Shared product centres, ms | Existing vector kernel, ms | Fewer centre evaluations |
| --- | ---: | ---: | ---: | ---: | ---: |
| 40 | 0.052 | 0.068 | 0.078 | 1.088 | 0.0% |
| 48 | 0.152 | 0.184 | 0.199 | 1.219 | 0.8% |
| 64 | 1.556 | 1.823 | 1.919 | 3.254 | 3.5% |
| 80 | 29.307 | 26.040 | 26.062 | 25.098 | 6.7% |

These are medians of per-input medians in a shared environment, not a
claimed tuned classical benchmark. At 80 bits product sharing is about
11% faster than the native per-row powers but about 4% slower than our
existing vector kernel; at smaller sizes its setup costs dominate.

All 12 public theorems compile with warnings treated as errors. The
focused check passes 14 linters and audits all 21 module declarations,
including 20 proof declarations with generated helpers: only `propext`,
`Classical.choice` and `Quot.sound` are used. No side-project module is
added to the RH umbrella or ordinary CI.

The remaining quantitative target is to process a **root-preserving**
joined product of many centre-coupled rows implicitly. Cancelling their
centres without retaining the target boundary changes the observable;
retaining them currently leaves an explicit row cost. This is precisely
where a new batching theorem, rather than another cheap scalar group
test, would have to improve the exponent. Harvey already identifies a
full square-root speedup over the Lehman `N^(1/3)` range as a possible
route to `N^(1/6)` in
[his one-fifth paper, Remark 3.4](https://arxiv.org/html/2010.05450).
No universal such batching theorem has been obtained in this pass.

Focused replay, outside normal builds and CI:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_row_structure.py --output docs/semiprime-row-structure-audit.json
lake build RiemannGaussian.SemiprimeRowStructure --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeRowStructure.lean
~~~

## October 2, 2026: implicit Cartesian batching and the literal-centre gap

The follow-up implements one root-preserving bulk operation in
[the probe](../scripts/probe_semiprime_cartesian_completion.py), with
[a complete replay](semiprime-cartesian-completion-audit.json),
[12 public Lean theorems](../RiemannGaussian/SemiprimeCartesianCompletion.lean)
and [a focused checker](../scripts/CheckSemiprimeCartesianCompletion.lean).
The every-run, every-semiprime `Õ(N^(1/6))` bit-operation guarantee remains
**unproved**. The new detector does not provide a universal separating hit,
or a cost proof for recovering a proper factor from every coherent batch.

### What can actually be batched

For two short root lists, `grid_resultant_eq` proves in any nontrivial
commutative ring that

\[
\operatorname{Res}\!\left(\prod_{a\in A}(X-x_a),
                          \prod_{b\in B}(X-y_b)\right)
 =\prod_{a\in A}\prod_{b\in B}(x_a-y_b).
\]

`grid_resultant_eq_zero_iff` proves that over either hidden prime field
this has exactly the union of the original pair collisions as its zero
set. For unit y values, multiplying by their known unit product changes
neither the zeros nor the GCD signal: the quotient target `x_a/y_b=1` is
retained. Repeated roots are retained with multiplicity. The Python replay
checks the signed resultant orientation, including odd list sizes.

`rowAnchor_separatedCentre` connects this directly to weighted rows when
the centre is **additive**, `c(a,b)=r(a)+s(b)`:

\[
V_{a,b}=\frac{g^{aN-r(a)}}{g^{s(b)-b}}.
\]

The implementation reuses the existing classical `MonicBatch` product and
remainder tree, including exact GMP-packed multiplication and monic
division. No unknown field order, factor label, or division by a nonunit
is supplied. This is an implementation and formal root-preservation
result for a classical batching method, not a new resultant algorithm.
See [Harvey's one-fifth construction](https://arxiv.org/html/2010.05450)
for the related factoring use of product polynomials and multipoint
evaluation.

### Quantitative model replay

The timed model fixes a public centre from the primitive corner
`(width-1,width)` and applies that one centre to the entire Cartesian grid.
It does **not** substitute that centre for the literal one in a factoring
algorithm. Seed `2026100487` generates fresh exact 32-, 40-, 48-, 64- and
80-bit products, plus the saved four-rough 79-bit control. Reference primes
are used only for generation and descriptive validation. Every timed call
receives public N and width, and rebuilds its input-specific roots, powers,
integer square root and GCD. Imports are warm; three repetitions shuffle
the method order.

| Input | Width | Explicit pair product, median ms | Implicit resultant, median ms | Detector speedup |
| --- | ---: | ---: | ---: | ---: |
| Fresh 80-bit | 1,024 | 212.42 | 63.34 | 3.35× |
| Fresh 80-bit | 2,048 | 849.24 | 145.67 | 5.83× |
| Fresh 80-bit | 4,096 | 3,388.56 | 323.29 | 10.48× |
| Saved 79-bit control | 4,096 | 3,385.43 | 328.68 | 10.30× |

At width 4,096 the two lists contain 8,192 residues and represent
16,777,216 pairs. The implicit path performs no pair-product loop; the
saved counters include 11,720 polynomial convolutions, 8,191 monic
reductions and 4,096 final point products. Small widths can be slower
because of setup. These shared-environment measurements compare two
evaluations of the **same model**, not two full factoring algorithms.
All 17 large benchmark configurations have GCD one; none is a new
factorisation success.

The exact regression checks 128 batches over eight small composite/prime
rings and 11,968 normalized pair identities. A separate N=77, width-two
regression has aggregate GCD 77; retaining the leaves recovers proper
factor 7 after two leaf GCDs. This tests coherent-batch handling on a toy
input, not a universal recovery bound. The timed replay represents
45,062,144 pairs per repetition and saves every input, value, counter,
timing and runtime-source hash.

### The literal curvature survives

The actual unrounded centre is

\[
c(a,b)=2\sqrt N\sqrt a\sqrt b.
\]

`realCentre_mixed_increment` proves exactly

\[
c(a,b)+c(a+h,b+h)-c(a,b+h)-c(a+h,b)
 =2\sqrt N(\sqrt{a+h}-\sqrt a)(\sqrt{b+h}-\sqrt b).
\]

This factorization is genuine structure in the curvature. It does not
make the modular exponential an additive row/column centre. For the
literal integer centre `ceil(c)`, rounding changes the mixed increment
by less than two. `roundedCentre_mixed_lower` proves, when both weights
and their increments are at most B,

\[
D_{\rm ceil}>\frac{\sqrt N\,h^2}{2B}-2.
\]

For any additive row/column fit, `separated_correction_width` proves that
if all four integer corrections lie in one interval of width W, then
`|D_ceil| <= 2W`. `sixth_regime_correction_gt_budget` therefore proves
that with `B>=4`, `N>=(B-1)^6` and step two, necessarily **W>B**.
This rules out this particular width-B flattening. It is **not** a lower
bound on all algorithms: a longer interval might itself admit sublinear
processing, and an exact nonlinear root-preserving completion is not
excluded.

The saved primitive, balanced four-corner probes show the size of that
boundary without using floating-point centres:

| Input bits | Sixth-root budget B | Mixed integer defect | Required integer correction width, at least |
| --- | ---: | ---: | ---: |
| 32 | 38 | 3,331 | 1,666 |
| 48 | 240 | 134,652 | 67,326 |
| 64 | 1,586 | 6,196,839 | 3,098,420 |
| 80 | 9,880 | 240,772,214 | 120,386,107 |

The correction cannot simply be dropped. `flattening_can_erase_hit`
checks N=77 and primitive balanced corners `(8,11),(8,13),(10,11),(10,13)`.
Their literal centres are 165, 179, 185, 201; matching the first three by
an additive fit predicts 199 at the last corner. The literal anchor is
15 and reveals factor 7, while the flattened anchor is 60 and gives GCD
one. The two omitted units erase the hit. These toy weights exceed N=77's
sixth-root budget; the example certifies failure of the identity, not a
hard-input runtime claim.

### Validation and the remaining research target

The focused build passes with warnings as errors. All 12 public theorems
pass 14 linters; the audit checks all 30 declarations, including 27 proof
declarations with generated helpers, using only `propext`,
`Classical.choice` and `Quot.sound`. The main thread has registered the
proof module in the ordinary library; numerical replay remains optional.
The original replay hashes are retained. Separate validation hashes
record the currently compiled Lean source, including edits since replay;
all executable Python runtime hashes still match the measured replay.

The next required improvement is either a cheap, **exact** batch for the
nonlinear rounded-centre detector, or an independently proved cover that
needs fewer literal rows. A real-valued cancellation or an approximate
centre is insufficient unless the target roots and proper-factor descent
are preserved. The working resultant removes a quadratic pair loop only
where separability is actually established; it does not yet remove that
loop for all semiprime inputs.

The remaining proof obligations are distinct:

1. **Literal batching:** evaluate a root-preserving detector for the exact
   rounded centres, including their coupled correction, at the target cost.
2. **Coverage:** prove that every allowed semiprime supplies a separating
   collision in the searched public-input family; the constant-centre
   benchmark currently supplies no such guarantee.
3. **Recovery:** extract a proper factor even when the aggregate GCD is N,
   with all descent and ambiguous-collision work charged.
4. **Complexity:** prove the complete every-run `Õ(N^(1/6))` bit-operation
   bound, including setup, storage, modular arithmetic and recovery.

The 10.48× model-detector timing and compiled algebra address part of the
first obligation only. They do not discharge any of the four obligations
for the literal universal algorithm.

Focused replay and checks:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_cartesian_completion.py --output docs/semiprime-cartesian-completion-audit.json
lake build RiemannGaussian.SemiprimeCartesianCompletion --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeCartesianCompletion.lean
~~~

## October 2, 2026: exact shared-root recovery and the charged construction gap

This continuation implements [an exact recovery pass](../scripts/probe_semiprime_batch_recovery.py)
and saves [the complete audit](semiprime-batch-recovery-audit.json).
The additional proofs extend the already registered
[SemiprimeCartesianCompletion module](../RiemannGaussian/SemiprimeCartesianCompletion.lean).
The terminal target remains a guaranteed every-run `Õ(N^(1/6))` bit bound
for every semiprime, including prime squares. That target is **unproved**.

### Recovery without a quadratic ambiguous-pair search

Let S be the set of distinct supplied residues modulo N and write

\[
P(X)=\prod_{x\in S}(X-x),\qquad
D_S(t)=\begin{cases}P'(t)&t\in S,\\P(t)&t\notin S.\end{cases}
\]

`deflatedColumn_eq_product` proves over every commutative ring that

\[
D_S(t)=\prod_{x\in S\setminus\{t\}}(t-x).
\]

This reuses `SemiprimeRoughProjection.derivative_strips_shared_root`;
the derivative identity itself was already proved. Distinct global
residues are required: differentiating a polynomial which still has a
repeated global root would leave an unwanted zero factor.
`deflatedColumn_map_zero_iff` proves that after reduction to either hidden
prime field the zero set consists exactly of collisions with **globally
unequal** residues. The original multiplicity-preserving resultant remains
available as a separate observable. The original roots and literal row
labels are retained by the replay.

Evaluate these columns by the existing monic product/remainder trees and
scan their GCDs. A proper column GCD is returned immediately. If a column
GCD is N, scan only that column's off-diagonal differences. Each remaining
canonical residue is strictly between zero and N. A nonunit product
therefore has a proper-divisor leaf, for any composite N, and recovery
stops after this one scan.

The main new checked statements are:

- `deflatedColumn_val_eq` and `deflatedColumn_gcd_eq`: the polynomial and
  lazy leaf callback have exactly the same modular product and GCD.
- `proper_leaf_of_product_gcd`: nonzero canonical leaves guarantee a
  proper factor whenever their product is nonunit; no semiprime or local
  order assumption is needed.
- `recoverResidueBatch_sound`: every returned value is a proper divisor.
- `recoverResidueList_succeeds_of_proper_pair`: every original proper pair
  hit survives deduplication and is recovered, irrespective of earlier
  whole-modulus equalities.
- `recoverResidueBatch_gcd_bound`: recovery uses at most
  `targets.length + S.card` GCD queries. The list version also bounds this
  by the two original list lengths.

The Python implementation uses deterministic sorting, deduplication and
merging to classify shared points; its cost discussion does not rely on
expected hash-table lookup time. P is evaluated at ordinary points and P'
at shared points. A final witness search visits at most one root list.
All polynomial, derivative, sorting, modular-difference and root-setup
work must still be charged in a bit bound. The Lean query count is not a
formal execution-cost proof for Python.

The classical product/remainder infrastructure and collision descent are
related to [Harvey's Lemmas 2.3 and Proposition 4.1](https://arxiv.org/html/2010.05450).
That collision algorithm excludes whole-modulus matches as an input
condition. The present recovery pass uses exact deflation to handle
arbitrary shared-root inputs. No novelty claim is made for polynomial
deflation or product trees.

### Exact controls and literal rows

Seed `202610020619` gives 4,769 exact comparisons against an independent
oracle which explicitly checks whether any original pair has a proper
GCD. These include every pair of subsets of size at most two over moduli
4, 6 and 9, plus 2,048 randomized lists with negative representatives,
duplicate residues, empty lists, prime squares and prime controls.
The explicit and implicit implementations agree on every deflated column
and returned factor, and every measured recovery respects the GCD bound.

Separate controls include:

- N=35, roots `[1]`, targets `[1,6]`: the first globally equal pair is
  deflated and the later proper hit recovers 5.
- N=35, roots `[1,11,15]`, target `[1]`: the deflated column is zero modulo
  N, but one lazy leaf GCD recovers 5.
- N=35, roots `[1,1,6]`, targets `[1,1]`: deduplication before
  differentiation preserves factor 5.
- N=77, 128 copies of residue 1 in each list: all 16,384 original pairs
  are whole-modulus equalities, with no proper hit. The pass correctly
  returns no proper collision after one column GCD.
- N=49, roots `[1,8,1]`, target `[1]`: the proper factor 7 is recovered.

The literal replay uses fresh balanced 32-, 40-, 48-, 64- and 80-bit
products, plus the saved 79-bit four-rough control. Every timed call
receives only N and the public widths, rebuilds its roots and points,
and retains the actual centre
`c(a,b)=ceil(sqrt(4*N*a*b))` in the anchor `2^(a*N+b-c) mod N`.
The weight cone is `1 <= a <= b <= min(2*a,width)` with coprimality
filtering. Weights and baby intervals are capped at 128 for this replay;
only the 32- and 40-bit cases use their complete sixth-root widths.

Both methods recover a factor in the 32-, 40- and 48-bit cases. The
64-, 80- and saved 79-bit cases exhaust this capped cover. This is an
exact implementation comparison within the prototype, not universal
coverage or a comparison against tuned conventional factoring software.
The shared-root benchmark separately evaluates consecutive residues in
both lists; its speedup is a detector timing, with no factor hits in those
large benchmark grids. Every timing, witness, source hash and counter is
saved in the audit, with three repetitions and shuffled method order.

### Construction still has quadratic width cost

The replay records every attempted weight pair, coprimality GCD, integer
square root, modular power, exponent-bit total and baby update. For width
B=2m or B=2m+1, its visited pair count is respectively

\[
m^2+2m,\qquad m^2+3m+1.
\]

`candidateWeights_card_lower` proves that whenever `0<t` and `4*t<=B`,
the visited cone contains a t-by-t rectangle and therefore at least t²
pairs. `candidateWeights_card_gt_width` checks that this count already
exceeds B for B>=20. With B on the sixth-root scale, the explicit weight
enumeration thus has quadratic width cost before any collision recovery.
These theorems concern this enumeration; they do not rule out a different
exact implicit construction or a smaller independently proved cover.

The new recovery theorem removes an ambiguous-collision search gap for
**supplied** lists. It does not make the centre-coupled list cheap to
construct and does not prove that every semiprime has a proper hit.
Whole-modulus weighted matches may also carry discriminant information;
this recovery-only replay preserves their original row labels but does
not use that separate factor-sum path.

The next substantive target is an exact construction or detector which
preserves the required weighted collisions without visiting a quadratic
number of weight pairs, together with a universal cover. The complete
bit-operation proof must charge base acquisition, setup, polynomial work,
sorting and proper-factor recovery. A one-sixth-size axis by itself is
insufficient.

Focused local replay and checks, with no publication gates:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_batch_recovery.py --output docs/semiprime-batch-recovery-audit.json
lake build RiemannGaussian.SemiprimeCartesianCompletion --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeCartesianCompletion.lean
lake env lean -DwarningAsError=true RiemannGaussian.lean
~~~

## October 2, 2026: universal literal-centre coverage and discriminant recovery

The new [SemiprimeLehmanCoverage module](../RiemannGaussian/SemiprimeLehmanCoverage.lean)
proves complete correctness of a public arithmetic factorizer, with
26 public theorems. It is imported by the ordinary library and registered
in the semiprime family locally. The terminal guaranteed every-run
`Õ(N^(1/6))` bit-operation objective remains **unproved**.

This formalizes a classical cover rather than proposing a new factoring
exponent. [Harvey's Lemma 3.3 and Remark 3.2](https://arxiv.org/html/2010.05450)
give the weighted approximation and recovery from the weight product.
His Remark 3.4 identifies a full square-root speedup over the original
Lehman cover as a potential route to the one-sixth exponent. The present
Lean proofs retain the literal integer rounding and connect that cover
to the already checked small-factor prefix.

### Exact public cover

Let B be the least natural number satisfying N<=B^6. The definition
`sixthWidth N` is computable and consults only N; its upper and lower
budget bounds are proved. The existing quadratic prefix is reused,
not counted as a new theorem: it recovers p whenever p<=B² in the
non-square, B>=4 semiprime branch. If the prefix finds no proper factor,
the larger prime is also above B² and the prefix product has GCD one.

For N=p*q with p<q in this complement,
`exists_literal_window_after_prefix` proves the existence of positive
integer weights a,b and a nonnegative integer i satisfying

\[
ab\le B^2,\qquad
c_N(ab)=\left\lceil\sqrt{4Nab}\right\rceil,\qquad
aq+bp=c_N(ab)+i,\qquad
i<\frac{B}{4\sqrt{ab}}<B.
\]

The proof uses Dirichlet approximation to establish
`(a*q-b*p)^2*B² < N`, then proves the weighted sum gap and exact
ceiling conversion. The weights and hidden primes are existential
witnesses in the proof. They are never arguments to the factorizer.
`exists_literal_prime_collision` additionally proves that for every
unit base g modulo p the corresponding literal anchor equals g^i.
No factor-ratio, order, smoothness or curve hypothesis is used.

The arithmetic candidate list receives only N and B. For each public
k=1,...,B² it visits sums c_N(k)+i for

\[
0\le i<\left\lfloor\frac{B}{\lfloor\sqrt{k}\rfloor}\right\rfloor+1.
\]

`sharp_window_inside_width` and
`candidatePairs_have_factor_after_prefix` prove that the existential
weighted sum belongs to this actual list. The enclosing width is
deliberately padded; no floating-point endpoint test is used.

### Complete proper-factor recovery

At a true candidate, s=aq+bp and k=ab, so

\[
s^2-4kN=(aq-bp)^2,\qquad
\frac{s+\sqrt{s^2-4kN}}2=\max(aq,bp).
\]

Both identities are checked over natural numbers, including truncated
subtraction, integer square roots and integer division. Because ab<=B²<p,
the relevant weight is strictly smaller than either hidden prime.
The GCD of this quadratic root with N therefore recovers p or q.
`recoverWeighted_succeeds` proves this proper-factor claim, while
`recoverWeighted_sound` rejects every uncertified output.

This recovery uses k, not the separate hidden weights. It retains useful
information from a collision modulo all of N: a globally shared modular
root can still carry its original candidate sum and weight product.
For example, N=323, k=1 and s=36 give discriminant 4, quadratic root 19
and proper factor 19 even when the associated modular difference is zero.

`factor N` handles B<4 by a finite GCD scan, exact prime squares by their
integer square root, and all other cases by the existing prefix followed
by the full literal cover. The terminal theorem is

~~~lean
theorem factor_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d, factor (p*q) = some d ∧
      SemiprimeGroupSelection.ProperDivisor (p*q) d
~~~

This is unconditional universal correctness of this defined baseline.
It does not assert its runtime or the runtime of an implicit replacement.

### Construction cost and exact replay

`candidatePairs_length_ge` proves
`B² <= (candidatePairs N B).length`: each public weight-product row
contributes at least one sum. Thus materializing this specification's
candidate list already exceeds the one-sixth target, independently of
how quickly individual discriminants or supplied-list collisions are
processed. This bound concerns the explicit list, not all algorithms.
The definition's exact natural-number prefix product also has no fast
execution-cost certificate.

The [optional exact replay](../scripts/probe_semiprime_lehman_coverage.py)
and [complete audit](semiprime-lehman-coverage-audit.json) use seed
`202610021613`. The recovery kernel receives only N, uses the saved
polynomial-tree prefix, and streams the complete, uncapped literal rows
until a proper factor is found. The Python streaming/prefix implementation
differs from the Lean list/product specification; its timings are not a
cost proof for that Lean program.

All 351 semiprimes from unordered prime pairs up to 101 are recovered,
including squares, even products, unbalanced factors and the B=4 boundary.
An independent factorial oracle checks the prefix classification. The
exact candidate-count formula is checked for widths 0 through 64.
All 16 larger replay inputs are also recovered: four fresh balanced
inputs at each of 32, 40 and 48 bits, both saved 36-bit controls, one
unbalanced input and one prime square. Every replay has three timed
repetitions, including width setup, square check, prefix construction,
visited centre roots, candidate discriminants and GCD recovery.
Reference primes are used only in generation and untimed validation.
No comparison with conventional factoring software is made here.

The audit separately charges the full explicit Lean candidate list,
even when the streaming replay returns early. Public budgets at
N=2^bits-1 give these counts; the large entries are cost diagnostics,
not timed factoring runs:

| Bits | B | Centre rows B² | Explicit candidate entries |
| --- | ---: | ---: | ---: |
| 32 | 41 | 1,681 | 4,527 |
| 48 | 256 | 65,536 | 174,644 |
| 64 | 1,626 | 2,643,876 | 7,003,988 |
| 80 | 10,322 | 106,543,684 | 281,886,559 |
| 96 | 65,536 | 4,294,967,296 | 11,360,609,588 |

The focused warning-as-error build, ordinary-root check and all 14
namespace linters pass. The transitive audit checks all 67 module
declarations, including generated helpers and 55 proof declarations;
only `propext`, `Classical.choice` and `Quot.sound` occur. Commands and
source hashes are saved with the replay. This is local work, without
publication gates.

The next target is an exact implicit construction or detector for this
complete literal cover with Õ(B) total bit work. A substitute cover must
have its own universal correctness proof. Base acquisition, square-root
centres, modular arithmetic, sorting, polynomial work and recovery all
remain in the cost ledger. The complete classical cover now has a proof;
the one-sixth search and cost theorem remain open.

## October 2, 2026: short square-class caches and verified coverage misses

The next construction attempt replaces the full weight-product range by
square classes k=d*m². This is attractive because the exact centre becomes
linear in the short integer index m before its final ceiling. The new
[SemiprimeSquareProductCover module](../RiemannGaussian/SemiprimeSquareProductCover.lean)
contains 21 public theorems, including the cache identities and two complete
coverage controls. It is imported by the ordinary library and registered
in the semiprime family locally. The terminal guaranteed every-run
`Õ(N^(1/6))` bit bound is **unproved**.

### What the construction saves

`square_product_weights` proves that every positive weight pair with
square product has the form a=h*u², b=h*v². It includes common multipliers
and does not assume coprimality. Under ab<=B², its centre index m=h*u*v
is at most B. `square_product_centre` and `square_class_centre` retain the
literal ceiling:

\[
c_N((h u v)^2)=\left\lceil2huv\sqrt N\right\rceil,\qquad
c_N(d m^2)=\left\lceil2m\sqrt{dN}\right\rceil.
\]

`squareCentres_length` proves that the square-product cache has exactly
B entries. `mem_squareCentres` proves that every positive square-product
weight pair in the full budget uses one of them. This is an exact
construction-count result, not a bit-operation theorem or a coverage
assumption.

The public replay additionally partitions a fixed class d into da*db=d,
then generates a=h*da*u², b=h*db*v² with d*(h*u*v)²<=B². Its exact integer
centres are cached before the private-factor coverage oracle is run.
Every generated representation and every centre root is counted, including
duplicates. A finite independent oracle confirms the parametrization
against all admissible positive weight pairs for widths 1 through 20 and
class limits 1, 2, 6 and 16. The broader-class parametrization's universal
correctness is not claimed as a new Lean theorem here; the class-window
counterexamples below directly quantify over every weight product in the
specified classes.

### Square products alone lose the window

The checked first control is

\[
N=3{,}036{,}046{,}577=46{,}337\cdot65{,}521,\qquad
38^6<N\le39^6,\qquad39^2<46{,}337<65{,}521.
\]

`counterexample_semiprime_budget` proves both primality statements and all
these integer bounds. For **every** positive a,b with ab<=39² and square
product, `counterexample_square_product_gap` proves

\[
c_N(ab)+100\le a\cdot65{,}521+b\cdot46{,}337.
\]

Consequently no such pair has a hit even in the looser interval i<39.
The proof uses `square_weight_gap`:

\[
u^2q+v^2p-2uv\sqrt{pq}=(u\sqrt q-v\sqrt p)^2.
\]

Exact rational bounds on the two square roots give a uniform real gap of
at least 100 before the final ceiling. The executable oracle visits all
384 common-multiplier representations and finds the actual minimum
offset 137 at a=25,b=36. This finite minimum is replay evidence; the
universal lower bound 100 is the compiled theorem.

The primitive pair a=12,b=17 has nonsquare product 204 and exact offset
zero: c_N(204)=1,573,981=12*q+17*p. This is checked by
`counterexample_nonsquare_hit`. Dropping non-square products causes the
coverage miss; the original cover remains valid.

### A class menu through 16 also fails

For every d=1,...,16 and m>0 with d*m²<=39², construct the public
candidate sums c_N(d*m²)+i with i<floor(39/(4*m))+1. The last width
encloses the original sharp window, as proved by
`sharp_class_inside_width`; its squared integer version is also checked.
`classCandidates` is the actual public list, not a private witness set.

`counterexample_class_recovery_none` checks all 620 entries by Lean kernel
reduction. Every entry returns `none` under the already proved proper
discriminant recovery function. Primality and the weight budget ensure
that a true weighted sum would return a proper factor. Thus
`counterexample_no_small_class_sharp_window` proves that **every** positive
weight pair in classes through 16 misses the original sharp window on
this control. It does not assume that d is squarefree or that the
weights are primitive.

Widening each window to i<B still fails on the second checked control:

\[
N=209{,}843{,}003=13{,}309\cdot15{,}767,\qquad
24^6<N\le25^6,\qquad25^2<13{,}309<15{,}767.
\]

`wide_control_semiprime_budget` proves these primality and budget facts.
`wide_control_recovery_none` kernel-checks all 3,975 entries of the full
width-25 public class list through 16. Its consequence
`wide_control_no_small_class_window` excludes every positive weighted
hit in this family, including all common multipliers. The reference
oracle's minimum offset is 35. The original cover has an exact offset-zero
row a=16,b=19, product 304=19*4² and centre 505,143, checked by
`wide_control_outside_menu_hit`. Square class 19 lies just outside the menu.

Both finite certificates use `decide +kernel`; no compiler-trusting
evaluation or additional axiom is used. The diagnostic arithmetic lists
are exhaustive proof controls and have no claimed fast runtime. A
proposed modular batch would generate weight anchors and baby powers
instead; these controls show that the specified literal-hit guarantee
cannot be transferred to that smaller family. Order aliases may still
produce a proper GCD, so this is not a proof that every such modular
attempt fails to factor these inputs.

### Saved evidence and remaining target

The [optional exact diagnostic](../scripts/probe_semiprime_square_product_cover.py)
and [complete audit](semiprime-square-product-cover-audit.json) use seed
`202610021622`. They reproduce 80 all-weight oracle comparisons and
17,148 generated representations, both Lean controls, and two fresh
balanced semiprimes at each of 32, 40, 48, 64 and 80 bits. The second
control's reference-prime search is reproduced from seed `202610021623`;
it is found after 503 accepted prime pairs. These searches are explicitly
labelled oracle diagnostics, not inputs to public construction.

Across the 12 saved inputs, square products alone miss the full-width
window on 11. The squarefree class menu through 16 misses it on six,
and misses the sharp window on 11. The larger fixed menu helps some
inputs but does not recover universal coverage. For the two 80-bit
diagnostics its minimum offsets are 1,012,425 and 7,651,834, compared
with sixth-root widths 9,489 and 9,460. All centres and strict sharp
boundaries are checked with integer arithmetic. The diagnostic's
weighted-sum oracle uses reference primes; its counts are not timings
of a public factoring algorithm.

Focused warning-as-error build, ordinary-root check and all 14 namespace
linters pass. The transitive audit checks all 51 module declarations,
including generated helpers and 48 proof declarations; only `propext`,
`Classical.choice` and `Quot.sound` occur. Commands and source hashes
are saved with the replay. Work remains local, without publication gates.

This attempt rules out inheriting the full coverage theorem merely by
keeping square products or a fixed class-1-through-16 menu. A larger or
adaptive menu needs a new universal bound on both coverage and total
construction/search work. The main target remains processing the complete
literal centre family implicitly, or proving a different complete cover
with the full every-run one-sixth bit-operation cost.

## October 2, 2026: RH cancellation with the original row targets retained

The user's suggested source search examined the cancellation mechanisms
already proved along the RH path. The new
[Lean module](../RiemannGaussian/SemiprimeRHCancellation.lean),
[optional exact replay](../scripts/probe_semiprime_rh_cancellation.py),
[audit](semiprime-rh-cancellation-audit.json) and
[scoped checker](../scripts/CheckSemiprimeRHCancellation.lean) distinguish
identities that preserve the factor observable from signed aggregates that
observe a different quantity. No every-run one-sixth cost bound is claimed.

### Relevant identities in the RH chain

| RH source | Exact mechanism | Transfer requirement |
| --- | --- | --- |
| `ZetaRieszPrimeFourier.divisorCharacter_eq_primeProduct` | Complete signed divisor characters become finite Euler products. | Use original row/target ratios as the atomic factors to retain collision zeros. |
| `ZetaRieszSignedFrequency.primePair_eq_centered` | Reflection pairing keeps both phases around the common centre. | Retain the common phase and the target channel before combining rows. |
| `ZetaRieszShortDivisorCancellation.signed_block_eq_zero` | A complete affine divisor fibre cancels its constant and logarithmic moments. | The row exponents are not affine in divisor logarithms; cancelling their common centre instead produces a projected-period signal. |
| `pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_abel` | Internal shell boundaries telescope, leaving the alternating bulk and outer boundary. | Keep the remaining bulk and boundary; the identity does not justify an endpoint-only collision detector. |
| `ZetaRieszPairMatching.sum_eq_pairs_add_remainder` | Disjoint pairings keep the original unmatched support. | Preserve each pair's collision factors and the unmatched rows when partitioning a detector. |
| `ZetaRieszComplexNullFloor.increment_coherent_zero` and `ZetaRieszQuantitativeNullStep.cubicIncrement_coherent_zero` | Orthogonal corrections vanish on coherent prefixes. | The earlier `SemiprimeLongPeriodExtraction.coherent_phase_cross_zero` already proves that the perpendicular channel can erase the entire coherent factor signal. |

The checker verifies that these seven RH declarations exist in their
compiled environments and audits their transitive axioms. Their analytic
norm estimates are not silently applied to composite residue rings.

### A root-preserving signed product

For a supplied finite family of anchors r_j and common target t, put

\[
P(t)=\prod_j(r_j-t).
\]

`collisionProduct_eq_subset_expansion` gives the complete signed subset
expansion over every commutative ring. For a unit target,
`collisionProduct_eq_euler_product` gives

\[
P(t)=(-t)^{|S|}\prod_j(1-r_jt^{-1}).
\]

`collisionProduct_map_zero_iff` proves that, after reduction to either
hidden prime field, this vanishes **exactly** when some original row
equals t. Repeated anchors are allowed. `collisionProduct_euler_gcd_eq`
proves equality of the full public GCD before and after normalization,
for every modulus, including prime squares. The target multiplier is a
unit; it contributes no new factor signal.

The distinction from a tempting cheap subset circuit is precise:
`signedSubsetSum_zero_iff` detects an atomic factor z_j=1. If the z_j are
phase increments between rows, that is a period condition on the
increments, not the union of original row/target collisions. The same
Euler identity is valid in both applications, but the atomic inputs carry
different information.

This supplies a certified observable for future implicit product circuits.
It does not show that the many original atoms can be generated or processed
in sixth-root work, nor that an aggregate GCD equal to N is already a proper
factor. The existing deflation and proper-leaf recovery results retain
their separate role.

### Centre cancellation has a target companion

Write V_ab=g^(aN+b-c_ab) and let

\[
R_{ab}=g^{aN+b}-t g^{c_{ab}}=g^{c_{ab}}(V_{ab}-t).
\]

`rephasedResidual_eq`, `rephasedResidual_map_zero_iff` and
`rephasedResidual_gcd_eq` prove this common-phase transport and exact
GCD preservation. Rephasing only the anchor would change the target.

For a block with increments u,v, `rephasedResidual_mixed_difference`
proves the exact cancellation

\[
R_{00}-R_{01}-R_{10}+R_{11}
=g^{aN+b}(g^{uN}-1)(g^v-1)
-t(g^{c_{00}}-g^{c_{01}}-g^{c_{10}}+g^{c_{11}}).
\]

The first term uses a small separable circuit. The second is the exact
mixed centre-power companion. Keeping it makes the signed value correct;
it does not make that value a root-preserving union detector.

The kernel-checked control is
N=3,036,046,577=46,337*65,521, width B=39, with all four primitive rows
(12,17), (12,19), (13,17), (13,19). All products fit B², and both
primes are beyond B², as already proved by
`SemiprimeSquareProductCover.counterexample_semiprime_budget`.
For base 2 and offset zero the first row is a genuine weighted hit:
c(12,17)=1,573,981=12*65,521+17*46,337.

`control_literal_row_hit` gives proper GCD 46,337.
`control_mixed_difference_misses` proves that both the complete mixed
signal and its centre-free axis term have GCD one. The mixed residue is
1,242,297,734. `control_collision_product_preserves_hit` proves that
the original four residuals' product has proper GCD 46,337; its residue
is 1,896,063,703. `control_primitive_weight_budget` verifies that the
control does not depend on nonprimitive rows.

### A complete divisor orbit cancels its centre exactly

The four pairs (1,rs), (r,s), (s,r), (rs,1) share one literal centre.
`rowAnchor_block_divisor_ratio` proves, over any commutative group,

\[
\frac{V_{1,rs}V_{rs,1}}{V_{r,s}V_{s,r}}
=g^{(r-1)(s-1)(N+1)}.
\]

`block_divisor_ratio_eq_one_iff` identifies the result with exact local
order divisibility. This is a genuine inexpensive common-centre
cancellation, but it observes the N+1 projected period.
For r=12,s=17 on the same control, the original middle rows expose
46,337 and 65,521 respectively. `control_divisor_orbit_ratio_misses`
proves that the closed ratio minus one instead has GCD one. The public
replay checks the ratio residue 921,552,857 against all four original
anchors. No hidden factor is used to compute that ratio.

### Saved evidence and scope

The exact replay uses seed `202610021843`: all 171 unordered odd-prime
pairs through 67, including squares; the two prior coverage controls;
and four fresh balanced inputs at each exact size 32,40,48,64,80 bits.
Reference prime labels are used only after public block construction.
There are 3,390 rectangular offset tests and 4,953 divisor-orbit offset
tests. Euler normalization and phase normalization preserve every checked
GCD. Among 281 rectangular tests with a proper original row GCD, the
signed mixed signal has GCD one on 244. Among 273 divisor-orbit tests
with such a witness, the cancelled ratio has GCD one on 151.

These are conditional block statistics, not factoring success rates.
The axis cap is 16, and only offsets 0,1,B-1 are replayed; the corpus
does not test a complete new cover or establish an asymptotic cost.
The larger exact primitive controls above are separately recorded.

All 19 public theorems pass the focused warning-as-error build and
ordinary-root import check. The namespace passes all 14 linters, and
the complete declaration/helper audit permits only `propext`,
`Classical.choice` and `Quot.sound`. Finite certificates use
kernel-checked `norm_num` and `reduce_mod_char` proofs; there is no
compiler-trusting evaluation. Source hashes and commands are saved in
the audit. Work remains local.

The useful next target is an exact circuit for the original collision
product that retains its centre-dependent target companions and charges
all construction. The signed sum and common-centre ratio failures do
not rule out other RH-inspired product identities or implicit algorithms.
The guaranteed every-run one-sixth bit-operation theorem remains open.

## October 2, 2026: complete additive prefix and exact complement interface

The new [Lean module](../RiemannGaussian/SemiprimeStrassenPrefix.lean),
[public-input replay](../scripts/probe_semiprime_strassen_prefix.py),
[audit](semiprime-strassen-prefix-audit.json) and
[focused checker](../scripts/CheckSemiprimeStrassenPrefix.lean) complete
the additive small-factor prefix as an input to the universal factorizer.
This is the classical Strassen method recalled in
[Harvey, Proposition 2.5](https://arxiv.org/html/2010.05450#S2.SS3),
not a new factoring method or an achieved one-sixth theorem.

### Exact detector and recovery

Use the single polynomial

\[
F_B(X)=\prod_{i=0}^{B-1}(X+i+1)
\]

at the B points 0,B,...,(B-1)B. `blockPolynomial_eval` proves that
F_B(jB) is exactly the descending-factorial block ending at B(j+1).
`blockPolynomial_joined` proves that the product of all these evaluations
is (B²)! in every commutative coefficient ring. `blockPolynomial_degree`
proves the degree is B over every nonzero ring.

The polynomial roots and target points represent every integer 1 through
B². `prefix_integer_decomposition` gives the literal public block/leaf
indices. Under B²<N, `blockLeaves_bounds` proves each integer leaf is
strictly between zero and N. The first column with GCD greater than one
either returns a proper factor or has GCD N and triggers one lazy
length-B scan. `block_column_gcd_eq` proves exact evaluation/leaf
consistency, including prime squares and columns containing both primes.

`prefix_succeeds_of_nonunit` proves success if **any** integer in the
full cover has nonunit GCD. `prefix_succeeds_of_small_divisor` covers
every proper divisor at most B², without a prime or separating-column
premise. `prefix_gcd_bound` proves at most 2B GCD queries after evaluation;
`blockColumns_length` and `blockLeaves_length` supply the exact counts.
The full B-by-B grid is absent from the batch inputs.

The kernel certificate `saturated_column_control` checks N=35, B=4.
The four modular columns are 24,0,15,0. The second block contains both
5 and 7 and has GCD 35, yet the lazy scan returns the proper factor 5.
Treating a full-modulus column as failure would lose this coverage.

### Universal factorizer integration

`prefix_none_iff_clear` proves the exact equivalence

\[
\operatorname{factorPrefix}(N,B)=\mathrm{none}
\quad\Longleftrightarrow\quad
\gcd(N,(B^2)!)=1
\]

whenever B²<N. `prefix_none_excludes_small_prime` then excludes every
prime divisor at most B². Neither theorem supplies a reference prime,
local order or smoothness promise to the algorithm.

`sixth_budget_prefix_below_input` discharges B²<N from the actual
ceiling-sixth-root budget when B≥4. The finite small-input and square
branches are retained. `factorByBatchCover_semiprime` connects the new
prefix to the complete literal-centre Lehman complement, discharging its
factorial-clear antecedent. `factor_semiprime` proves that the resulting
single-public-input specification returns a proper divisor for every
product of two primes, including equal primes and arbitrary factor ratios.
`factor_sound` supplies unconditional soundness of any returned result.

The polynomial functions are **noncomputable Lean specifications**.
The optional Python engine constructs a product tree and monic remainder
tree using the already saved exact GMP coefficient packing. Their common
mathematical detector is certified; the Python program and its bit cost
are not thereby verified in Lean. The literal-centre complement is still
the earlier explicit candidate search.

### Executable evidence and validation

The independent small replay checks every N from 4 through 256 and every
B with B²<N: 2,851 complete batches. It compares every polynomial value
against its direct integer-block product and verifies the exact
factorial-clear equivalence. It includes 217 successful recoveries from
whole-modulus columns, prime powers and prime inputs. The separately saved
controls include N=35,49,77,101.

Seed `202610022104` selects four fresh small-factor and four balanced
semiprimes at each exact size 32,48,64,80 bits, followed by three prior
controls. All 16 fresh small-factor cases return proper factors; the
16 balanced cases and three prior controls correctly report clear prefixes.
Reference factors label coverage only after the public routine runs.
All root construction, both polynomial trees, evaluations and recovery are
inside the reported elapsed time. The 80-bit widths are 9,353 through
10,302; this run takes roughly 0.905 through 0.985 seconds per prefix.
These are component timings, with no full-factoring baseline or exponent
inference. No B² grid candidates are constructed; a full-modulus block
can construct one length-B lazy leaf list.

All 25 public theorems and one private helper pass the warning-as-error
module build and ordinary-root import check. The namespace passes all
14 linters. The complete transitive audit checks 54 declarations,
including 22 generated helpers and 46 proof declarations; only
`propext`, `Classical.choice` and `Quot.sound` occur. Commands and
source hashes are saved with the replay. Work remains local.

The next missing work is the exact implicit construction/search of the
centre-coupled complement and a Lean-verified total bit-cost model.
The linear prefix input and GCD counts do not discharge either obligation.
The full every-run one-sixth theorem remains open.

## 2026-10-03: complete centre-free relation and charged interval search

Artifacts: [Lean cover](../RiemannGaussian/SemiprimeCentreFreeCover.lean),
[optional focused check](../scripts/CheckSemiprimeCentreFreeCover.lean),
[public replay](../scripts/probe_semiprime_centre_free_cover.py),
[exact audit](semiprime-centre-free-cover-audit.json).

### The information retained

For N=pq with p<q, B=ceil(N^(1/6)), and a clear complete B² prefix,
`exists_short_linear_relation_after_prefix` transports the existing
universal Lehman cross-difference witness to positive weights a,b and an
exponent u satisfying

\[
1\le a\le B,\quad ab\le B^2,\quad a+b\le B^2+1,\quad
0\le u\le3B^2,\qquad
aN+B^2-u=(p-1)(aq+b).
\]

Specifically, u=B²+b+aq-bp. The strict cross-difference bound gives
|aq-bp|<B². The prefix complement forces a≤b, hence a≤B; the positive
weight product also gives a+b≤ab+1. The second weight becomes part of
the target exponent. It is a proof-side witness, never an algorithm input.

`exists_centre_free_prime_collision` proves that every unit in F_p has
a collision between g^(aN+B²), a=1,...,B, and g^u, u=0,...,3B².
`root_step` gives the public geometric root recurrence with ratio g^N.
No rounded square-root centre is constructed. The complete target interval
is longer than the literal Lehman window, so this is a new complete cover,
not an identity replacing each original row by an axis increment.

### Proper factor recovery and public certificates

The public unit projection is alpha=(g^(N-1))^((B!)^L), with
L=clog 2 (N+1). `stagedProjection_eq` proves that B successive powers
(i+1)^L compute the same value without constructing the full exponent.
`surviving_power_dvd`, `factorial_projection_rough` and
`public_projection_rough` prove that no prime at most B divides a local
projected period. Existing order separation makes the two periods coprime.

`projected_order_coprime_cardinality` uses p≤B³: if the smaller field's
period exceeds B², a shared prime r>B between the other period and p-1
would force r*d_p> B³ to divide p-1. The resulting coprimality, together
with 0<a+b≤B²+1<d_q, prevents the true relation from closing the other
field's period. `exists_projected_proper_hit` therefore retains a proper
GCD of the original residual.

The short-period search uses 2B+1 roots and 2B+1 targets.
`failed_projected_short_forces_long` proves that a failed search and the
public certificate gcd(N,alpha-1)=1 force both local periods above
(2B+1)². `recoverShifted_after_failed_short` consequently needs public
branch certificates rather than private local-period bounds. This still
does not prove that a fixed public base always supplies those certificates.

### The remaining input cost

For m>0, set J=floor(3B²/m)+1. `interval_decomposition` and
`shifted_difference_gcd` prove exact coverage and exact GCD preservation
after shifting each first-weight/block root by alpha^(-jm). The search
constructs BJ shifted roots and m babies. `recoverShifted_succeeds_of_proper_hit`
connects their literal proper hit to the earlier shared-root deflation and
lazy recovery specification.

`explicit_reshape_input_bound` proves

\[
12B^3 < \bigl(m+B(\lfloor3B^2/m\rfloor+1)\bigr)^2.
\]

The selected m=floor(sqrt(3B³))+1 thus has input scale B^(3/2), or
N^(1/4). This bound concerns the explicit reshape; it is not an
impossibility result for a compressed interval-product circuit. An
exact detector with linear-width construction remains missing.

### Exact controls and executable evidence

`control_long_original_hit` certifies N=2,803,308,161=44,963*62,347,
B=38, a=13,b=18,u=2639 and a proper original GCD of 44,963. Its small
public illustrative projection 2^((N-1)*6^32) is 1,823,692,905.
`control_long_local_orders` proves its exact local periods 22,481 and
10,391, both above 77². This finite projection is distinct from the general
factorial projection; the replay uses the full latter projection.

`control_public_base_kernel` independently certifies
N=1,373,653=829*1657, B=11, a clear quadratic prefix, and 2^(N-1)=1 mod N.
All subsequent common powers remain trivial. This is an exposed failure
of this base, not a factoring impossibility result.

The saved replay uses seed `202610022233`, fixed before outcomes, with four
fresh balanced and four fresh small-factor cases at each exact size
32,40,48 bits, two prior long-period controls and the explicit kernel:
27 inputs total. It returns 12 prefix factors, two projection factors,
nine short-period factors and three centre-free factors, exposing the
one kernel. All setup, staged powers, list construction, polynomial
evaluation and recovery are timed. Reference primes and orders are used
only after the public computation. Independent checks cover 272 small
public runs and 502 exact shifted/original GCD comparisons.

| N | B | Shifted roots | Babies | Full charged pass |
|---:|---:|---:|---:|---:|
| 2,180,376,197 | 37 | 407 | 390 | 23.30 ms |
| 2,803,308,161 | 38 | 418 | 406 | 23.42 ms |
| 723,392,533,321 | 95 | 1,615 | 1,604 | 110.85 ms |

These component timings have no complete-factoring baseline and establish
no empirical exponent. The constructor visits no literal centres or pair
matrix, but does charge every shifted root and baby. The Lean routines are
algebra/recovery specifications; their GMP engine and total bit cost remain
unverified. The universal every-run one-sixth theorem is still open.

All 35 public theorems pass the warning-as-error module build and ordinary
root import. All 14 namespace linters pass on 42 public declarations and
36 generated helpers. The transitive audit checks all 78 declarations,
including 71 proof declarations, and permits only `propext`,
`Classical.choice` and `Quot.sound`. The audit records commands and final
source hashes. The module is registered in the ordinary root and the
semiprime explorer family. This work remains local.

## Geometric interval derivatives and CRT-index extraction (2026-10-03)

Proof module:
[`SemiprimeIntervalJet.lean`](../RiemannGaussian/SemiprimeIntervalJet.lean).
Optional executable:
[`probe_semiprime_interval_jet.py`](../scripts/probe_semiprime_interval_jet.py).
Saved replay:
[`semiprime-interval-jet-audit.json`](semiprime-interval-jet-audit.json).
Focused linter and transitive-axiom check:
[`CheckSemiprimeIntervalJet.lean`](../scripts/CheckSemiprimeIntervalJet.lean).

### Information retained by the three scalars

Continue with B=ceil(N^(1/6)), the projected public unit alpha, interval
length L=3B²+1 and a row target x=alpha^(aN+B²). Define

\[
P(\alpha,x)=\prod_{0\le u<L}(x-\alpha^u),\qquad
D=\partial_x P,\qquad E=\alpha\,\partial_\alpha P.
\]

The target x is held fixed in the base derivative. The compiled
`targetDerivative_eq_derivative` and `baseDerivative_eq_derivative` identify
the literal polynomial derivatives with their cofactor formulas. At a
root x=alpha^k in a prime field, all cofactor terms except the k-th vanish:
`cofactor_at_other_root`, `targetDerivative_at_root` and
`baseDerivative_at_root` prove

\[
E=-k\,xD,\qquad S=-E/(xD)=k.
\]

This cancellation extracts a label for the original root. The detector P
retains the complete original root union; the marked derivative E retains
the integer exponent. Neither an endpoint product ratio nor an unmarked
signed row sum supplies this label.

If P=0 over Z/NZ, its two simple local roots may be alpha^k modulo p and
alpha^l modulo q with k different from l. `decodedIndex_map_root` proves
that the public scalar S reduces to k and l respectively.
`distinct_index_gcd` then proves gcd(N,S-k)=p for k,l<L≤q.
For a globally shared root, `decodedIndex_at_global_root` instead gives
the same literal index in the original ring. The executable recognizes
that common-index case and continues; it is not a proper-factor hit.
`decodedIndex_small_iff_shared_root` proves this public test exact on the
certified simple-root branch, so the skip preserves separating hits.

### Discharging inverses and recovering the original cover

The previous failed short-period search and the public certificate
gcd(N,alpha-1)=1 force both local periods above (2B+1)².
`projected_interval_periods_long` proves they cover the entire interval L.
Consequently every local interval root is simple.
`saturated_targetDerivative_isUnit` proves that D is a unit when P=0;
since x is also a unit, the denominator xD has a checked inverse. The
definition `decodedIndex` receives that inverse certificate, never a
hidden prime or an exponent index.

The final decoder uses b integer roots i+1 and b points S+1-jb, with
b²≥L. Their differences cover S-k for every 0≤k<L. The compiled
`recoverIndex_succeeds` connects a proper index difference to the earlier
complete shared-root deflation and lazy recovery.
`index_input_lengths` certifies the two length-b lists and
`index_recovery_gcd_bound` bounds this recovery stage by 2b GCD queries.
Polynomial construction/evaluation is a separate charge.

`saturated_proper_hit_recovers` constructs the denominator certificate and
derives the distinct second local index from a proper original hit.
`recoverInterval_succeeds_of_proper_hit` covers both a proper detector GCD
and a saturated detector. `recoverInterval_sound` proves every returned
factor proper. Finally, `exists_recoverable_projected_row` connects this
decoder to the complete centre-free arithmetic cover using the public
prefix, projected GCD and failed short-search certificates. It proves
that some row a=1,...,B succeeds, not that a successful row is found within
the required total time.

`interval_annihilator_degree` also proves that a nonzero polynomial
vanishing on all L distinct geometric targets has degree at least L.
This limits an explicit annihilating polynomial representation; it is
not an impossibility theorem for implicit products or other algorithms.

### Computing one row without the long target list

The optional prototype divides the interval into blocks of width
s=floor(sqrt(L))+1. It constructs only the polynomial
A(T)=product over u<s of (T-alpha^u), its logarithmic base derivative
H(T), and A'(T). For block j, put z=x*alpha^(-sj) and h=alpha^(s²j).
The original block's three scalars are

\[
P_j=hA(z),\quad D_j=h\alpha^{-sj}A'(z),\quad
E_j=h\bigl(s^2jA(z)+H(z)-sjzA'(z)\bigr).
\]

Product-rule multiplication combines these triples, retaining a short
tail. Balanced polynomial multiplication, three monic remainder-tree
evaluations and checked unit powers use O(sqrt(L)) coefficients and
evaluation points for one row. No length-L geometric target list or
row-target matrix is constructed. Independent direct scalar recurrences
verify all three outputs; they are outside the timed construction.

The block strategy follows the q-factorial fast-evaluation direction in
[Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic
Sequence and Applications*](https://arxiv.org/abs/2012.08656).
Their field-arithmetic bounds do not certify this composite-ring GMP
implementation or its bit cost. The generic jet identities above are
compiled Lean proofs; the executable's blocked construction currently has
diagnostic validation only.

### Exact control and executable replay

For N=2,803,308,161=44,963*62,347, alpha=1,823,692,905,
x=387,888,406 and L=4,333, `control_saturated_local_roots` verifies the
original roots k=2639 and l=4067 and their CRT index S=1,001,733,316.
`control_saturated_detector` proves P=0 over the entire modulus and D a
unit. `control_decodedIndex` proves that every denominator satisfying its
checked defining equation gives this same S. `control_saturated_recovery`
constructs such a denominator and certifies recovery with 66 roots and
66 points. No numerical derivative values from Python enter these proofs.
These controls reuse the preceding entry's small fixed projection; the
full-pass replay uses the general factorial projection.

The executable independently obtained D=2,009,853,433 and E=228,888,655,
then recovered 62,347 from gcd(N,S-4067). Those derivative values and
timings are diagnostic evidence. This row used 66 baby factors, 67
coefficients in each of A and H, 65 points per polynomial and 43 tail
factors. Its three-scalar evaluation took about 6.2 ms; evaluation plus
index recovery took 8.5 ms. A shared-root control decoded S=2639 and
continued without a factor. Separate clear-row and proper-product controls
checked the other branches.

The saved seed is `202610030044`, fixed before outcomes. All 388 exact
three-scalar comparisons pass, including random composite rings with
nonunit targets and small or repeated base periods. The public full-pass
replay contains three fresh balanced and three fresh small-factor inputs
at each exact size 32,40,48 bits, two prior long-period controls and the
explicit base kernel: 21 inputs total. It gives nine prefix factors, one
projection factor, eight short-period factors and two interval factors,
and exposes the one kernel. All setup is timed. Reference primes are
attached after public computation; both compared algorithms construct
their own setup.

| N | B | Rows evaluated | Full interval pass | Standard reshape |
|---:|---:|---:|---:|---:|
| 2,803,308,161 | 38 | 3 | 22.67 ms | 23.75 ms |
| 723,392,533,321 | 95 | 6 | 131.17 ms | 112.05 ms |

The replay stops before reaching its saturated control row; that row is
tested separately. These two full-pass timings establish no speedup over
tuned factoring software or empirical asymptotic exponent.

There are still B possible row targets. Evaluating each separately at
O(B) coefficient/point inputs uses O(B²) such inputs in the worst case,
before polynomial arithmetic. The earlier B^(3/2) standard reshape remains
the smaller of these two worst-case input constructions. Compression of
the row search, public base selection outside the projection kernel and
an every-run bit-cost theorem remain open. The new extraction channel
preserves information after saturation, but does not achieve the guaranteed
one-sixth factorization target.

All 36 public theorems pass the warning-as-error module build and ordinary
root import. All 14 namespace linters pass on 45 public declarations and
22 generated helpers. The transitive audit checks all 67 declarations,
including 58 proof declarations, permitting only `propext`,
`Classical.choice` and `Quot.sound`. The saved audit records commands and
final source hashes. The module is registered in the ordinary root and
semiprime explorer family. This work remains local.

## Shared exact block jets, padding and row-label retention (2026-10-03)

Proof module:
[`SemiprimeSharedIntervalJet.lean`](../RiemannGaussian/SemiprimeSharedIntervalJet.lean).
Optional executable:
[`probe_semiprime_shared_interval_jet.py`](../scripts/probe_semiprime_shared_interval_jet.py).
Saved replay:
[`semiprime-shared-interval-jet-audit.json`](semiprime-shared-interval-jet-audit.json).
Focused checker:
[`CheckSemiprimeSharedIntervalJet.lean`](../scripts/CheckSemiprimeSharedIntervalJet.lean).

### Exact circuit and safe padding

The preceding row-by-row engine reconstructs its baby polynomial for each
target and processes a separate tail. Sharing one polynomial of degree m
among R rows uses R*J normalized points, where J is the number of exponent
blocks. A separate tail of almost m factors per row would still be a large
hidden construction cost. This continuation pads to complete blocks instead:

\[
J=\lfloor3B^2/m\rfloor+1,\qquad L_{\rm pad}=mJ.
\]

`padded_contains_original`, `padded_length_le` and
`padded_below_short_square` prove, for 0<m≤B²,

\[
3B^2+1\le L_{\rm pad}\le3B^2+m\le4B^2<(2B+1)^2.
\]

The public failed short-search certificate puts both local periods strictly
above that last square. The padded powers therefore remain distinct; adding
targets does not erase a proper original residual or invalidate the simple
root inverse. `exists_recoverable_padded_row` connects the decoder for this
full-block interval to the complete centre-free cover, using the original
prefix, projected GCD and failed short-search certificates.

Let A be the degree-m baby polynomial and H its logarithmic base derivative
with its target held fixed. For block j, use z=x*alpha^(-jm) and
h=alpha^(jm²). The exact normalized triple is

\[
\bigl(hA(z),\ h\alpha^{-jm}A'(z),\
 h\bigl(jm^2A(z)+H(z)-jmzA'(z)\bigr)\bigr).
\]

`cofactor_first_moment` pays the target drift term without division by a
possibly zero detector. `blockBaseDerivative_rescale` retains the absolute
exponent jm+u, rather than merely the position u inside a block.
`normalizedBlockJet_eq` proves all three channels equal those of the
original exponent block. The product-rule concatenation theorems and
`sharedBlockedJet_exact` then certify the full normalized block fold for
every commutative ring, including zero rows and nonunit targets. Only the
base used for point normalization must be a checked unit.

These are new Lean proofs of the blocked circuit's algebra. They do not
formalize the GMP multipoint/remainder implementation or certify its bit
cost. The prototype shares the same monic point tree across A, A' and H;
its ring arithmetic uses no inverses of unchecked residues. The block
strategy remains in the classical q-factorial evaluation direction of
[Bostan–Yurkevich](https://arxiv.org/abs/2012.08656).

### Cost that remains after sharing

For a group of R≤B rows, choose m=floor(sqrt(R*(3B²+1)))+1, subject to
the public cap m≤B². `sharedWidth_le_quadratic` shows the cap unnecessary
for B≥4. `sharedPoints_length` proves the point list has exactly R*J
entries. The compiled `shared_group_input_bound` and
`shared_group_squared_bound` give, for this uncapped width,

\[
C=m+RJ\le3m,\qquad C^2\le18R(3B^2+1)+18.
\]

These counts concern baby factors and normalized points. Three polynomial
coefficient arrays, three scalar evaluation channels and the one shared
point tree change constants, while their construction and arithmetic still
have to be charged. For R=B the count has B^(3/2) scale.
`shared_input_floor` independently proves 12B³<C² for every positive m.
This is a floor for the explicit shared-block representation, not for all
possible implicit circuits.

The executable grows disjoint groups as 1,2,4,... and stops at the first
proper factor. It charges the entire computed group, including rows after
the successful row. Each group may have a different padded interval;
every one retains the complete original interval and stays within the
certified period range. The generic group-count inequalities above are
compiled; a full adaptive scheduling and bit-operation cost theorem is not.

### Why first jets cannot be pooled across rows

When two row products vanish in a field, multiplying their first jets
gives product zero and both derivative channels zero. The compiled
`two_zero_rows_erase_first_jet` certifies this exact information loss.
The new evaluator shares construction and evaluation while retaining each
row's scalar triple, so it does not perform this destructive pooling.

`control_shared_local_roots` verifies public rows a=9 and a=13 for
N=2,803,308,161 and the preceding fixed illustrative alpha=1,823,692,905.
Their original row targets are 964,233,038 and 387,888,406. The first has
local indices 542 and 862, with CRT index 585,688,580; the second retains
indices 2639 and 4067. It also certifies m=406, J=11, L_pad=4466 and
C=824 for the complete 38-row shared group.

`control_pool_erases_first_jets` proves both padded row products zero over
the entire modulus, their target derivatives units, and their pooled
three-scalar value exactly (0,0,0). The earlier generic index theorems still
apply to each separate row. This is a verified failure of direct first-jet
pooling, not an impossibility theorem for higher derivatives or a different
label-preserving aggregate.

### Exact replay and remaining target

The saved seed is `202610030114`, fixed before outcomes. Independent direct
product-rule recurrences check all 941 computed row triples: 192 random
multirow groups over prime/composite rings and the complete 38-row control.
For the control, the shared evaluator constructs 406 baby factors and
418 points, with 407 coefficients in A and H and 406 in A'. All three
channels use one point tree, with no full interval target list, pair matrix
or per-row tail. It computes every control row in about 53.52 ms.
Four rows, a=9,13,22,31, are saturated; each separately yields a proper
CRT-index factor. Pooling all first jets gives (0,0,0), as anticipated by
the checked two-row theorem. The executable's numerical derivative values
and timings remain diagnostic evidence.

The public replay contains three fresh balanced and three fresh small-factor
inputs at each exact size 32,40,48 bits, two prior long-period controls and
the explicit base kernel: 21 inputs. The adaptive shared pass, all-row
shared pass, separate-row pass and standard reshape each build and time
their own setup. All agree on factor availability: nine prefix factors,
one projection factor, eight short-period factors, two interval factors
and the one exposed kernel. Reference primes are attached afterwards.

| N | B | Adaptive shared | Separate rows | Standard reshape | Shared all rows |
|---:|---:|---:|---:|---:|---:|
| 2,803,308,161 | 38 | 18.21 ms | 22.46 ms | 23.52 ms | 57.73 ms |
| 723,392,533,321 | 95 | 98.51 ms | 131.43 ms | 111.28 ms | 278.28 ms |

The first control computes groups of one and two rows, charging 320 combined
baby/point inputs; the second computes groups of one, two and four rows,
charging 1,459. This is an early-stop benefit in two controls, not an
empirical exponent or a claim against tuned factoring software. The
all-row construction reduces the preceding rowwise worst-case O(B²)
input scale to B^(3/2), matching the standard reshape. It remains too
large for a guaranteed O(B) total construction, and the fixed-base kernel
and total bit-cost proof remain open. The requested every-run one-sixth
factorization guarantee has not been achieved.

All 34 public theorems pass the warning-as-error module build and ordinary
root import. All 14 namespace linters pass on 50 public declarations and
20 generated helpers. The transitive audit checks all 70 declarations,
including 54 proof declarations, and permits only `propext`,
`Classical.choice` and `Quot.sound`. The saved audit records commands and
final source hashes. The module is registered in the ordinary root and
semiprime explorer family. This work remains local.

## Tagged higher coefficients and individual row indices (2026-10-03)

The new [Lean module](../RiemannGaussian/SemiprimeTaggedPooling.lean),
[optional probe](../scripts/probe_semiprime_tagged_pooling.py),
[saved audit](semiprime-tagged-pooling-audit.json) and
[focused checker](../scripts/CheckSemiprimeTaggedPooling.lean) continue the
row-cancellation investigation. The construction retains information
before taking an unlabelled sum. It does not yet obtain that information
within the sixth-root total budget.

For each original interval row, retain its residual, target slope and
exponent marking:

$$
r_a=P_a,\qquad v_a=x_aD_a,\qquad w_a=-E_a.
$$

`original_row_marking_at_root` discharges the key source identity
\(w_a=k_av_a\) at the literal root \(x_a=\alpha^{k_a}\), using the
original interval product's logarithmic derivative. No hidden index vector
is supplied to the constructors. At each stage, hidden zero-row sets are
proof bookkeeping after reducing the public source to a local field.

First construct the scalar deformation

$$
F(e)=\prod_a(r_a+ev_a).
$$

`deformation_coeff_below` proves that every coefficient below the local
zero-row count \(m\) vanishes. `deformation_head_coeff` identifies the head
scale as

$$
U=\prod_{a\in Z}v_a\prod_{a\notin Z}r_a.
$$

`deformation_head_coeff_ne_zero` proves this is nonzero in a domain when
the local zero slopes are nonzero. `unequal_zero_counts_gcd` then proves
that the coefficient at the smaller of two different local zero counts
has a proper prime gcd. `deformation_hasse_at_zero` identifies the
coefficient with a Hasse derivative at zero, without dividing by a
factorial. These observations remain valid in small characteristic.

Equal counts require retaining the row tags. The two public deformations
are

$$
Q(e,T)=\prod_a\bigl(r_a+ev_a(T-a)\bigr),\qquad
H(e,T)=\sum_a w_a\prod_{b\ne a}\bigl(r_b+ev_b(T-b)\bigr).
$$

The constructors use original row triples and public tags. They omit
factors in the marked sum without dividing by any vanishing residual.
`tagged_head_coeff` proves

$$
Q_m(T)=U\prod_{a\in Z}(T-a).
$$

`tagged_marked_head_coeff` retains the marked cofactors at order \(m-1\).
`tagged_head_eval_zero_iff` proves that, with distinct local tags and
nonzero local slopes, the head vanishes exactly at the original zero-row
labels. `different_zero_labels_gcd` therefore proves proper-factor
recovery when the two fields have equal counts but different zero-row
sets.

When the same row vanishes in both fields, its individual exponent label
still survives. `tagged_marked_identity_at_zero_tag` proves

$$
H_{m-1}(a)=k_aQ_m'(a).
$$

`tagged_head_derivative_ne_zero` gives the local derivative's nonvanishing
under distinct-tag and simple-slope conditions. The public decoder uses
a unit checked against that derivative. `decodedHead_original_row_root`
reduces the decoded scalar to the actual interval exponent in each local
field; `decodedHead_original_distinct_index_gcd` proves the proper integer
difference gcd when these indices differ and the interval is short enough.
`decodedHead_rescale` permits the same unit normalization on both heads.
These are source and decoder identities, not a verification of the Python
coefficient engine or a theorem about its total bit cost.

The compiled small control uses \(N=35\), \(\alpha=2\), interval length
three and targets 32 and 9. `control_original_rows` checks every residual,
slope and marking from the literal finite products.
`control_first_jet_loss` shows that ordinary pooled first jets vanish.
`control_normalized_heads` gives

$$
C(T)=T^2-3T+2,\qquad M(T)=3T+16\pmod{35}.
$$

`control_decoder_denominators` checks the public unit denominators.
`control_decoded_heads` recovers 16 and 22 individually. Their reductions
encode opposite local index assignments \((1,2)\) and \((2,1)\), while
`control_local_indices` proves their unlabelled sum is just 3 in both
fields. `control_equal_sum_retains_individual_factors` checks the proper
gcds 5 and 7 against the individual indices. This is a generic decoder
control, not an instance of the global centre-free coverage theorem.

The distinction between payload and acquisition remains essential.
`tagged_head_degree_le` and `tagged_marked_head_degree_le` bound the final
degrees by \(m\) and \(m-1\). But `densePrefixSlots_length` proves that
an explicit prefix through order B contains
\((B+1)(B+2)/2\) slots for the product alone. The prototype also retains
the marked prefix; `dense_combined_prefix_length` checks their combined
allocated capacity through order m is \((m+1)^2\) slots. It updates these
prefixes at every source row. A
linear final payload is not a linear construction.

The diagnostic replay uses seed **202610030201**. All 256 independent
small batches agree with a literal per-pair proper-collision oracle:
171 separate unequal counts, 25 separate different row labels, 18 recover
marked indices, 34 are clear and eight contain no proper labelled hit.
The public pooling constructor receives neither the reference primes nor
the reference collision labels. Three larger controls exercise unequal
counts, equal counts with different row labels, and the same labels with
different exponent indices. The last recovers index **585,688,580** at
row 9 and factor **62,347** through the existing short integer batch.
These larger control computations are numerical evidence; the small
original-source control and general identities above are Lean proofs.

The fresh complete replay contains 18 new balanced/small-factor inputs,
the two saved long-interval inputs and the exposed fixed-base kernel. It
finds factors on 20/21 inputs: nine prefix, three projection, six short
period and two unequal-count results. The kernel remains exposed. Each
comparator constructs and times its own public setup. The full pooling
path computes all original shared row jets before testing its coefficients:

| N | B | Full tagged pooling | Adaptive shared row decoder |
|---:|---:|---:|---:|
| 2,803,308,161 | 38 | 58.63 ms | 18.32 ms |
| 723,392,533,321 | 95 | 284.00 ms | 100.05 ms |

These runs show no speedup from this acquisition path. Given all row jets,
the existing individual decoder already suffices. The value of the new
identities is to specify what a future shared construction must preserve
without first computing those rows. The existing source still has the
shared B^(3/2) input scale proved in `shared_input_floor`; the dense tagged
prefix adds another construction cost. Cheap acquisition of the two heads,
deterministic base selection and the complete every-run bit-operation
bound remain open. The guaranteed one-sixth rate has not been achieved.

All 45 public theorems pass the warning-as-error module build and ordinary
root import. All 14 namespace linters pass on 58 public declarations and
31 generated helpers. The transitive audit checks all 89 declarations,
including 76 proof declarations, and permits only `propext`,
`Classical.choice` and `Quot.sound`. The saved audit pins 31 source inputs,
including the frozen shared-row audit, all project proof imports, probe
dependencies and toolchain manifests. The module is registered in the
ordinary root and semiprime explorer family. This work remains local.

## Original source heads, public classification and deferred jets (2026-10-03)

The new [Lean module](../RiemannGaussian/SemiprimeSourceHead.lean),
[optional probe](../scripts/probe_semiprime_source_head.py),
[saved audit](semiprime-source-head-audit.json) and
[focused checker](../scripts/CheckSemiprimeSourceHead.lean) remove a
construction cost identified in the previous entry. The dense bivariate
prefix is unnecessary once the original row residuals have been publicly
classified. Acquiring those residuals within O(B) total work remains open.

The complete original row deformation and marking are

$$
\mathcal P_a(e,T)=\prod_{u<L}
  \bigl(x_a-\alpha^u+ex_a(T-a)\bigr),
$$

$$
\mathcal W_a(e,T)=\sum_{u<L}u\alpha^u
  \prod_{v<L,\ v\ne u}\bigl(x_a-\alpha^v+ex_a(T-a)\bigr).
$$

The constructors `fullSource` and `fullMarked` retain these complete row
polynomials in the same product/cofactor construction as before. They
take the original base, targets, tags and interval length, rather than
precomputed row jets. The target is held fixed in the exponent marking.
`taggedRowSource_coeff_zero`, `taggedRowSource_coeff_one` and
`taggedRowMark_coeff_zero` identify the constant/linear source data as
\(P_a\), \(x_aD_a(T-a)\) and \(-E_a\).

`sourceProduct_zero_factorization` factors one deformation variable out of
each row with zero constant coefficient using `divX`, an explicit
coefficient shift. It divides by no residual. `weighted_source_coeff_below`
proves that all lower orders vanish. `source_head_eq_first_jet` and
`source_marked_head_eq_first_jet` then show that all higher source/marking
terms drop out at precisely orders m and m-1, where m counts zero rows.
`fullSource_head_eq_tagged` and `fullMarked_head_eq_tagged` transfer this
identity to the complete literal collision source. These are first
surviving heads only when the zero-row slopes are nonzero. The generic
identities also hold with multiple roots, when these coefficients can
themselves vanish. `control_full_source_heads` checks the full literal
two-row source over ZMod 35 against the earlier exact heads.

The executable construction starts with public residual GCDs. A proper
GCD returns a factor. `residual_zero_of_gcd_eq_modulus` shows that a GCD
equal to N means a zero residual in the public ring;
`residual_isUnit_of_gcd_eq_one` gives a public unit certificate otherwise.
`public_gcd_classification` discharges the zero-or-unit classification
from these checked GCDs. `rowGcdTrace_length` charges exactly one query
per row for a complete classification pass. It does not charge residual
construction for free.

After this classification, `zeroIndices_map_of_units` proves that every
nontrivial local ring has the same zero-row set as the public ring. The
positions of the relevant heads are thus public. Different hidden row
sets have already produced a proper row GCD. The remaining globally zero
rows use leaves

$$
(A_a(T),M_a(T))=(v_a(T-a),w_a),
$$

with the exact combination rule

$$
(A,M)\cdot(B,J)=(AB,\ MB+AJ).
$$

`sourceProduct_union` and `sourceMarked_union` prove this rule for disjoint
subtrees. A balanced construction reuses each child product rather than
constructing omitted-factor products separately. Multiply both outputs
by the retained product of nonzero row residuals.
`publicHeadProduct_eq_coeff` and `publicHeadMarked_eq_coeff` prove that
these are the earlier tagged heads. `public_original_head_eq_fullSource`
and `public_original_marked_eq_fullMarked` identify them as coefficients
of the full original source. No lower deformation coefficients are needed.
`publicHead_original_root` and `publicHead_original_distinct_index_gcd`
retain the original local exponent and proper integer-difference factor
after a checked public denominator. No hidden zero set or index vector is
an input to this homogeneous construction.

`homogeneousTreeSlots_exact` checks the representation budget

$$
T_d+1=(2d+4)2^d
$$

for a complete binary head tree with \(2^d\) linear leaves and constant
markings. This budget counts both outputs at every node, including child
storage. It is an algebraic slot model, not a proof of the Python tree's
machine allocation or bit cost. `control_tree_slot_budget` checks 447
slots for 32 leaves against 1,089 allocated slots in the dense deformation
prefix. The executable tree controls at 8, 16 and 32 saturated rows match
the model exactly, with 79, 191 and 447 cumulative coefficient slots and
21, 45 and 93 polynomial convolutions. The inputs are generic original
interval rows over N=1,591, with a fixed public mixed target 520 and
otherwise global aliases. They test the head tree, rather than the
centre-free universal cover.

The new public source pass computes only the residual channel at first.
It builds and evaluates the same padded normalized baby polynomial.
Only globally saturated rows request derivative channels. The deferred
logarithmic derivative reuses the existing baby product tree; selected
target points get one additional shared point tree. Original block
offsets and point-drift terms remain exactly those of
`SemiprimeSharedIntervalJet.sharedBlockedJet_exact`. The backend and lazy
scheduler remain unverified implementations; the new Lean source and
head identities do not certify their total bit-operation cost.

The replay uses seed **202610030307**. There are 454 independent literal
residual comparisons, 133 deferred-jet comparisons and 368 head
comparisons, including literal full-pair source deformations after local
reduction. All 256 small batches agree with a literal proper-collision
oracle: 191 return residual factors, 20 marked-index factors, 42 are clear
and three contain no proper labelled hit. Two additional multiple-root
controls confirm the coefficient identities while exposing vanishing
slopes, rather than treating those coefficients as nonzero heads.

The lazy saturated large control computes original rows 9 and 13 with
94 baby factors, 94 residual points and 188 deferred derivative channel
evaluations, over padded length 4,418. It obtains CRT index 585,688,580
and factor 62,347 without a deformation prefix. This is diagnostic
evidence; the compiled small original-source control and general
identities above provide the mathematical certificates.

The fresh complete replay contains 18 balanced/small-factor samples,
the two saved long-interval inputs and the exposed fixed-base kernel.
It finds factors on 20/21 inputs: nine prefix, one projection, eight short
period and two residual results. Reference primes are attached only after
each public computation. Both comparators construct and time their own
public setup.

| N | B | Residual-first source | Adaptive three-channel source |
|---:|---:|---:|---:|
| 2,803,308,161 | 38 | 9.36 ms | 18.35 ms |
| 723,392,533,321 | 95 | 44.90 ms | 99.83 ms |

Both saved long inputs return proper row residual GCDs, so these runs
compute no derivative channels. This is a measured constant-factor
improvement, not evidence for an exponent or a comparison with tuned
factoring software. Removing the dense head prefix and unused derivative
channels does not change the all-row residual input floor proved in
`SemiprimeSharedIntervalJet.shared_input_floor`. The residual source still
has B^(3/2) inputs in the worst shared group. Cheap residual acquisition,
deterministic base selection and an every-run classical bit-operation
certificate remain open. The guaranteed one-sixth rate is not achieved.

All 33 public theorems pass the warning-as-error module build and ordinary
root import. All 14 namespace linters pass on 47 public declarations and
27 generated helpers. The transitive audit checks all 74 declarations,
including 55 proof declarations, and permits only `propext`,
`Classical.choice` and `Quot.sound`. The module is registered in the root
and semiprime explorer family. The saved audit pins 35 source inputs,
including both preceding audit artifacts and their frozen source chains.
This work remains local.

## Raw seed screening and literal geometric row cancellation (2026-10-03)

The new modules
[`SemiprimeStagedSeed`](../RiemannGaussian/SemiprimeStagedSeed.lean) and
[`SemiprimeGeometricRows`](../RiemannGaussian/SemiprimeGeometricRows.lean),
[optional public-input replay](../scripts/probe_semiprime_staged_seed.py),
[saved audit](semiprime-staged-seed-audit.json) and
[focused checker](../scripts/CheckSemiprimeStagedSeed.lean) separate two
questions: obtaining a usable public seed, and obtaining the original row
residuals cheaply. Neither module proves the terminal one-sixth bit bound.

### What adjacent-power cancellation actually gives

Keep the original polynomial

\[
P_L(X)=\prod_{u=0}^{L-1}(X-\alpha^u).
\]

`adjacent_target_telescoping` and `adjacent_polynomial_telescoping` prove
the exact cleared identity

\[
P_L(\alpha X)(\alpha X-\alpha^L)
=\alpha^L(\alpha X-1)P_L(X).
\]

It holds in every commutative ring, including zero endpoint factors and
nonunit alpha. No inverse or division is used. Overlapping root sets
explain why adjacent powers admit a degree-one endpoint recurrence. The
source polynomial is retained before evaluation, so its zero and marking
information has not been replaced by an endpoint quotient.

Our actual row targets are `x_a=alpha^(a*N+B^2)`, however, and their step
is `beta=alpha^N`. `functional_step_denominator_degree` proves the precise
restriction on a proposed rational recurrence: if `D` is nonzero and

\[
A(X)P_L(X)=D(X)P_L(\beta X),
\]

and the shifted polynomial is nonzero at every original interval root,
then `L<=natDegree D`. Evaluating the identity at the original roots forces
`D` to vanish at all L distinct powers. The proof uses the already checked
`SemiprimeIntervalJet.interval_annihilator_degree`; it does not infer a
general computational lower bound.

`control_row_step` checks the literal long-period control with
`N=2803308161`, `B=38`, `L=4333`, `alpha=1823692905`. In the field modulo
44963, the checked period is 22481 and `alpha^N=alpha^17385`. The intervals
`[0,4333)` and `[17385,21718)` are disjoint inside that period.
`control_row_denominator_degree` therefore proves degree at least 4333,
and `control_no_degree_one_step` excludes the adjacent-power shortcut for
this actual row step. These statements concern a polynomial functional
identity. They do not rule out interpolation at just 38 row targets,
higher-order recurrences, other transforms or other residual algorithms.

### A raw seed needs only one checked projection

Write `raw=g^(N-1)`, `L=clog 2 (N+1)`, and retain each intermediate
`raw^((i!)^L)`. `factorial_step_not_both_one` proves that a successor
factorial stage cannot annihilate two nontrivial components with coprime
local orders. Every surviving prime divisor of the preceding orders is
larger than i. If both components became one at stage i+1, each would
have a prime divisor equal to i+1, contradicting coprimality.

`raw_order_lt_public_repetitions` discharges the repetition-size bound
for the actual prime fields. `map_staged_raw` retains the original public
unit and transports each labeled stage to both reductions. The existing
`SemiprimeOrderSeparation.projected_orders_coprime` supplies coprimality
for the raw N-1 power. Thus `stage_gcd_ne_modulus_of_clear` proves that a
public GCD of one cannot jump to the whole modulus at the next stage.

`public_projection_clear_or_factor` and `checkedProjection_none_clear`
assemble the full result: after a nontrivial raw seed, either the staged
checks expose a proper factor, or the final projected seed has GCD one.
`checkedProjection_succeeds_of_final_kernel` covers a globally trivial
final scalar explicitly: a proper factor must already occur in the trace.
No hidden local period or prime is an algorithm input.

`unitTrace` uses a scan of the preceding powers, rather than separate
factorial-power calculations. `unitTrace_eq_map` identifies every retained
entry with the original public stage. `checkedProjection_sound` checks
every returned divisor, and `checkedProjection_gcd_count` bounds the
queries by B+1 for this one projection. These are exact operation counts,
not a bit-complexity certificate for a backend.

The new `screenSeed` examines B public bases, 2 through B+1, using only a
unit check and the raw N-1 power. `screenSeed_sound` and
`screenSeed_unit_certificate` supply the usable public unit when it
succeeds. `screenSeed_test_count` charges at most B raw tests, and the
long factorial-stage pass is run only for the first usable seed. This
avoids introducing B separate B-stage projections. `screenSeed_none_iff`
retains the exhausted-scan outcome explicitly. A proof that the sixth-root
menu always succeeds after the prefix is still missing.

### Exact controls and the charged replay

`control_all_final_bases_kernel` strengthens the prior single-base
control: every unit on `N=1373653=829*1657` has final projection equal to
one at B=11. Both field cardinalities divide the full public exponent,
as checked by `common_field_exponent_kernel`. A selector of final scalar
values alone cannot obtain a nontrivial projected seed on this input.

Nevertheless, `control_raw_seed_factor` checks that bases 2 and 3 have
raw power one while base 5 has raw power 1370338 and raw residual GCD 829.
`control_raw_four_kernel` checks base 4 as well. The saved public replay
therefore uses four cheap raw powers and returns 829 without any rows or
factorial stages. `control_two_base_screen_exhausted` checks a deliberately
short failed menu; it is not a counterexample to sixth-root coverage.
`control_staged_factor_before_final` supplies a separate positive staged
control on 551=19*29: base 2 starts with clear raw GCD, stage 2 remains
clear, stage 3 exposes 19, and the final width-7 scalar is one.

The probe uses seed 202610030408 and replays the same 21 saved inputs
from the frozen source-head audit. All 21 are factored, versus 20 in the
fresh fixed-base replay. The statuses are nine prefix factors, one raw
factor, one staged projection factor, eight short-period factors and two
original residual factors. Every attempted factorial projection uses one
screened seed. Prefix, raw tests, stages, short search and original row
construction are all included in the complete-pass timing. Known factors
are validation references only; the algorithm receives N.

Independent exact checks cover 256 telescoping comparisons, including 16
zero-endpoint cases; 955 nontrivial raw seeds and 46 raw-kernel cases;
and 4196 labeled stages. All 316 globally collapsed stages in that small
diagnostic have a preceding proper factor. The geometric control retains
4332 common roots for an adjacent-power shift and zero common roots for
the literal row step. Explicit root sets are used only in this validation,
not in the public factorization pass. The saved audit pins 40 source inputs,
including the prior audit and its frozen source chain.

The screened prototype reuses the residual-first shared source and deferred
jets without modifying the earlier programs or audits. It still has the
worst shared residual input scale B^(3/2). The new degree statement excludes
one proposed endpoint recurrence on an actual input; it does not prove that
this input scale is unavoidable for all constructions. Cheap exact residual
acquisition, guaranteed bounded raw-seed selection and a complete every-run
bit-operation bound remain open. Recovering this finite corpus does not
establish the one-sixth guarantee.

Both modules pass the warning-as-error build and strict ordinary root
import. All 14 namespace linters pass in each namespace. The staged module
has 26 public theorems, eight definitions and 28 generated helpers; all
62 declarations, including 49 proofs, pass the transitive axiom audit.
The geometric module has ten public theorems, one definition and six
generated helpers; all 17 declarations, including 16 proofs, pass the same
audit. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Both modules are registered in the ordinary root and semiprime explorer
family. This work remains local.

## Raw-kernel common orders and retained quadratic carries (2026-10-03)

[`SemiprimeCommonOrder`](../RiemannGaussian/SemiprimeCommonOrder.lean),
the [public-input replay](../scripts/probe_semiprime_common_order.py),
[saved audit](semiprime-common-order-audit.json) and
[focused checker](../scripts/CheckSemiprimeCommonOrder.lean) provide a
factor-recovery branch that constructs no geometric interval rows. Its
modulus must be obtained by charged public work. The terminal guaranteed
one-sixth bit-operation bound remains open.

### The information needed for direct reconstruction

`kernel_global_order_common` proves that a unit with `g^(N-1)=1` over a
distinct-prime semiprime has global order dividing both p-1 and q-1.
The two local orders may differ: the proof retains both reductions and
uses the coprimality of the distinct prime moduli to reconstruct the
global power equality.
Thus the exact global order, once obtained, is a usable common modulus.
`common_modulus_of_public_checks` supplies a second route through public
prime-divisor power checks with GCD one at each check.

For any known positive modulus m dividing p-1 and q-1, write
`p=m*a+1`, `q=m*b+1`. `orderQuotient_encoded` proves the exact relation

\[
U=\frac{N-1}{m}=a+b+mab.
\]

The two retained public channels are `S=U mod m` and `C=U div m`.
When N<m^3, `index_sum_lt_modulus` proves a+b<m, and
`encoded_sum_product` identifies S=a+b and C=ab. The discriminant
`S^2-4*C` is exactly `(b-a)^2`. `recoverCommon_semiprime` reconstructs
the smaller prime with one integer square root and a checked GCD;
`recoverCommon_of_kernel_order` connects this to the actual raw-kernel
unit. Common-modulus reconstruction also includes prime squares.

### Retaining the carry extends the useful modulus range

Discarding the quotient of (a+b)/m would lose information. Retain the
wrap label `t=(a+b) div m`. `wrapped_sum_product_encoded` proves

\[
s_t=S+tm=a+b,\qquad v_t=C-t=ab.
\]

`wrappedCandidate_encoded` then recovers p from

\[
m\frac{s_t-\sqrt{s_t^2-4v_t}}2+1.
\]

The public algorithm enumerates the labels, without receiving a or b.
After the quadratic prefix excludes primes at most B^2, assume
N<=B^6 and m^2>=B^3. `wrap_label_bound` proves t<2B: the smaller
prime exceeds B^2, hence q<B^4 and p+q<2B^4, whereas
`t*m^2<=p+q-2`. `recoverWrapped_semiprime` therefore guarantees a
proper factor in that bounded public enumeration.
`recoverWrapped_kernel_after_prefix` discharges the hidden common-modulus
and prefix premises from the actual unit order and failed prefix.
`recoverWrapped_gcd_count` bounds recovery by 2B GCD queries. This
is a query count for a known modulus, excluding modulus acquisition and
any backend bit-complexity theorem.

All candidate outputs are checked by `recoverCommon_sound` or
`recoverWrapped_sound`, including guesses outside the coverage conditions.
`recoverSquare_semiprime_square` handles repeated prime factors by public
integer-square-root preprocessing before the distinct-prime transport.

### Charge order extraction and reuse its original source

The replay partially factors N-1 by constructing one degree-B additive
prefix polynomial and evaluating it at B column targets. Every subsequent
residual R divides that original modulus. `retainedPrefixValues_downcast`
proves that reducing the saved B values modulo R gives the literal prefix
values at R; `retained_column_gcd` preserves each original column's GCD.
The polynomial is constructed once, even when several small prime powers
are removed. Lazy leaf scans and trial division use integers at most B^2.

`rough_residual_cases` proves that a positive remaining R<=B^6, with no
prime divisor at most B^2, is one, prime, or a semiprime; repeated factors
are included. `rough_residual_prime_after_prefix` certifies primality when
R<=B^4. Larger rough residuals are retained as unresolved. The routine
uses no factorization or primality oracle to classify them.
`rough_residual_half_bound` records the strict recursive size reduction
after removing two from N-1; it does not provide a free recursive solver.

Known prime factors are peeled from a retained annihilating exponent
using modular powers and GCDs. A proper GCD returns a factor immediately.
A whole-modulus GCD removes the proposed divisor; a GCD of one retains
it. An unresolved rough part is tested as a whole and removed only if
its quotient power is globally one. Otherwise the result explicitly
reports `unresolved-rough-order`. When the remaining prime-divisor set
is complete, public power checks certify the exact order before recovery.
Raw powers, the original polynomial, residual reductions, GCDs, trial
divisors, order powers, certificate checks and quadratic candidates are
all included in the standalone control timing.

`rough_kernel_order_prime` further narrows the unresolved channel: a
nontrivial raw-kernel unit annihilated by an actually rough exponent has
prime global order greater than B^2, so N is smaller than its order cubed.
Its numerical order remains unknown. This theorem must not be interpreted
as an algorithm that obtains that prime for free.

### Why adjacent cancellation can still lack a separating signal

Keep the raw-kernel unit itself as a possible row base, upstream of the
older projection that sends it to one. `kernel_row_step` proves
`alpha^N=alpha`, and `kernel_row_target` identifies the original target
`alpha^(a*N+B^2)` with `alpha^(a+B^2)`. The adjacent-power identity from
`SemiprimeGeometricRows` now applies to this step.

However, whenever a+B^2 lies in the root interval,
`kernel_row_diagonal_zero` proves that the original scalar row is already
globally zero. `kernel_row_mark` retains the first marked channel exactly:
its base derivative is `-(a+B^2)*target*targetDerivative`. That index is
public and is shared by both reductions. Endpoint cancellation and this
marked identity alone do not discover the missing common order. These
statements preserve the cofactor source and do not exclude information
in higher jets, unequal local multiplicities or other transforms.

The retained polynomial also supplies cancellation after those scalar
zeros. Differentiate the cleared polynomial identity first, then evaluate
at adjacent roots. `adjacent_root_first_jet` proves, writing
`D_k=P_L'(alpha^k)`,

\[
\alpha D_{k+1}(\alpha^{k+1}-\alpha^L)
=\alpha^L(\alpha^{k+1}-1)D_k.
\]

It holds over every commutative ring, including nonunit alpha and zero
endpoints. `kernel_row_first_jet_step` transports it to the literal
raw-kernel row labels. This keeps a cofactor relation after the scalar
detector has saturated; no division by a zero endpoint occurs in the
proof. Using it for a scalar row update would require checking the
endpoint's invertibility first. A complete update algorithm and coverage
bound are not supplied by this identity.

### Positive and unresolved controls

On the saved `1373653=829*1657` input, the charged base-2 routine exposes
1657 during order peeling. For base 3, `control_base_three_kernel_order`
certifies order 207, and `control_kernel_certificate_recovers` proves
direct recovery of 829. The retained channels are sum 12, product 32
and discriminant 16. A deliberately capped two-base scan, previously
exhausted, now returns 1657 through this fallback without any row source.

`control_wrapped_kernel_order` and `control_wrapped_certificate_recovers`
check `769841=641*1201`, B=10, and literal base 508038 with order 40.
Here m^3<N, while m^2>=B^3. `control_wrapped_recovery` checks S=6, C=481:
label zero gives candidate 121 and GCD one; label one restores sum 46
and product 480 and returns 641. The public replay obtains the order
from N-1, including the retained-prefix primality certificate for 9623.
The literal base is an offline diagnostic control, not a guaranteed
output of a small automatic base menu.

`control_small_order_wrap_exhausted` checks `697=17*41`, B=3 and common
modulus 2: the actual label is 14 and all six enumerated candidates miss.
The charged base -1 routine certifies order two and reports
`unresolved-common-order`. A further `299=13*23` control removes the
unknown rough part 149 as a whole, certifies order two, and remains
unresolved at recovery.

For `13747=59*233`, B=5 and base 4, the charged routine strips 2 and 3
from N-1, leaving `2291=29*79>B^4`. Its active quotient power has GCD
one, so it reports `unresolved-rough-order`. The separate proposed-order
certificate `control_active_rough_kernel_order` proves order 29, and
`control_active_rough_reconstruction` checks that knowing this order
would recover 59. The runtime receives no such order or reference factors.
This isolates an actual missing acquisition step rather than silently
replacing it with oracle advice.

The exact replay has 4841 retained-source comparisons, including 15709
saturated residual values; 2045 partial-factorization comparisons; 911
rough-prime certificates and 889 explicitly unresolved setup tails.
It checks 129 zero-wrap and 200 bounded-wrap reconstructions, 244 square
reconstructions, 35 square-preprocessing cases and 24 saturated kernel-row
and marked-channel identities. Another 1260 exact first-jet cancellation
comparisons include 402 zero-endpoint cases. Reference factorization and order checks
occur only in independent validation outside timing.

The same frozen 21-input corpus is again recovered in full. Its ordinary
path still uses nine prefix factors, one raw factor, one projection
factor, eight short-period factors and two original residual factors.
The new common-order fallback is exercised by the additional controls,
not by an altered corpus. Replay identifier 202610030603 records this
deterministic extension; no new random input sample is generated.
The audit pins 44 source inputs, preserving the preceding 40-input
source chain and its parent artifact.

The warning-as-error module build, strict direct ordinary-root import,
all 14 namespace linters and complete transitive axiom audit pass.
There are 53 public theorems, nine definitions and 37 generated helpers;
all 99 declarations, including 90 proofs, use only `propext`,
`Classical.choice` and `Quot.sound`. The module is registered in the
ordinary root and semiprime explorer family. Work remains local.

A sufficiently large known common order now has a proved linear-in-B
recovery branch. The remaining universal requirements include obtaining
useful order data when a rough part is active, handling a common order
below the wrap threshold, proving bounded seed coverage, reducing the
nonkernel residual source cost, and proving the complete backend bit
bound. No guaranteed one-sixth factorization theorem is claimed.

## Bounded order acquisition and a scaled progression prefix (2026-10-03)

[`SemiprimeProgressionPrefix`](../RiemannGaussian/SemiprimeProgressionPrefix.lean),
the [charged public replay](../scripts/probe_semiprime_progression_prefix.py),
[saved audit](semiprime-progression-prefix-audit.json) and
[focused checker](../scripts/CheckSemiprimeProgressionPrefix.lean) strengthen
the known-common-modulus branch and implement bounded order acquisition.
The ordinary prefix, square handling and all previous source chains are
retained. Universal one-sixth bit complexity remains open.

### A common modulus only needs to reach B

After the ordinary prefix, p>B^2 for the smaller prime. In the budget
N=pq<=B^6, `smaller_factor_le_cube` proves p<=B^3. If an actual common
modulus m>=B divides p-1 and q-1, the positive index a in p=ma+1 obeys
a<=B^2, as proved by `common_index_le_square`. Thus the progression
`mk+1`, for 1<=k<=B^2, covers the smaller factor.

The B^2 members stay implicit. Use the monic polynomial

\[
Q_{m,B}(X)=\prod_{i=0}^{B-1}(X+m(i+1)+1)
\]

at the B points `X=m*j*B`, 0<=j<B. `blockPolynomial_eval` retains the
exact original block product. `blockPolynomial_degree` proves degree B,
including repeated roots and nonunit m over the coefficient ring.
`block_column_gcd_eq` connects each column to its original lazy leaves.

`common_progression_extent` discharges an important size condition:
m<=p-1 and B^2<p imply m*B^2+1<N. Every leaf is therefore positive
and below N. A whole-modulus column can safely trigger one lazy B-leaf
scan rather than terminate without recovering either prime.
`factorProgression_semiprime` proves complete recovery for this branch.
`factorProgression_gcd_count` bounds the post-evaluation queries by 2B;
`factorProgression_sound` checks every returned divisor.

This lowers the proved modulus-size premise from the earlier
`m^2>=B^3` carry scan to m>=B. `factorProgression_of_kernel_order`
connects it to an actual raw-kernel order. The public-power route
`factorProgression_of_public_checks` does not require a kernel base.
`known_order_factor_or_progression` removes the clear-check premise:
for an actual known order reaching B, either a prime-divisor power check
returns a proper factor, or every check is clear and the common progression
recovers a factor. `order_prime_test_ne_one` excludes a whole-modulus
GCD at these exact-order tests.

### Preserve global collisions before deflation

The bounded acquisition retains b baby records `((g^i).val,i)`, 0<=i<b,
and b giant records `((g^(j*b)).val,j)`, 1<=j<=b. Both lists are sorted
by the public residue and merged once. Matching labels are retained even
when their residues agree globally: their distance `j*b-i` is useful
integer information, rather than an ambiguous factor GCD to discard.

`matchSorted_sound` keeps both original labels.
`matchSorted_none_no_common` proves that ordered merge misses no common
residue, including duplicate records. `matchComparisons_le` bounds the
merge by the sum of the list lengths. `sortedRecords_pairwise` and
`mem_sortedRecords` discharge its sorting and information-preservation
premises for the actual source lists.

`boundedCollision_annihilator` proves that each returned pair yields a
positive annihilator at most b^2. `boundedCollision_succeeds` proves
coverage of every actual global order in that range.
`boundedCollision_none_iff_large` identifies exhaustion exactly with
order greater than b^2 for the positive input modulus.
`boundedCollision_merge_count` bounds lookup by 2b comparisons after
the two sorts. These are implemented ordered lists, not a Cartesian scan.

The public probe chooses b=2B, hence its cap is 4B^2. It generates each
source iteratively, charging one modular power and 4B-2 modular
multiplications, both comparison sorts, at most 4B merge comparisons
and its unit checks. A collision may give a multiple of the order.
The derived annihilator is at most 4B^2, so ordinary trial factorization
tests divisors only up to 2B. Power/GCD peeling then obtains an exact
order or a proper factor. Every final prime-divisor power check is charged.
The prototype uses no factorization of N-1 or hidden numerical order.
It reports orders below B and lookup exhaustion explicitly.

This closes the bounded acquisition range rather than the full target:
a useful unit whose order exceeds the cap need not yield its order value
through this lookup. The sorting and trial-factor runtime are independently
replayed; the module does not provide a complete backend bit-cost proof.

### Exact controls and independent replay

For `2929=29*101`, B=4 and literal base 2535,
`control_small_common_certificate` checks the order-four public powers.
`control_small_common_arithmetic` verifies that all eight earlier carry
candidates miss and that m^2<B^3. The new ordered search first derives
annihilator 8, then peels it to 4. `control_small_common_recovers`
assembles the public certificate and failed ordinary prefix, while
`control_small_progression_result` checks that the actual four-point
polynomial recovery returns 29. No reference factor enters that algorithm.

The formerly unresolved `13747=59*233`, B=5 and base 4 control now has
`control_active_rough_collision`: the literal sorted lookup returns
labels (1,3), deriving annihilator 3*10-1=29 itself. The public replay
certifies the order and reconstructs 59 without factoring N-1.
`control_active_rough_bounded` also connects it to generic lookup coverage.
The saved 1373653 base-3 control obtains a nonexact distance 414, peels
to order 207 and returns 829. The wrapped 769841 control obtains order
40 and returns 641 using the progression batch.

The negative small-order control 697 at base -1 obtains order two and
reports `unresolved-small-order`. The new large-order control is
`14608133=2207*6619`, B=16, literal base 64. `control_large_arithmetic`
checks the actual semiprime, prefix complement and public unit.
`control_large_bounded_exhausted` proves global order 1103, raw-kernel
membership and exhaustion of the chosen cap 1024. It is not reported
as a factor or as successful exact-order acquisition.

The independent replay compares 3089 exact progression batches,
including 153 saturated-column recoveries; 5960 bounded-order tests,
including 2873 exhausted tests and 1488 nonexact distances; and 1010
covered common moduli. It also checks 339 prefix-clear semiprime/unit
cases with actual order in [B,4B^2]: all return a factor, with 325 found
during power checks. Of these 339 cases, 287 lie outside the raw kernel.
Reference orders and factorizations are validation-only, outside timing.

All 21 frozen normal inputs remain recovered with the same ordinary
status split. The two new recovery improvements are additional controls,
not a replacement corpus. Replay identifier 202610030701 records the
deterministic replay; no fresh random sample is generated. Complete
timings include square and ordinary-prefix work, unit checks, source
generation, sorting, lookup, trial divisors, power checks and any new
progression polynomial. The new audit pins 48 sources, preserving the
preceding 44-source chain and its parent artifact.

The module passes warning-as-error compilation, strict direct ordinary-root
import, all 14 namespace linters and the complete transitive axiom audit.
It has 41 public theorems, ten definitions and 77 generated helpers;
all 128 declarations, including 110 proofs, depend only on `propext`,
`Classical.choice` and `Quot.sound`. It is registered in the ordinary
root and semiprime explorer family. Work remains local.

Remaining universal obligations include handling useful orders beyond
the fixed cap, obtaining a suitable seed when the known order stays below
B, reducing the nonkernel interval source cost, and certifying the full
every-run bit-operation bound. These are not assumed by the new coverage
or lookup theorems. The goal remains the complete one-sixth guarantee.

## Complete bounded collision-to-factor transport (2026-10-03)

[`SemiprimeCollisionPeeling`](../RiemannGaussian/SemiprimeCollisionPeeling.lean)
closes the order-reduction step between retained collision labels and the
common-modulus progression. The [public replay](../scripts/probe_semiprime_collision_peeling.py),
[saved audit](semiprime-collision-peeling-audit.json) and
[focused checker](../scripts/CheckSemiprimeCollisionPeeling.lean) accompany
the new ordinary-library module. The complete one-sixth guarantee remains open.

### Derive the order rather than supply it

The bounded lookup returns labels (i,j), hence a positive annihilator
e=j*b-i<=b^2. It need not be the exact order: the 2929 control gives e=8
for an order-four base, and the 1373653 control gives e=414 for order 207.
Discarding a global equality as a whole-modulus GCD would discard this
integer distance. Retaining it avoids constructing the row matrix for
this branch.

`removablePrime` searches the current exponent's ordinary prime factor list
for a public equality g^(m/r)=1. `peelOrder` removes that prime and repeats.
`removablePrime_some` proves that every removal preserves an annihilator;
`removablePrime_none` supplies the complete prime-divisor nonunity tests.
`peelOrder_eq_order` proves that any positive annihilator is reduced to
the exact global order. Neither the order nor a factorization of N-1 is
an input. `peelOrder_pos_dvd` also retains positivity and divisibility
of the result, even outside the annihilator case.

`primePowerValues` retains all final prime labels and power-test residues,
including repeated prime factors. `primePowerValues_none_clear` proves
that a proper-factor scan returning none is a complete clear certificate
for an exact positive order: a whole-modulus GCD is impossible there.
`primePowerValues_clear_none` proves the reverse transport.

`factorAnnihilator` performs this actual reduction, scans the retained
prime-test values, then calls the common-modulus progression when the
derived order reaches B. `factorAnnihilator_semiprime` proves recovery
for every prefix-clear semiprime with a useful positive annihilator.
`factorCollision` obtains the annihilator internally from the actual
sorted lookup. `factorCollision_semiprime` proves complete recovery when
the supplied public unit has order in [B,b^2], in the same N<=B^6 budget.
It includes unequal prime sizes and does not require raw-kernel membership.
The unit-order range is a coverage condition, not an algorithm input or a
proved universal seed theorem. Both return paths have unconditional
proper-divisor soundness theorems.

### Count the retained operations

For a positive annihilator e, let R be the number of successful removals
and L its prime-factor-list length. `peelRounds_pow_le` proves 2^R<=e;
`primeFactors_length_pow_le` proves 2^L<=e. The actual first-prime search
has at most its list length power queries (`primeSearchPowerCount_le`).
`peelPowerCount_le` bounds all stripping searches by (R+1)*L queries.
`annihilatorGcdCount_le` bounds the final prime-power scan and progression
recovery together by L+2B GCDs. These are separate from the collision
source/sorting work and polynomial construction/evaluation.

The Python variant mirrors this global-power-first reduction. It charges
every repeated trial factorization, including the final prime list, all
unit and annihilator checks, source generation, comparison sorts, merge,
stripping powers, final residue powers/GCDs and any progression polynomial.
It can perform more work than the frozen early-GCD prototype; no runtime
speedup is inferred. The trial-factor loop and complete residue/bit backend
are still not formal complexity certificates.

### Exact controls and independent replay

`control_nonexact_peeling` proves that the literal 2929 base reduces
annihilator eight to four. `control_nonexact_factor` checks the actual
annihilator-to-factor function returning 29. `control_active_rough_factor`
connects the 13747 base-4 control to the complete bounded lookup and
internally derived order, without supplying order 29 to that function.

The independent replay checks 8415 exact reductions, including 5610 from
nonexact annihilators. All 339 prefix-clear semiprime/unit cases in the
covered order range return a factor: 325 from exact-order prime tests and
14 from the common progression. Of these cases, 287 are outside the raw
kernel. Reference orders and factorizations are validation-only, outside
the public routines and their timing.

The four positive controls return 29, 59, 829 and 641. The 1373653 control
first reduces 414 to 207, then reaches a whole-modulus progression column
and recovers 829 through its lazy leaves. The 697 base-minus-one control
still returns unresolved-small-order; the 14608133 base-64 control still
exhausts the cap 1024, below its true order 1103. Neither is counted as a
factor. The original 21-input corpus is inherited from the verified frozen
parent audit and is explicitly not rerun for this stripping extension.
Replay identifier 202610030801 records a deterministic replay, without a
fresh random sample. The new audit verifies and pins 52 source inputs,
including the complete preceding 48-source chain and its parent artifact.

Warning-as-error compilation, strict direct ordinary-root import, all
14 namespace linters and the complete transitive axiom audit pass. There
are 19 public theorems, nine definitions and 48 generated helpers; all
76 declarations, including 53 proofs, use only `propext`, `Classical.choice`
and `Quot.sound`. The module is registered in the ordinary root and
semiprime explorer family. All work remains local.

The bounded information pipeline is now proved through an actual factor
function: collision labels -> positive annihilator -> exact order ->
proper power-test factor or common progression factor. Useful seed
coverage, above-cap orders, the nonkernel interval source cost and the
complete every-run bit-operation bound remain open. No general factoring
exponent or universal one-sixth theorem follows from this branch alone.

## Deterministic small-seed extension and universal routing (2026-10-03)

[`SemiprimeSeedLcm`](../RiemannGaussian/SemiprimeSeedLcm.lean), the
[charged public replay](../scripts/probe_semiprime_seed_lcm.py),
[saved audit](semiprime-seed-lcm-audit.json) and
[focused checker](../scripts/CheckSemiprimeSeedLcm.lean) remove unresolved
small orders from a universal factor-or-large-order routing stage. This
is a reduction toward the full target, not a complete sixth-root factorizer.

### A public nonroot replaces a successful-seed premise

Maintain a known positive modulus M dividing both p-1 and q-1. Initially
M=1, with no hidden information. When M<B, test the public integers
1,...,M+1 against X^M-1. After the ordinary prefix, p>B^2, so all these
integers are distinct modulo p and are units modulo N. A nonzero degree-M
polynomial cannot have M+1 roots in that field.

`small_power_nonroot` proves this degree-count argument.
`seedChoice` implements the actual ordered modular-power scan;
`seedChoice_some` retains its integer label and nonunity certificate.
`seedChoice_succeeds` proves the public scan cannot exhaust in this
range, and `seedChoice_unit_after_prefix` derives the unit property from
the preceding prefix result. Neither a reference prime nor a numerical
order enters the scan. X^M-1 is a coverage argument: the implementation
performs modular powers and constructs no coefficient or row matrix.

A proper GCD of the selected power residual returns a factor immediately.
Otherwise the bounded power lookup derives an annihilator, and the
previous `peelOrder` derives the exact order m. A proper prime-power GCD
again returns a factor. If those checks are clear, m divides both hidden
prime cardinalities, so M is replaced by lcm(M,m). Since the selected
seed was not annihilated by M, m does not divide M. `lcm_doubles` proves
the new modulus is at least 2M. `certified_lcm_extension` combines this
growth with the actual public order reduction and clear-check certificate.
Retaining the LCM preserves useful integer order information from earlier
seeds rather than starting every seed attempt from scratch.

### The complete N-only routing theorem

`seedLoop` stops with a progression factor when M reaches B. If its
bounded lookup instead exhausts, it returns the selected integer base as
a large-order certificate. `seedLoop_progress` proves that fuel satisfying
B<=2^fuel*M prevents every unresolved seed, unit, small-order or fuel
outcome for a prefix-clear semiprime with the maintained common modulus.
The algorithm uses public fuel clog(2,B), starting at M=1.

`routeByWidth` checks prime squares and the complete ordinary prefix before
the loop. Its tiny-width classical fallback is restricted to N<=729 by
`small_width_input_bound`. `routeByWidth_semiprime` discharges the loop's
initial common-modulus and fuel premises. `publicRoute` receives only N
and computes its minimal sixth-power width.
`publicRoute_semiprime` proves, for every product of two primes and either
ordering, that the actual procedure returns either a proper divisor or
an explicit public unit with order greater than 4B^2. Squares and arbitrary
factor ratios are included. A large-order outcome is not counted as a factor.
There is no successful-seed, known-order or smoothness premise.

`seedModuli` retains the common modulus at each actual seed stage.
`seedModuli_budget` bounds the number of stages by the supplied fuel and
the sum of their candidate capacities by B*fuel.
`logarithmic_setup_budget` specializes these bounds to the actual public
fuel and block: at most B*clog(2,B) seed power candidates and
4B*clog(2,B) baby/giant records across all bounded lookups. Sorting, every
trial factorization and order-stripping test, GCD recovery and polynomial
arithmetic are separate charged categories. These source/query bounds
are not a complete bit-operation implementation theorem.

### Small-order control and independent replay

The new control is 2199023255551=2^41-1=13367*164511353, with B=115.
`control_mersenne_arithmetic` checks both primes, the sixth-power bracket
and p>B^2. `control_mersenne_power` and `control_mersenne_order` certify
the literal base-two order 41, below B. The frozen bounded branch obtains
annihilator 9430, reduces it to 41 and reports unresolved-small-order.
`control_mersenne_next_seed` proves the actual M=41 scan returns base 3.
`control_mersenne_routing` discharges every arithmetic premise of the new
complete route on this input. The public replay records moduli [1,41],
seeds [2,3] and a base-3 above-cap outcome. This is a resolved routing
failure, not a newly extracted factor.

The deterministic small-input replay checks all 1081 ordered prime products
with 2<=p<=q<200, including 46 prime squares. It returns 358 proper factors
and 723 independently verified large-order units, with no unresolved
outcomes. Four of these cases perform an LCM update; the separate Mersenne
control performs two seed stages. Reference orders and factors are used
only after the timed public call. Additional controls cover a recovered
13747 factor, the above-cap 14608133 and 2929 inputs, and the finite-small
697 factor. No fixed-base positive control is silently substituted for
the N-only seed policy.

All 21 frozen normal inputs are freshly replayed through this new routing
procedure: nine prefix factors, twelve large-order certificates and no
unresolved routes. The preceding factorizer and its 21 recorded factor
recoveries are unchanged; this new route does not claim twelve additional
factors or replace that baseline with a partial factorizer. Replay
identifier 202610030901 records the deterministic extension, without a
fresh random corpus. The audit verifies and pins 57 sources, preserving
the preceding 52-source chain and its parent artifact and adding the
bounded tiny-input baseline source.

The warning-as-error module build, strict direct ordinary-root import,
all 14 namespace linters and the complete transitive axiom audit pass.
The module has 17 public theorems, seven definitions and one routing
datatype. The checker covers all 120 declarations, including 77 proofs,
using only `propext`, `Classical.choice` and `Quot.sound`. It is registered
in the ordinary root and semiprime explorer family. Work remains local.

The universal target is now reduced, without a seed-menu hypothesis, to
handling the certified above-cap unit population at sixth-root cost and
certifying the complete bit backend. Both large raw-kernel and large
nonkernel cases remain; the latter's existing retained interval source
still has its B^(3/2) cost. The one-sixth guarantee remains open.

## Extracting local periods without a pair matrix (2026-10-03)

[`SemiprimeLocalOrderRouting`](../RiemannGaussian/SemiprimeLocalOrderRouting.lean),
the [charged N-only replay](../scripts/probe_semiprime_local_order_routing.py),
[saved audit](semiprime-local-order-routing-audit.json) and
[focused checker](../scripts/CheckSemiprimeLocalOrderRouting.lean) refine the
previous factor-or-large-global-order route. The global order can be large
even when one prime field has a short period. Extracting that local
information can give a factor before the old factorial projection or
long exponent-interval construction.

### The original-unit batch preserves the separating collision

Retain the selected unit g. For b=2B construct b giant roots
g^(b*j), 1<=j<=b, and b baby targets g^i, 0<=i<b. The existing
`recoverShort` constructs the distinct-root polynomial P from the giants.
At an ordinary target it evaluates P; at an exactly shared root it uses
P' to remove the zero difference. `deflatedColumn_eq_product` in the
preceding Cartesian module identifies this value with the product of
all off-diagonal differences. It preserves a zero in exactly one prime
field, while an exact equality modulo N cannot permanently saturate the
detector. A whole-modulus column triggers at most one lazy root scan.
The signed sum of rows is not substituted for this root-preserving
product.

`recoverShort_of_pair` connects either prime-field orientation to a proper
GCD and the actual recovery function. `recoverShort_of_unequal` applies
the previously checked `unequal_small_periods_have_cover`: unequal local
orders suffice whenever their minimum is at most b^2. The old
coprimality premise is unnecessary for this original-unit batch. Neither
local order nor a numerical reference prime enters the public scan.

`global_order_eq_lcm` proves the exact CRT relation between the global
order and the two retained local orders. If those local orders are equal,
the global order is their common value. Combining this relation with
unequal-order extraction gives `failed_original_short_forces_long`: a
failed batch on an above-cap global-order unit forces BOTH local orders
above b^2. The proof does not assume that the runtime knows either order.

`short_source_budget` proves b source records per axis and polynomial
degree at most b, including repeated global residues. `shortGcdCount_le`
charges at most 2b GCD queries after evaluation. No b-by-b candidate matrix
is constructed by the optional polynomial replay. These source and query
bounds do not certify the cost of its polynomial or bit backend.

### Universal routing now exposes two specific residual populations

`refineBase` runs the original-unit batch first. If it fails and the raw
N-1 power is one, `KernelData` retains the seed, both large local periods,
and the fact that its global order divides both p-1 and q-1. The numerical
order is still unavailable to the procedure. If the raw power is nontrivial,
the existing checked staged projection either supplies a factor or a
clear projected GCD. A second short batch then extracts another factor
or certifies two projected local periods above 4B^2.

`projected_local_structure` connects that retained projected unit to
coprime local orders and proves that every prime factor of either order
exceeds B. `LongData` preserves those properties together with the
original seed, its two original local-period bounds and the public clear
GCD. It does not discard the richer seed after summarizing its periods.

`refineBase_semiprime` proves correctness of this exact public refinement
for a unit supplied by the preceding above-cap certificate. The N-only
`publicRoute` checks squares, invokes the previous universal seed route,
and refines each of its large-base outputs. `publicRoute_semiprime`
discharges the unit, cap, distinct-prime and positive-width conditions
for EVERY semiprime, including arbitrary factor ratios. There is no seed
menu, smoothness or supplied-order hypothesis. Its outputs are a proper
factor, `KernelData`, or `LongData`; unresolved outcomes are excluded.
The latter two outputs remain nonfactors.

`refinementGcdCount_le` charges at most 9B+1 GCD queries to the two batches
and checked projection when reached. `refineBaseGcdCount_le` includes the
additional base-unit check, giving 9B+2. The preceding seed costs are
separate and retain their earlier logarithmic setup bounds. Powers,
sorting, polynomial arithmetic, all setup and their bit costs must also
be charged in the terminal complexity theorem.

### Exact controls, remaining cases and validation

`control_twenty_nine_short` verifies a factor exists in the original
degree-eight batch for base two on 2929=29*101. The fresh replay returns
29 in one batch GCD query. `control_mersenne_short` verifies recovery from
the degree-230 original-unit batch for base three on
2199023255551=13367*164511353. Its other-field power certificate is checked
in `control_mersenne_other_power`; numerical order advice is unnecessary.
The replay returns 13367 after the seed loop retains M=1,41 and switches
from base two to three. The former above-cap 14608133=2207*6619 control
now yields 2207 in the checked projection. This is its actual N-only
base-two route, not the earlier deliberately supplied kernel base 64.

The separate retained control 1266003461=20543*61627, with B=33, remains
a large-kernel certificate under the N-only policy. Its base-two local
orders are verified as 10271 and 20542 by `control_large_kernel_orders`,
using the checked field powers and exact prime arithmetic.
`control_large_kernel_certificate` proves the raw power is one and both
periods exceed 4B^2=4356. It is not a successful factoring example; obtaining
its order and factor within the target budget remains an extraction task.

All 1081 ordered semiprimes with 2<=p<=q<200 are freshly replayed, including
46 squares. All return proper factors: 706 original short, eight projected
short, nine projection, 35 exact-order seed, 178 finite-small, four LCM
progression, 95 prefix and 46 square recoveries. This finite successful
population is an implementation regression, not the universal complexity
theorem. Independent factors and orders are checked only outside timing.

The 21 frozen normal inputs are also freshly replayed: nine prefix factors,
three original short factors, six projected short factors, one projection
factor and TWO projected-long certificates. There are no unresolved
routes. The remaining numerical controls are 2803308161=44963*62347 with
cap 5776, and 723392533321=714107*1013003 with cap 36100. Their independently
checked projected local orders are respectively (22481,10391) and
(357053,506501); none fits this short cover. These numerical values are
not new Lean order theorems. The earlier complete baseline and its saved
21 factor recoveries remain unchanged.

Replay identifier 202610031001 denotes this deterministic replay, without
a new random corpus. All N-specific seed work, repeated wrapper setup,
source construction, sorting/deduplication, derivative and polynomial
work, lazy witness recovery, raw power, every staged exponent and power,
retained trace and GCD are timed. The replay sorts distinct targets while
the Lean specification scans their supplied order; it validates coverage
and work categories, not equality of the first returned factor.

The audit verifies and pins 61 sources, preserving the complete 57-source
parent chain and its audit. Strict targeted compilation, strict direct
ordinary-root import, all 14 namespace linters and the complete transitive
axiom audit pass. The new module has 23 public theorems, 11 definitions
and one routing datatype. All 108 declarations, including 68 proofs and
generated helpers, depend only on `propext`, `Classical.choice` and
`Quot.sound`. It is registered in the ordinary root and the semiprime
explorer family. Work remains local.

The global above-cap population is now split without hidden local-order
premises. Large common-kernel extraction, projected-long extraction at
linear source width, and the complete every-run bit backend remain OPEN.
The existing long-interval source still costs B^(3/2); a small GCD-query
count does not pay for it. No guaranteed one-sixth factorization exponent
or full factorizer follows from this refined route.

## Public kernel stripping and certified smaller-semiprime transport (2026-10-03)

New local artifacts:

- [SemiprimeKernelResidual.lean](../RiemannGaussian/SemiprimeKernelResidual.lean)
- [Optional N-only replay](../scripts/probe_semiprime_kernel_residual.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeKernelResidual.lean)
- [Source-pinned replay](semiprime-kernel-residual-audit.json)

This continues the preceding kernel branch. It does not replace any earlier
source, replay or negative result. The implementation receives N alone;
neither local orders nor the factors of N-1 are supplied to its routine.

### Reuse one source and extract a complete small-prime list

For E=N-1 and B=sixthWidth(N), `splitSmall` constructs the additive prefix
with B roots and B labelled targets once. `retained_column_data` proves
that its original values have exactly the same GCD with each residual
R dividing E as freshly constructed R-values. Thus the source stays
available while R changes; no quadratic leaf matrix is constructed.

`smallPrimeChoice` finds the first nonunit retained column and expands
only its B integer leaves. The chosen leaf GCD is at most B^2, so its
minimal prime can be obtained by trial division through B. If R itself
is at most B^2, its minimal prime has the same trial bound.
`smallPrimeChoice_some` proves each selected prime is real, divides R,
and is at most B^2. `smallPrimeChoice_none` proves that termination leaves
every prime divisor strictly above B^2.

`smallPrimeLoop` removes ONE prime per stage and retains multiplicities
in its list. `splitSmall_complete` discharges its fuel bound
clog(2,E+1): the final R is positive, its small-prime product S satisfies
S*R=E, and its prime list has length at most that fuel. Cached column
queries, the selected leaf scan and the recomputed chosen leaf GCD are
all charged by `splitSmall_gcd_budget`, at most
(2B+1)*clog(2,E+1). This count does not certify polynomial or bit costs.

The smooth case also reuses the extracted list. `orderFromPrimes`
tests each suffix annihilator. A successful suffix removes the head
prime; a failed suffix contributes that prime to the order and replaces
the active element by its corresponding power.
`orderFromPrimes_eq_order` proves this returns the actual order whenever
the retained list annihilates the element.
`orderFromPrimesPowerCount_le` charges at most twice the list length in
modular powers. It does not factor the large original annihilator again.

### Transport a rough order from a strictly smaller input

Let h=g^S be the retained active unit. If h=1, the preceding prime-list
procedure determines orderOf(g); `smooth_kernel_recovers` proves one
quadratic candidate recovers a factor. The large original order is
already a common divisor of both field group sizes and supplies the
required cubic reconstruction bound.

If h is nontrivial, `activeUnit_certificate` proves its order is prime,
divides both p-1 and q-1, annihilates h at R, and satisfies
N<orderOf(h)^3. The proof uses the roughness of R and the checked common
order bound `common_order_lt_cube`; the order is not given to the routine.
When R<=B^4, roughness forces R to be that prime order and one candidate
again suffices.

For R>B^4, `active_large_residual_semiprime` proves R is a semiprime,
including the possibility of a square. `splitSmall_half_bound`, with
the kernel's discharged parity condition, proves 2R<N. The procedure
calls the preceding N-only local-order router on R once. A returned
proper divisor d identifies orderOf(h) by a single test of h^d=1:
choose d on success, otherwise R/d. `selectedOrder_eq_order` proves this
selection, including repeated residual prime factors.
`recoverResidual_semiprime` then proves single-candidate reconstruction
of a factor of the original N.

If that child router returns a kernel or projected-long certificate,
`KernelRoute.residual` retains R, the original unit, the active unit,
the full extracted prime list, and the child route. `GoodKernel` keeps
the exact encoding and active-order facts alongside the child's semiprime
certificate. `residual_transport` proves that any later proper factor
of R yields a proper factor of N. This is a transport theorem; obtaining
the child factor remains a charged task.

`kernelRoute_semiprime` proves the whole kernel handler correct.
`publicRoute_semiprime` discharges every condition for the N-only wrapper
on every semiprime. Its result is a proper factor, an original
projected-long certificate, or the above smaller-semiprime carrier.
Original-input kernel outputs are eliminated, but this is not a complete
recursive factorizer.

### Saved recoveries, a pending child and scoped validation

The new control 3542303047=29759*119033 has B=40 and public kernel base 2.
The split extracts S=6 and leaves
R=590383841=14879*39679, beyond B^4. The child public router, with B=29,
returns 39679 from its projected short batch. The active value is 64;
its single order-selection test chooses 14879, and one quadratic candidate
returns 29759. The split uses 49 GCD queries. The preceding common-order
kernel routine still reports `unresolved-rough-order` on this same N;
that negative baseline is saved alongside the new result.
`control_residual_arithmetic`, `control_residual_powers`,
`control_residual_selected` and `control_residual_recovery` check the
arithmetic, active powers, selection and final recovery in Lean. Equality
of the executable child's particular first factor is replay evidence,
not a new closed Lean evaluation theorem.

The earlier 1266003461=20543*61627 control now returns 20543. It extracts
S=20, factors R=63300173 through the child projection, and selects common
order 10271. Two extra fixed controls exercise the other kernel branches:
117987841=7681*15361 derives order 3840 from its retained small-prime list,
while 801866647=14159*56633 leaves prime residual 7079. Both recover their
smaller original prime from one candidate. These particular routes and
orders are executable regressions under the universal compiled contracts.

A separate control retains a real pending task:
87851329807=148199*592793, B=67, S=6, and
R=14641888301=74099*197599. Its child router has B=50 and returns a
projected-long certificate. Independent checking finds projected local
orders 37049 and 32933, both beyond its 4B^2=10000 cover. The original
factor is not recovered. This control is saved as
`certified-smaller-residual`, without calling the child a free solver.

The replay additionally checks 512 smooth/rough splits and 1259
prime-list order extractions. It repeats all 1081 ordered semiprimes with
2<=p<=q<200, including 46 squares; all return factors with the same
distribution as the preceding replay. The frozen 21 normal inputs retain
19 factors and TWO projected-long certificates. All seven fixed controls,
including the pending one, are retained. Reference factorizations and
orders are checked outside the timed N-only routine. The extra fixtures
were selected outside timing from the specified prime families; no
discovery search is part of the routine or a new random corpus.

Replay identifier 202610031101 denotes this deterministic replay. Timing
includes every input-specific preceding route, cached prefix construction,
column/leaf GCD, minimal-prime trial test, prime division, prime-list
product, active/order power, optional child route, selection power,
quadratic square root and GCD. Its audit pins 65 sources and verifies
the unchanged complete 61-source parent chain. Python target order and
minimal-prime scan order need not match the Lean specification's first
choice; the replay checks the proved contracts and actual work categories.

The strict targeted build and direct ordinary-root check pass. All 14
namespace linters pass. The new module has 32 public theorems, 19
definitions and one routing datatype; the full transitive audit checks
179 declarations, including 110 proofs and generated helpers, using only
`propext`, `Classical.choice` and `Quot.sound`. The module is registered
in the ordinary root and semiprime explorer family. Work remains local.

The remaining obligations are recursive completion and its accumulated
source/width costs, extraction from the projected-long population at
linear B source width, and the complete every-run classical bit backend.
The existing B^(3/2) long-interval construction is still too large.
None of the new correctness, query-budget or successful-control theorems
proves the guaranteed one-sixth factorization bound.

## Complete retained kernel descent and charged width envelopes (2026-10-03)

New local artifacts:

- [SemiprimeKernelDescent.lean](../RiemannGaussian/SemiprimeKernelDescent.lean)
- [Optional N-only descent replay](../scripts/probe_semiprime_kernel_descent.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeKernelDescent.lean)
- [Source-pinned descent replay](semiprime-kernel-descent-audit.json)

This completes the recursive kernel handling left open by the preceding
entry. It preserves that entry and its entire 65-source audit. It does
not discharge the projected-long branch or the one-sixth bit theorem.

### Keep every transport frame and consume the actual child result

`Trace` is indexed by its literal input. A child frame retains the smaller
input, both parent units, the complete small-prime list, the actual child
local-order route and its recursively constructed trace. `Certified`
attaches the same semiprime, exact encoding, strict half-input and active
order facts proved by the kernel handler. A factor option and terminal
leaf are named downstream views of this richer object.

`descend` consumes an existing local-order route. A kernel result invokes
the preceding kernel handler; a residual result passes its ACTUAL child
route into the next descent level. It does not repeat that child's seed
search, polynomial source or projection. The N-only `publicTrace` computes
the initial local route once and supplies fuel L=clog(2,N+1).

`half_fuel` proves that 2R<N and N<2^(fuel+1) imply R<2^fuel.
`descend_certified` applies this inequality at every retained edge, so
the fuel cannot run out on a semiprime. `publicTrace_certified` discharges
the initial fuel bound. There are no unresolved, pending or kernel
terminal leaves in this certified trace.

`recoveredFactor` follows the retained active units when a factor is
available below. Each successful edge runs its own order-selection power,
quadratic candidate and checked GCD. `recoveredFactor_sound` proves every
returned factor proper. `certified_cases` and the universal
`publicTrace_cases` prove the exhaustive alternative: a recovered factor
of the original N, or a projected-long leaf with a certified semiprime
input at most N. The complete parent carrier remains available even in
the second alternative. This is not a factorizer: that leaf still needs
an extractor.

### Charge the whole chain, including folded child success

`depth_descend_le` bounds the number of nonempty levels by public fuel.
`sixthWidth_mono` proves every smaller input has no larger base width.
`publicTrace_width_budget` therefore bounds the sum of descended input
widths by B*L. No geometric-series estimate or free recursion is assumed.

A child local route can return a factor immediately INSIDE a kernel
handler, so its work need not appear as an additional trace frame.
`kernel_child_width_le` covers this case as well: its actual split residual
has no larger sixth-root width. `routingWidthCharge` reserves three base
width slots per descended input for its local route, cached kernel source
and optional child local route. `publicTrace_routing_width_budget` bounds
this envelope by 3*B*L. These are base-width slots; the source lists and
polynomial work of the earlier local router retain their separate
constants and logarithmic factors. The envelope is not a bit-cost proof.

`split_queries_le` places the literal small-prime stripping GCD count
inside (2B+1)*L at each input. `prefixAllowance_mono` and
`publicTrace_prefix_budget` bound the sum of these allowances by
(2B+1)*L^2. Terminal nonkernel nodes are harmlessly overcharged.
`recoveryCount_le` pays at most one downstream transport call per retained
edge; successful candidates internal to a terminal kernel handler retain
their separate preceding-stage charge. Seed work, all modular powers,
root computations, sorting, polynomial arithmetic and their bit costs
remain explicit categories outside these two envelopes.

### Deterministic replay and remaining population

Replay identifier 202610031201 uses exactly the preceding 21 normal
inputs, seven fixed controls and all 1081 ordered semiprimes below the
same prime bound 200. All small semiprimes, including 46 squares, return
proper factors. The normal population remains 19 factors and TWO
projected-long leaves. Both saved kernel recoveries still succeed; their
immediately successful child routes are charged even though their final
traces have one level.

The pending control 87851329807 now produces a two-level certified trace
ending at the projected-long leaf on 14641888301. It uses exactly two
actual local-routing calls and reuses the one computed current kernel
route. Its descended width sum is 67+50=117; the charged routing/kernel
base-width slots actually used total 184. The cached split makes 76 GCD
queries. There are no downstream recovery queries because no leaf factor
is available. This is preserved negative evidence for the remaining
extractor, not a recovered factor.

The optional replay uses a scoped adapter to give the preceding wrapper
the actual already computed current route; any smaller-input request
runs the real public router. The adapter is restored before recursion.
This prevents duplicate child work without supplying order or factor
advice. Every new routing call, kernel split, prime-list/order operation,
trace construction and successful transport is included in timing.
Independent literal factor/order/route checks occur outside timing.
The fixtures exercise immediate child success and a descent to a long
leaf; they do not constitute empirical coverage of arbitrary multi-kernel
chains. Universal chain termination is the compiled theorem above.

All 69 source pins verify, preserving the entire 65-source parent chain.
Strict targeted build and strict direct ordinary-root checking pass.
All 14 namespace linters pass. The module adds 18 public theorems,
11 definitions and two indexed datatypes. Its full audit checks 171
declarations, including 85 proofs and generated helpers, with only
`propext`, `Classical.choice` and `Quot.sound`. The ordinary root and
semiprime explorer family register the module. Work remains local.

All kernel descents and their factor transport are now discharged as a
public reduction. The unresolved mathematical extraction population is
the projected unit with two large, coprime, B-rough local periods, possibly
on a smaller retained leaf. Its known long-interval source still needs
B^(3/2) work. Linear-source extraction and the complete every-run bit
backend remain the requirements for the guaranteed one-sixth theorem.

## Public power refinement and the exact global-order information target (2026-10-03)

New local artifacts:

- [SemiprimeLongPowerRouting.lean](../RiemannGaussian/SemiprimeLongPowerRouting.lean)
- [Optional public-power replay](../scripts/probe_semiprime_long_power_routing.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeLongPowerRouting.lean)
- [Source-pinned replay](semiprime-long-power-routing-audit.json)

This preserves the full preceding descent and its 69-source audit. It
strengthens the projected-long terminal branch and recovers two selected
former long controls. It does not prove universal extraction or the
guaranteed one-sixth bit bound.

### Retain the carrier and identify the exact missing information

`CoreData` retains the projected unit, both local periods greater than
(2B)^2, their coprimality, and B-roughness. `projected_core` obtains those
facts from the actual preceding `LongData`. `projectedUnit_val` exposes
the exact public scalar without replacing the retained unit.

For a literal semiprime input n=pq at width B, `local_card_divisors` and
`local_card_bounds` relate these periods to p-1 and q-1. Under n<=B^6,
`factor_sum_bound` proves p+q<=2B^4. CRT and coprimality then give
`global_order_totient_and_sum`: the actual global order M divides
(p-1)(q-1) and strictly exceeds p+q. The proof uses the lower bound
M>16B^4 from the two retained long periods.

`sumSignal_eq_sum` consequently identifies (n+1) mod M with the literal
factor sum, since n+1=(p-1)(q-1)+(p+q). `sumCandidate_of_sum` proves the
integer quadratic decoder returns the smaller factor. The checked
`recoverKnownOrder` is sound even for an incorrect proposed modulus;
`recoverKnownOrder_of_long` proves completeness when M is the actual
global order. M is an explicit supplied value in this theorem. No order
oracle, numerical order or factorization of a group cardinality enters
the new public routine. Acquiring M at the target cost remains open.

### Public powers extract further constraints using short sources

The active projected unit h supplies `nPower=h^n` and
`successorPower=nPower*h=h^(n+1)`. `scanPowers` checks the n-power direct
GCD, its short batch, the successor direct GCD and its short batch in that
order, stopping at the first proper factor. Each short batch uses 2B
giant roots and 2B baby targets. The preceding
`SemiprimeLocalOrderRouting.short_source_budget` bounds each polynomial's
degree by 2B. The shared-root derivative and distinct-root product backend
recover proper collisions without constructing the pair matrix.

`cross_power_order_bounds` proves that a local period containing the OTHER
hidden prime becomes short after the n power, while the first field's
period remains long. `recover_N_of_cross` closes both orientations with
the existing complete short extractor. `failed_N_forces_coprime` therefore
certifies that a failed n short batch leaves the global order coprime to n.

`successor_power_ne_one` proves that n+1 cannot annihilate both long
coprime fields. `small_card_power_bound` proves that a B-rough divisor of
the smaller field's period shared with n+1 would shorten that period to
at most B^2. `powered_orders_unequal` supplies the other short-extraction
premise. Thus `failed_successor_forces_min_coprime` certifies coprimality
to n+1 for the field attached to the smaller factor. It does not assert
this conclusion for the larger field.

The original projection supplies an additional constraint without a new
query. `retained_raw_power_dvd` proves that any divisor surviving the raw
exponent consumes one stripped copy together with the final local period
in its field cardinality. A rough prime r dividing both a surviving
period and n-1 would divide BOTH field cardinalities. Coprimality lets
its copy multiply the other retained period as well. Then both p and q
would exceed B^3, contradicting pq<=B^6.
`projected_left_coprime_predecessor`,
`projected_right_coprime_predecessor` and
`projected_predecessor_coprime` formalize the resulting local and global
coprimality to n-1. This is information from the retained projection and
the actual input budget, rather than an extra tested exponent.

### Preserve every parent frame and charge the new work

`PowerRoute.remaining` retains the original unit, active projected unit,
n-power and successor power. `GoodPower` attaches the original long
certificate, actual power equalities, both failed short outcomes, global
coprimality to n and n-1, and the proved smaller-field n+1 condition.
`refineLong_good` proves the actual public seed handler returns a proper
factor or this stronger object.

`leafRefinement_certified` refines the terminal leaf of the entire
certified descent. `transportCandidate_sound` and
`transportCandidate_complete` transport a new leaf factor back through
EVERY retained parent active unit. Each successful edge runs its charged
order-selection power, quadratic candidate and GCD. `Packet` keeps the
original trace and refined leaf alongside its downstream original factor
option. `publicPacket_cases` proves the universal alternative of a proper
original-input factor or a certified nonfactor leaf. No unresolved route
is treated as a factor.

`scanGcdCount_le` bounds the two direct tests and two possible batches by
8B+2 GCD queries. `refinementGcdCount_le` additionally pays the seed-unit
check, giving 8B+3. `certified_leaf_input_le` and
`publicPacket_refinement_queries_le` bound this new allowance by the
ORIGINAL input's width after any kernel descent.

The handler regenerates the projection from its public seed; the replay
pays the raw n-1 power, B staged projection powers, B constructed
exponents and their sizes. The new n power, conditional successor
multiplication, all source powers and multiplications, sorting,
polynomial/remainder/derivative operations, witness recovery and GCDs are
also timed. Parent descent and successful transport retain their original
charges. The GCD and source-size theorems are not complete bit-cost bounds.

### Selected successes and preserved long leaves

Replay 202610031301 repeats all 1081 small semiprimes, including 46
squares, the 21 normal inputs and seven controls. All small inputs factor;
the normal inputs remain 19 factors and two strengthened long leaves.
The two previous kernel successes persist. The two-level pending input
87851329807 still retains the long leaf on 14641888301.

Two new fixed controls exercise the added direct signals:

| Original input | Factors used only for independent validation | Public projected value | Added successful test | Returned factor |
| --- | --- | --- | --- | --- |
| 206583301 | 10163, 20327 | 125510454 | n direct GCD | 20327 |
| 263684129 | 11483, 22963 | 116995666 | n+1 direct GCD after the n short batch | 11483 |

Both preceding N-only descents terminate at a projected-long leaf.
Discovery used reference orders outside timing in the families q=2p+1
and p=2r+1,q=4r-1. These are selected examples, not an unbiased coverage
or scaling sample. The timed procedure receives N only.

`control_cross_projection_value` and
`control_successor_projection_value` check the literal projected scalars
from public base two and public exponents. The power, primality and direct
GCD arithmetic are also compiled checks. `control_cross_refine` proves
the complete new handler returns 20327 at public seed two without a
supplied projected value. `control_successor_scan` explicitly retains
the preceding short-batch-none premise; that literal failure is verified
by the replay and is not silently promoted to a closed Lean theorem.
Neither control theorem claims a closed evaluation of the whole
preceding descent; universal routing remains `publicPacket_cases`.

All three previous long leaves survive BOTH new short batches:

| Original input | Terminal input | Actual local periods, independent reference | Added refinement GCDs |
| --- | --- | --- | --- |
| 2803308161 | 2803308161 | 22481, 10391 | 155 |
| 723392533321 | 723392533321 | 357053, 506501 | 383 |
| 87851329807 | 14641888301 | 37049, 32933 | 203 |

Independent validation computes their global orders and confirms the
factor-sum decoder. Those order acquisitions are outside the timed public
routine and remain labelled reference data in the saved JSON.
No full matrix, random scaling corpus or tuned-software comparison is
generated in this replay.

All 73 source pins verify, preserving the entire frozen 69-source parent
chain. The strict targeted build and direct ordinary-root check pass.
All 14 namespace linters pass. The module adds 53 public theorems,
17 definitions, two indexed certificate/route datatypes and one retained
packet structure. Its complete transitive audit checks 199 declarations,
including 128 proofs and generated helpers, with only `propext`,
`Classical.choice` and `Quot.sound`. The ordinary root and semiprime
explorer family register the module. Work remains local.

The extraction frontier is now a retained projected unit with two large,
coprime, B-rough local periods, global coprimality to n and n-1, and
smaller-field coprimality to n+1. Its actual global order would decode the
factor sum exactly. A universal method to obtain that information from
linear-size public sources, and the complete classical every-run bit
backend, remain required for the guaranteed one-sixth theorem.

## Retaining global collision labels around a public quarter-totient centre (2026-10-03)

New local artifacts:

- [SemiprimeTotientWindow.lean](../RiemannGaussian/SemiprimeTotientWindow.lean)
- [Optional retained-window replay](../scripts/probe_semiprime_totient_window.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeTotientWindow.lean)
- [Source-pinned replay](semiprime-totient-window-audit.json)

This stage preserves the entire 73-source public-power audit and every
preceding descent frame. It recovers all three earlier long leaves with
linear-size sources, while retaining a new larger negative control.
The guaranteed one-sixth theorem remains open.

### Cancel an annihilator without acquiring the actual order

The two coprime B-rough local periods are odd at B>=2.
`core_order_coprime_four` consequently proves that the actual global
order M is coprime to four. Since M divides the totient, M also divides
T=(p-1)(q-1)/4. `quarter_totient_properties` proves h^T=1, T divides
the totient, and p+q<T. T is an arithmetic object in the proof, not an
input to the public routine. It need not equal M: two of the recovered
old leaves have T=3M.

With sqrt denoting the integer square root, define the public centre
and proof-side offset by

```
C = (n+1-2*sqrt(n))/4
d = (p+q-2*sqrt(n))/4
```

`quarter_centre_encoding` proves C=T+d with all divisions, floors and
natural-number subtractions accounted for. Thus h^C=h^d. The large
totient component cancels, leaving the factor-sum offset as an exponent.
The runtime receives n and the cached h; no factor, order, totient or
cofactor is supplied.

### Keep the equality's labels instead of discarding a whole-modulus hit

At b=2B, construct b baby records h^i and b shifted giant records
h^C*(h^(b*j))^(-1), each with its actual exponent or block label.
Sort both lists by their integer residue and run the existing ordered
merge. A global equality carries the offset b*j+i<b^2. This retains
information that a whole-modulus GCD alone would not decode.

`shiftedCollision_succeeds` proves that a covered d produces an actual
match. `shiftedCollision_unique_offset` identifies the returned label
with d, using the retained lower bound on M. Subtracting it from C
therefore yields T. `known_totient_divisor_recovers` proves that any
totient divisor larger than p+q gives the exact factor sum through
(n+1) mod T. The checked quadratic decoder then returns a proper factor.
`recoverQuarter_complete` assembles this argument under d<(2B)^2.
`recoverQuarter_sound` remains valid for every returned candidate.

`recoverQuarter_none_gap` proves that an actual failed window forces
p+q-2*sqrt(n)>=16B^2. Failure is a certified restriction on the residual
population, not universal extraction. Proper CRT collisions among these
same shifted records are a further possible channel; this stage handles
global equalities only.

### Retain the source and every parent, and charge the work

`Source` keeps the cached active unit, centre, target power, both sorted
labelled lists, actual collision and decoded factor option. `buildSource`
constructs that source once. `WindowCertified` attaches the preceding
actual long-power certificate without supplying hidden arithmetic.
The richer `Packet` retains the preceding power packet and its entire
kernel descent. Already successful parent packets construct no new
window. A new leaf factor is transported through the retained parent
units, using the previously proved complete transport.

`publicPacket_cases` proves either a proper original-input factor or an
actual certified source on a true semiprime leaf with the large literal
factor-sum gap. `buildSource_budget` proves exactly two 2B-entry lists
and at most 4B merge comparisons; `publicPacket_source_budget` bounds
these quantities by the ORIGINAL input's sixth-root width after descent.
Neither theorem claims that sorting, group operations or the complete
backend have free bit cost.

The replay pays a new integer square root and centre, centre power,
modular inverse and inverse-step power, both geometric lists, actual
comparison merge sorts and ordered merge. A successful candidate pays
its quadratic square root and GCD. Every successful parent transport is
timed as well. The active unit is reused without projection regeneration.
Python generates the lists by geometric recurrence; Lean specifies the
corresponding residues by public powers. Their complete bit implementation
and the every-run bit theorem remain unproved.

### Three old recoveries and a new preserved negative

Replay 202610031401 verifies all 1081 small semiprimes, including 46
prime squares; all factor. All 21 normal inputs, seven earlier controls
and two preceding positive controls now factor. Exactly three inputs
require the new window:

| Original input | Terminal input | Public centre C | Retained offset d | Decoded quarter totient T | Original factor |
| --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 700800567 | 354 | 700800213 | 44963 |
| 723392533321 | 723392533321 | 180847708068 | 6515 | 180847701553 | 714107 |
| 87851329807 | 14641888301 | 3660411574 | 7423 | 3660404151 | 148199 |

The last source decodes leaf factor 74099. One charged transport edge
then recovers original factor 148199, with one order-selection power,
one quadratic square root and one GCD. Each successful window uses one
candidate GCD. No full pair matrix is constructed.

`control_old_leaf_arithmetic` checks all three offsets, public centres
and literal factor decoders. `control_first_leaf_powers` checks the first
leaf's scalar equality h^C=h^354. These are closed Lean arithmetic
checks; literal preceding route selection and the other source matches
are independently checked by replay. They are not presented as closed
Lean evaluations of every fixed routing trace.

The new selected input is
1400000552800003801=1000000007*1400000543. Its public width is B=1058,
giving window cap (2B)^2=4477456. The true offset is 8392042 and the
literal factor-sum gap is 33568170. The public packet returns no factor
and its actual global merge finds no equality. Independent validation
gives local periods 500000003 and 700000271, and M=T=350000137600000813.
These acquisitions are outside timing. Discovery chose the first safe
primes at or above the specified half-prime thresholds 500000000 and
700000000, outside the public routine. This single selected negative
is not an asymptotic lower bound or random coverage corpus.
`control_large_gap_arithmetic` checks its product, offset, cap and public
sixth-power budget without asserting a closed route-failure theorem.

All 77 source pins verify, preserving the entire frozen 73-source parent
chain. The strict targeted build and strict direct ordinary-root check
pass. All 14 namespace linters pass. The module adds 30 public theorems,
11 definitions, one indexed certificate datatype and two retained
structures. The complete transitive audit checks 132 declarations,
including 72 proofs and generated helpers, with only `propext`,
`Classical.choice` and `Quot.sound`. The ordinary root and semiprime
explorer family register the module. Work remains local.

The new information is a labelled global collision that recovers a
large totient divisor by cancellation, without first computing the
actual order. Its covered offsets still exclude the larger retained
negative. Universal coverage at linear source width and a complete
classical bit backend remain necessary for the guaranteed one-sixth
theorem.

## Proper field collisions from the cached quarter-window source (2026-10-03)

New local artifacts:

- [SemiprimeTotientResidues.lean](../RiemannGaussian/SemiprimeTotientResidues.lean)
- [Optional cached-residue replay](../scripts/probe_semiprime_totient_residues.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeTotientResidues.lean)
- [Source-pinned replay](semiprime-totient-residues-audit.json)

This stage preserves the entire 77-source quarter-window audit and
extends its extraction coverage. It recovers a selected offset far beyond
the literal window by detecting a proper prime-field collision on the
same two cached lists. The larger negative remains. The guaranteed
one-sixth theorem is still open.

### The useful information is a short local remainder

`quarterOffset_lt_order` proves the actual d is below the global period M,
even when d exceeds the window cap. `global_match_offset` consequently
proves that every global equality's returned offset is exactly d.
`failed_window_no_global` shows that a failed actual global decoder has
no global match. This is derived from the preceding certified data,
not an extra no-equality assumption in the public route.

The same cancellation h^C=h^d holds in each hidden field. If
d mod Dp<(2B)^2, decompose that local remainder as (2B)*j+i with
both indices below 2B. Its baby and shifted giant are equal modulo p.
The failed global lookup proves that they differ modulo the whole input,
so their original residual is nonzero. `proper_gcd_of_reduction` proves
that a nonzero residual vanishing modulo any nontrivial divisor has a
proper original GCD. The actual pair belongs to the two cached lists.
The existing complete distinct-root polynomial recovery therefore
recovers a proper factor.

`residue_source_of_reduced_offset` proves this for any divisor-ring
reduction. `residue_source_of_left_offset` and
`residue_source_of_right_offset` discharge both hidden-field orientations
using the actual quarter-centre power. The local periods and offset
remainders are used in the coverage proof only; the runtime computes
neither. `residue_source_none_offsets` proves that an actual failed batch
forces BOTH d mod Dp and d mod Dq to be at least (2B)^2.

### One retained polynomial batch, with every parent available

`recordValues`, `windowRoots` and `windowTargets` cast the cached labelled
records back to public-ring residues. `ResidueSource` retains both actual
residue lists, the distinct root set, evaluated columns and checked factor
option. `buildResidueSource` constructs each item once and runs the
existing column recovery, including its possible lazy root scan.
There are no new square-root centres, window powers or projections.

`buildResidueSource_budget` proves two 2B-entry lists, at most 2B distinct
roots and exactly 2B evaluated columns. `buildResidueSource_degree` bounds
the detector degree by 2B. `buildResidueSource_gcd_bound` proves at most
4B batch GCD queries, including a possible lazy root scan. These bounds
describe the actual representation and recovery; the virtual Cartesian
pair count does not occur as a constructed matrix.

`ResidueCertified` keeps the actual preceding long-power certificate and
failed global decoder. The new `Packet` retains the entire quarter-window
packet, including all original parent frames and power channels.
`packetSource` skips every already successful preceding packet. A new
proper leaf factor is transported through the retained original descent;
each leaf check and parent transport is still charged separately.

`publicPacket_cases` proves proper original-factor recovery or an actual
certified failed residue source on a true semiprime leaf. Its residual
alternative keeps the earlier literal gap and both local remainder
exclusions, along with an equality identifying the actual source with its
certified active unit. `publicPacket_source_budget` bounds both source
axes, distinct roots, evaluated columns and batch GCD queries by the
ORIGINAL input's sixth-root width after every retained descent.
No order or hidden factor is an input to this N-only procedure.

The replay times the whole preceding public packet, cached-record casts,
deterministic distinct-root and target sorting, polynomial product tree,
remainder/derivative evaluation, every column GCD, any lazy leaf or witness
scan, retained signals and successful transport. It uses the previously
validated packed polynomial backend. Polynomial operation counts and
linear source/GCD bounds are not a complete bit-complexity theorem.

### A wrapped-offset recovery and the surviving large-gap control

Replay 202610031501 repeats all 1081 small semiprimes, including 46
squares; all factor. The 21 normal inputs, seven earlier controls and two
prior positive controls preserve their successful factors. The new residue
stage skips those already successful packets. It adds one selected
63-bit recovery and repeats the preceding 61-bit negative:

| Input | B | Literal offset d | d mod Dp | d mod Dq | Window cap | Result |
| --- | --- | --- | --- | --- | --- | --- |
| 5828428599798999913 | 1342 | 500000208 | 205 | 500000208 | 7203856 | Factor 1000000007 |
| 1400000552800003801 | 1058 | 8392042 | 8392042 | 8392042 | 4477456 | No factor |

The new input is 1000000007*5828428559. Discovery outside timing fixes
the first factor and chooses the first safe prime strictly above
3*p+2*floor(sqrt(2*p*p)). This puts the true quarter offset just above
the reference first period (p-1)/2=500000003. Only the product N is
passed to the timed routine. The independently validated second period
is 2914214279. This is a selected control, not a random coverage corpus
or an exponent measurement.

The public cached scalar is 3505347010863074752 and its centre is
1457107148742643045. The actual recovered witness uses baby index 205
and shifted block index zero. `control_wrapped_pair` checks the scalar
powers 5616586799466348465 and 904283392480224847 and their original
residual GCD 1000000007. `control_wrapped_arithmetic` checks the product,
centre, offset, reference-period remainder and window inequalities.
These compiled arithmetic checks do not claim a closed evaluation of the
preceding routing trace or acquire a numerical order for the runtime.
Actual route selection and reference periods are independently validated
after timing by the replay.

The successful batch uses 2684 roots and 2684 targets, representing
7203856 virtual pairs without constructing them. It performs 2573
column GCDs and 416 witness remainders, with no pair products, derivative
columns or lazy leaf GCDs. Its successful leaf transport pays one extra
leaf GCD. The preserved negative uses 2116 roots and targets and performs
2116 column GCDs; all are units. Its two true local remainders exceed
the cap, so the new coverage theorem does not eliminate this input.

All 81 source pins verify, preserving the entire frozen 77-source parent
chain. Strict targeted build and strict direct ordinary-root checking
pass. All 14 namespace linters pass. The module adds 28 public theorems,
eight definitions, one indexed certificate datatype and two retained
structures. The complete transitive audit checks 110 declarations,
including 58 proofs and generated helpers, with only `propext`,
`Classical.choice` and `Quot.sound`. The ordinary root and semiprime
explorer family register the module. Work remains local.

The extraction frontier now excludes short local remainders of the
quarter factor-sum offset in either long field, rather than only a short
literal offset. Both remainders can still exceed the cap, as the retained
negative demonstrates. Universal coverage at linear source width and
the complete classical every-run bit backend remain required for the
guaranteed one-sixth theorem.

## Executable binary powers and charged recurrence construction (2026-10-03)

New local artifacts:

- [SemiprimeWindowConstruction.lean](../RiemannGaussian/SemiprimeWindowConstruction.lean)
- [Optional counted-construction replay](../scripts/probe_semiprime_window_construction.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeWindowConstruction.lean)
- [Source-pinned replay](semiprime-window-construction-audit.json)

This stage preserves the entire 81-source residue audit and implements
the exact source construction behind its recovery information. It adds
no coverage assumption or new recovered input. The geometric recurrence
now has an executable Lean implementation whose labelled outputs provably
equal the public-power specification. The Python port is independently
checked by replay. Full bit complexity and universal one-sixth extraction
remain open.

The weighted alternative was also checked against the existing universal
Lehman cover and literal-centre construction. That cover is already proved;
the literal candidate enumeration still visits quadratically many weight
pairs, as `SemiprimeCartesianCompletion.candidateWeights_card_lower`
records. No linear-cost weighted-centre constructor was obtained or
silently substituted. The concrete progress here addresses the source
construction part of the complete cost contract.

### Actual executable operations, with their counters

`countedPower` is natural-number binary modular exponentiation. Its
`PowerReport` retains the actual value, every residue multiplication,
recursive halving and modulus-N reduction. `countedPower_correct`
identifies its residue with the mathematical ZMod power. At positive N,
`countedPower_value_lt` bounds every result below N.

For exponent e, let E=clog(2,e+1). `countedPower_halvings` proves exactly
E halvings; `countedPower_multiplications` proves at most 2E
multiplications. `countedPower_reductions` proves at most 3E+1
modulus-N reductions, including the base normalization and both extra
odd-step reductions. Each positive recursive level also performs one
parity test. The public exponent is halved; no full unreduced large
integer power is constructed at positive N. Mathlib already provides
binary powering too; the new implementation exposes its own actual
operation counters rather than treating a power query as a unit bit cost.

`countedWalk` generates the actual successive modular residues and labels.
`countedWalk_records` proves the complete labelled array equals the
geometric-power specification. A length-b walk performs exactly b-1
multiplications and b+(b-1) reductions, with natural subtraction at zero.
The final unused advance is omitted. Each current residue is normalized
once and reused for its record and next product. The retained counters
therefore include those normalizations, not just the advances.

`RawSource` retains the active and inverse scalars, public centre and block,
both setup-power reports and both walk reports. `buildRawSource` is
executable natural-number code. The inverse scalar comes from the actual
public unit; its acquisition is not included as a free operation in the
raw counters. The public square root is likewise a separate charged call.
`ReadySource` then retains the actual sorted arrays, ordered match and
checked decoded factor, computing each stage once.

### Exact recovery-source linkage and original-input bounds

`buildRawSource_babies` and `buildRawSource_giants` prove exact equality
with the preceding baby and shifted arrays, preserving every original
label and the zero block. `prepareSource_collision` and
`prepareSource_factor` prove the actual match and candidate equal the
proved preceding decoder. `prepareSource_arrays` also retains its at-most
4B ordered-merge comparison bound. Sorting remains a separate charge.

`windowCertified_reconstruction` applies these equalities to every actual
certified window, without a supplied period or hidden factor.
`publicWindow_source_certified` obtains that certificate from the actual
N-only routing trace, including already successful windows.
`windowCertified_input_bounds` proves that the actual active and inverse
scalar inputs are below N.

At the actual public width B and bit length L=clog(2,N+1),
`buildRawSource_public_counts` proves the following raw bounds:

```
residue multiplications <= 4B+4L+2
modulus-N reductions    <= 8B+6L+5
exponent halvings       <= 2L+1
```

`publicWindow_construction_budget` lifts all three bounds to the ORIGINAL
input after every retained kernel descent. It uses both width and input
size monotonicity, so a smaller leaf's work is not charged at an unrelated
or unrecorded modulus.

`residue_product_lt_square` and `residue_product_bit_width` bound a product
of actual reduced operands below N squared and at most 2L bits.
`countedPower_temporary_widths` covers both repeated squares and odd-step
products; `countedWalk_temporary_width` covers every recurrence advance.
`buildRawSource_values_lt` bounds both setup residues and both actual
arrays. The source arithmetic therefore cannot hide huge full-power
integers behind its multiplication counter.

These are executable-operation counts, source equality and operand-width
theorems. They do not claim an implemented bit-cost certificate for every
arithmetic primitive, inverse acquisition, square root, sorting, polynomial
evaluation, decoder, preceding descent or transport. Those costs remain
required by the full objective; no weighted cost reserve is substituted
for their missing implementation proofs.

### Whole-route substitution replay, with all outcomes preserved

Replay 202610031601 uses a scoped adapter to replace only the preceding
window builder with the counted binary-power and recurrence implementation.
The adapter is restored before the public call returns. The entire N-only
route, its actual new source, residue continuation and successful transport
are timed. Inverse acquisition, centre and optional decoder square roots,
sorting, ordered lookup, GCDs and polynomial operations keep their existing
separate charges. No reference factor, period or offset is supplied to
the timed procedure.

Independent primitive checks compare 6864 binary-power cases with native
modular exponentiation and 1554 labelled walks with the geometric
specification, including zero exponents, empty and singleton lists,
trivial moduli and composite moduli. These checks occur outside timing.
All 1081 small semiprimes, including 46 squares, still factor. The 21 normal
inputs, seven earlier controls, two prior positives, wrapped-offset control
and preserved negative keep exactly their preceding factor/status pairs.

All five constructed windows reproduce every original sorted record,
centre, target, inverse step, collision, candidate and leaf factor:

| Original input | Leaf input | Leaf B | Residue multiplications | Modulus-N reductions | Halvings/parity tests | Largest product bits |
| --- | --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 38 | 207 | 381 | 37 | 63 |
| 723392533321 | 723392533321 | 95 | 448 | 854 | 46 | 79 |
| 87851329807 | 14641888301 | 50 | 258 | 481 | 39 | 68 |
| 1400000552800003801 | 1400000552800003801 | 1058 | 4335 | 8603 | 71 | 121 |
| 5828428599798999913 | 5828428599798999913 | 1342 | 5478 | 10887 | 73 | 125 |

Each builder also performs one actual modular-inverse acquisition and one
centre square root. Those operations are recorded separately. The remaining
61-bit input still has no factor, and the 63-bit wrapped input still
recovers 1000000007. There is no random scaling corpus, tuned-software
comparison or new empirical exponent claim in this replay.

All 85 source pins verify, preserving the entire frozen 81-source parent
chain. The strict targeted build, strict direct ordinary-root check and
all 14 namespace linters pass. The module adds 32 public theorems, seven
executable definitions and four retained structures. Its complete
transitive audit checks 163 declarations, including 81 proofs and generated
helpers, with only `propext`, `Classical.choice` and `Quot.sound`. The
ordinary root and semiprime explorer family register the module. Work
remains local.

The actual raw window construction now has an exact implementation bridge
and linear arithmetic counts with logarithmic-size operands. Universal
coverage of the remaining long leaves and the complete classical every-run
bit backend remain necessary for the guaranteed one-sixth theorem.

## Counted Euclidean inverse and complete arithmetic initialization (2026-10-03)

New local artifacts:

- [SemiprimeWindowInverse.lean](../RiemannGaussian/SemiprimeWindowInverse.lean)
- [Optional counted-inverse replay](../scripts/probe_semiprime_window_inverse.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeWindowInverse.lean)
- [Source-pinned replay](semiprime-window-inverse-audit.json)

This stage preserves the entire frozen 85-source construction audit. It
replaces the remaining opaque inverse inside that builder with an explicit
natural-number Euclidean implementation and charges its actual operations.
It adds no new collision coverage or recovered input. The complete
guaranteed one-sixth bit theorem remains open.

### Actual inverse algorithm and invariant

`countedInverse N a` initializes remainders `(N,a mod N)` and modular
coefficients `(0,1 mod N)`. For each positive second remainder, it computes
the quotient q and Euclidean remainder. The next coefficient is

```
(c0+N-(q*c1 mod N)) mod N
```

`makeFrame_coefficient` proves this natural subtraction represents the
intended modular difference: the reduced product is below N, so padding
by N prevents truncation. `makeFrame_invariant` preserves both exact
relations `c0*a=r0` and `c1*a=r1` in the original public ring. The entire
recursive run retains each actual state and temporary in its trace.

`euclidLoop_gcd` identifies the returned natural gcd, and
`countedInverse_correct` proves the returned coefficient times a equals
that gcd modulo N. This also applies to nonunits. The returned coefficient
is below N for positive N. `countedInverse_unit_gcd` and
`countedInverse_unit` prove that a proof-side public unit gives gcd one
and exactly its canonical inverse. Neither that inverse nor an order,
factor or coverage witness is an executable input.

`euclid_remainder_half` proves the two-step halving bound. Using it,
`euclidLoop_steps` bounds the actual recursion depth by twice the binary
length of the initial second remainder. At public modulus width
L=clog(2,N+1), `countedInverse_budget` proves:

```
Euclidean steps         <= 2L
quotient calls           = steps
coefficient products     = steps
remainder calls          = 3*steps+2
retained trace length    = steps
```

The two extra reductions normalize the initial scalar and coefficient.
Every step also performs one coefficient addition, one natural subtraction
and one positive/zero test; the final stopping test is retained separately
in the replay. Quotient and remainder calls are charged separately.

`countedInverse_trace_bounded` bounds every retained frame. Both remainders
and the quotient are at most N; both input coefficients, the reduced
product and the updated coefficient are below N. The actual unreduced
product is below N squared, and the padded coefficient is below 2N.
`countedInverse_temporary_widths` therefore bounds those two temporaries by
2L and L+1 bits respectively. The proof covers every actual intermediate
frame rather than only the returned inverse. No large unreduced Bezout
coefficient is constructed.

### Source equality and original-input charges

`initialiseSource N a B` retains the actual inverse report and constructs a
ready source exactly when its gcd equals one. Nonunits are rejected by
that computed gcd. `initialiseSource_unit` links successful initialization
to the existing counted builder. `windowCertified_initialisation` proves
that every actual certified window has the same sorted baby and shifted
arrays, collision and factor option. All exponent labels and cached rows
remain available to the proper-residue continuation.

At the actual public width B, `initialiseSource_budget` includes the inverse
work together with both binary powers and geometric walks:

```
residue/coefficient multiplications <= 4B+6L+2
all charged remainder calls         <= 8B+12L+7
Euclidean quotient calls            <= 2L
binary exponent halvings            <= 2L+1
```

`publicWindow_initialisation_budget` lifts these bounds to the ORIGINAL
semiprime input after every retained descent. The actual certified scalar
is below its leaf modulus by the preceding input-bound theorem, so its
initial normalization also has a bounded operand. These are arithmetic
counts and operand bounds. They do not certify implemented bit costs for
division, remainder, multiplication, square roots, sorting, polynomial
evaluation, the decoder, preceding routing or factor transport.

### Frozen-input replay and validation

Replay 202610031701 substitutes only the inverse inside the frozen counted
builder and restores that adapter before returning. It times the complete
preceding N-only pipeline, explicit Euclid, retained reports, constructed
rows, residue continuation and transport. Native Python inverse calls are
used only for independent validation after timing. Reference factors,
local periods, offsets, invariant checks and source comparisons stay
outside timing. Historical raw counters remain intact; the added
`initial_arithmetic` report includes the inverse and records zero opaque
inverse queries.

Independent checks cover 14064 inverse inputs, including 8419 units and
5645 nonunits, plus 32 consecutive-Fibonacci checks through larger bit
widths. They verify the exact gcd, modular equation, canonical inverse
when applicable, every trace state and temporary, and all count bounds.
All 1081 small semiprimes, including 46 squares, still factor. The 21
normal inputs, seven earlier controls, two prior positives, wrapped-offset
control and preserved negative keep every prior factor/status pair.
All five constructed sources reproduce every prior sorted record, centre,
target, inverse step, collision, candidate and leaf factor.

| Original input | Leaf input | Leaf B | Multiplications including inverse | Reductions including inverse | Euclidean quotients | Power halvings |
| --- | --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 38 | 225 | 437 | 18 | 37 |
| 723392533321 | 723392533321 | 95 | 476 | 940 | 28 | 46 |
| 87851329807 | 14641888301 | 50 | 272 | 525 | 14 | 39 |
| 1400000552800003801 | 1400000552800003801 | 1058 | 4371 | 8713 | 36 | 71 |
| 5828428599798999913 | 5828428599798999913 | 1342 | 5519 | 11012 | 41 | 73 |

Each window acquires its inverse once with the counted algorithm. The
largest construction products retain the preceding 63, 79, 68, 121 and
125-bit bounds. The 61-bit negative still produces no factor; the 63-bit
wrapped-offset case still recovers 1000000007. This is neither a new
scaling corpus nor a factoring speed comparison.

All 89 source pins verify, preserving the entire frozen 85-source parent
chain. The strict targeted build, strict direct ordinary-root check and
all 14 namespace linters pass. The module adds 25 public theorems, seven
executable definitions, one bound predicate and three retained structures.
Its complete transitive audit checks 128 declarations, including 62 proofs
and generated helpers, using only `propext`, `Classical.choice` and
`Quot.sound`. The ordinary root and semiprime explorer family register
the module. Work remains local.

Inverse acquisition now has its actual arithmetic implementation and
bounded intermediates. Universal recovery of the remaining long leaves
and the complete every-run classical bit implementation are still required
for the guaranteed one-sixth theorem.

## Restoring square roots and counted quadratic decoding (2026-10-03)

New local artifacts:

- [SemiprimeWindowSqrt.lean](../RiemannGaussian/SemiprimeWindowSqrt.lean)
- [Optional root/decoder replay](../scripts/probe_semiprime_window_sqrt.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeWindowSqrt.lean)
- [Source-pinned replay](semiprime-window-sqrt-audit.json)

This stage preserves all 89 source pins of the preceding inverse audit.
It implements both square roots in the retained window and the optional
decoder gcd, retaining their actual operation reports. It changes no
collision cover and recovers no additional input. Universal guaranteed
one-sixth factorization remains unproved.

### Restoring recurrence and exact root

`countedSqrt n` recursively removes the final base-four digit. If the child
returns root r and square remainder u, it computes

```
digit    = n mod 4
expanded = 4*u+digit
trial    = 4*r+1
doubled  = 2*r
```

When trial is at most expanded, the new root and remainder are
`(doubled+1,expanded-trial)`; otherwise they are `(doubled,expanded)`.
`makeSqrtFrame_invariant` preserves the exact square/remainder equation
and the bound remainder<=2*root. `countedSqrt_invariant` establishes them
for the entire run, including input zero. `countedSqrt_correct` then proves
the returned root equals `Nat.sqrt n`, and `countedSqrt_remainder` identifies
the literal remainder. The algorithm never multiplies two variable operands
to compute a root; its only multiplications are fixed shifts by two or four.

Let D=clog(4,n+1). `countedSqrt_steps` proves exactly D positive frames.
`countedSqrt_counts` proves the actual counters:

```
divisions by four       = D
base-four reductions    = D
fixed shifts            = 3D
trial comparisons       = D
additions               = 2D+subtractions
subtractions           <= D
recursion zero tests    = D+1
retained frame count    = D
```

The root-bit choice also has one Boolean test per positive frame.
`countedSqrt_budget` bounds these arithmetic categories by the binary
input width. `countedSqrt_trace_bounded` proves bounds on every retained
prefix state and actual temporary. Expanded remainders, roots and output
remainders are at most the current input; the trial is at most that input
plus one. `countedSqrt_temporary_widths` therefore bounds expanded and trial
widths by L and L+1, with L=clog(2,n+1). These are implementation and
operand theorems, not a certificate for native arithmetic bit costs.

### The optional quadratic candidate and gcd

`countedDecoder N m` computes the public signal `(N+1) mod m`, its
nonnegative discriminant, the restoring root and the quadratic candidate.
It then computes the candidate gcd with the preceding `countedInverse`,
retaining that complete Euclidean report even when the candidate is a
nonunit. Its final proper-divisor check uses the computed gcd.
`countedDecoder_candidate` and `countedDecoder_factor` prove exact equality
with `sumCandidate` and `recoverKnownOrder`. `countedDecoder_sound` proves
that every returned factor is proper, including at an incorrect modulus.

For positive N, `countedDecoder_input_bounds` bounds the signal by N+1,
the discriminant by N squared and the candidate by N. The proposed modulus
may be zero; no coverage premise is used for these bounds. With
L=clog(2,N+1), the root input has at most 2L bits, while its literal signal
square has at most 2L+1 bits. The extra product bit is retained because
modulus zero can give signal N+1. Every decoder-root temporary is bounded
at the same original leaf width, using `countedDecoder_temporary_widths`.
`countedDecoder_budget` charges at most 2L restoring frames and 2L Euclidean
quotients/products, with at most 6L+2 Euclidean remainder calls.

### Complete source linkage and charged categories

`buildRootedSource` computes the centre root, raw rows, both sorted arrays,
global collision and optional counted decoder once each. Its retained
reports do not erase the rows needed by the proper-residue continuation.
`buildRootedSource_raw` and `buildRootedSource_ready` prove exact equality
with the preceding raw and ready sources for arbitrary natural inputs.
`initialiseRootedSource_ready` retains unit/nonunit initialization behavior.
`windowCertified_rooted_initialisation` supplies the exact rows, collision
and factor for every actual certified public window.

At the actual width B and bit length L, `initialiseRootedSource_budget`
and `publicWindow_rooted_initialisation_budget` include:

```
variable-operand products       <= 4B+8L+4
general remainder calls         <= 8B+18L+10
Euclidean quotient calls        <= 4L
restoring digit pairs           <= 3L
binary-power halvings           <= 2L+1
```

The latter theorem charges these at the ORIGINAL input's width after all
retained descent. The variable products include the collision-label product
and discriminant square, as well as all residue and Euclidean coefficient
products. The general remainders include the decoder's signal reduction
and both Euclidean initializations. Restoring digit extraction and fixed
divisions/shifts remain separate retained categories: each restoring pair
pays one division by four, one modulo-four reduction and three fixed shifts.
The centre and optional candidate also pay their fixed quotient calls.
Earlier parity tests stay in the power report.

`countedWalk_label_bound` and `buildRootedSource_collision_bounds` prove
that both retained exponent labels are below the actual block width.
`publicWidth_offset_product_bits` bounds the literal block-label product
by 2L+2 bits. Thus the additional decoded arithmetic cannot hide an
unbounded exponent-label product behind its product counter.

Sorting, polynomial operations and their source budgets remain separate.
The primitive bit implementations, preceding routing/descent operations
and transport still need the complete every-run cost certificate. The
root and decoder implementation bridge does not discharge universal
collision coverage or establish a new factoring exponent.

### Whole-route replay with frozen outcomes

Replay 202610031801 replaces only the retained window's inverse, centre
root, candidate root and candidate gcd. The preceding public-input pipeline,
all actual window construction, recursive reports, residue continuation
and transport are timed. The adapters restore their original globals
before returning and do not mutate Python's shared math module. Native
roots, gcds and inverses are independent references after timing; private
factors, periods, offsets, trace checks and frozen source comparisons stay
outside timing. Unrelated earlier routing primitives retain their existing
charges.

Independent root checks cover 8765 inputs, including zero, square
boundaries, powers of two and inputs through 4097 bits. They verify the
exact root/remainder, every recursive frame and counter/temporary bound.
The 9600 decoder cases include incorrect and zero moduli; 1426 return
proper factors and all other results agree with the native specification.
All 1081 small semiprimes, including 46 squares, still factor. The 21 normal
inputs, seven earlier controls, two prior positives, wrapped-offset input
and preserved negative keep every earlier factor/status pair.

Every retained source reproduces its sorted rows, centre, target, inverse
step, collision, candidate, factor and all preceding raw/inverse counters:

| Original input | Leaf input | Leaf B | Variable products | General reductions | Euclidean quotients | Restoring pairs | Power halvings |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 38 | 228 | 443 | 19 | 31 | 37 |
| 723392533321 | 723392533321 | 95 | 479 | 946 | 29 | 39 | 46 |
| 87851329807 | 14641888301 | 50 | 275 | 531 | 15 | 34 | 39 |
| 1400000552800003801 | 1400000552800003801 | 1058 | 4371 | 8713 | 36 | 31 | 71 |
| 5828428599798999913 | 5828428599798999913 | 1342 | 5519 | 11012 | 41 | 32 | 73 |

All five sources compute their centre roots explicitly. The first three
also compute candidate roots and gcds; the two failed global windows perform
neither optional operation. The wrapped-offset input still recovers
1000000007 from the retained polynomial continuation. The preceding 61-bit
negative still has no factor. There is no new scaling corpus or speed claim.

All 93 source pins verify, preserving every frozen 89-source parent pin.
The strict targeted build, strict direct ordinary-root check and all
14 namespace linters pass. The module adds 32 public theorems, eleven
executable definitions, one bound predicate and five retained structures.
Its complete transitive audit checks 189 declarations, including 83 proofs
and generated helpers, using only `propext`, `Classical.choice` and
`Quot.sound`. The ordinary root and semiprime explorer family register
the module. Work remains local.

The retained window now has explicit root and candidate-gcd implementations
linked to its earlier recovery proof. Universal long-leaf recovery and the
complete classical primitive bit implementation are still necessary for
the guaranteed one-sixth theorem.

## Boolean-list addition and scalar-product pricing (2026-10-03)

New local artifacts:

- [SemiprimeBitArithmetic.lean](../RiemannGaussian/SemiprimeBitArithmetic.lean)
- [Optional primitive/raw-product replay](../scripts/probe_semiprime_bit_arithmetic.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeBitArithmetic.lean)
- [Source-pinned replay](semiprime-bit-arithmetic-audit.json)

This stage preserves the complete frozen 93-source root/decoder audit.
It moves two scalar operations from native integer arithmetic to explicit
Boolean-list implementations with an actual primitive cost model. It does
not add universal coverage, implement the entire arithmetic backend or
prove a complete one-sixth bit-cost theorem.

### Data path and charged primitive model

Digits are little-endian Boolean lists. `bitValue` is their mathematical
natural evaluation, used in specifications and proofs. The addition and
multiplication data paths do not call it or native integer multiplication.
`fullAdder` is a fixed six-gate circuit: two XORs, two ANDs and two ORs.
`fullAdder_correct` checks its digit/carry identity for all inputs.

`BitReport` retains the actual output bits and four clocks: fixed-circuit
Boolean gates, input bit-cell reads, new bit-cell writes and list/Boolean
branch tests. `bitCost` is their sum. Clocks are mathematical instrumentation;
their natural arithmetic is not an integer operation in the Boolean data
path. The model prices immutable bit-cell access and allocation directly.
It does not establish a concrete machine execution, address representation,
call-stack implementation or total factorizer runtime certificate.

`addBits` executes the circuit at every position, using literal false when
an input ends. The final carry may allocate one last cell. With
W=max(input lengths), `addBits_counts` proves:

```
Boolean gates       = 6W
input bit reads     = left length + right length
new bit cells       = actual output length
branch/list tests   = 2W+3
output length      <= W+1
total clock        <= 11W+4
```

`addBits_correct` proves the output value equals both input values plus
the input carry. Unequal lengths, high zero padding, zero input and a final
carry all retain their actual work. No operand-width or canonicalization
assumption is used in the correctness theorem.

`mulBits` recursively multiplies the tail of the left operand, allocates
one false bit to shift that intermediate, and adds the right operand when
the current bit is true. `mulBits_correct` proves the literal input product.
Every adder visit to the right operand is charged again. Intermediate
shifted lists and additions are included in the write clock; discarded
intermediates are not free.

For physical input lengths m and n, `mulBits_length` bounds output length
by 2m+n. `mulBits_cost` proves a composed clock bound

```
12*m*(m+n+2)+1
```

When both actual inputs have length at most L, `bounded_mulBits` gives
clock<=24(L+1)^2+1 and output length<=3L. `bounded_addBits` gives the
corresponding linear addition bound. These bounds use physical list length;
small represented value alone does not grant free removal of high zeros.
`bitValue_lt_width` and `bitValue_bits` prove the represented value fits
the physical list, without assuming the converse canonical-width property.

### Batch composition without supplied product advice

`multiplyBatch` actually calls `mulBits` for every requested pair and retains
each result once. It charges each scalar clock, one list test and one
retained report cell, plus the terminal list test. `multiplyBatch_correct`
proves all output values equal their original input products in order;
`multiplyBatch_length` proves exactly one result per input pair.

For M actual pairs with physical input lengths at most L,
`multiplyBatch_cost` proves clock<=M*(24(L+1)^2+3)+1.
`multiplyBatch_output_width` bounds the total retained output bit cells by
3LM. The batch does not receive products, a clock or an assumed fast
scalar arithmetic oracle as input. Its width hypothesis bounds its literal
supplied bit lists; constructing those lists in a larger algorithm still
requires its own implementation and price.

### Primitive tests and raw-row substitution

Replay 202610031901 checks all eight full-adder cases, 16918 additions
through 4096-bit inputs and 8460 products through 257-bit inputs. Cases
include zero, unequal widths, both carry values, dense-bit operands and
explicit high zero padding. Native natural sums/products independently
check output values, and every retained primitive clock/width bound is
checked outside the timed public route.

The whole public-input replay then replaces only the scalar products in
the two raw setup powers and the two walks. Each uses the linked-Boolean
implementation. The prior root/decoder adapter still times the entire
N-only route, actual new scalar data path and reports, legacy conversion
and remainder interface, cached residue continuation and factor transport.
Native product references, ledger hashes, private factors, periods, offsets
and source comparisons are evaluated after its timer stops. The scoped
function replacements are restored before returning.

The mixed-interface replay records integer-to-bit cell construction and
bit-to-integer digit visits separately. These legacy conversions and native
remainder calls have no new Lean bit-cost certificate. The inverse and
decoder coefficient products and earlier routing primitives also keep
their existing backend obligations. The proved Boolean multiplication
clock is therefore one component price, not a proved price for the entire
public source or factorizer.

All 1081 small semiprimes, including 46 squares, still factor. The 21 normal
inputs, seven earlier controls, two prior positives, wrapped-offset case
and preserved negative keep every earlier factor/status pair. Every sorted
record, centre, target, inverse step, collision, candidate, factor and old
construction report is identical to the frozen parent.

| Original input | Leaf input | Actual raw products | Primitive clock | Proven per-product sum bound | Legacy encode cells | Legacy decode visits |
| --- | --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 207 | 1482537 | 5410359 | 12223 | 12091 |
| 723392533321 | 723392533321 | 448 | 5452175 | 18074560 | 34422 | 34203 |
| 87851329807 | 14641888301 | 258 | 2127974 | 7585458 | 16200 | 15996 |
| 1400000552800003801 | 1400000552800003801 | 4335 | 123964574 | 399934095 | 514789 | 512751 |
| 5828428599798999913 | 5828428599798999913 | 5478 | 169462561 | 538514790 | 678092 | 674979 |

The primitive clock includes all four model categories. The raw native
remainder calls remain 381, 854, 481, 8603 and 10887 respectively. The
largest physical multiplication inputs remain bounded by each actual
leaf's input width. Every concrete product is independently validated;
ledger hashes retain their order. The 61-bit negative still has no factor,
and the wrapped-offset input still recovers 1000000007. No new empirical
exponent or software speed comparison is claimed.

All 97 source pins verify, preserving the complete 93-source parent chain.
The strict targeted build, strict direct ordinary-root check and all
14 namespace linters pass. The module adds 15 public theorems, seven
definitions and two retained structures. Its complete transitive audit
checks 127 declarations, including 72 proofs and generated helpers, using
only `propext`, `Classical.choice` and `Quot.sound`. The ordinary root and
semiprime explorer family register the module. Work remains local.

The next arithmetic obligations include bit-list comparison/subtraction,
quotient/remainder, controlled canonicalization and the complete interface
to the retained public procedure. Sorting, polynomial work, preceding
routing/descent, transport and universal long-leaf recovery also remain
necessary for the guaranteed one-sixth theorem.

## Boolean restoring division and modular-product pricing (2026-10-03)

New local artifacts:

- [SemiprimeBitDivision.lean](../RiemannGaussian/SemiprimeBitDivision.lean)
- [Optional primitive/raw-remainder replay](../scripts/probe_semiprime_bit_division.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeBitDivision.lean)
- [Source-pinned replay](semiprime-bit-division-audit.json)

This stage preserves the complete frozen 97-source Boolean-arithmetic audit.
It supplies actual subtraction, quotient/remainder and modular multiplication
in the existing gate/read/write/branch model. It does not add universal
collision coverage or establish the whole public factorizer's bit cost.

### Borrow decisions and paid word fitting

`fullSubtractor` uses seven Boolean gates: two XORs, one NOT, two ANDs and
two ORs. `fullSubtractor_correct` proves its exact digit/borrow equation.
`subBits` executes that circuit across the longer physical input word,
using literal false after either input ends. It retains every low difference
bit and the final borrow. For W=max(input lengths), `subBits_counts` proves:

```
Boolean gates       = 7W
input bit reads     = left length + right length
new bit cells       = W
branch/list tests   = 2W+2
output length       = W
total clock        <= 12W+2
```

`subBits_equation` proves the exact unsigned equation

```
value(left) + 2^W*finalBorrow
  = value(right) + initialBorrow + value(lowDifference).
```

`subBits_borrow_iff` therefore supplies the ordering decision from the
actual circuit: final borrow is true exactly when the left value is less
than the right value plus initial borrow. `subBits_difference` recovers
natural subtraction when initial and final borrow are false. No native
ordering or subtraction oracle computes these results.

`fitBits` copies, truncates or zero-pads to a literal template word's
physical length. `fitBits_counts` prices every visited input bit, new
output cell and list test; `fitBits_cost` bounds its clock by 4L+1.
`fitBits_value` proves exact value retention when that value fits the
template, and `fitBits_zero_value` identifies the constructed zero word.
Fitting is executed at every division step, including copying a remainder
whose subtraction was rejected. High zero padding is not removed for free.

`nonzeroBits` scans the full divisor with an OR circuit.
`nonzeroBits_correct` proves its flag is true exactly for a positive
represented value, and `nonzeroBits_cost` prices the complete scan at
3L+1, including all-zero padded words.

### Actual restoring division and composed modular products

`divideLoop` processes the most significant prefix first. Its child retains
quotient q and remainder r; adding the next input bit expands the remainder
to 2r+bit. One full subtraction against the divisor supplies the quotient
bit and decides whether to keep the expanded word or the difference. The
chosen remainder is then physically fitted to the divisor width.
`divideLoop_invariant` proves D*q+r equals the processed input and r<D
at every recursive state when D>0. `divideLoop_widths` retains literal
remainder width, quotient width and number of rounds.

`divideBits` pays the divisor scan before entering that loop. A zero divisor
returns an empty quotient and shares the original dividend as remainder,
matching the natural zero-divisor conventions. `divideBits_correct` proves
the actual quotient and remainder for every input word, without canonical
encoding assumptions. `divideBits_widths` proves that positive-divisor
remainders occupy exactly the divisor's physical width.

For physical dividend length K and divisor length L, `divideBits_cost`
proves the complete clock bound

```
K*(16L+20)+7L+4.
```

This includes zero-word construction, every borrow circuit, every remainder
copy, quotient and expanded cells, input reads and branch/list tests.
For K<=3L, `bounded_divideBits` gives clock<=72(L+1)^2. The factor three
matches the earlier multiplier's physical output-width bound; correctness
does not assume its output was canonically trimmed.

`modMulBits` actually calls `mulBits` and divides the resulting Boolean word
by the actual modulus. `modMulBits_correct` proves the resulting residue
for every modulus, including zero. For physical input and modulus lengths
at most L, `bounded_modMulBits` proves clock<=96(L+1)^2+2.
`modMulBits_width` keeps the positive-modulus result at the fixed modulus
width, so repeated modular products do not grow their operand words.

`modMulBatch` computes each requested modular product and retains its report.
`modMulBatch_length` and `modMulBatch_correct` prove the exact count and
ordered residues. With M actual input pairs of physical width at most L,
`modMulBatch_cost` proves clock<=M*(96(L+1)^2+4)+1, including traversal
and retained report cells. It receives neither products nor residue advice.

These are local primitive-model prices. Mathematical natural clocks and
`bitValue` are instrumentation and specifications, not computations of the
Boolean output. Concrete machine execution, address representation,
stack management and the full procedure still need their own certificate.

### Primitive checks and whole-route remainder substitution

Replay 202610032001 checks all eight full-subtractor inputs, 37636 padded
subtractions with both initial borrow values, 4369 word-fitting cases,
16802 divisions and 11979 modular products. Division includes zero,
all-zero padded divisors, unequal widths and dividend inputs through
2049 bits. Every result, physical-width invariant and retained clock bound
is checked against independent native references outside the public timer.

The scoped raw-power and raw-walk replacements now compute every general
modulus-N remainder with the linked-Boolean divider. They reuse one cached
Boolean modulus word per actual retained source. The inherited root/decoder
adapter still times the entire N-only route, actual bit computations and
reports, legacy conversions, cached residue continuation and transport.
Native reference arithmetic, ledger hashing, private factors, periods,
offsets and trace/source validation are outside that timer. All original
globals are restored before returning.

The integer/Boolean adapters retain their actual encode-cell and decode-digit
counts. Those interfaces, exponent halvings/parity, label arithmetic,
inverse/decoder operations and preceding routing primitives are not supplied
with a new complete bit-cost certificate by this replay. Native reference
checks are distinct from arithmetic that computes the raw rows.

All 1081 small semiprimes, including 46 prime squares, still factor. The
21 normal inputs, seven earlier controls, two prior positives, wrapped-offset
case and preserved negative retain all prior factor/status pairs. Exactly
five sources are constructed. Every sorted row, centre, target, inverse
step, collision, candidate, factor and preceding construction report agrees
with the frozen parent. Raw multiplication counts and clocks also agree.

| Original input | Leaf input | Actual raw remainders | Division clock | Proven per-division sum bound | Product plus division clock |
| --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 381 | 9236550 | 29873448 | 10719087 |
| 723392533321 | 723392533321 | 854 | 32974515 | 103361328 | 38426690 |
| 87851329807 | 14641888301 | 481 | 13111541 | 42424200 | 15239515 |
| 1400000552800003801 | 1400000552800003801 | 8603 | 765202865 | 2381035104 | 889167439 |
| 5828428599798999913 | 5828428599798999913 | 10887 | 1038159893 | 3210706944 | 1207622454 |

Each row's sum bound uses its actual retained leaf input bit width and the
compiled 72(L+1)^2 division price. General native quotient and remainder
calls computing these raw updates are both zero. The retained division
round counts are 17254, 49721, 23111, 765849 and 1006817; they equal the
actual dividend bits visited. Maximum dividend widths are 63, 79, 68,
121 and 125 bits; fixed divisor widths are 32, 40, 34, 61 and 63.
Every operand/result ledger retains its original order.

The 61-bit negative still returns no factor. The wrapped-offset continuation
still recovers 1000000007. No new unbiased corpus, software speed comparison
or empirical exponent is claimed.

All 101 source pins verify, preserving every frozen 97-source parent pin.
The strict targeted module build, strict direct ordinary-root check and
all 14 namespace linters pass. The module adds 25 public theorems, eight
definitions and five retained structures. Its complete transitive audit
checks 212 declarations, including 107 proofs and generated helpers,
using only `propext`, `Classical.choice` and `Quot.sound`. The ordinary
root and semiprime explorer family register the module. Work remains local.

The remaining backend work includes bit-only power/walk interfaces and
the full retained public procedure. Sorting, polynomial arithmetic,
preceding routing/descent, transport and universal long-leaf recovery
also remain necessary for the guaranteed one-sixth theorem.

## Bit-only setup powers and geometric row walks (2026-10-03)

New local artifacts:

- [SemiprimeBitPowerWalk.lean](../RiemannGaussian/SemiprimeBitPowerWalk.lean)
- [Optional bit-loop/public-route replay](../scripts/probe_semiprime_bit_power_walk.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeBitPowerWalk.lean)
- [Source-pinned replay](semiprime-bit-power-walk-audit.json)

This stage preserves the frozen 101-source division chain. It composes
the Boolean scalar operations into actual powers and geometric row loops,
with no natural evaluation of intermediate residues. It does not supply
the public-input encoding or universal collision-coverage theorem.

### Literal exponent words and scalar counts

`powerBits` recurses on a literal little-endian exponent tail. Its empty
case constructs and divides the one-bit word `[true]`. Each positive frame
computes the child's modular square. A true exponent bit also normalizes
the actual base and computes its modular product with that square. The
scalar backend pays all Boolean products and restoring divisions; each
exponent frame additionally pays its bit read, list test and bit branch.

`powerBits_correct` proves that the actual output value is a^e modulo N
for every modulus and physical exponent encoding, including modulus zero
and high zero padding. No natural exponent halving or parity oracle drives
the loop. `powerBits_width` proves that positive-modulus outputs retain
exactly the modulus's physical width.

`powerBits_counts` proves exactly E rounds for a physical E-bit exponent,
between E and 2E products, at most 3E+1 reductions, and the exact relation
reductions+E=2*products+1. High zero exponent bits still perform their
actual squares. `powerBits_countedPower_counts` identifies these scalar
counts with the earlier natural binary power when the supplied exponent
word already has its canonical width. That explicit hypothesis grants
no free canonicalization of padded words.

For actual base/modulus word lengths at most L and positive N,
`powerBits_cost` proves clock<=E*(264(L+1)^2+7)+72(L+1)^2+2.
`bounded_powerBits` gives the convenient bound 272(E+1)(L+1)^2.
Exponent encoding and its physical size remain explicit inputs to these
theorems; a small represented exponent alone does not bound a padded list.

### Literal row templates and the two-axis constructor

`walkBits` follows a supplied unit-list template. Each row normalizes the
current bit word, retains its residue and, except at the last row, advances
by an actual modular product. Residues remain bit words from one iteration
to the next. The empty template pays its final list test; each row pays
two list tests and its retained list cell in addition to scalar work.

`walkBits_values` identifies every computed residue with the earlier
`countedWalk`, for all moduli. `walkBits_counts` proves exactly R rows,
R-1 advances and R+(R-1) reductions, with natural subtraction for R=0.
`walkBits_widths` retains fixed physical modulus-width words at positive N.
`walkBits_cost` prices the complete walk at R*(168(L+1)^2+5)+1
when the actual start, step and modulus lengths are at most L.

`constructBitRows` computes both setup powers and both residue axes. The
baby walk starts from a literal one-bit word; the giant walk uses the
actual computed target and inverse-step bit words. It charges all four
reports, the baby-start cell and the retained source report.
`constructBitRows_lengths` proves exactly the template length on each axis.
For physical exponent lengths E_c and E_b and R template cells,
`constructBitRows_cost` proves

```
clock <= 272*(E_c+E_b+2)*(L+1)^2
         + 2R*(168*(L+1)^2+5)+4.
```

`constructBitRows_raw_values` proves equality of both residue arrays with
the previous `buildRawSource` when the actual centre/block words represent
quarterCentre(N) and 2B and the template has length 2B. Its inputs remain
literal supplied words and a literal template. It does not assume those
interfaces were constructed without cost. Labels are a separate interface;
this theorem identifies all residues in their original order.

### Validation and retained interfaces

The strict focused module build and strict direct ordinary-root check pass.
All 14 namespace linters pass for 41 explicit and 90 generated declarations.
The complete transitive axiom audit checks 131 declarations, including
68 proofs, using only `propext`, `Classical.choice` and `Quot.sound`.
The 408-line module adds 15 public theorems, three executable definitions
and three retained structures. The ordinary root and semiprime family
register the module. Work remains local.

The optional replay's boundary adapters encode the two bases, modulus and
two exponent words, and construct one shared row template. They decode
only the final two power outputs and final row residues for the existing
natural/label/sorting interface. Every intermediate square, normalization
and row advance stays in Boolean words. Diagnostic product-width scans
retain their actual bit visits separately from the compiled loop clocks.
Initial encoding/template construction, final decoding/labels and these
diagnostics still need their own complete bit certificate.

The entire preceding N-only route, bit loops and retained reports, these
legacy boundaries, cached residue continuation and factor transport are
inside the inherited timer. Native references, ledger hashing, private
factors, periods, offsets and source/trace comparisons are outside it.
Old mixed-interface bit diagnostics are replaced by the fresh loop report;
the preceding natural arithmetic, inverse and root reports are compared
against their frozen values.

Replay 202610032101 checks 4242 powers and 4410 walks, including zero
moduli, explicit padding, modulus words through 257 bits and exponent
words through 256 physical bits. The zero-valued 256-bit exponent is
fully traversed and squared, retaining the work of its padding. Native
references verify all residues and scalar/physical-width clock bounds.

All 1081 small semiprimes, including 46 prime squares, still factor. The
21 normal inputs, seven earlier controls, two prior positives, wrapped-offset
case and preserved negative keep their earlier factor/status pairs. Exactly
five sources are constructed. Every sorted row, centre, target, inverse
step, collision, candidate and factor agrees with the frozen parent; so
do all preceding natural construction, inverse and root reports.

| Original input | Leaf input | Physical L | Rows per axis | Exponent bits, total | Primitive clock | Proven composed bound |
| --- | --- | --- | --- | --- | --- | --- |
| 2803308161 | 2803308161 | 32 | 76 | 37 | 10991252 | 39361580 |
| 723392533321 | 723392533321 | 40 | 190 | 46 | 39011531 | 129264080 |
| 87851329807 | 14641888301 | 34 | 100 | 39 | 15540125 | 54822204 |
| 1400000552800003801 | 1400000552800003801 | 61 | 2116 | 71 | 897925293 | 2809339372 |
| 5828428599798999913 | 5828428599798999913 | 63 | 2684 | 73 | 1216899014 | 3777456348 |

The same sources perform 207, 448, 258, 4335 and 5478 raw products, and
381, 854, 481, 8603 and 10887 raw reductions. Each reduction now uses
the Boolean backend. There are zero intermediate native encodes, decodes,
quotient calls or remainder calls in the bit-only data path. Both
exponent words are encoded only at their initial boundary. Every modulus
word and row template is reused rather than reconstructed per row.

The initial modulus/base encoding cell counts are 92, 119, 96, 180 and
184; exponent encoding adds 37, 46, 39, 71 and 73 cells. Final decoding
visits are 4928, 15280, 6868, 258274 and 338310, respectively, for the
two power outputs and every final row. The two retained axes occupy
4864, 15200, 6800, 258152 and 338184 residue bit cells. Their exact
total is 2RL; sharing the template does not omit either residue axis.

Diagnostic product-width scans visit 12304, 34437, 16216, 514053 and
675222 bits. They remain separate from the proved primitive-loop clock,
with their observed total below 3L times the actual product count. Final
label assignment and these boundaries still use the legacy interface.
No concrete machine or complete public-factorizer bit certificate is claimed.

All 105 source pins verify, preserving every frozen 101-source parent pin.
The probe checks its complete inventory again before writing the audit,
so a source change during replay cannot retain a success result. The 61-bit
negative still returns no factor; the wrapped-offset input still recovers
1000000007. No software speed comparison or new empirical exponent is made.

### Additional RH cancellation interfaces inspected

[`ZetaRieszJointNullCredit.sum_jointIncrement_zero`](../RiemannGaussian/ZetaRieszJointNullCredit.lean)
cancels one complete
signed cutoff sum on squarefree support with at least three distinct
prime factors. It does not apply directly to a semiprime's two-factor
support, nor state that an individual modular collision is preserved.
The surrounding overlap identities join corrections before pricing their
absolute values; they do not make constructing the underlying support free.

[`ZetaRieszRoughPrimePairCancellation.shell_joint_comparison`](../RiemannGaussian/ZetaRieszRoughPrimePairCancellation.lean)
bounds a
complete rough row PLUS its prime-cofactor head MINUS a density main.
The exact weighted prime-pair head remains in the later global theorem.
This is an analytic signed-sum estimate, not an exact replacement for
the original modular collision product. Its source parameter and masks
remain those of the RH arithmetic band, with their stated hypotheses.

The earlier `SemiprimeRHCancellation.collisionProduct_map_zero_iff`
still supplies the relevant exact logical requirement: over each hidden
prime field, a zero of the constructed product is equivalent to at least
one original row collision. A signed-row cancellation needs an additional
preservation/recovery theorem to replace that product. None is supplied
by these two further RH interfaces. The universal coverage and complete
every-run one-sixth theorem remain open.

## Universal signed-multiplier coverage and streamed recovery (2026-10-03)

New local artifacts:

- [SemiprimeTotientMultipliers.lean](../RiemannGaussian/SemiprimeTotientMultipliers.lean)
- [Optional public-route multiplier replay](../scripts/probe_semiprime_totient_multipliers.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeTotientMultipliers.lean)
- [Source-pinned replay](semiprime-totient-multipliers-audit.json)

This stage preserves the frozen 105-source bit-power/walk parent. It
proves universal coverage and recovery of the preceding route's remaining
leaves. The new source has linear retained caches, but its expanded target
work remains quadratic. It does **not** establish the terminal every-run
`~O(N^(1/6))` bit bound.

### A complete signed-multiple cover

Write B for the public leaf sixth-root width, b=2B and H=b². On an
actual certified remaining leaf N=p*q, the cached active unit h has
coprime local periods Dp,Dq>H. The public quarter centre C and literal
factor-sum offset d satisfy h^C=h^d. Failure of the preceding global
window gives d>=H. These are upstream proved properties, not additional
inputs or coverage assumptions.

`exists_short_signed_multiple` bins the first floor(D/H)+2 residues
of i*d modulo a positive local period D into floor(D/H)+1 intervals
of width H. Two lie in the same bin. Their label difference gives

```
0 < k <= floor(D/H)+1
k*H <= D+H
0 <= t < H
either k*d mod D = t, or D divides k*d+t.
```

The negative orientation is retained rather than discarded. Apply this
to the period attached to the smaller factor, say p<=q. Then D<=p-1,
p<=B³ and D>H imply k<=B and k*H<=2p. The literal offset also retains
4d<=p+q. `multiplier_offset_bound` multiplies these inequalities and uses
p<=q to prove

```
16*k*d*B² <= 2p(p+q) <= 4N
k*d*B² <= N <= B⁶
k*d <= B⁴.
```

`core_global_order_lower` proves order(h)>16B⁴ from the coprime long
local periods. Thus k*d is positive, does not wrap globally and is at
least H. Also k*d+t<order(h). `signed_global_ne` proves that neither
h^(k*d) nor its inverse equals h^t globally. In the smaller field, one
of these orientations equals h^t by the signed modular relation.

Split t=i+b*j with i,j<b. The actual residual is

```
signedPoint((h^C), k, negative) * h^(-b*j) - h^i.
```

It is nonzero modulo N and zero in at least one hidden prime field.
`exists_multiplier_proper_pair` consequently proves its GCD with N is
proper. The proof handles both factor orientations without providing a
smaller-factor or local-period oracle to the public detector.

### Information extracted without a pair matrix

The detector reuses the preceding public beta=h^C and baby residues.
Its three caches are:

| Cache | Actual entries | Construction |
| --- | --- | --- |
| Baby roots | h^i, 0<=i<2B | Cast the existing labelled baby list |
| Block steps | h^(-2B*j), 0<=j<2B | Multiply each existing giant by beta inverse |
| Signed centres | beta^k and beta^(-k), 1<=k<=B | Two public geometric recurrences |

`buildMultiplierSource_budget` proves all three list lengths equal 2B
and the distinct baby-root count is at most 2B.
`buildMultiplierSource_degree` proves the fixed baby polynomial's degree
is at most 2B. Each streamed row scales all block steps by one signed
centre and evaluates that same polynomial at the resulting points.
Shared roots use the existing exact derivative/deflation recovery, so
global equalities do not erase later proper hits. The Python detector
constructs the fixed root polynomial once and lazily constructs at most
one derivative polynomial.

The extracted arithmetic object is a proper original residual GCD;
the multiplier, sign, baby label and block label identify the collision.
No actual local period is acquired by the public stream. The independent
replay checker acquires periods and offsets only after timing.

`buildMultiplierSource_complete` proves every failed certified long
window succeeds in this actual list/row specification.
`publicPacket_complete` integrates it into the preceding residue packet
and proves original-input recovery for all products of two primes,
including equal primes and arbitrary ratios. Earlier successful packets
skip the new source. New leaf factors pass through every retained
original descent frame. `publicPacket_sound` checks the returned original
factor is proper. This is universal correctness of the Lean public
specification; full machine refinement is a separate obligation.

### The cost still requiring compression

`buildMultiplierSource_expanded_points` gives exactly
(2B)*(2B)=4B² possible scaled target points.
`buildMultiplierSource_gcd_bound` gives at most 8B² queries for the
literal row stream, including its possible lazy root scans.
`publicPacket_source_budget` retains the linear cache bounds and this
quadratic query bound at the ORIGINAL input's width after every descent.
These are representation/query statements, not a complete polynomial
evaluation or bit-operation theorem.

The new family has a public two-dimensional geometric structure:
beta^(signed k)*h^(-2B*j). It is a concrete complete family whose implicit
norm or evaluations can now be investigated without assuming coverage.
Taking a signed sum of its rows still needs a theorem preserving every
proper collision. The RH signed-sum identities reviewed in the preceding
entry do not provide that theorem. Building a larger norm polynomial or
flattening every target would still pay quadratic work; compact notation
does not remove that price. The displayed query bound is an upper bound
for this literal implementation, not a lower bound for other detectors.

Strict local Lean validation passes: the focused module builds with
warnings as errors and the ordinary root elaborates with
`-DwarningAsError=true`. The root-import checker passes all 14 namespace
linters on 57 explicit declarations plus 95 generated declarations.
Its transitive axiom audit checks all 152 declarations, including 98
theorem/helper declarations, with only `propext`, `Classical.choice`
and `Quot.sound`. This is local validation; no commit, push, remote CI
or broad explorer regeneration was performed.

### Complete public-route replay and the previous negative

Replay `202610032201` verifies all **109 source pins**, preserving every
frozen 105-source parent pin. The inventory is checked again before the
audit is written. The optional probe command is

```bash
../.venv/bin/python scripts/probe_semiprime_totient_multipliers.py \
  --output docs/semiprime-totient-multipliers-audit.json
```

Component regressions compare 261 cached-polynomial cases and 1,029
evaluated rows against the previous independent batch implementation and
exhaustive proper-pair oracle. These include shared/repeated roots,
full-modulus deflated columns and prime squares. A further 32,768 finite
arithmetic cases verify the stated short signed-multiple bounds. Those
finite checks validate the prototype; the universal statements come from
the Lean pigeonhole and public-route theorems.

The whole N-only replay factors all 1,081 unordered semiprimes from primes
below 200, including 46 squares. The 21 normal inputs, seven prior controls,
two positive controls and one wrapped-offset control preserve all 31
previous successes and skip the new source. Their preceding retained
windows, decoded candidates and complete construction reports match the
frozen parent data. The one previous negative now factors through the
new multiplier source.

That selected 61-bit input is

```
N = 1400000552800003801 = 1000000007 * 1400000543
B = 1058, b = 2116, H = 4477456
literal offset d = 8392042
reference local periods = 500000003, 700000271
```

Only N enters the timed routine. Its first successful signed multiplier
is k=60, positive. The reference identity, acquired after timing, is

```
60*d = 503522520
60*d mod 500000003 = 3522517
3522517 = 1493 + 2116*1664 < H.
```

The actual retained centre is 1198780255856505610 and the selected block
step is 1129077541308301537. Their scaled point is
1326300823977657556; the baby root at label 1493 is 513708482289511204.
The evaluated polynomial column is 589487659126413585. Its proper GCD
recovers **1000000007**. The checker verifies the exact original residual,
both retained exponent labels and the original-input factor after timing.

The charged observed new-source work is:

| Quantity | Actual retained count |
| --- | ---: |
| Root polynomials constructed | 1 |
| Polynomial degree/distinct roots | 2116 |
| Derivative polynomials constructed | 0 |
| Signed rows evaluated | 119 |
| Target products/evaluated points | 251804 |
| Column GCDs | 251687 |
| Lazy leaf GCDs | 0 |
| Successful witness remainders | 799 |
| Polynomial convolutions | 469428 |
| Packed coefficient visits | 20520658 |
| Monic remainder reductions | 503489 |
| New cache products/reductions | 4230 each |
| New target inverse acquisitions | 1 |
| New centre/projection powers | 0 |
| Retained scalar cache entries | 6348 |
| Maximum cache/target product widths | 120 / 121 bits |
| Full possible evaluation points | 4477456 |
| Full virtually represented pair differences | 9474296896 |
| Explicit pair-grid products | 0 |

The full whole-route outer timer is approximately 78.6 seconds in this
replay; the inherited inner route timer is approximately 60.7 seconds.
These are one selected run with the existing Python Boolean-loop backend,
not a performance comparison or empirical exponent. The outer timer also
includes the preceding bit-loop routine's public-value diagnostics,
normalization inverse, cache recurrences, actual root/target sorting,
one polynomial construction, every streamed remainder tree, column GCDs,
successful witness scan, retained row signal hashes, scalar-width scans
and complete transport. Independent private primality/order/offset checks
occur afterward. No saved input-specific cache is supplied to timing.

The new prototype's cache products, inverse and polynomial/remainder work
still use the native scalar/packed backend. Their observed operation and
width counts are retained, but they do not carry a complete new Boolean
bit or concrete machine certificate. The earlier proved Boolean raw-row
loops remain intact. Deterministic ordering and Python-to-Lean refinement
of the complete selected factor also remain unproved; universal proper
recovery of the list/ring specification is already checked in Lean.

The coverage counterexample is removed. The remaining mathematical
algorithmic target is a faster evaluation or root-preserving norm of this
complete two-dimensional signed geometric family, followed by a complete
charged implementation of every pipeline stage. A product tree could
also reduce the literal stream's GCD queries without removing its
quadratic evaluation work; the displayed 8B² query bound is not an
impossibility result. The guaranteed every-run one-sixth bit theorem
remains **OPEN**, and the goal remains active.

## Exact shared norms on the complete multiplier family (2026-10-03)

New local artifacts:

- [SemiprimeMultiplierNorm.lean](../RiemannGaussian/SemiprimeMultiplierNorm.lean)
- [Optional exact-norm public-route replay](../scripts/probe_semiprime_multiplier_norm.py)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeMultiplierNorm.lean)
- [Source-pinned replay](semiprime-multiplier-norm-audit.json)

This stage preserves the frozen 109-source multiplier parent. It uses
the complete signed-centre cover already proved there, replaces its
expanded per-column detector and proves universal recovery of the new
N-only exact-norm specification. The desired every-run one-sixth bit
theorem remains **OPEN**.

### What a row retains after compression

Let h be the actual cached projected unit, beta=h^C the cached quarter
centre power, H=(2B)² and x one of beta^k,beta^(-k), 1<=k<=B. The earlier
coverage theorem gives an x and t<H with x=h^t in at least one hidden
prime field and x!=h^t globally. Replace all its individual shifted
columns by three exact scalars:

```
P(x) = product_(0 <= t < H) (x-h^t)
D(x) = target derivative of this same product
E(x) = logarithmic h derivative, retaining the exponent t in each mark.
```

`recoverInterval_of_local_root` proves that a nonshared local root on
either side is recoverable from these channels. A proper GCD of P
already factors N. If P=0 modulo N, the long local periods make every
interval root simple in both fields. Then x*D is a proved unit and
`s=-E/(x*D)` reduces to the original exponent index in each field.
The two indices differ whenever the selected local root is nonshared.
The existing ordinary integer-index batch recovers a proper difference
with at most 2B roots and 2B translated points. No hidden field index
enters the consumer.

`recoverNormJet` consumes the actual three computed scalars and checks
each candidate. It does not reconstruct the long interval or supply
an assumed hit. `recoverNormJet_exact` identifies it with the existing
interval-recovery specification. `normRows_complete` and
`publicPacket_complete` prove universal recovery for every product of
two primes, including squares and arbitrary factor ratios, preserving
every original descent frame. Previously successful packets skip the
new detector. The expanded multiplier detector is replaced, not run
as a preliminary factor oracle.

### Full blocks plus an exact shared tail

For a group of R actual centres, choose the public width

```
m = floor(sqrt(R*H))+1
J = floor(H/m)
T = H mod m
H = J*m+T.
```

One degree-m baby polynomial and its target/base derivatives evaluate
all R*J normalized full-block points. A second degree-T baby polynomial
and its two derivatives evaluate R normalized tail points. The tail
roots and coefficients are shared, so the implementation does not pay
R separate T-factor loops. The two polynomial/derivative families use
the same h and are independent of their row targets.

`exactSharedJet_exact` proves that product-rule composition of these
two parts gives exactly P,D,E on the original H-term interval.
`offsetJet_exact` proves the shared tail's phase and marked-offset
corrections; no nonunit factor is divided out. Both identities hold in
arbitrary commutative rings. The simple-root recovery theorem then uses
the upstream long local periods. The interval is never enlarged by
padding, which could otherwise exceed the available local-period range.

The exact explicit degree/point input count for this representation is

```
S(B,R,m) = m + R*floor(H/m) + (H mod m) + R.
```

The R tail points remain counted, including a zero-degree tail. For
0<B and R<=2B, `normWidth_le_length` proves 0<m<=H.
`normInputs_bound` proves S<=4m and
`normInputs_squared_bound` proves S²<=32R*H+32. The complete 2B-centre
family therefore satisfies

```
S(B,2B,m)^2 <= 256B^3+32.
```

`normInputs_full_floor` also proves 32B³<S(B,2B,m)² for EVERY positive
m in this explicit full-block/tail representation. This is a source-list
floor with B^(3/2) scale, not a lower bound for other norm algorithms or
factoring methods. Merely tuning its block width cannot produce the
required O(B) full-family input count. Polynomial arithmetic and all
other pipeline bit operations still need their own implemented price.

The prototype grows actual centre groups by powers of two, recomputing
their shared widths from public R and H and stopping on the first factor.
All positive widths have the same compiled exact scalar meaning. Native
phase powers/products/inverses, root generation, three-channel remainder
work and all index recovery are timed and counted separately. The
grouping/ordering and native polynomial backend do not carry a complete
machine or Boolean bit refinement certificate.

Strict local validation passes: the focused module builds with warnings
as errors and the ordinary root elaborates with
`-DwarningAsError=true`. The root-import checker passes all 14 namespace
linters on 40 explicit plus 52 generated declarations. Its complete
transitive audit checks 92 declarations, including 55 theorem/helper
declarations, with only `propext`, `Classical.choice` and `Quot.sound`.
No commit, push, remote CI or broad explorer regeneration was performed.

The previously reviewed
[q-holonomic computation paper](https://arxiv.org/abs/2012.08656)
provides literature context for square-root block methods. The existing
repository identities and the new exact-tail/recovery proofs are checked
independently; its complexity results are not imported as Lean axioms.
The [Umans–Wang structured divisor-difference conjecture](https://arxiv.org/abs/2511.10851)
describes a conditional route to a one-sixth integer-factorisation
exponent. This slice neither proves that conjecture nor assumes it to
claim the requested guarantee.

Replay `202610032301` freezes 113 source hashes, including all 109 hashes
from the multiplier parent. They agree both before and after replay and
in the final source check. All 1,081 semiprimes from primes below 200
factor, including all 46 prime squares. The 31 saved cases already
factored by the preceding residue route retain their factors and skip
norm construction. The previous multiplier route's final factors are
also preserved. Component checks cover 192 exact shared groups,
835 directly compared three-channel rows and 509 public width layouts,
including zero intervals, zero targets, repeated targets and multiple
local roots.

The saved remaining case is still
`N=1400000552800003801=1000000007*1400000543`, at public width B=1,058
and exact interval H=4,477,456. Seven adaptive groups evaluate 127 norms;
the stream examines 119 before recovering p=1,000,000,007 at positive
multiplier k=60. Its exact retained channels are

```
x = 1198780255856505610
P =  687618931813332489
D = 1037894082712853645
E =  648704852072209225
gcd(N,P) = 1000000007.
```

Eight selected long-interval triples, including the successful row, are
independently checked after timing against the preceding blocked interval
jet implementation. The four CRT controls separately recover a factor
from a one-sided root in either orientation, decode distinct saturated
local indices 3 and 9 when P=0, and correctly return no factor for the
same global root index 3. Thus a zero norm alone is not treated as a
factor, and its two derivative channels are exercised in recovery.

The new source and preceding expanded multiplier source, on that same
saved input, have the following actual counts:

| Charged source work | Expanded multiplier source | Exact shared norm source |
| --- | ---: | ---: |
| Constructed evaluation points | 251,804 | 52,756 |
| Column or norm GCDs | 251,687 | 119 |
| Polynomial convolutions | 469,428 | 418,979 |
| Packed coefficient visits | 20,520,658 | 18,242,364 |
| Monic reductions | 503,489 | 316,494 |

The exact source constructs 52,629 full-block points and 127 tail points,
14 shared root/derivative families and 14 point trees. Its degree/point
input budget summed over the seven groups is 129,033. The complete fixed
2B-centre group's budget would be 291,964. The implementation retains
2,116 signed centre values and constructs neither the original long
interval target list nor the full pair matrix. The separate native scalar
ledger counts 1,022,456 products, 1,022,747 reductions, 28 powers with
663 square/multiply rounds and two inverses; its largest scalar product
has 121 bits. Polynomial and packing work is counted in its own ledger,
so these scalar totals are not a price for every polynomial operation.

The original-input outer timer, containing the preceding bit-power/walk
route, all new construction and recovery, public diagnostics and factor
transport, reports 73,927.1 ms for this saved case. Private factors,
periods and independent triples enter only after that timer. This is one
saved execution, not a paired timing experiment or a scaling-rate proof.
The earlier expanded source is not executed before the new norm source.

This completes a universally correct exact-norm replacement with a
proved smaller explicit construction bound. The requested every-run
one-sixth bit guarantee remains OPEN: the full-family degree/point floor
is still of B^(3/2) scale, the native polynomial/grouping implementation
has no complete machine refinement, and the complete public pipeline
has no corresponding bit clock. Further cancellation must eliminate or
avoid the explicit shared-point family, rather than only change its width.

## First nonunit norm and deferred derivatives (2026-10-03)

New artifacts:

- [SemiprimeFirstNorm.lean](../RiemannGaussian/SemiprimeFirstNorm.lean)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeFirstNorm.lean)
- [Scalar-only source and single late-jet replay](../scripts/probe_semiprime_first_norm.py)
- [Saved replay and pinned sources](semiprime-first-norm-audit.json)

The richer preceding norm carrier is preserved. This continuation proves
that its derivatives need not be constructed on every signed multiplier
row, and that integer-index recovery is needed at most once. It replaces
the preceding three-channel norm source, rather than paying for it first.
The public parent is again the residue packet and its bit-power/walk
implementation.

`exists_bounded_field_relation` retains the existing smaller-period
pigeonhole witness with its actual offset bound. If D is the literal
quarter factor-sum offset and H=(2B)^2, it gives a positive multiplier
k<=B with k*D<=B^4 and a local root in the original H-term interval.
For a failed quarter window, D>=H. The retained coprime long periods
give global order M>16B^4. Consequently every positive multiplier j<=k
has H<=j*D<=B^4: neither its positive nor negative orientation can equal
a global h^t with t<H. `preceding_point_ne` proves this for every actual
earlier public index. The hidden smaller prime is used only in the
coverage proof, never supplied to selection or construction.

`nonunit_interval_has_root` shows that every nonunit norm has a local
root in at least one prime field. `scanFrom_exists_le` proves that an
actual nonunit witness is selected at or before its index. The selected
row therefore cannot be a shared global root. If its product has a proper
GCD, that GCD is the factor. If its norm is zero modulo the whole input,
the two local root indices must differ, and the existing exact derivative
and integer-index recovery applies. `first_norm_complete` closes this
argument for the actual first scan result. It does not assume away bad
rows or select a favourable row using private factors.

The scalar construction is separate from the three-channel carrier:
`scalarBlock` evaluates one shared baby polynomial after a unit phase
rescaling, `scalarBlocks` multiplies full blocks, and
`scalarSharedProduct` appends the original exact tail. These definitions
contain no derivative or jet calls. `scalarSharedProduct_exact` proves
their complete interval product in every commutative ring and at every
width; the native backend uses positive widths. The commuting identity
`scalarSharedProduct_eq_jet` retains the connection to the richer exact
carrier. The public scalar cache has precisely 2B entries, as proved by
`buildFirstSource_products_length`.

`scanFrom` is an actual recursive scanner that computes and charges one
GCD per inspected cache entry. It retains the selected index and that
already-computed GCD. `scanCache_gcd_bound` proves at most 2B queries.
`lateJet` is one optional retained triple: a proper selected GCD constructs
none, as proved by `lateJet_none_of_proper`. Only saturation constructs
one exact full-block/tail jet with width `normWidth B 1`. Its scalar
meaning is the original H-term interval, and `lateJet_input_bound` proves
its squared degree/point budget at most 128B^2+32. Thus this late input
is linear in B.

The actual late consumer counts its repeated norm GCD, its denominator
unit GCD and the existing integer-index batch. `jetGcdCount_bound` gives
at most 2b+2 such queries. This tally specifies the GCD/unit/index
protocol; its unit decision and inverse still require a literal machine
refinement. The scanner's `Nat.gcd` calls are explicit in its recursion.
Setting b=2B yields

```
new source GCD queries <= 2B + (4B+2) = 6B+2.
```

`buildFirstSource_gcd_bound` proves this on the constructed source;
`packetSource_gcd_bound` transports it to the actual public descent leaf
and that leaf's sixth width. It is a GCD-query bound. Polynomial
construction/evaluation, unit inverse construction, GCD bit cost and the
preceding pipeline bit interfaces require their own complete prices.

`windowCertified_first_complete` discharges coverage on every remaining
public window. `publicPacket_sound` and `publicPacket_complete` preserve
all earlier successes and transport every new candidate through every
retained descent frame. The N-only list/ring specification is universally
correct for all semiprimes, including prime squares and arbitrary factor
ratios. It supplies no local orders, smaller-prime orientation or short
collision index to the executable.

Focused warning-as-error build and strict ordinary-root elaboration pass.
The root-plus-explicit-module checker passes all 14 namespace linters on
65 explicit plus 96 generated declarations. Its transitive audit checks
all 161 declarations, including 99 theorem/helper declarations, with only
`propext`, `Classical.choice` and `Quot.sound`. The new sources are frozen
for replay. No commit, push, wider CI or broad explorer regeneration is
performed.

Replay `202610032401` freezes 117 source hashes, preserving all 113 from
the exact-norm parent. They agree at replay start/end and in the final
source check. All 1,081 semiprimes generated from primes below 200 factor,
including all 46 prime squares. The 31 saved preceding successes retain
their factors and skip the new source. Every preceding saved final factor,
and the original first winning norm's multiplier/sign, is preserved.
Component checks cover 192 scalar-only groups and 828 products compared
with the independent direct product-rule recurrence. Every scalar group
constructs zero derivative polynomials.

The saved remaining input is again
`N=1400000552800003801=1000000007*1400000543`, at B=1,058 and exact
H=4,477,456. Seven adaptive groups evaluate 127 scalar norms, of which
119 are inspected. Index 118 selects positive multiplier k=60 with
`x=1198780255856505610`, `P=687618931813332489` and
`gcd(N,P)=1000000007`. Every earlier inspected GCD is one. This proper
selected product GCD constructs no late jet and no derivative polynomial.
The source retains 2,116 public signed centre values. Eight selected
large products, including the winning one, are checked independently
after timing against the earlier blocked interval-jet implementation.

The component controls also exercise both branches requiring more care:
distinct saturated indices 3 and 9 invoke precisely one late jet and
recover factor 103, while a shared global index 3 correctly invokes one
late jet and returns no factor. This latter control is outside the
remaining-core guarantee and demonstrates why the derived preceding-row
separation theorem is needed. The one-sided-root controls in either
prime orientation reuse their proper GCD and construct no late jet.

Actual new-source counts on the saved remaining input compare as follows:

| New norm-source work | Three-channel norm source | Scalar scan with late derivatives |
| --- | ---: | ---: |
| Constructed evaluation points | 52,756 | 52,756 |
| Degree/point input budget | 129,033 | 129,033 |
| Norm GCDs | 119 | 119 |
| Evaluated three-channel rows | 127 | 0 |
| Polynomial convolutions | 418,979 | 174,825 |
| Packed coefficient visits | 18,242,364 | 6,632,620 |
| Monic reductions | 316,494 | 105,498 |
| Native scalar products | 1,022,456 | 289,960 |

The scalar source still pays for 52,629 full-block points, 127 tail
points, 14 shared root polynomials and 14 point trees. Its separate
native ledger records 290,251 reductions, 28 powers with 663 binary
square/multiply rounds and two public inverses; the largest scalar
product has 121 bits. Its total source GCD count is 119, with zero late
recovery queries. Polynomial/packing operations have their own counters;
the scalar ledger alone is not their complete bit price.

The original-input outer timer reports 67,244.1 ms for this saved case.
It includes the whole preceding bit-power/walk/residue route, public
inverse and centre construction, scalar full-block/tail polynomials,
point generation and evaluation, all selection/recovery, diagnostics
and complete original-input factor transport. Private factors and
independent reference products enter only after timing. The old
three-channel source is not executed first. This saved execution is
not a paired timing experiment or evidence of a proved runtime exponent.

The main complete norm family still requires the preceding explicit
B^(3/2) degree/point layout. Deferring its derivatives removes repeated
recovery and two scalar channels, without proving an O(B) construction.
The grouping/native polynomial implementation and full public bit clock
remain uncertified. The guaranteed every-run one-sixth rate remains OPEN.

## Phase-free bulk norms and saturated left-first recovery (2026-10-03)

New artifacts:

- [SemiprimeBulkNorm.lean](../RiemannGaussian/SemiprimeBulkNorm.lean)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeBulkNorm.lean)
- [Concrete aggregate and saturated-search replay](../scripts/probe_semiprime_bulk_norm.py)
- [Saved replay and pinned sources](semiprime-bulk-norm-audit.json)

This continuation extracts the factor information from a group without
retaining a norm value for each row. The public parent is the residue
packet and its bit-power/walk implementation. The preceding scalar norm
source is used as a theorem in the recovery proof; it is not executed
before the new source. All preceding sources remain frozen.

Let H=(2B)^2, x_i be the existing public signed centre powers, and
P_m(X)=product_{0<=u<m}(X-alpha^u). With H=J*m+T and 0<=T<m,
the canonical row norm satisfies

```
r_i = product_{0<=t<H}(x_i-alpha^t)
    = alpha^(m^2*J*(J-1)/2 + J*m*T)
      * product_{0<=j<J} P_m(x_i*alpha^(-j*m))
      * P_T(x_i*alpha^(-J*m)).
```

The leading factor is a unit. `normalizedBlocks_rephase`,
`normalizedInterval_rephase`, and `modelBlock_rephase` prove the exact
full-block, original-tail, and group identities. The native detector
omits all these phases and folds evaluated values directly into one
aggregate scalar. It constructs neither original per-row norm outputs
nor derivative channels. `bulkDetector_gcd` proves that its GCD is
exactly the GCD of the original canonical row product, including when
that GCD equals N. This uses the earlier RH-transfer identity
`SemiprimeRHCancellation.unit_mul_gcd_eq`.

The information retained by the aggregate test is the original union
of nonunit rows. A GCD of one clears the whole group; a proper GCD
already gives a factor. If the aggregate GCD is N, the source splits
the group into its left and right halves and constructs only the left
aggregate. A proper left GCD factors immediately. A saturated left
GCD continues left. A unit left product and a known zero whole product
imply that the right canonical product is zero, by exact unit
cancellation. The source continues right without constructing or
testing that right aggregate at this level. Widths may change between
queries, because each normalized constructor has its own exact
GCD-preservation proof.

`splitZero_correct` proves this actual recursive search. Its leaf
alternative keeps the original index, exact zero canonical norm, and
a position no later than any nonunit leaf of the group. It makes
at most one left GCD query per level, as proved by
`splitZero_gcd_bound`. The proof works with an abstract producer only
when supplied its exact GCD identity; the actual public source
supplies `bulkDetector` and discharges that identity. No fast or free
bulk oracle is assumed.

`forest` inspects successive groups of sizes 1,2,4,..., starting at
indices 0,1,3,7,..., and stops on the first nonunit group. It charges
every aggregate and split GCD in its recursion. Unit dummy leaves
after the 2B real rows do not add interval roots, change H, or enter
the native evaluation points. `forest_sound` retains the earliest
nonunit property over the whole prefix. `forest_exists` proves that
any original nonunit witness forces a result. At
D=(2B).log2+1, `publicDepth_covers` proves complete signed-row coverage
and `scanForest_gcd_bound` proves at most 2D bulk queries.

`bulk_norm_complete` transfers the frozen first-nonunit theorem to
this actual forest. A proper aggregate candidate finishes directly.
If the forest returns a saturated row, its earliest-row invariant
and the deterministic first scan identify the same earliest nonunit
index. Consequently the already proved exclusion of shared global
roots applies, and this row has the existing exact interval recovery.
The scalar scan and its private-prime coverage witnesses occur in
this proof only; they are not inputs or construction calls of the
new source.

`treeLateJet` constructs at most one exact original three-channel
row. It does not test or rebuild that row's long norm before
constructing the jet. `factorFromAnswer_inr_exact` proves the same
interval-recovery meaning. A proper aggregate candidate constructs
no jet. The actual retained source has no scalar-cache field and
uses the existing late consumer's GCD/index protocol, giving

```
bulk/search GCDs <= 2D
total new-source GCD queries <= 2D + 4B + 2.
```

`buildBulkSource_gcd_bound` and `packetSource_gcd_bound` prove these
on the constructed source and its actual public descent leaf.
Polynomial construction, evaluation, inversion, and GCD bit costs
are not supplied by this query-clock theorem. The late unit decision
and inverse remain part of the open machine refinement.

`windowCertified_bulk_complete` closes every remaining public-window
premise. `publicPacket_sound` and `publicPacket_complete` preserve
earlier successes and transport new candidates through every retained
descent frame. This N-only specification is universally correct for
all semiprimes, including squares and arbitrary factor ratios.

The focused warning-as-error build takes 3.4 seconds and strict
ordinary-root elaboration passes. The root-plus-explicit-module
checker passes all 14 namespace linters on 66 explicit plus 163
generated declarations. The transitive axiom audit checks all 229
declarations, including 141 theorem/helper declarations, with only
`propext`, `Classical.choice`, and `Quot.sound`. The module is registered
in the ordinary root and the semiprime explorer family. No commit,
push, broader CI, or broad explorer regeneration is performed.

Replay `202610032501` freezes 121 source hashes and preserves every one
of the 117 parent pins. They agree at replay start/end and in the final
source check. All 1,081 semiprimes from primes below 200 factor,
including all 46 prime squares. All 31 saved preceding successes
retain their factors and skip the new source. Every saved final
factor is preserved. The direct component recurrence checks 192
phase-free groups containing 899 original row products, across
different moduli, interval lengths, widths, and both empty and
nonempty tails. It compares GCDs, not the phase-changed scalar values.

Six synthetic controls separate the relevant recovery cases. A unit
group clears; a proper aggregate returns its existing factor with
no jet. A group containing a p-only and a q-only root saturates, and
the paid left query gives a proper factor with no derivatives. Two
saturated rows have combined first jet `(0,0,0)`, but the balanced
search retains one original saturated row and its single late jet
recovers factor 103. A unit left row and saturated right row infer
the right zero product without constructing or testing that right
aggregate, then recover from one late jet. The shared-global-root
control correctly returns no factor; it lies outside the retained
core guarantee and is not assumed recoverable.

The saved remaining input is
`N=1400000552800003801=1000000007*1400000543`, with B=1,058 and
exact H=4,477,456. Seven root groups have sizes 1,2,4,8,16,32,64,
starting at indices 0,1,3,7,15,31,63. The first six aggregate GCDs
are one. The final group's phase-free product is
`581176320068234212`, with GCD `1000000007`. Its canonical product
is `1387298492711089381`, with the same GCD. This proper aggregate
returns the factor without selecting a row, performing a split,
or constructing a derivative jet. All seven group GCDs are checked
after timing against separately constructed phase-correct products
from the frozen scalar constructor.

The saved source counts compare with the immediately preceding
scalar scan as follows:

| New norm-source work | Scalar scan with late derivatives | Phase-free aggregate forest |
| --- | ---: | ---: |
| Constructed evaluation points | 52,756 | 52,756 |
| Degree/point input budget | 129,033 | 129,033 |
| GCD queries | 119 | 7 |
| Retained per-row norm outputs | 127 evaluated before stopping | 0 |
| Returned aggregate outputs | 0 | 7 |
| Late derivative rows | 0 | 0 |
| Polynomial convolutions | 174,825 | 174,825 |
| Packed coefficient visits | 6,632,620 | 6,632,620 |
| Monic reductions | 105,498 | 105,498 |
| Native scalar products | 289,960 | 184,130 |
| Native scalar reductions | 290,251 | 184,244 |
| Native scalar powers | 28 | 14 |
| Binary square/multiply rounds | 663 | 254 |

The per-row-output comparison concerns the evaluated stopping
prefix, not a claimed native allocation of all 2B norms. Both
sources cache 2,116 public signed centres. Both still construct
52,629 full-block points, 127 tail points, 14 root polynomials,
and 14 point trees. The new detector computes zero phase factors.
Its scalar product count falls by 105,830, approximately 36.5%,
while its separate polynomial/packing counters are unchanged.
It pays for two public inverses; its largest scalar product has
121 bits. These are native operation counters, not a complete
bit-price certificate.

The original-input outer timer reports 64,482.0 ms. It includes the
whole preceding bit-power/walk/residue route, public inverse and
centre construction, concrete phase-free block/tail polynomials,
point generation and evaluation, all aggregate/search/consumer
work, diagnostics, and complete original-input factor transport.
Neither the preceding full scalar norm source nor its per-row GCD
scan is executed first. Private factors and canonical reference
products enter only after timing. This saved execution is not a
paired timing experiment or evidence of a proved runtime exponent.

The new detector still uses the same shared degree/point layout
S=m+R*floor(H/m)+(H mod m)+R. Unit cancellation removes phase work
and retained scalar outputs; it does not remove these evaluation
inputs. The previous complete-family layout obstruction therefore
still applies, giving B^(3/2) scale rather than the required linear
B construction. Native polynomial/group execution and the full
public bit clock remain uncertified. The guaranteed every-run
one-sixth rate remains OPEN.

## Transposed scalar q-aggregate and its growing degree (2026-10-03)

New artifacts:

- [SemiprimeQAggregate.lean](../RiemannGaussian/SemiprimeQAggregate.lean)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeQAggregate.lean)
- [Transposed constructor probe](../scripts/probe_semiprime_q_aggregate.py)
- [Saved constructor audit](semiprime-q-aggregate-audit.json)

This investigates the actual aggregate construction after the previous
bulk source removes per-row outputs. It retains the original aggregate
as `rowAggregate` and proves a commuting sign identity for the scalar
q-prefix in `qPrefix_eq_rowAggregate`. Its recurrence has order one,
but its monic coefficient is product_i(X-x_i), of degree exactly r.
`recurrenceCoeff_natDegree` proves this over every nontrivial
commutative ring, including composite-modulus rings and repeated targets.

For a positive exponent-block width s, the monic transposed baby
polynomial is

```
Q_s(X) = product_{0<=u<s} product_{0<=i<r}(X-x_i*alpha^(-u)).
```

Its values at alpha^(j*s) retain all original block factors because

```
x_i-alpha^(j*s+u) = -alpha^u * (alpha^(j*s)-x_i*alpha^(-u)).
```

The omitted factors are units. `originalBlock_rephase`,
`qBlocks_rephase`, and `qDetector_rephase` prove the exact full-block
and original-tail identities. `qDetector_gcd` preserves the entire
canonical aggregate GCD, including saturation, for every modulus.
It assumes no hidden field orientation, order, or collision index.

The native constructor shares one s-root polynomial, scales it
homogeneously for each target without any inverse of that target,
and multiplies those polynomials. It folds the giant-point evaluations
directly into one scalar. `normalizedBlock_natDegree` proves the
baby degree is exactly r*s. Thus avoiding a list of r*s roots has
not removed the coefficient storage or multiplication of that degree.
The exact tail has degree r*(H mod s). The explicit degree/point
budget is

```
S_q(r,H,s) = r*s + floor(H/s) + r*(H mod s) + 1.
4*r*H < S_q(r,H,s)^2.
32*B^3 < S_q(2B,(2B)^2,s)^2, for every s>0 and B>0.
```

`qInputs_squared_floor` and `qInputs_full_floor` prove these statements.
They restrict this explicit polynomial block representation. They
do not prove an impossibility theorem for other scalar aggregate
representations, geometric circuits, or factoring algorithms.

The parameter-dependent analysis in Theorem 5 of
[Bostan–Yurkevich](https://arxiv.org/pdf/2012.08656) likewise retains
the recurrence coefficient degree d: for scalar order one its
arithmetic estimate depends on sqrt(H*d), not merely sqrt(H).
Here d=r grows with B. This literature result is context, not a
Lean axiom, a composite-ring backend proof, or a bit-cost certificate.

The focused warning-as-error build takes 3.2 seconds. Strict ordinary
root elaboration and all 14 namespace linters pass. The transitive
audit checks 24 explicit plus 19 generated declarations, 43 in total,
including 30 theorem/helper declarations, with only `propext`,
`Classical.choice`, and `Quot.sound`. The module is registered in the
ordinary root and semiprime explorer family.

Replay `202610032601` freezes 125 sources, preserving all 121 parent
pins at start, end, and final verification. Component checks compare
192 groups and 872 direct row products over varied composite moduli,
widths, repeated/nonunit targets, zero intervals, and exact tails.
All six preceding synthetic saturation/global-root controls preserve
their aggregate GCDs.

The seven saved public groups again give GCDs
`1,1,1,1,1,1,1000000007`. Their explicit budgets are
`4233,8833,8465,17378,16929,33604,34881`, totaling 124,323.
The constructor performs 107,711 polynomial convolutions,
5,777,291 packed coefficient visits, 105,437 monic reductions,
257,740 scalar multiplications, and 257,776 scalar reductions.
Each separate group constructor acquires its public inverse and
charges its coefficient/point/polynomial construction and final GCD.
The sum of the seven separate constructor timers is 4,523.3 ms.
This is not a whole public-pipeline timer or a paired source benchmark.

Complete-family shape controls use the same fixed public modulus/base
and widths B=2,8,32,128,512. All canonical GCDs agree with separately
constructed preceding aggregates. Their baby degrees are
`8,64,512,4096,32768`, with budgets `17,129,1025,8193,65537` and
zero tails. Quadrupling B multiplies the baby degree by eight.
The exact layout growth, not a fitted timing exponent, is the evidence
for this representation's B^(3/2) scale.

This constructor experiment does not replace the already certified
N-only bulk factorizer and does not execute its whole public prefix.
Target acquisition is outside its explicitly labelled constructor
timer. No hidden factors enter a constructor. The native backend and
all bit-operation prices remain uncertified. A useful next aggregate
representation must avoid this growing explicit polynomial degree;
the guaranteed one-sixth rate remains OPEN.

## Known-residue polynomial content and height audit (2026-10-03)

New artifacts:

- [SemiprimeKnownBitsBudget.lean](../RiemannGaussian/SemiprimeKnownBitsBudget.lean)
- [Root-import namespace and axiom checker](../scripts/CheckSemiprimeKnownBitsBudget.lean)
- [Exact coefficient/content probe](../scripts/probe_semiprime_known_bits_budget.py)
- [Saved known-residue diagnostic audit](semiprime-known-bits-budget-audit.json)

A fresh primary-source search found
[Carella's claimed one-sixth algorithm](https://arxiv.org/pdf/1308.2891v3).
The application in Section 5 is not a usable proof of the requested
guarantee: its listed linear coefficients omit factors B from its
own expansion, and the unscaled integer polynomial has common
content B. The checks below address these specific steps and the
height budget after removing the guaranteed content. They are not
a blanket negative result about other lattice or known-bit methods.

For the literal known-residue encoding p=A+B*x, q=C+B*y, and
A*C-N=B*D, the correct identity is

```
(B*x+A)*(B*y+C)-N = B*(B*x*y+C*x+A*y+D).
```

`originalForm_eq_content` proves this as a bivariate integer-polynomial
identity, and `originalForm_coeff_dvd` proves B divides every coefficient.
The divided polynomial need not be primitive for arbitrary A,C,D;
the probe's coprimality condition makes it primitive on its reference
cases. `dividedForm_mixed_coeff` retains its nonzero xy coefficient B.
`dividedForm_not_unit` and `content_not_unit` therefore make both factors
nonunits when B>1. `originalForm_not_irreducible` proves that the
unscaled polynomial is reducible over the integer polynomial ring.
Rational irreducibility does not license inflating the integer height
with an arbitrary common coefficient factor.

The correctly normalised leading scale has XY=N/B² and W=N/B.
Clearing the idealised condition (XY)^3<W² gives

```
N^3 < N^2*B^4  iff  N < B^4, for N>0.
```

`cleared_height_budget_iff` proves this exact integer equivalence.
`sixth_scale_fails_height_budget` proves failure at N=B^6 for B>1.
This audits the idealised height argument. It neither imports a
small-root algorithm nor proves a lower bound for all lattice solvers.

The compiled `control_integer_content` checks the balanced semiprime
10403=101*103, B=4, A=65, C=67, D=-1512, with root x=y=9.
Its correct coefficients are `16,268,260,-6048`, with integer
content four; the divided coefficients are `4,67,65,-1512`.
Dropping B from the two linear coefficients changes the root value
from zero to -3564. The control also proves the primality and balanced
range of this factor pair.

The focused warning-as-error build takes 2.4 seconds. Strict ordinary
root elaboration and all 14 namespace linters pass. The transitive
audit checks 14 explicit plus 10 generated declarations, 24 in total,
including 20 theorem/helper declarations, with only `propext`,
`Classical.choice`, and `Quot.sound`. The module is registered in the
ordinary root and semiprime explorer family.

Replay `202610032701` freezes 129 sources, preserving all 125 parent
pins at start/end and final verification. It checks 192 seeded balanced
reference cases, the exact small control and the saved larger factor
pair, plus 256 exact sixth-scale budgets B=2,...,257. Each correct
polynomial vanishes at its labelled reference root, coefficient content
and height normalization agree, and every idealised cleared criterion
matches N<B^4. All sixth-scale criteria fail.

For the saved N=1400000552800003801, the paper's floor sixth modulus
is B=1,057. The original coefficient content is 1,057; the scaled
height drops from 1398200607445408900 to 1322800953117700.
The supplied reference box has width 1,118,690. Its normalised
height criterion fails, and dropping the two linear B factors
gives nonzero root value -44991616803372096.

Private factors are used only in labelled diagnostic reconstruction.
This probe is not an N-only factorizer or a timing/bit certificate.
The previously proved public factorizer and all frozen positive/no-go
artifacts remain intact. No commit, push, broad CI, or broad explorer
regeneration is performed. The complete guaranteed every-run one-sixth
bit theorem remains OPEN.

## Public Euclidean quotient rows and matrix-free collision search (2026-10-03)

Artifacts:

- [SemiprimeQuotientRows.lean](../RiemannGaussian/SemiprimeQuotientRows.lean)
- [CheckSemiprimeQuotientRows.lean](../scripts/CheckSemiprimeQuotientRows.lean)
- [probe_semiprime_quotient_rows.py](../scripts/probe_semiprime_quotient_rows.py)
- [semiprime-quotient-rows-audit.json](semiprime-quotient-rows-audit.json)

The primary lead is [Gao–Feng–Hu–Pan's rank-three lattice
paper](https://eprint.iacr.org/2025/1004.pdf), whose balanced-semiprime
result has exponent one-fifth with improved logarithmic factors.
Its second-vector mechanism avoids a trivial linear collision. Its
large-order toolkit discusses potential future one-sixth algorithms;
this is not a proved one-sixth factorization theorem. No external Lean
code, lattice reduction theorem, short-vector oracle or complexity axiom
is imported into the new module. The identities and executable Euclidean
constructor below are checked by the local Lean kernel.

For public N, m and a unit candidate residue j, set
u=N*j^(-2) modulo m. The new `euclidShort` retains both signed Euclidean
coordinates. `shortPair_correct` proves that it returns a nonzero a and
a positive t with a≡u*t modulo m, |a|≤S and (S+1)*t≤m. At S=floor(sqrt m),
both coordinates are at most sqrt m. `euclidShort_divisions_bound`
counts the actual quotient/remainder iterations and bounds them by twice
the input bit-length envelope. This is an iteration count, not a complete
bit-operation or Boolean-circuit theorem.

The public lift computes D=(N*t-j²*a)/m, chooses b congruent to
−j^(-1)*D modulo m in a centered interval, and computes c=(D+j*b)/m.
`publicInverse_correct`, `quotientSlope_coprime` and `publicRow_correct`
discharge the public coprimality and exact-division conditions. The
retained integer polynomial g(x)=a*x²+b*x+c satisfies exactly

    m²*c-j*m*b+j²*a=N*t.

Adding a multiple of the trivial linear direction changes b and c by
k*m and k*j while retaining the same quotient class;
`quotientRelation_shift` proves this identity. This cancellation takes
place in coefficient space. It does not replace the original collision
product by a signed sum of evaluated residuals.

For the correct residue j=p mod m and x=p/m, Lean proves an integer i with
g(x)=p*i, and the exact retained factor-sum identity

    m²*i=a*p+b*m-2*a*j+t*q.

The corresponding public giant exponent is

    E=c*m²+b*m*(1-j)+a*(1-j)².

`publicRow_balanced_power_coverage` proves the actual Fermat collision
alpha^E=alpha^(m²*i) in the hidden p field, with |i| below the explicit
public `indexLength`. It also proves that the actual p lies in the
public integer-root list for

    a*p²+(b*m-2*a*j-m²*i)*p+t*N=0.

The leading coefficient is nonzero, so this is informative quadratic
recovery. Both square-root orientations are retained, and native recovery
validates every returned candidate as a proper divisor of N. The exact
kernel control at N=10403, m=4, j=1 has (a,b,c,t)=(-1,-1,650,1), i=0,
E=10400, and root list [-103,101].

For p≤q≤2p the current public index envelope is

    K = floor((sqrt(m)*(3*(sqrt(N)+1)+2*m)+(floor(m/2)+1)*m)/m²)+1,

where every square root in the formula is the exact floor square root.
The source enumerates the unit residues j, retains both giant-step
orientations, removes whole-modulus matches through quadratic recovery,
then evaluates their one product polynomial at K geometric baby points.
A saturated aggregate uses one selected column of individual differences.
No full baby/giant pair grid is constructed. Local-period GCD checks,
Bezout inverses, Euclidean division, modular powers, polynomial construction,
evaluation and recovery are all inside the public-source timer and counters.
If a local-period setup saturates modulo N, the prototype reports an
inconclusive stage; it does not claim an unsupported recovery theorem.

The explicit row/point budget has scale m+sqrt(N)/m^(3/2), balancing at
m of fifth-root scale. `indexLength_fifth_budget` proves K≤10*M²+1 when
N≤M^10 and m=M²; `fifth_layout_budget` includes both signed row orientations
and proves 2*M²+K≤12*M²+1. This is a positive construction budget, not a
complete deterministic factoring bit-complexity theorem. At sixth-root
modulus scale, this prescribed public baby axis still has quarter-root
scale. The exact perfect-power shape controls in the replay record this
parameter price; they are not hard semiprime inputs or lower bounds on
all algorithms, actual collision indices, or executions that finish in
an earlier prefix.

Frozen replay 202610032801 preserves all 129 parent source pins and adds
the parent audit plus the new module, checker and probe, for 133 pins.
It checks 20,203 public short relations (maximum six Euclidean steps),
192 balanced reference rows, three exact controls and six parameter
shapes. All 128 small N-only source calls return a reference factor:
32 local-period GCDs, 28 selected-column recoveries, 38 one-axis product
GCDs and 30 global quadratic recoveries. Private factors select rows
only in labelled reference checks. The public source receives N and
public presets and enumerates candidate residues itself.

For N=1400000552800003801, both timed N-only sources succeed:

| Public modulus choice | m | Constructed rows | Signed giant steps | Baby points | Explicit row/point inputs | Returned factor | Time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Sixth-root scale | 1089 | 660 | 1320 | 98775 | 100095 | 1400000543 | 6440.48 ms |
| Fifth-root scale | 4356 | 1320 | 2640 | 12348 | 14988 | 1000000007 | 1164.66 ms |

Both use selected-column recovery after an aggregate saturates. They
construct 796 and 1090 individual differences respectively, in one
selected column; they do not construct the corresponding 130,383,000
and 32,598,720-entry pair matrices. The sixth-root source records 183,821
convolutions, 7,240,164 packed coefficients and 197,549 monic reductions.
The fifth-root source records 25,608 convolutions, 1,045,261 packed
coefficients and 24,695 monic reductions. Their total counted integer
GCD calls are 117,357 and 19,186, including the local-period prefix.
Their Euclidean/integer divmod calls are 10,748 and 23,594. Maximum integer
construction operands are 79 and 83 bits; maximum modular product size
is 121 bits in both. These are native measurements on one common N,
not a fitted runtime exponent or a paired benchmark against a frozen
older pipeline with a different setup and proof scope.

The focused strict build passes, as do the strict ordinary root,
all 14 namespace linters and the complete axiom audit: 65 explicit
declarations plus 71 generated declarations, 136 total, with 83
theorem/helper declarations using only the three permitted standard axioms.
The root import and semiprime metadata family are registered. All frozen
parents and concurrent RH work are preserved; no commit, push, wider CI
or broad explorer regeneration is performed.

The exponent-changing requirement is now explicit: at sixth-root modulus
scale, acquire enough informative collision indices within a linear-m
budget, or compute a sufficient detector without enumerating the current
larger baby axis. A stronger signed factor-sum estimate must preserve its
public construction, hidden-field collision and quadratic recovery, and
eventually include arbitrary factor ratios and complete local-period
setup. The requested every-run N-only one-sixth bit theorem remains OPEN.

## Public row centering with exact target transport (2026-10-03)

Artifacts:

- [SemiprimeQuotientCentering.lean](../RiemannGaussian/SemiprimeQuotientCentering.lean)
- [CheckSemiprimeQuotientCentering.lean](../scripts/CheckSemiprimeQuotientCentering.lean)
- [probe_semiprime_quotient_centering.py](../scripts/probe_semiprime_quotient_centering.py)
- [semiprime-quotient-centering-audit.json](semiprime-quotient-centering-audit.json)

This continuation uses the actual RH-path unit-phase cancellation from
`SemiprimeRHCancellation.unit_mul_gcd_eq`, with the original row target
transported as well. It retains the Euclidean quadratic in
`CenteredPacket.original` and its exact public integer shift separately.
It does not replace the collision product by a signed sum or interpret
the difference of two giants as the union of their original hits.

For a public shift k, the new row is

    (a,b,c,t) -> (a,b-k*m,c-k*j,t).

`shiftRow_relation` retains m²*c-j*m*b+j²*a=N*t.
`shiftRow_quadratic` proves g_new(x)=g_original(x)-k*(m*x+j).
Thus at the correct residue, where m*x+j=p and g_original(x)=p*i,
the shifted index is exactly i-k. `shiftRow_giant` proves
E_new=E_original-k*m². `shiftRow_recovery` shows that the complete
two-orientation integer candidate list is unchanged at these transported
indices. In particular, the leading quadratic coefficient remains
nonzero and no integer recovery information is lost.

The key ring identity in `shiftRow_residual` is

    alpha^(E-k*m²) - alpha^(m²*(i-k))
      = alpha^(-k*m²) * (alpha^E - alpha^(m²*i)).

The multiplier is a public unit. `shiftRow_residual_gcd` consequently
preserves the exact residual GCD for every modulus, including prime
powers and saturation. Centering the giant alone does not preserve the
signal. The kernel-checked `control_target_transport` shows this in the
actual 101 component: 2^10400=1, whereas 2^10368!=1; transporting the baby
target restores the equality. The native control for N=10403 also checks
that the original and transported residuals have GCD 101, while the
untransported centered giant has GCD 1.

The shift is constructed from N-only information. For the balanced
promise p<=q<=2p, `balanced_factor_box` proves the exact integer bounds

    L = floor(sqrt(N/2)) <= p <= U = floor(sqrt(N))
    U <= q <= V = floor(sqrt(2*N)).

All divisions and square roots here are literal integer operations.
If v=b*m-2*a*j and t>0, `lowerSum` and `upperSum` bound
a*p+t*q+v by choosing the p endpoint according to a's sign.
`factor_sum_interval` proves the bound, and `factor_sum_width` retains
the exact width

    hi-lo = |a|*(U-L)+t*(V-U).

The original signed identity is retained before this estimate.
`publicShift` computes k=floor((lo+hi+m²)/(2*m²)), rounding the interval
midpoint to the nearest whole m-squared phase. `rounded_interval` proves
the rounding bound for arbitrary signed intervals and boundary ties.
The square-root bounds on the actual Euclidean coordinates then give
the common public length

    Kc = floor((sqrt(m)*(V-L)+m²)/(2*m²))+1.

`centered_index_bound` proves |i-k|<Kc. The ordinary-root theorem
`publicPacket_balanced_coverage` connects this bound to the actual
executable public packet, retains both the original and shifted indices,
and proves p belongs to the shifted candidate list.
`publicPacket_balanced_power_coverage` additionally discharges the local
Fermat period and proves the literal alpha^E_new=alpha^(m²*(i-k)) collision.
No hidden factor or period is an input to the constructor.

This is a smaller explicit construction bound. For N<=M^10 and m=M²,
`centeredLength_fifth_budget` gives Kc<=M²+2 and
`centered_fifth_layout` includes both signed giant orientations in
2*M²+Kc<=3*M²+2. For N<=M^12 at the same square modulus,
`centeredLength_sixth_budget` gives Kc<=M³+2. These are input-envelope
theorems, not complete bit clocks or lower bounds on all algorithms.
The shared interval still scales as sqrt(N)/m^(3/2), so its exponent
has not changed. Further work must shrink that width using additional
information, or obtain a sufficient detector without enumerating it.

Frozen replay 202610032901 preserves all 133 parent source hashes and
adds the parent audit plus the new module, checker and probe, for
137 pins. They match before and after replay and at the final check.
The new N-only source reuses the frozen preceding controller bytecode
with independent globals binding the new row and length constructors;
the parent's globals and physical sources are unchanged. This preserves
its public local-period setup, both orientations, global-match quadratic
recovery, product evaluation and selected-column saturation recovery.
Every new endpoint square root, shift arithmetic and transported row
construction is charged inside the source timer. Original row packets
are retained; no full pair matrix is constructed.

The same 192 parent reference cases satisfy the new shorter bound and
recover the same actual p from the transported candidate list. A further
31 prime-square reference rows also pass. There are 12,288 exact signed
rounding checks, 678 original/transported residual GCD comparisons, three
exact controls and six parameter shapes. All 128 small N-only calls
return a reference factor: 4 local-period GCDs, 5 selected-column
recoveries, 85 one-axis product GCDs and 34 global quadratic recoveries.
Private factors enter only these separately labelled reference checks.

Two paired executions on the same saved input
N=1400000552800003801=1000000007*1400000543 give:

| Public modulus | Rows / signed giants | Old points | Centered points | Old input count | Centered input count | Old time | Centered time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| m=1089, sixth-root scale | 660 / 1320 | 98,775 | 11,642 | 100,095 | 12,962 | 6,403.50 ms | 884.31 ms |
| m=4356, fifth-root scale | 1320 / 2640 | 12,348 | 1,456 | 14,988 | 4,096 | 1,158.66 ms | 460.48 ms |

The new source returns 1,000,000,007 by a proper aggregate GCD at baby
indices 493 and 1 respectively, without constructing a selected column.
The actual p reference row shifts from i=16,696 by k=17,189 to i-k=-493
for m=1089; for m=4356 it shifts from i=-1,391 by k=-1,390 to i-k=-1.
At m=4, N=10403, `control_public_shift` checks k=2, Kc=6 instead of
the preceding 41, and the unchanged root list [-103,101].

The sixth-root replay reduces total integer GCDs from 117,357 to 13,225,
convolutions from 183,821 to 22,824, packed coefficient visits from
7,240,164 to 831,145, and monic reductions from 197,549 to 23,283.
The fifth-root replay reduces those counts from 19,186 to 5,814 GCDs,
25,608 to 5,344 convolutions, 1,045,261 to 151,844 packed visits, and
24,695 to 2,911 monic reductions. New centering costs are included:
integer divmod counts rise from 10,748 to 12,068 and from 23,594 to
26,234 respectively. Scalar power counts and square/multiply rounds
remain 1,321 / 84,677 and 2,641 / 171,849. Maximum integer construction
sizes remain 79 and 83 bits, and modular products remain at most 121 bits.
These paired timings on one common N are not a fitted scaling exponent.

The focused strict build, strict ordinary root and explicit checker all
pass. The 14 namespace linters check 32 explicit and 32 automatically
generated declarations with zero errors. The complete transitive axiom
audit covers all 64 declarations, including 41 theorem/helpers, and
finds only propext, Classical.choice and Quot.sound. No sorry, custom
axiom or native_decide is used. The new ordinary-root import and explicit
semiprime family assignment are registered; concurrent RH changes and
every frozen source are preserved. No commit, push, broader CI or broad
explorer regeneration is performed.

The remaining scope is explicit: this is balanced collision coverage
and a native prototype with an inconclusive saturated local-period route.
It is not a complete arbitrary-ratio factorizer or native/Boolean machine
refinement. The requested deterministic every-run N-only one-sixth bit
theorem remains OPEN.

## Complete Euclidean intermediate rows and the short-window audit (2026-10-03)

Artifacts:

- [SemiprimeEuclidRowFamily.lean](../RiemannGaussian/SemiprimeEuclidRowFamily.lean)
- [CheckSemiprimeEuclidRowFamily.lean](../scripts/CheckSemiprimeEuclidRowFamily.lean)
- [probe_semiprime_euclid_row_family.py](../scripts/probe_semiprime_euclid_row_family.py)
- [semiprime-euclid-row-family-audit.json](semiprime-euclid-row-family-audit.json)
- [Reference-only index-growth probe](../scripts/probe_semiprime_euclid_family_scaling.py)
- [Reference-only index-growth audit](semiprime-euclid-family-scaling-audit.json)

The tested exponent-changing candidate expands the preceding public
short relation into every Euclidean convergent and intermediate vector.
It keeps the original quadratic in each packet, gives it both public
balanced-factor center orientations, and tests a signed index window
of radius m at sixth-root modulus scale. This is a candidate detector
audit, not a replacement for the already checked universal factorizer.
The request for an arbitrary-ratio deterministic one-sixth bit guarantee
is unchanged.

`euclidPairs` returns the current signed remainder/denominator, all
intermediate quotient updates, and the recursive full update. It omits
duplicate full-step rows and zero leading coordinates. Its actual
recursion terminates by the decreasing Euclidean remainder.
`intermediate_congruence` and `euclidPairs_correct` prove that every
emitted vector retains a nonzero signed numerator, positive denominator
and its exact modular class. `publicPairs_correct` connects the actual
N-only slope to N*j^(-2), and `intermediate_row_correct` discharges the
inverse and lift conditions. Each original quadratic satisfies
m²*c-j*m*b+j²*a=N*t. The new list includes larger coordinates than the
first short vector; no square-root coordinate bound is asserted for it.

`FamilyPacket` retains the source residue, original quadratic and shift.
`reflectedShift` centers the larger-factor orientation without assigning
it the smaller-factor box. `publicPackets` enumerates every public unit
residue and both centers of every informative intermediate row.
`packetExponent_eq` keeps the exact shifted giant exponent proved by the
preceding public-centering module. It does not mix original residuals
into a signed sum or discard the target's center phase.

The complete short-window counterexample is

    N = 369867514421371 = 14799739 * 24991489,
    m = 269.

`control_arithmetic` kernel-checks that both factors and m are prime,
the factors satisfy p<=q<=2p, and m is the first prime at or above the
ceiling sixth root: 267^6<N<=268^6, 268 is composite, and 269 is prime.
It also checks the public modulus is coprime to N. The public native
modulus constructor reaches 268, rejects it, then checks 269, charging
both candidates and all 16 actual trial divisions inside its timer.

The kernel-checked `control_p_order` and `control_q_order` prove that
base 2 has orders 4,933,246 and 12,495,744 in the two actual components.
Both orders are coprime to m². `control_baby_orders` consequently gives
the same orders for gamma=2^(m²); the short setup does not saturate or
find a proper factor. The literal stride inverses are 3,615,823 and
5,350,681, with m²*inverse congruent to 1 modulo the corresponding order.

`control_all_far` performs closed Lean-kernel reduction of the complete
public exponent family. For every actual exponent E it checks

    m < (E*inverse) mod order < order-m

in both components. This checks every public unit residue and both
center orientations, including incorrect-residue aliases, rather than
only selecting the two correct factor residues. It uses `decide +kernel`,
not `native_decide` or an unchecked compiler result.
`emod_short_window`, `collision_index_modEq` and `no_short_collision`
transport these literal residue checks to the actual signed powers.
`control_no_short_collisions` excludes every |i|<=269 collision in both
prime fields. `control_residual_isUnit` then proves that every original
giant/baby difference is a unit over the actual semiprime ring.
`control_column_isUnit` keeps the whole original product, and
`control_column_gcd_one` proves its public GCD is 1 for every signed
column in that window.

The native N-only short detector constructs 7,484 original quadratic
rows, retains 14,968 centered packets, computes 29,936 signed giants,
and evaluates their one product at 270 positive baby points. The two
giant orientations cover the signed index window [-269,269]. Every
one of its 269 local-period checks and 270 aggregate GCDs is 1, and it
returns `exhausted-family-window` after 2,756.06 ms. No full pair matrix
or selected column is constructed. All public modulus search, inverses,
Euclidean intermediates, lifts, centers, powers, polynomial work and
GCDs are within that original-N timer. The source does not receive a
hidden factor, period, selected residue or reference index.

Its counters include 1,346 full Euclidean divisions, 40,992 total
integer divmod calls, 269 public inverses, 810 total integer GCD calls,
195,740 integer products and 202,411 additions. The scalar ledger
records 29,937 powers, 1,606,097 square/multiply rounds, 2,411,078
products and 3,245,727 reductions. Polynomial work has 30,430
convolutions, 737,701 packed coefficient visits and 539 monic reductions.
Maximum integer construction size is 63 bits and modular products have
at most 97 bits. These are actual native prices of a failed candidate
execution, not a complete bit-clock certificate or an asymptotic bound.

Frozen replay 202610033001 preserves all 137 parent source hashes and
adds the parent audit, new module, checker and probe, for 141 pins.
It checks 5,021 coprime modular inputs and 95,878 emitted intermediate
vectors. Its 32 sampled small N-only calls all return a reference
factor: 1 local-period GCD, 21 selected-column recoveries, 9 product
GCDs and 1 global quadratic recovery. The complete public-family
failure above is separately retained. Private factor/order checks run
only after its timer. The smallest actual correct-residue index across
both center orientations is -306, at q's residue j=44, a=3, t=17.
The frozen preceding centered source still factors this same N, returning
14,799,739 in 125.76 ms with its own prescribed m=289, 272 rows and
1,385 baby points. That is a different layout and window, not an
equal-layout speed comparison or a failure of semiprime factorization.

The focused strict build completes in 46 seconds. The strict ordinary
root and explicit checker also pass. All 14 namespace linters report
zero errors in 44 explicit and 41 automatically generated declarations.
The complete transitive axiom audit covers all 85 declarations,
including 53 theorem/helper declarations, and finds only propext,
Classical.choice and Quot.sound. The ordinary-root import and explicit
semiprime family assignment are registered. No earlier pinned source,
concurrent RH work, default factorizer, public endpoint or optional
certificate has changed; no commit, push or broader CI is performed.

The counterexample rules out this particular radius-m coverage claim.
It does not rule out C*m for every fixed C, every public center or
modulus choice, other bases, correlated row detectors, or all algorithms
with exponent one-sixth. Increasing the radius by a small constant
therefore remains an unresolved hypothesis, not an impossibility theorem.

The supplementary reference-only replay 202610033002 tests that
hypothesis on 192 newly generated prime pairs, 32 per nominal input-size
band, retaining all intermediates and both public centers at both
correct factor residues. The private factors deliberately select those
two residues outside any N-only source. Its actual index fractions are:

| Nominal bits | Largest tested minimum index magnitude | Corresponding public prime m | Exact ratio |
| --- | ---: | ---: | ---: |
| 48 | 311 | 269 | 311/269 |
| 64 | 6,252 | 1,693 | 6252/1693 |
| 80 | 81,786 | 11,197 | 81786/11197 |
| 96 | 1,006,424 | 64,693 | 1006424/64693 |
| 112 | 14,042,254 | 382,373 | 14042254/382373 |
| 128 | 350,336,470 | 2,850,493 | 350336470/2850493 |

All raw p,q,N, actual bit lengths, modulus choices and best retained
packets are saved; the worst nominal-128-bit case has actual N bit
length 129. In that band, 3 of 32 cases miss every correct-residue
index within 64*m. These native exact-integer diagnostics are not Lean
prime certificates for those larger inputs, full public-family failure
checks, N-only runtime measurements, or an unbounded asymptotic proof.
Incorrect-residue aliases at larger sizes have not been excluded.
The reference ledger is partial: it tracks selected integer constructor
operations and modulus search, while center/evaluation arithmetic also
uses ordinary Python operations. No complete construction price is
claimed from that ledger. This supplementary artifact freezes the
141 parent pins, parent audit and reference script, for 143 source pins.

An additional untimed native reference pass exposes a useful distinction:
the literal short-window failure still has row-to-row collisions.
Of its 14,968 public centered packets, 14,966 giant values are distinct
modulo N. After whole-modulus deduplication, private component hashes
find 18 repeated values in the p field and 13 in the q field. One p-field
pair is

    j=44, a=-29, t=15, shift=-1767, E=5548012844175291,
    j=60, a=-14, t=37, shift=8695, E=13685097404436363.

Their native public giant values are 82387083281361 and 297936993962521;
their difference has native GCD 14,799,739 with N. A q-field pair at
j=81 and j=87 has public values 169655271304872 and 265844713419104,
whose difference has GCD 24,991,489. These are uncompiled reference
leads, not a claimed N-only selection algorithm or coverage theorem.
They are reproducible by enumerating `public_packets(N,269,...)`, computing
2^E modulo N and deduplicating those public values before the private
reference grouping.

The next candidate is to detect repeated local giant roots through
P(X)=prod(X-G), evaluating P' on its globally distinct roots. This can
reuse the repository's product/derivative recovery machinery and test
correlations between rows without constructing a pair matrix. A full
coverage argument, global-duplicate handling, saturated-output recovery
and paid public construction are still required. Neither the literal
counterexample nor the supplementary data establishes that this new
detector, or any fixed C*m window, meets the requested one-sixth rate.
The complete arbitrary-ratio, every-run, N-only bit theorem remains OPEN.

## Row derivative compression and exact pair recovery (2026-10-03)

The relevant cancellation is already present in the repository as
`SemiprimeRoughProjection.derivative_strips_shared_root` and
`SemiprimeCartesianCompletion.deflatedColumn_eq_product`. The new
[SemiprimeRowDerivative module](../RiemannGaussian/SemiprimeRowDerivative.lean)
connects those exact identities to the actual public intermediate-row
packets. It preserves the rich source upstream: `publicPackets` retains
the residue, original quadratic, multiplier t and public center shift;
`publicRowValues` evaluates its signed giant exponent. Only the downstream
`publicRoots` fork removes equal values modulo the entire N. Removing a
whole-modulus duplicate does not remove any proper pair factor.

For r distinct public values S={G_j}, construct

    P(X)=prod_j (X-G_j),
    P'(G_j)=prod_{k != j} (G_j-G_k).

`rowDerivative_eq_product` proves this over every commutative ring, with
no division or generic-position premise. `rowDerivative_map_zero_iff`
proves that a hidden prime field sees a zero exactly when two globally
unequal row values coincide there. Thus the derivative extracts local
duplicate-root information from the original row correlations; it does
not extract the unknown quadratic index directly.

`recoverRows_none_iff` proves that the exact detector returns none if
and only if every globally unequal original pair difference has GCD 1
with N. `recoverRows_none_iff_prime_separation` identifies this criterion
with separation in both actual prime fields, including p=q. A proper
derivative GCD supplies a factor directly. A derivative with GCD N
triggers the existing proved scan of one selected row's differences.
Every globally unequal canonical difference lies strictly between 0
and N; a nonunit product of those differences must have a proper-factor
leaf. No lucky separator, supplied pair or hidden-factor routing is
assumed. `recoverRows_gcd_bound` proves at most 2*r GCD queries, and
`publicRows_input_bound` gives at most two scalar-axis inputs per original
packet. Neither statement prices polynomial arithmetic, establishes the
total row-count scale, or is a Boolean/bit-machine theorem.

The literal earlier baby-window failure now has a compiled positive
result. `control_pair_exponents` checks two packet exponents at public
residues j=44 and j=60; those membership checks use kernel reduction of
the actual residue constructors. `control_pair_values` checks their
public modular powers, and `control_pair_gcd` checks the proper original
pair GCD. `control_derivative_recovers` consequently proves the entire
public derivative detector recovers a proper factor on

    N=369867514421371=14799739*24991489, m=269.

The pair is a proof witness only: neither packet, hidden factor nor local
order is an input to `recoverRows (publicRoots 269 controlBase)`.
The prior complete-family theorem still proves every short baby column
has GCD 1. The two observables keep different correlations.

The frozen native
[derivative replay](../scripts/probe_semiprime_row_derivative.py) and
[147-pin audit](semiprime-row-derivative-audit.json) time the complete
N-only source: square/base/modulus checks and prime search, all Euclidean
intermediates and lifts, both public factor centers, every giant power,
whole-modulus bucket construction, one monic product tree, coefficient
derivative, reuse of that same tree for evaluation, all derivative GCDs
and lazy recovery. Original packet lists remain in their value buckets
throughout extraction and in retained recovery witnesses. Dictionary
query counters and operand traffic are diagnostic rather than a complete
machine refinement. No pair matrix is constructed.

With seed 202610033101, the timed source on the earlier control keeps
14,968 packets in 14,966 distinct whole-modulus buckets. It returns
14,799,739 after 68 derivative GCDs in 2562.17 ms, including construction.
Its first selected value comes from j=3, not the j=44/j=60 proof pair;
this independently checks that the algorithm was not handed that witness.
The separate reference audit confirms 18 repeated p-values and 13
repeated q-values after global deduplication. All 32 small N-only cases
return factors: 30 directly from a derivative and two by a selected row
scan. An independent native oracle compares the polynomial derivative
to direct omitted products and the full proper-pair union on 132 cases,
including duplicate roots, empty sets and a square; 17 use saturation
recovery. Its recovery GCD counts satisfy the proved 2*r envelope.
These oracle checks are tests, not formal arithmetic refinement.

The first larger reference corpus has eight inputs in each nominal
60- and 72-bit band. Every one has a local row alias, but these are
private-order reference classifications and do not establish coverage.
A supplemental seed-202610033102
[coverage replay](../scripts/probe_semiprime_row_derivative_coverage.py)
conditions reference primes on base 2 having full component order, then
feeds only the selected N into the unchanged public source. It finds

    N=2518766418595894637609
      =39167077933*64308254573,
    m=3691.

The complete timed native source constructs 197,138 original quadratics,
394,276 centered packets and 394,276 distinct row values. It constructs
one degree-394,276 monic polynomial, computes and evaluates its derivative,
and performs all 394,276 derivative GCDs. Every GCD is 1; it returns none
after 101440.31 ms. The
[149-pin coverage audit](semiprime-row-derivative-coverage-audit.json)
retains that full source result and its four reference cases. Private
factors/orders selected the stress input and classify it only outside the
source timer. This is a native exact-arithmetic failure of the fixed
original row axis, not yet a kernel-checked literal failure, a general
factoring lower bound or a failure of all row orientations. Indeed a
separate private-order reference pass on the doubled inverse-row axis
finds two p-value and four q-value repeats. That extension must be priced
and tested separately; it cannot be claimed covered by this positive
result or ruled out by the original-axis failure.

The focused strict leaf build and strict ordinary root both pass.
All 14 namespace linters report zero errors in 24 explicit and seven
generated declarations; the complete module audit includes its private
helper and checks all 32 declarations and 28 theorem/helper declarations.
Their only transitive axioms are propext, Classical.choice and Quot.sound.
All earlier frozen source pins remain unchanged. A separate compact
local-order certificate for the larger failure is under investigation;
until compiled and audited it must not be promoted from native evidence.
The arbitrary-ratio, every-run, N-only one-sixth bit theorem remains OPEN.

## Structural residue checker and the larger failure audit (2026-10-03)

The new
[SemiprimeDerivativeCoverage module](../RiemannGaussian/SemiprimeDerivativeCoverage.lean)
checks a finite residue list by a sort followed by adjacent strict
comparisons. `mergeFuel_perm` and `sortFuel_perm` prove that its structurally
recursive audit sorter preserves the complete input multiset, even with
insufficient fuel. A successful `checkedResidues` result cannot discard
a duplicate. `checkedResidues_nodup` and `checkedResidues_power_injective`
transport that result to all original power pairs at a verified actual
order. `publicRows_none_of_checked_orders` gives full public-family
exhaustion, **conditional on both residue certificates**. It does not
supply those certificates.

`control_arithmetic` checks both actual component primes of the larger
stress input, balancedness, the product N, sixth-root rounding and the
first public prime modulus 3691. `control_p_order` and `control_q_order`
check actual base-2 orders 39167077932 and 64308254572 using every
prime-divisor power test. The N-only base and both component projections
are connected by compiled theorems. `checker_control` checks the audit
sort itself by kernel reduction on a small closed list.

The full 394,276-row kernel certificate remains OPEN. The library's
proof-dependent merge sort did not reduce in the kernel even on a
three-element control. The structural replacement fixes that issue,
but monolithic kernel reduction of the whole actual public family was
stopped after memory exceeded 50 GB. No literal exhaustion theorem,
custom axiom or assumed certificate was added. The
[153-pin audit](semiprime-derivative-coverage-certificate-audit.json)
records both independent native residue sorts, each with 394,275 strict
adjacent comparisons, and explicitly sets `kernel_checked_failure_control`
to false. Its
[reference script](../scripts/probe_semiprime_derivative_coverage_certificate.py)
is not an N-only runtime measurement. It preserves the complete frozen
149-pin native source experiment and its native-only failure status.

The focused strict build and ordinary root pass. All 14 namespace linters
report zero errors in 25 explicit and 43 generated declarations; the
all-declaration audit checks all 68 declarations and 45 theorem/helper
declarations with only the three permitted standard axioms. These are
checker soundness and literal-order results, not a proved failure of every
row orientation, a factoring lower bound or a one-sixth theorem.

## Reciprocal cross-products from the existing row polynomial (2026-10-03)

The inverse row channel keeps a correlation absent from the ordinary
derivative: products of two row values equal to one in a hidden field.
The new
[SemiprimeReciprocalRows module](../RiemannGaussian/SemiprimeReciprocalRows.lean)
proves `inverse_residual_eq` and `inverse_residual_gcd`:

    x-y^(-1)=y^(-1)*(x*y-1),
    gcd(N,x-y^(-1))=gcd(N,x*y-1).

This exact unit-phase transport uses the repository's compiled
`SemiprimeRHCancellation.unit_mul_gcd_eq`. It keeps prime powers and
saturated products. There is no local-order assumption in that GCD identity.

For the retained distinct original values S={G_j}, define

    P(X)=prod_j (X-G_j),
    Q(X)=prod_j (1-X*G_j)=reverse(P)(X).

`reciprocalPolynomial_eq_reverse` proves coefficient reversal over every
nontrivial commutative ring, including composite coefficient rings.
`reciprocalPolynomial_map_zero_iff` identifies its hidden-field root union
exactly with products G_j*G_k=1. The reciprocal polynomial is also the
monic inverse-root polynomial times the retained public unit phase
prod_j(-G_j). `reciprocalPolynomial_eq_unit_phase` keeps that phase;
`reciprocalPolynomial_eval_gcd` and `reciprocalPolynomial_derivative_gcd`
prove exact GCD equality in both channels. At a whole-modulus inverse
match the derivative removes just that global root. Other proper local
hits, including saturation, remain recoverable by the proved
deflated-column recovery.

`reciprocalRows_succeeds_of_product_pair` gives complete proper original
product-pair recovery. `reciprocalRows_gcd_bound` bounds recovery by twice
the original packet count; construction and polynomial bit costs need
their own proof. The N-only specification uses all public original roots
as targets and all their inverse roots in the detector; no hidden factor
or proof witness selects a target.

The new literal compiled result is `control_reciprocal_recovers` on
N=2518766418595894637609, m=3691. `control_exponents` checks actual public
packets at j=768 and j=2283, `control_values` checks their public modular
powers, and `control_product_pair` checks the proper GCD:

    E_1=3596798445668641429783915,
    E_2=3037632300775047433790237,
    G_1=459898352550707889411,
    G_2=588586918346787592002,
    gcd(N,G_1*G_2-1)=39167077933.

That pair is a proof witness only. The complete `recoverReciprocalRows`
detector receives the public base, modulus and N-only family, with neither
factor, order nor pair supplied. The earlier larger ordinary-axis failure
remains a complete native experiment rather than a closed Lean failure
theorem; reciprocal recovery itself is compiled.

The frozen native
[reciprocal source](../scripts/probe_semiprime_reciprocal_rows.py) constructs
one power per original packet and one monic root tree. It computes all
public root inverses with one extended-GCD inverse and three short scalar
products per root, only to identify global inverse matches. It reverses
the existing coefficient list and evaluates that polynomial on the
original root tree. If any global inverse target exists, a second
evaluation of its coefficient derivative supplies exact deflation.
No additional giant powers, doubled root polynomial or pair matrix is
constructed. All constructor work, inversion, lookup, coefficient work,
evaluation, GCDs and selected product-row recovery are timed. The native
arithmetic engine and batch inversion remain unrefined; the ledgers are
not a formal machine or full bit-complexity certificate.

With seed 202610033104, the source on the larger ordinary-axis failure
constructs the same 197,138 original quadratics and 394,276 giant values.
It reverses 394,277 coefficients and evaluates all 394,276 reciprocal
targets. Its public inverse lookup finds no whole-modulus inverse targets,
so this control needs only one evaluation on the original monic tree.
It returns 39,167,077,933 at root index 87,398 after 87,399 aggregate GCDs
in 101542.51 ms, including all construction. The saved earlier ordinary
derivative replay on the same layout took 101440.31 ms and returned none.
These are separate saved timings, not a statistically paired comparison
or evidence for a new runtime exponent. The reciprocal source retains
the same 394,276 counted giant exponentiations, adds 1,182,828 scalar
products for public batch inversion, and builds no pair matrix.

All 32 smaller N-only cases factor: 28 from a reciprocal product and four
by one selected product-row scan. Independent native oracles check exact
reversed-polynomial phase, deflated inverse-root products and the full
proper cross-pair hit union on 133 cases. Those include 49 cases with a
whole-modulus inverse match and 27 saturated selected-row recoveries;
empty root sets, duplicate inputs and squares are included. Recovery query
counts obey the 2*r envelope. The
[157-pin audit](semiprime-reciprocal-rows-audit.json) preserves all parent
pins and this source's exact native output. It does not turn the native
engine or public batch inversion into a formal machine implementation.

The focused strict reciprocal build and ordinary root pass. All 14
namespace linters report zero errors in 18 explicit and eight generated
declarations; all 26 declarations and 22 theorem/helper declarations have
only propext, Classical.choice and Quot.sound as transitive axioms.
Universal product-pair coverage, paid row-count and polynomial budgets,
arbitrary factor ratios and the every-run one-sixth bit theorem remain
OPEN.

## 2026-10-03: combined-row coverage and guarded trace compression

The [combined-channel reference probe](../scripts/probe_semiprime_combined_row_coverage.py)
uses seed 202610033201 and native component orders only after constructing
the complete public packet exponents. It first removes whole inverse-orbit
duplicates modulo the component-order LCM, then folds each local exponent
with its negative. It separately checks local-only self-inversion and
proper plus/minus-one endpoints. The folded classifier agrees with explicit
signed-value grouping on 512 independently generated finite lists and
orders. All 16 nominal-84-bit balanced full-order reference cases have at
least one combined hit; some have only one. This is coverage evidence, not
a deterministic guarantee or an N-only source run. The
[159-pin audit](semiprime-combined-row-coverage-audit.json) preserves the
original ordinary and reciprocal control classifications.

The [wider reference continuation](../scripts/probe_semiprime_folded_row_coverage.py),
seed 202610033202, labels every original packet supporting the rarest prior
hit and searches nominal-90-bit balanced cases. The labelled prior case has
just one reciprocal alias modulo 4,269,956,531,178, across residues 11,462
and 8,057 and different public factor-center orientations. These labels do
not provide a general Euclidean adjacency identity. The second wider case
has no ordinary, reciprocal, local-only self-inverse or proper sign-endpoint
hit in the complete reference classification:

\[
N=788096216222522769981991129
 =24862649616491\cdot31697997935819,\qquad m=30403.
\]

It has 4,894,756 original public packets and 4,894,754 distinct whole inverse
orbits. The native reference orders are 24,862,649,616,490 and
31,697,997,935,818. The [161-pin audit](semiprime-folded-row-coverage-audit.json)
keeps those values explicitly reference-only: neither these component orders
nor the complete failure is a Lean certificate. A miss here concerns this
fixed base, modulus and retained family, and is not a lower bound for all
factoring algorithms or other cancellation observables.

`SemiprimeTraceRows` retains the original unit and projects it to
`traceValue x = x+x⁻¹`. Its compiled `trace_difference` proves, over every
commutative ring with unit inputs,

\[
T(x)-T(y)=(xy)^{-1}(x-y)(xy-1).
\]

`trace_difference_gcd` proves exact GCD preservation of this two-channel
product over every modulus, including prime powers and saturation.
`trace_map_eq_iff` identifies its two local hidden-field channels, and
`trace_difference_isUnit_iff` preserves their complete unit criterion.
This uses the RH-path exact unit-phase transport rather than a norm or a
field-only division identity. A monic polynomial on distinct global traces
and its derivative extract both inter-trace channels with one root tree
and one reused evaluation.

Whole trace equality requires a guard before compression. In the literal
mod-35 `mixed_trace_control`, the units 2 and 32 have the same trace 20, but
their original difference recovers five. `mixed_trace_collision_proper`
proves this mechanism over every positive modulus.
`checkedSignal_none_iff` and `global_trace_guard_none_orientation` prove
that, after the actual checked difference fails, a coalesced row is the
representative or its global inverse. Raw `x-1` and `x+1` checks retain
self-inversion: `self_product_endpoint_proper` proves every proper diagonal
product hit reaches one of those endpoints. They keep the original sign
channels instead of replacing them by a squared trace expression.

`SemiprimeGuardedTrace.guardTraces` is a complete executable representative
scan, with the richer row list upstream. Compiled `guardTraces_orientation`,
`guardTraces_separated` and `guardTraces_trace_mem` prove accepted original
orientations, trace separation and preservation of every original trace.
`guardedTraceRows` runs raw endpoints, those checked representative guards,
then the folded derivative detector. `guardedTraceRows_none_pair_checks`
and `guardedTraceRows_succeeds_of_pair` prove that every supplied proper
ordinary or reciprocal pair hit survives, including diagonal reciprocal
hits and saturated derivative outputs. `guardedTraceRows_sound` certifies
every returned divisor; `guardedTraceRows_succeeds_of_endpoint` includes
the separate endpoint channel.

The compiled `guardedTraceRows_none_iff` is the full converse as well:
exhaustion is equivalent to failed proper-factor checks in every original
ordinary pair, every original reciprocal pair and all raw sign endpoints.
`recoverTraceRows_none_of_pair_checks` proves the folded stage creates no
additional proper-factor channel. This is an exact information-extraction
criterion; it does not assert that any public family always has a hit.

`guardedTraceGcdCount_le` proves at most five recovery GCD queries per
original unit: two raw endpoints, at most one whole-trace guard, and the
two-per-trace derivative/recovery envelope. `publicGuardedTraceRows_gcd_bound`
transports that bound to the actual public packet count.
`control_public_guarded_recovers` proves the complete N-only public guarded
procedure recovers on the earlier 72-bit ordinary-row stress input, using
its original packet membership and modular-power proofs. Its witness pair
and component factors are not procedure inputs. This does not prove that
every retained public family contains a hit. The association-list guard
specification also does not provide a fast deterministic table or price
its lookup work as bit operations.

The [native guarded trace source](../scripts/probe_semiprime_trace_rows.py),
seed 202610033203, constructs the original N-only family, retains every
packet bucket, computes original giant powers once, checks raw endpoints,
batch-inverts units, guards whole-trace matches and builds one distinct-trace
derivative polynomial. It constructs no pair matrix and no extra giant
powers. Independent finite signed-pair/endpoint and direct-product oracles
pass on 306 cases, with 20,528 exact phase-pair GCD checks, seven whole-trace
guard recoveries and three saturated trace-row recoveries. The 72-bit
positive source returns 39,167,077,933 from the trace derivative at row
index 87,398. It constructs and evaluates all 394,276 original units and
traces, with 788,552 raw endpoint GCDs and 87,399 derivative GCDs, in
104828.28 ms including construction. All 32 smaller N-only cases factor:
25 from raw endpoints, four from trace derivatives, one from a whole-trace
guard and two by a saturated selected trace-row scan. These timings are
separate saved runs, not a statistically paired comparison with the earlier
ordinary/reciprocal timings or evidence for a new runtime exponent.

The full paid 90-bit N-only source also returns none. It constructs all
4,894,756 original packet powers, retaining their source buckets; two whole
unit duplicates leave 4,894,754 original units. All 9,789,508 raw endpoint
checks have GCD one. The public batch inverse uses 14,684,262 short scalar
products; every whole trace is distinct, so there is no trace-match guard
query. One degree-4,894,754 polynomial and reused derivative evaluation
visit 9,789,507 tree nodes. All 4,894,754 derivative outputs have GCD one;
recovery exhausts the full folded axis after 1749159.57 ms including every
construction stage. There are 14,684,262 recovery-stage GCD queries in total,
within the proved five-query-per-original-unit envelope. No pair matrix or
extra giant powers are constructed.

The [165-pin full native replay](semiprime-trace-rows-audit.json) records both
controls, all 32 smaller sources, the independent oracles and this complete
stress exhaustion. The [169-pin guarded-specification audit](semiprime-guarded-trace-certificate-audit.json)
inherits those exact runs and checks their recovery query counts without
rerunning the factor sources. This is a completed native failure for this
fixed base, public modulus and retained family. It agrees with the separate
private-order classification, but neither the native polynomial engine nor
the complete failure is thereby promoted to a Lean certificate. The full
native procedure is not a formal machine/bit implementation, and dictionary
lookup counts do not establish deterministic bit costs.

Both focused strict builds and the ordinary root pass. The trace module's
14 namespace linters find zero errors in 30 explicit and 12 generated
declarations, and its all-declaration audit checks all 42 declarations and
35 theorem/helper declarations. The complete guarded module's 14 linters
find zero errors in 39 explicit and 35 generated declarations; its audit
checks all 74 declarations and 52 theorem/helper declarations. Both use
only propext, Classical.choice and Quot.sound transitively. Universal row
coverage, arbitrary factor ratios, paid construction and polynomial/table
bit budgets, and every-run one-sixth factorization remain OPEN.

## 2026-10-03: weighted adjacent rows expose a new cross-center signal

This slice is **PROGRESS**, not completion of the one-sixth goal.
[SemiprimeWeightedRows](../RiemannGaussian/SemiprimeWeightedRows.lean)
retains both original quadratic packets and their separate public centers.
For same-residue rows, write

\[
D=t_2a_1-t_1a_2,\qquad B=t_2b_1-t_1b_2,\qquad
C=t_2E_1-t_1E_2.
\]

Compiled `weightedRow_relation` cancels the common `Nt` term exactly.
`weighted_giant_exponent` identifies the remaining exponent as
`D*(1-2j)+m*B`. `weighted_scaled_factorization` proves

\[
m^2(t_2g_1(X)-t_1g_2(X))
 =(mX+j)\{D(mX-j)+mB\}.
\]

When `D=m*d`, public coprimality supplies the integral companion
`B=j*d+m*h`: `weighted_integral_companion` and `weighted_factorization`
give the exact factorization `(mX+j)*(dX+h)`. This preserves the public
linear direction rather than silently interpreting a common resultant
zero as a hidden-factor signal. These identities apply to rows satisfying
the original checked quotient class; they assert no coverage premise.
`weighted_power` and `weightedPacket_power_reuse` prove
`g^C=(g^E1)^t2*(g^E2)^(-t1)`, so the richer original unit carrier supports
these additional weighted correlations without a row-pair matrix.
`publicPairs_denominator_le` bounds every emitted denominator by `m`,
including all intermediate Euclidean rows.

The center errors are retained explicitly. With unrounded midpoint
`H=a*A+t*B+2*(b*m-2*a*j)`, the literal public shift is
`k=(H+m^2)/(2*m^2)`, with signed error `epsilon=2*m^2*k-H`.
`publicShift_midpoint`, `reflectedShift_midpoint` and
`roundingError_abs_le` connect the actual two constructors to this carrier
and prove `abs(epsilon)<=m^2`. For physical unshifted indices, compiled
`weighted_centered_index` gives the complete two-center identity

\[
\begin{aligned}
2m^2 I_C={}&D(2p-A_1)+t_1a_2(A_2-A_1)
 +t_1t_2(B_2-B_1)\\
 &-(t_2\epsilon_1-t_1\epsilon_2),
\qquad I_C=t_2(i_1-k_1)-t_1(i_2-k_2).
\end{aligned}
\]

The hidden cofactor cancels, but the center difference and rounding terms
remain. In the same-center primitive-determinant case,
`same_center_index_deviation` proves
`abs(2p-A)<=2*m*abs(IC)+m*(t1+t2)`.
`same_center_window_obstruction` excludes the literal short physical index
when `abs(2p-A)>m*(2*M+t1+t2)`. This is a precise restriction on this index,
not on modular aliases, cross-center correlations or factoring algorithms.
The separately labeled private-factor diagnostic finds best adjacent
weighted physical indices 3,376, 330,520 and 18,572,888 on the three earlier
controls, against public moduli 269, 3,691 and 30,403. Cancelling `Nt` alone
therefore does not shorten those correct-residue windows. These diagnostic
minima are native calculations, not new Lean exhaustive failure theorems.

The actual candidate constructor pairs adjacent original rows at every
public unit residue, retaining all four smaller/larger-center choices.
`publicWeightedPackets_length_le` proves its count is at most twice the
original packet count. `recoverWeightedRows` runs the complete inherited
guarded trace procedure on these new units; `recoverWeightedRows_sound`
certifies returned divisors. `recoverWeightedRows_original_gcd_bound`
includes all its endpoint, whole-trace guard and derivative recovery
queries, at most ten per original public packet. This counts recovery
queries only. It does not price original construction, inversion, group
powers, lookup or polynomial operations as bit work. It also does not
assert that original pair hits are present in the weighted family; both
original carriers remain available for a future combined detector.

There is a new positive control on the inherited native 90-bit failure
input `N=788096216222522769981991129`, public `m=30403`, fixed base two.
The two adjacent cross-center packets at public residues 7,483 and 11,359
have weighted exponents

\[
C_1=966926180542225069170,\qquad
C_2=5440830797789338080020.
\]

Compiled `control_weighted_exponents` proves both belong to the complete
public family, reducing only their literal residue constructors rather
than all public packets. `control_weighted_values` checks their original
modular powers, 339724066659803716926062920 and
406912301288304218152558959. The native product-minus-one GCD is
24,862,649,616,491; `control_weighted_product` proves that GCD is proper
without a component-order or primality oracle. Finally,
`control_public_weighted_recovers` proves that the **complete public
guarded procedure** returns some proper divisor on this input. Neither
the proving residues, the pair nor a factor is an algorithm input. Its
success is a Lean certificate; the inherited exhaustion of the original
ordinary/reciprocal family remains a separate **native-only** result.
Cross-center weighted correlations thus supply information that the
original pair observables missed on this control.

The [new replay](../scripts/probe_semiprime_weighted_rows.py), seed
202610033205, checks 171 complete public constructor comparisons, 192,816
integral quadratic factorizations and 31,952 weighted group-power identities.
All 32 smaller N-only paid sources return proper factors: 26 raw endpoints,
one square prefix, four trace derivatives and one saturated selected-row
recovery. The first older control `N=369867514421371` recovers 14,799,739
from a trace derivative after constructing 14,968 original packet powers,
28,864 weighted packets and 22,618 distinct weighted units. It uses 57,728
short weighted powers and 28,864 short products after public batch inversion.
Its 45,236 endpoint, 1,252 trace-guard and 257 derivative GCD queries fit
the compiled envelope. The complete paid native run takes 4147.23 ms on
this saved execution. This is one runtime, not a new asymptotic exponent.

The separate private-order search locates the 90-bit proving pair after
3,516,559 derived packets. It is an uncharged reference search, not an
N-only factorizer runtime. The full paid native weighted procedure has
**not** been replayed on the 90-bit input; its complete success here is
established by the Lean procedure theorem. No full native failure theorem,
private component-order certificate or machine refinement follows.
The [173-pin audit](semiprime-weighted-rows-audit.json) retains the full
169-pin parent, all new sources, paid small controls and the explicitly
separated physical-index and witness diagnostics.

Strict leaf build and ordinary-root import pass. The namespace has zero
errors under all 14 linters, covering 48 explicit and 31 generated
declarations. The transitive audit checks all 79 declarations, including
50 theorem/helper declarations, with only `propext`, `Classical.choice`
and `Quot.sound`. The association-list specification still supplies no
fast deterministic lookup proof, and the native dictionary and polynomial
engine are not a formal bit machine. Universal useful-hit coverage,
arbitrary-ratio completion, all paid setup/row-count/polynomial bit bounds
and guaranteed every-run one-sixth factorization remain **OPEN**.

## Complete original and weighted reference union (2026-10-03)

The [175-pin augmented-row replay](semiprime-augmented-row-coverage-audit.json)
extends the frozen 173-pin weighted-row record with all original packets,
all four adjacent weighted center combinations, cross-family pairs, both
signed channels and raw sign endpoints. Replay seed 202610033206 validates
the signed-union classifier on 512 finite oracle cases and tests eight
new balanced semiprimes of actual bit lengths 89 through 91. Base two has
full component order in this separately generated private reference corpus.
Every case has a proper local signed alias, with no proper sign endpoint
or local self-inversion. Original packet counts range from 4,161,344 to
5,618,824; weighted counts range from 8,206,848 to 11,104,144. Distinct
whole inverse-orbit counts range from 10,176,647 to 13,833,660.

These are complete finite reference classifications of the specified
union, rather than paid public source runs. Private component orders,
larger-input primality and useful-hit coverage are not Lean certificates.
The eight positive cases do not imply a uniform sixth-root bound. A
separate disk-backed larger-corpus replay keeps both signed CRT residues
and a consistent whole inverse-orbit sign; its source and original live
run remain preserved while the full classification finishes.

## Exact cached relation compression and balanced reconstruction (2026-10-03)

The new [SemiprimeRowPeriods module](../RiemannGaussian/SemiprimeRowPeriods.lean)
retains each original signed exponent beside its already constructed
unit power. Equal whole-modulus values provide exponent differences;
they remain available even when the factor detector's original difference
is globally zero. `collectPeriodGcd` keeps one representative per cached
value, and `periodGcdCount_le` bounds its integer relation-GCD operations
by the original packet count. This counts integer exponent GCDs, not
factor-checking GCDs against N, cache comparisons or construction work.

The exact cancellation is

\[
 (e_i-e_j)=(e_i-e_0)-(e_j-e_0).
\]

`centeredRelationGcd_eq_pair` proves that one reference star within an
equality class preserves the entire pair-difference GCD. More strongly,
`collectPeriodGcd_divisibility` and `retainedPeriod_divisibility` prove
this for the actual executable cache scan. Its compiled
`retainedPeriod_eq_cachedPairRelationGcd` equals the GCD obtained from
the full equal-value pair matrix, including arbitrary untrusted cache
values and zero output. That comparison matrix is only a mathematical
carrier; the representative procedure does not construct it. Complete
original packets, signed exponents and cached powers remain upstream.

The executable sorted counterpart removes association-list lookup from
this consumer. `sortedAdjacentPeriod_eq_retained` proves that ordering
complete natural-valued tags and taking differences only between adjacent
equal values returns the same relation GCD. For every positive original
modulus, `naturalValueTags_period_eq` proves that projecting a unit cache
to its canonical natural residues preserves all signed congruence data.
The original unit cache remains available upstream.
`publicSortedRetainedPeriod_eq` therefore identifies the actual N-only
sorted constructor with its original representative constructor, and
`publicSortedRetainedPeriod_certificate` supplies the same annihilating
power. `publicSortedRetainedPeriod_scan_bound` proves exactly
max(0,R-1) adjacent value comparisons after sorting, and at most that many
integer GCDs, for R original public packets. This scan count is separate
from sorting, Boolean comparison, label copying and integer GCD bit costs.

`period_of_equal_powers`, `period_of_gcd` and
`publicRetainedPeriod_certificate` prove that correctly constructed
cached powers give an annihilating exponent D for the original public
base. D may be zero or a multiple of its actual order. Neither
exact-order equality nor divisibility of both p-1 and q-1 follows merely
from this theorem. `signed_power_reduce_of_period` reduces any original
signed power from a certified positive period without an order oracle.

Two downstream observables remain separately available. `probePeriod`
checks b^D-1 and b^D+1 at each further public integer base; its compiled
soundness and `periodProbeGcdCount_le` give at most two checked factor
GCDs per base. `recoverPublicWrappedPeriod` uses the original cache's
actual D in the retained wrapped quadratic reconstruction, with at most
4B checked reconstruction GCDs by `recoverPublicWrappedPeriod_gcd_bound`.
Both routines return only independently checked proper divisors.

The balanced branch now requires only D>=B, rather than the older
arbitrary-ratio branch's D^2>=B^3 threshold. Write p=D*a+1 and q=D*b+1
for an actual common modulus. For p<=q<=2p and N=p*q<=B^6, p<=B^3,
and the true sum wrap label t=(a+b)/D satisfies

\[
 D^2t\le p+q-2\le3B^3-2.
\]

`balanced_wrap_label_bound` proves t<3B when 0<B<=D, and
`recoverWrapped_balanced` proves coverage of the existing scan of 4B
labels. The quotient (N-1)/D retains both the sum and product channels;
adding t*D to its sum remainder and subtracting t from its product
quotient reconstructs a+b and a*b exactly. The quadratic discriminant
then recovers p before the separate GCD check. This uses the already
compiled `wrapped_sum_product_encoded` and `wrappedCandidate_encoded`
from `SemiprimeCommonOrder`; no interval rows or pair matrix are needed
by this reconstruction stage.

`recoverPublicWrappedPeriod_of_checks` upgrades the **actual discovered**
cache period to a common modulus through explicit public prime-divisor
power checks. The annihilating-power premise is discharged by the cache
certificate. `recoverPublicWrappedPeriod_of_prime_period` needs only a
prime discovered D and the single public gcd(N,g-1)=1 check, besides the
balanced size premises. No local order, factor, collision witness or
correct wrap label is an algorithm input. This remains a conditional
branch: nonzero/large/prime D and the public-check acquisition price are
not proved for every input.

The complete public procedures have two kernel-checked positive controls:

| Input | Public row modulus | Actual cached D | Recovery observable |
| --- | ---: | ---: | --- |
| 2047=23*89 | 5 | 11 | Further public base 3 gives gcd(3^11-1,N)=23 |
| 2304167=1103*2089 | 13 | 29 | Bounded wrap scan recovers 1103 at label 3 |

`control_public_period` and `control_public_period_recovers` check the
first complete constructor and recovery. `control_order` certifies its
base-two order eleven. `control_finite_pair_checks` and
`control_finite_endpoint_checks` cover its whole finite cyclic carrier;
`control_any_power_rows_none` consequently proves failure of the original
guarded pair/endpoint detector for **every list of signed powers** of this
fixed base. `control_public_original_none` and
`control_public_weighted_none` include every modulus m in those original
and weighted detector bodies. Reweighting exponents within this base's
same carrier cannot repair that detector. The theorem does not rule out
other bases, period observables, higher correlations or factoring methods.

`balanced_control_public_period` checks the second full public constructor.
It has 176 original packets and 147 representative matches in the native
replay; neither number nor period 29 is supplied as advice. The compiled
`balanced_control_probe_menu_none` proves that all further bases from
3 through 13 still fail at this period. In contrast,
`balanced_control_public_wrapped_recovers` proves the entire cache plus
bounded reconstruction returns 1103, and
`balanced_control_from_public_certificate` discharges every antecedent
of the generic prime-period guarantee on this input.
`recoverPublicSortedWrappedPeriod_eq` proves identical returned results
for the complete sorted constructor; its
`balanced_control_sorted_wrapped_recovers` checks the public sorted
cache and wrap procedure on the same input.
`balanced_control_arithmetic` checks the balanced factor ratio, prime
factors, public modulus and the small-factor-prefix complement 13^2<1103.

There is also an actual balanced unresolved control, not just a generic
empty-list example. `zero_control_public_period` proves the public
base-two cache at N=143=11*13 and m=3 has D=0. Its two consumers return
none for **every** further base menu or wrap budget, by
`zero_control_probes_none` and `zero_control_wrapped_none`.
`zero_control_sorted_wrapped_none` includes the sorted constructor.
`zero_control_arithmetic` checks 3^2<11 and N<=3^6. Other row observables
on this input are not excluded; the period branch is a complementary
source, rather than a full fallback guarantee.

The strict leaf build, ordinary-root import and explicit checker pass.
All 14 namespace linters report zero errors in 104 explicit and 130
generated declarations. The transitive audit checks all 234 declarations,
including 163 theorem/helper declarations, and allows only `propext`,
`Classical.choice` and `Quot.sound`. The ordinary root and semiprime
module-family registration are present. The original association-list
specification can still take quadratic lookup time; its compiled sorted
counterpart avoids that lookup. Neither the sorting bit cost nor a
universal original-packet budget follows from the adjacent scan bound.
Native list storage, integer/ring ledgers and this conditional balanced
reconstruction are not a complete deterministic bit machine.
Universal useful-period/hit acquisition, all row-count/setup/lookup/
polynomial bit costs, arbitrary factor ratios and the requested every-run
guaranteed one-sixth factorization remain **OPEN**.

The [179-pin retained-period replay](semiprime-row-periods-audit.json),
seed 202610033208, freezes the complete 175-pin parent, parent audit,
new module, explicit checker and new native source. All 179 source hashes
are verified after the terminal run. It checks 512 finite signed-power
lists against both an independent full-pair GCD oracle and the original
representative-star oracle: 181 certificates are zero and 331 nonzero.
These oracle checks are native validation, rather than additional Lean
proofs. The kernel equalities above apply to every input list.

The public native source constructs all original powers once, explicitly
merge-sorts complete tags by their cached residues, keeps every original
packet in its sorted equality bucket and extracts adjacent signed
differences. It charges sort comparisons and tag writes separately from
the scan and integer GCDs. It uses no cache hash lookup. Every construction,
power, public probe and candidate check is inside the source timer; the
later private component-order classification and original/weighted
baseline comparisons are separate diagnostic records.

| N-only source | Original powers | Sort value comparisons | Adjacent comparisons | Integer period GCDs | Returned factor | Saved ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| N=2047 | 32 | 126 | 31 | 21 | 23 | 2.10918 |
| N=2304167 | 176 | 1109 | 175 | 147 | 1103 | 13.43113 |
| N=143 | 12 | 28 | 11 | 4 | none | 0.69254 |
| N=369867514421371 | 14968 | 189647 | 14967 | 2 | none | 1772.34431 |

The second positive source needs 22 unsuccessful further-base GCDs
followed by four wrapped-candidate GCDs; label three recovers 1103. The
first source needs one further-base GCD. The two zero-period sources
reach no further probe or reconstruction. In particular, merely counting
global duplicate packets does not show useful period information: the
two retained differences on the older 42-bit control have GCD zero.
The inherited weighted procedure recovers that older input by a different
observable. These saved timings are single native executions, not a
scaling exponent or a formal clock.

There are 32 N-only source calls: eight fixed controls, including a square
and an arbitrary-ratio input, and 24 newly generated small balanced prime
pairs. Five return proper factors: three public period probes, one bounded
wrap reconstruction and one square prefix. Seventeen have zero relation
GCD and ten exhaust their public probes and wrap budget at a nonzero
period multiple. This branch is therefore deliberately recorded as
incomplete. The full every-run factorization guarantee remains **OPEN**.
The larger 108-bit augmented-family reference replay is a separate live
audit branch. Its sources are preserved; this completed 179-pin record
does not assume that pending classification has finished. The new source's
explicit `--include-audit` option can later merge both frozen branches
without changing or replacing either original record.

## Completed larger signed-family reference classification (2026-10-03)

The separate disk-backed run has now finished. Its
[177-pin sorted coverage record](semiprime-augmented-sorted-coverage-audit.json),
seed 202610033207, preserves the original 175-pin branch and the exact
[sorted classifier](../scripts/probe_semiprime_augmented_sorted_coverage.py).
All 177 source hashes match after completion. It checks the classifier
against 544 independent dictionary oracles, including 32 cases with
full-width unsigned 64-bit orders. These are native tests, not Lean proofs.

The four new balanced reference inputs have full base-two component orders
according to the private native reference checks. The nominal band is
108 bits; one actual input has 109 bits. Each scratch record retains both
signed CRT residues with one consistent whole inverse-orbit sign. Two
structured sorts classify the complete original-plus-weighted family,
cross-family pairs, reciprocal signs and raw endpoints.

| Reference N | Actual bits | Public m | Original plus weighted packets | Distinct whole inverse orbits | p aliases | q aliases |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 348013573799314852420340698259159 | 109 | 265231 | 180263412 | 149016418 | 2 | 2 |
| 180153020637494748859816514419367 | 108 | 237673 | 167166360 | 138522627 | 2 | 1 |
| 219807062341433225868190619154631 | 108 | 245671 | 165081180 | 136166447 | 1 | 0 |
| 232213427534885842287051403359599 | 108 | 247939 | 166833780 | 138513044 | 1 | 1 |

All four complete signed unions have useful local aliases. There are no
additional raw plus/minus-one endpoints or local-only self-inverse hits.
No large augmented-family miss was found in this corpus. The actual
component orders and larger primality checks remain private native data;
this is neither a kernel coverage theorem nor a paid public factorization
run. It constructs no public group powers or recovery polynomial and
reports no factorizer runtime. These four successes do not give a
universal collision, row-count or sixth-root bit guarantee.

## Integer companions before the power projection (2026-10-03)

The new [SemiprimeCompanionRows module](../RiemannGaussian/SemiprimeCompanionRows.lean)
retains another observable before exponentiation. For a centered original
row z define its cleared factor-coordinate polynomial

\[
 F_z(Y)=a_zY^2+(mb_z-2a_zj)Y+Nt_z.
\]

For two original rows at the same residue, let
D=t_2a_1-t_1a_2 and B=t_2b_1-t_1b_2. On the actual public primitive
filter D=m*d with d=1 or d=-1. Cancelling before any group map gives

\[
 t_2F_1(Y)-t_1F_2(Y)=md\,Y(Y-c),\qquad c=2j-dB.
\]

`primitive_coordinate_factorization` and
`weighted_coordinate_factorization` prove this integer identity.
The known global root Y=0 is stripped before the root c is projected.
Both signed coefficients, original quadratics and their individual
public centers remain upstream. The weighted centered exponent E obeys

\[
 E=md(1-c),\qquad c=1-d(E/m).
\]

`companion_giant_identity` proves the coefficient/exponent connection.
`PrimitivePacket` checks positive m, abs(D)=m and E modulo m equal to
zero using public integer operations. `primitivePacket_orientation`
and `primitivePacket_exponent` prove what these actual checks supply.
The divisor, local orders, selected pair and group base are absent from
the constructor.

The coefficient connection now applies to the actual complete family.
`weightedResiduePacket_relations` transports both exact original quotient
relations through every Euclidean intermediate row and all four public
center combinations. `centeredPacketRow` forks the retained original
row after its actual shift, and `packetLinearCoefficient` retains their
signed weighted coefficient. `publicPacketCompanion_eq_coefficient`
identifies the executable normalization with that coefficient root for
every filtered public packet. `publicPacket_coordinate_factorization`
then proves the displayed factorization with the actual packet companion.
These are compiled commuting identities, rather than independent generic
coefficient examples.

`publicCompanions` enumerates the complete public weighted packet family
and applies this primitive filter. Only its polynomial fork deduplicates
the resulting residues modulo N; the signed integer list and both
original packet objects remain available. `recoverCompanionRows` first
checks companion zero endpoints, then uses the existing single additive
root polynomial P(Y)=product(Y-c). The compiled
`SemiprimeRowDerivative.rowDerivative_eq_product` gives

\[
 P'(c_i)=\prod_{j\ne i}(c_i-c_j).
\]

Thus one derivative evaluation replaces the off-diagonal additive pair
matrix. Its known diagonal is removed exactly; a locally zero derivative
cannot be discarded merely because its GCD saturates at N. The existing
selected-row recovery retains that case.
`recoverCompanionRows_of_proper_pair` proves complete program recovery
from any proper additive pair in the full public family, and
`recoverCompanionRows_of_endpoint` covers a proper zero endpoint.
`recoverCompanionRows_sound` independently checks every returned divisor.

`publicCompanions_length_le` and `publicCompanionRoots_card_le` bound
companions and distinct roots by twice the complete original packet
count R. `recoverCompanionRows_gcd_bound` gives at most 6R factor-checking
GCD queries: one endpoint and at most two derivative/recovery queries
per distinct root. This does not count construction, sorting or dictionary
lookup, coefficient arithmetic, polynomial bit work or GCD bit cost.
The Lean recovery specification inherits a noncomputable finite-set
interface; it is not a formal native bit-machine refinement.

The complete public program has six kernel-checked positive controls:

| N | Actual bits | Public m | Public companion witness | Compiled recovery theorem |
| --- | ---: | ---: | --- | --- |
| 2047 | 11 | 5 | 66 and 43; difference -23 | `control_public_companions_recovers` |
| 2304167 | 22 | 13 | 2290 and 1187; difference -1103 | `balanced_control_public_companions_recovers` |
| 143 | 8 | 3 | Zero endpoint c=13 | `zero_period_control_public_companions_recovers` |
| 369867514421371 | 49 | 269 | -8584010 and 16407479 | `older_control_public_companions_recovers` |
| 2518766418595894637609 | 72 | 3691 | 185529023096 and -1229252577510 | `derivative_control_public_companions_recovers` |
| 788096216222522769981991129 | 90 | 30403 | 29719657945802267 and 83379602944995 | `larger_control_public_companions_recovers` |

For each pair, the corresponding `*_companions_mem` theorem checks
literal membership in the actual public residue subconstructors and
transports it into the complete family. The `*_companion_difference`
theorem checks a proper GCD of their difference. Neither the selected
residues nor those pairs enter `recoverCompanionRows`. The endpoint
control similarly checks public membership and the complete endpoint
procedure. The larger membership computations use kernel reduction;
the compiler, Python and the reference factor selection are not trusted
proof mechanisms.

The 2047 control exposes information beyond the fixed base-two carrier:
the previously compiled `SemiprimeRowPeriods.control_any_power_rows_none`
excludes the original guarded pair/endpoint detector for every list of
powers of that base on this input. The new additive program succeeds.
At 143, the earlier period consumers fail for every base menu and wrap
budget because their actual retained certificate is zero. The additive
zero endpoint now succeeds. The 72-bit input previously exhausted the
complete ordinary derivative axis in the saved native replay; that whole
negative classification remains native evidence, not a new kernel
failure theorem. The 90-bit control is a full public program success
theorem, but it is not a timed full native source run.

Earlier prose referred to these older controls as "42-bit" and "60-bit".
Their exact N values have 49 and 72 bits. The table corrects those labels,
and the new source records `input_bits` explicitly.

The strict leaf build and strict ordinary root import pass. All 14
namespace linters report zero errors in 49 explicit and 33 generated
declarations. The all-module transitive audit checks all 82 declarations,
including 67 theorem/helper declarations, and permits only `propext`,
`Classical.choice` and `Quot.sound`. The ordinary root and semiprime
module-family registration are present.

The [185-pin companion replay](semiprime-companion-rows-audit.json),
seed 202610033210, freezes the 179-pin period branch, its parent record,
the new module, checker and [native companion source](../scripts/probe_semiprime_companion_rows.py).
It explicitly merges the completed 177-pin sorted reference branch.
All 185 source hashes match after the terminal replay. The independent
native checks verify 109248 cleared coordinate identities for three
integer Y values, 36416 primitive companions and 137 complete public
constructor oracles. These finite oracle tests are not Lean proofs.

Every original coefficient lift, both public centers, weighted primitive
check, exponent division, signed companion, dictionary lookup, zero-endpoint
GCD, root polynomial, derivative evaluation and late recovery is inside
the actual N-only source timer. The source takes only N, has no group
base, and performs zero modular powers or scalar inverses. It retains
all original/weighted packet buckets and each signed integer companion.
One monic root polynomial and its reused evaluation tree suffice after
the endpoint scan. The native packing engine and dictionary lookup remain
unrefined; the operation ledgers are not a formal bit clock.

| Complete N-only source | Original packets R | Companion packets | Distinct roots | Endpoint plus recovery GCD queries | Factor | Saved ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| N=2047 | 32 | 48 | 27 | 29 | 23 | 2.41746 |
| N=2304167 | 176 | 304 | 225 | 233 | 1103 | 18.46539 |
| N=143 | 12 | 16 | 6 | 2 | 13 | 0.73849 |
| N=369867514421371 | 14968 | 28864 | 21366 | 21882 | 24991489 | 2756.91249 |
| N=2518766418595894637609 | 394276 | 773792 | 579420 | 595687 | 64308254573 | 107994.67370 |

The 143 endpoint source does not need a polynomial. The other four table
sources evaluate every derivative before their checked recovery scans.
The 72-bit source performs 579420 endpoint GCDs and 16267 derivative
GCDs. Its native polynomial ledger counts 1086341 convolutions,
96877741 packed coefficients and 1158839 monic reductions. Its integer
ledger counts 9009345 products, 7647820 additions and 3372841 divmods,
with maximum integer operand size 95 bits and operand-bit traffic
1361178399. These figures expose the remaining work after eliminating
group powers; they do not bound it by the requested bit exponent.
The timings are single saved executions and are not a scaling fit or
a statistically paired comparison with earlier power-based baselines.

All 32 small public source calls return proper factors: 19 by the ordinary
derivative GCD, 11 by a zero-companion endpoint, one by the public square
prefix, and one by selected-row recovery after derivative saturation.
The corpus contains the eight fixed controls, including a square and
arbitrary-ratio inputs, plus 24 newly generated small balanced prime
pairs. Both additional larger full sources also return proper factors.
The square-prefix source is separately charged native behavior; this
finite result is not a universal Lean square-inclusive bit bound.

The explicitly separate private 90-bit reference witness search is
reproduced inside the frozen replay. It finds the kernel-checked pair
after 4248991 companion packets and 3151285 distinct whole residues,
using the actual private prime fields only for witness location.
The new companion is 83379602944995 at j=13824; the old one is
29719657945802267 at j=1685. Their difference has proper GCD
24862649616491. Both complete source memberships and the entire public
Lean recovery program are checked by the theorems listed above.
The reference search stops at the witness and is explicitly not a
full native 90-bit constructor/recovery timing or exhaustive failure
classification.

Useful additive hits for every input, a universal original-row budget,
and complete deterministic bit costs for construction, lookup, polynomial
arithmetic and recovery remain **OPEN**. The count bounds, six controls
and larger signed-family reference successes do not imply the requested
every-run sixth-root rate. Arbitrary factor ratios and squares still need
the full acquisition and cost theorem.

## Complete companion exhaustion and the signed source (2026-10-03)

The new [SemiprimeCompanionCoverage module](../RiemannGaussian/SemiprimeCompanionCoverage.lean)
checks a coverage obstruction in the complete ordinary companion program.
The literal control is

    N=7303=67*109, m=5.

`missed_control_arithmetic` proves both primes, the balanced ratio
67<=109<=2*67, N<=5^6 and the small-factor-prefix complement 5^2<67.
The entire public family at this modulus is used. No selected row, factor
or pair is an input to `recoverCompanionRows`.
`missed_control_endpoints` proves every actual root endpoint has GCD one;
`missed_control_pairs` proves every difference between distinct actual
whole-modulus roots also has GCD one. These are bounded finite certificates
checked by kernel reduction, not trusted native computations.
`missed_control_public_none` consequently proves the entire original
program returns none, including the zero-endpoint scan and all derivative
and saturated-output recovery. This refutes universal coverage for that
specified family/modulus. It does not rule out other moduli, additional
observables or an arbitrary factoring algorithm.

The complete exhaustion criterion is now explicit. For the original
whole-modulus companion set S, `endpoints_none_iff` separates a global
zero from an actual unit. `recoverCompanionRows_none_iff` proves

\[
 \text{ordinary program returns none}
 \iff (\forall c\in S,\ c=0\ \text{or}\ c\text{ is a unit})
 \ \text{and}\ \forall c\ne e\in S,\ c-e\text{ is a unit}.
\]

`anchoredRoots` inserts a single public zero into S.
`anchoredRoots_unitSeparated_iff` proves that unit separation of this
larger set is exactly the same endpoint-plus-difference criterion.
`recoverAnchoredCompanions_none_iff` transports it through the actual
derivative/recovery specification. Thus one anchored derivative replaces
both old detector stages with exactly the same complete hit union.
This equality concerns exhaustion/success, not the identity of the first
returned divisor. `recoverAnchoredCompanions_sound` independently certifies
every returned factor. `recoverAnchoredCompanions_gcd_bound` gives at
most 4R+2 recovery GCD queries for R complete original packets, including
selected-row recovery. Its extra zero adds at most one polynomial root.

The further `signedRoots` fork is {0} union S union -S. It retains both
signs before testing local coincidences. `signedRoots_unitSeparated_iff`
and `recoverSignedCompanions_none_iff` prove its exact three-channel
criterion: endpoint zero-or-unit, unit differences between distinct roots,
and unit sums whenever the sum is not globally zero. A whole-modulus
zero sum is an actual signed diagonal and is excluded from the pair
product, rather than treated as a proper factor. Local saturation caused
by several genuine edges still retains the existing selected-row recovery.

`recoverSignedCompanions_of_proper_sum` proves complete recovery from any
proper sum in the original public family. On the failed control,
`missed_control_signed_witness` checks the public memberships of 57 and
77 at residue j=2. Their sum is 134=2*67 with proper GCD 67.
`missed_control_signed_recovers` proves the entire public signed program
returns a proper factor, with neither those residues nor that pair as
algorithm inputs. `recoverSignedCompanions_none_implies_original` and
`recoverSignedCompanions_preserves_success` prove that the extra sign
does not erase any original success. This does not assert identical
returned factors or identical root visitation orders.

`signedRoots_card_le` gives at most 2*card(S)+1 roots, and
`recoverSignedCompanions_gcd_bound` gives at most 8R+2 recovery GCDs.
These are counts of checked recovery queries, not bounds on sorting,
hashing, sign-tag copying, polynomial arithmetic or GCD bit work.
The noncomputable finite-set specification and native packing engine
remain separate from a full deterministic bit machine.

The strict leaf and strict ordinary root pass. All 14 namespace linters
report zero errors in 28 explicit and 15 generated declarations.
The all-module audit checks all 43 declarations, including 38 theorem/
helper declarations, with only `propext`, `Classical.choice` and `Quot.sound`.
Ordinary-root and semiprime module-family registration are present.
The previous 185-pin positive companion replay remains immutable.

The [189-pin coverage replay](semiprime-companion-coverage-audit.json),
seed 202610033212, freezes the previous 185-pin branch, its parent record,
the new module, explicit checker and
[anchored/signed native source](../scripts/probe_semiprime_companion_coverage.py).
All 189 source hashes match after the terminal replay. The finite oracle
compares 160 root lists against independent endpoint and full-pair GCD
unions in both anchored and signed variants. It checks 320 source variants,
including 24 lists with global zero roots and 91 selected-row saturation
recoveries. These are native validation cases, not formal machine proofs.

The complete private small corpus enumerates every prime pair with
11<=p<500 and p<q<=2*p, excluding the squared-public-modulus small-factor
prefix. It contains 3410 balanced inputs. Nine have exhausted ordinary
companion axes:

    7303, 7387, 8633, 11413, 14873, 13843, 93883, 98069, 111047.

All nine have signed local hits. Each is also fed only as N to the actual
old source, anchored source and signed source. All old and anchored calls
return none, and all signed calls return checked proper factors. Only
the complete negative classification at 7303 and its signed recovery
are the new literal Lean theorems; the other eight full failures/successes
remain native exact-arithmetic evidence. The source selects the same
public modulus as its reference classifier on every one of these cases.

A separate seed-202610033212 corpus samples 512 balanced inputs with p
chosen by next-prime rounding in [500,50000), and q by next-prime rounding
between p and 2*p. Every complete ordinary and signed reference axis has
a local hit. Private prime fields are used only for these classifications;
the tests are not unbiased large-input density samples, native factorizer
timings or universal Lean coverage certificates.

The complete native source constructs all original Euclidean coordinates,
both public centers and every weighted companion, then retains each signed
integer and original/weighted packet bucket. It inserts one public zero,
does exact whole-modulus deduplication, builds one signed root polynomial,
reuses its evaluation tree for the derivative and performs checked late
recovery. No endpoint scan, group base, modular powers, scalar inverses or
pair matrix is constructed. Every constructor, sign operation, dictionary
lookup, polynomial step and GCD is inside the N-only source timer.
The dictionary and packed monic backend remain unrefined bit operations.

| N-only control | Ordinary result | Anchored roots/result | Signed roots/result | Signed recovery GCDs | Signed saved ms |
| --- | --- | --- | --- | ---: | ---: |
| 7303 | none | 37 / none | 73 / 67 | 2 | 3.58449 |
| 369867514421371 | 24991489 in previous saved run | not replayed here | 42731 / 14799739 | 78 | 4859.16577 |
| 2518766418595894637609 | 64308254573 in previous saved run | not replayed here | 1158841 / 64308254573 | 32534 | 205492.71531 |

On 7303 the old source constructs 36 distinct ordinary roots; the anchor
adds one and performs all 37 derivative GCDs before returning none.
Its saved ordinary/anchored timings are 2.73572 and 2.62048 ms.
The signed source evaluates all 73 derivatives before its recovery scan.
The different factors on the 49-bit larger input illustrate why hit-union
preservation does not assert equality of the first returned divisor.

The 72-bit signed source retains the same 394276 original packets and
773792 weighted companions as its parent. It performs 1547584 signed
lookup queries, evaluates all 1158841 derivative roots, counts 2172754
convolutions, 206502815 packed coefficients and 2317681 monic reductions.
It needs 32534 recovery GCDs and zero modular powers. Its saved time is
205492.71531 ms; the prior ordinary companion source used 579420 roots,
595687 endpoint-plus-recovery GCDs and 107994.67370 ms. These are separate
saved executions, not a statistically paired benchmark or exponent fit.
The decreased GCD count does not erase the larger polynomial work.

There are 43 complete signed N-only calls: the parent's 32 small inputs,
the nine new ordinary-family misses and both larger controls. All return
proper factors: 36 directly from a derivative, six by selected-row recovery
after saturation, and one by the separately charged native square prefix.
The larger 90-bit control is not replayed through a full native signed
source. The generic compiled success-preservation theorem applies to its
already checked public ordinary recovery, but no new full timing is claimed.

The original universal ordinary-companion coverage claim is now refuted
on its literal specified family/modulus. Universal useful signed hits,
the full original-row bound and deterministic construction-inclusive bit
costs remain **OPEN**. Arbitrary factor ratios, squares and every-run
guaranteed one-sixth factorization retain their full original scope.

## Uniform complete Euclidean row count at the public modulus (2026-10-03)

**PROGRESS; the every-run one-sixth bit guarantee remains OPEN.**
The preceding entries' open original-row-count obligation is now discharged
for the literal prime-modulus constructor. The new ordinary-library module
[SemiprimeEuclidRowBudget](../RiemannGaussian/SemiprimeEuclidRowBudget.lean)
proves `publicPackets_length_le`: for **every N** and every prime m,

\[
 R=\operatorname{length}(\mathrm{publicPackets}(N,m))
 \le 8m(1+\lfloor\log_2 m\rfloor)^2.
\]

This counts the complete existing family: every public unit residue, every
Euclidean current and intermediate vector, and both original centers.
It imposes no factor-ratio, primality, squarefreeness, useful-collision or
unknown-factor premise on N. This is a uniform count theorem, not an
average Euclidean estimate, an empirical scaling fit, or a bit clock.

The source is retained before counting. `EuclidFrame` keeps both remainders,
both denominator weights and the signed orientation at each actual recursive
division. `euclidFrames_expand` proves that expanding these full frames
recovers the unchanged original `euclidPairs` list. The theorem
`euclidPairs_length_eq_frameSum` charges a division quotient q by **q** rows,
including its q-1 intermediate vectors. `publicPackets_length_two_charges`
then proves that the full original packet count is exactly twice the number
of actual charge slots, accounting for both centers.

In a frame with current positive remainder a, current weight t, previous
remainder r and previous weight x, the actual determinant invariant is
r*t+a*x=m. Each positive slot k<=q satisfies a*t*k<=m by
`frame_charge_product`. A charge retains the frame orientation, a, t, k
and the original public residue j. Strictly decreasing remainders and
the retained slot/residue labels prove `publicChargeTags_nodup`; there is
no multiplicity erased by the count projection. The full frame remains
available upstream to reconstruct every intermediate vector and its sign.

The same quadratic information used to construct the rows limits their
number. `residueFrame_square_eq` proves, for the **actual current frame**,

\[
 (\pm a)j^2=Nt\quad\text{in }\mathbb Z/m\mathbb Z.
\]

Because 0<a<m and m is prime, the signed leading coefficient is nonzero
in a field. `squareFiber_card_le` proves that each fixed signed (a,t)
has at most two canonical residue solutions j, even when N is divisible
by m. This congruence applies to the retained current frame used to charge
the full quotient; the proof does not pretend each intermediate vector
has the same coordinates or orientation as that current frame.

The positive triples (a,t,k) with a*t*k<=m have a universal count
`positiveTriples_card_le` of at most m*(1+floor(log2 m))^2. The proof
partitions a and t by their dyadic scales. Each box has volume at most
m (`dyadicBox_card_le`), and there are at most the squared logarithm
many boxes. `allowedCharges_card_le` combines two orientations, two
quadratic residue roots and this triple envelope. The second original
center supplies the final factor two in the stated 8m bound.
The finite triple envelope is a mathematical counting carrier; it is
**never constructed by the paid native row algorithm**.

Public modulus acquisition is also linked to the actual scale rather
than left as a prime input. `publicPrimeAtLeast` is the least-prime search
at or above a positive public B. Its primality, minimality and doubled-window
bound are proved, using Mathlib's kernel-checked Bertrand theorem.
`publicRowModulus` uses the existing literal ceiling-sixth-root
`SemiprimeLehmanCoverage.sixthWidth N`. For positive N,
`publicRowModulus_bounds` proves B<=m<=2B, and
`publicPackets_publicRowModulus_length_le` proves

\[
 R\le 16B(1+\lfloor\log_2(2B)\rfloor)^2,
 \qquad B=\lceil N^{1/6}\rceil.
\]

This proves the row-count envelope at the N-only public modulus. It does
not price least-prime acquisition or assert that the native trial-division
search already has the required bit bound.

The count transfers to the completed companion pipeline through named
compiled corollaries. With L=1+floor(log2 m),
`publicCompanions_length_prime_le` and
`publicCompanionRoots_card_prime_le` bound the complete companion list
and distinct ordinary roots by 16mL^2. `signedCompanionRoots_card_le`
bounds signed roots including zero by 32mL^2+1. The three
`recoverCompanionRows_gcd_prime_bound`,
`recoverAnchoredCompanions_gcd_prime_bound` and
`recoverSignedCompanions_gcd_prime_bound` bound their actual recovery
GCD-query counts by 48mL^2, 32mL^2+2 and 64mL^2+2 respectively.
These query envelopes include selected-row recovery after saturation;
they are not polynomial or integer bit-operation bounds.

Strict targeted build, strict leaf elaboration, strict root elaboration,
all 14 namespace linters and the explicit all-declaration transitive
axiom audit passed. The new module has 73 explicit and 67 generated
declarations, 140 in total, including 100 theorem/helper declarations.
Every audited dependency uses only propext, Classical.choice and
Quot.sound. The leaf is registered in the ordinary root and the
explorer's semiprime family. There was no broad CI run, generated
explorer refresh, commit or push.

The [193-pin replay](semiprime-euclid-row-budget-audit.json), seed
202610033214, preserves every source in the frozen 189-pin parent and
adds that parent record, the new leaf, its checker and its replay script.
All 193 hashes were verified after the replay finished. Native finite
correspondence checks cover 585 complete frame cases, 90011 division
frames, 372162 full quotient slots and 45010 actual quadratic fibers.
They include N=0, inputs divisible by m and quotients up to 97; all
expanded vector lists match the frozen original constructor exactly.
A separate complete small-prime oracle checks 29552 quadratic fibers.
The modulus-8 control has four roots for -2*j^2=3*2, so the two-root
argument is explicitly kept within its prime-modulus scope.
There are also 133 specified triple-envelope cases with 162247 triples
and 719 public selector/rounding cases. These finite checks are not
substitutes for the generic compiled theorems.

The replay makes 47 N-only calls to the **full original constructor**,
including four additional squares, the parent's controls and all nine
ordinary companion misses. No square or factor prefix skips its rows
in this count audit. The source timer includes public prime selection,
all public inverses, every original Euclidean quotient, all intermediate
vectors, coefficient lifting, both centers and retention of the complete
original packet list. Public scale checks and packet digests are replay
metadata computed after that constructor timer.

| N-only constructor | Actual input bits | Public B / m | Complete original packets R | Proved prime-m bound | Saved constructor ms |
| --- | ---: | --- | ---: | ---: | ---: |
| 369867514421371 | 49 | 268 / 269 | 14968 | 174312 | 522.03675 |
| 2518766418595894637609 | 72 | 3689 / 3691 | 394276 | 4252032 | 13947.74042 |

The 72-bit original constructor records 197138 vectors, 27338 full
Euclidean divisions, 5140384 integer products, 5326444 additions,
1051465 divmods, 3690 public inverses and maximum 93-bit integer
operands/results. Its operand-bit traffic is 671981187. No pair
matrix, giant-power array, companion polynomial or triple envelope is
built by this constructor-only replay. These saved times and ledgers
price a particular native construction stage; they are not complete
factorization timings or a formal refinement to bit operations.

The uniform **original-row count is PROVED** for the actual prime-modulus
family. Universal useful signed companion hits, deterministic prime
acquisition at the required bit price, full constructor arithmetic,
polynomial construction/evaluation and recovery bit refinement remain
**OPEN**. The count theorem includes arbitrary N, ratios and squares,
but the full guaranteed factorizer still must handle their recovery and
costs. The active goal retains its deterministic, every-run, N-only,
construction-inclusive one-sixth bit-operation scope.

## Shared ordinary polynomial for all signed companion channels (2026-10-03)

**PROGRESS; universal useful hits and the complete bit guarantee remain OPEN.**
[SemiprimeReflectedCompanions](../RiemannGaussian/SemiprimeReflectedCompanions.lean)
proves `recoverReflectedRows_none_iff_signed`: the compressed source
exhausts **exactly when** the full signed source exhausts, for every
positive modulus and every ordinary distinct root set S. The theorem
includes endpoints, ordinary differences, nonzero sums, exact global
negative matches, repeated product factors, prime powers and saturated
recovery. It imposes no prime-field, distinct-factor or generic-position
premise. No new useful hit is asserted by this compression.

Keep the complete original integer companions and ordinary residues
upstream. For P(X)=prod(c in S)(X-c), a retained ordinary root c uses

\[
 V(c)=e(c)P'(c)
 \begin{cases}
 P'(-c),&-c\in S,\\
 P(-c),&-c\notin S,
 \end{cases}
 \qquad
 e(c)=\begin{cases}1,&c=0,\\c,&c\ne0.\end{cases}
\]

The compiled `reflectedColumn_eq_cached` proves this exact formula for
the program's `reflectedColumn`. `reflectedPolynomial_eval` and
`reflectedPolynomial_coeff` prove that P(-c) is obtained by evaluating
the coefficient vector P(-X) at the **same ordinary roots**: only the
odd coefficient signs change. At an exact global negative match,
the already computed ordinary derivative at -c supplies the deflated
value. No extra reflected derivative stream is required.
`ordinaryPolynomial_natDegree` and `reflectedPolynomial_natDegree`
prove both polynomials have degree exactly |S| in a nontrivial ring.
The full signed-root polynomial of degree up to 2|S|+1 is absent from
this construction. One ordinary root tree supplies two evaluation
streams, the ordinary derivative and coefficient-reflected polynomial.

The endpoint guard is essential. A whole-modulus zero is excluded as
a useful endpoint; every other endpoint remains. The reflected product
excludes x=-c when that equality holds modulo the whole input, so an
exact global zero sum does not create a false factor signal. It still
retains nonzero sums, including the self-sum 2c whenever this is globally
nonzero. All signs and original integer/weighted packets remain upstream.

`reflectedColumn_isUnit_iff` proves that V(c) is a unit exactly when
its guarded endpoint, every original off-diagonal difference, and
every globally nonzero sum are units. Combining those complete tests
over c in S gives the precise full signed-family exhaustion criterion.
The compressed product can contain repeated factors when the ordinary
set already contains both signs. Accordingly, **hit unions**, rather
than equal column GCDs or equal first returned divisors, are preserved.
In particular, prime-power valuations may change between the two
observables without changing whether a proper factor is recoverable.

Recovery retains separate leaf channels: one guarded endpoint,
the ordinary differences c-x with x!=c, and reflected differences
(-c)-x with x!=-c. `reflectedColumn_val_eq` proves that their canonical
residue product is exactly the polynomial observable modulo N;
`reflectedColumn_gcd_eq` transports this equality through the GCD.
`reflectedLeaves_bounds` proves every surviving leaf lies strictly
between zero and N. A full-modulus column therefore triggers one lazy
scan with a proper-factor leaf; no complete pair matrix is constructed.
`recoverReflectedRows_sound` proves all returned divisors proper.

`recoverReflectedRows_gcd_bound` proves at most 3|S|+1 recovery GCDs,
one per ordinary column plus at most one scan of 2|S|+1 leaves.
`recoverReflectedCompanions_gcd_bound` transfers this to 6R+1 in the
complete original row count, improving the full signed source's
previous 8R+2 envelope. The compiled prime-modulus corollary
`recoverReflectedCompanions_gcd_prime_bound` gives 48mL^2+1,
where L=1+floor(log2 m). Construction, dictionary, polynomial and
integer bit prices are not part of these GCD-query bounds.

The end-to-end success transport is compiled as
`recoverReflectedCompanions_preserves_signed_success`. The literal
public 7303 source, and the earlier 72-bit and 90-bit public recovery
theorems, now yield `missed_control_reflected_recovers`,
`derivative_control_reflected_recovers` and
`larger_control_reflected_recovers`. Neither private factor is supplied
to these public programs. `global_negative_control_none` checks that
S={1,34} modulo 35 gives no false hit despite its exact global negative
matches. `square_saturation_control_recovers` checks saturated recovery
on S={0,7} modulo 49, preserving both the zero guard and prime-square
scope. The full native 90-bit source is not measured by these kernel
success transports.

Strict targeted build, strict leaf and root elaboration, all 14 namespace
linters and the explicit transitive audit of every declaration passed.
There are 37 explicit and 15 generated declarations, 52 in total,
including 45 theorem/helper declarations. Dependencies use only
propext, Classical.choice and Quot.sound. The leaf is registered in
the ordinary root and explorer's semiprime family. No broader CI,
explorer regeneration, commit or push was performed.

The completed [197-pin replay](semiprime-reflected-companions-audit.json),
seed 202610033216, preserves the entire 193-pin parent and adds its
record plus the new leaf, checker and probe. All 197 hashes were
verified after its original native process finished. Finite exact
oracles cover 853 axes, including every subset modulo 4, 6 and 9,
680 axes with global negative matches, 357 with zero, 585 saturated
selected-row recoveries and 68 exhausted axes. Every combined column
matches its separate endpoint/difference/reflection product exactly,
and success/failure matches the complete signed hit union. These
finite checks supplement the generic kernel theorem.

All 43 N-only native sources in the inherited corpus recover proper
factors: 40 directly from a combined column, two by selected-row
saturation recovery and one by the charged square prefix. They
retain exactly the parent's complete original and companion packet
counts. The native timer includes public modulus selection, original
rows, both centers, integer companions, ordinary dictionary lookups,
coefficient reflection, derivative caching, two evaluations on one
ordinary tree, combined scalar products and checked recovery. There
is no constructed signed-root union, pair matrix, group base,
giant-power array or scalar modular inverse.

| N-only control | Saved signed degree | New ordinary degree | Saved signed recovery GCDs | New recovery GCDs | New saved ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| 7303 | 73 | 36 | 2 | 1 | 3.14974 |
| 369867514421371 | 42731 | 21366 | 78 | 39 | 4356.21864 |
| 2518766418595894637609 | 1158841 | 579420 | 32534 | 16267 | 181644.04671 |

The corresponding older saved signed times were 3.58449, 4859.16577
and 205492.71531 ms. These are separate saved executions, not paired
benchmarks or a scaling-exponent fit. The new 72-bit run retains all
394276 originals and 773792 companions, uses 773792 ordinary
companion lookups, inserts 579420 cached derivatives and makes
579420 negative-target lookup queries. It builds one degree-579420
polynomial and visits 2317678 evaluation nodes over two streams.
Its 1593265 convolutions and 181761052 packed coefficients compare
with 2172754 and 206502815 in the saved full signed run. Monic
reductions are nearly unchanged: 2317678 versus 2317681.

The saving in degree and recovery queries does not halve all work.
The combined values need 1738260 native scalar products/reductions,
and the new cache/reflection instrumentation records integer
operand-bit traffic of 1603165506, compared with 1461085658 in
the previous signed run. Integer construction records 9009345
products, 8516950 additions, 4241971 divmods and maximum 95-bit
integer operands/results; scalar products reach 143 bits before
reduction. The exact native dictionaries and packed backend remain
unrefined bit operations. No complete bit-clock claim is inferred
from the lower polynomial degree, saved runtime or recovery count.

The complete signed information now fits in one ordinary polynomial
and one ordinary evaluation tree. The previously proved uniform
original-row envelope remains intact. The unresolved arithmetic
requirement is still a **universal useful signed hit** for the actual
N-only family; preserving its exact hit union cannot supply that
premise. Efficient priced prime acquisition, full construction,
polynomial and recovery bit refinement, arbitrary-ratio handling
and every-run deterministic construction-inclusive one-sixth
factorization remain **OPEN** under the original goal scope.

## Public proper-product sieve and Boolean ordering primitive (2026-10-03)

**PROGRESS; full acquisition pricing and the one-sixth guarantee remain OPEN.**
[SemiprimePrimeSieve](../RiemannGaussian/SemiprimePrimeSieve.lean)
proves `publicSievePrime_eq_least`: a bounded, public proper-product
sieve returns exactly the preceding least prime at or above B, for
every positive B. `sievedRowModulus_eq` applies this to the literal
N-only row modulus with B=max(1,ceil(N^(1/6))). The compiled
`sieved_publicPackets_eq` preserves the complete original packet list,
including every intermediate vector, both centers, signs and
multiplicities. `recoverSievedCompanions_eq` preserves the entire shared
companion recovery program at that public modulus. Acquisition changes
neither the signed cancellation identity nor its useful-hit union.

The rich event carrier consists of ordered factor pairs (d,k) with
d>=2, k>=2 and d*k<=X, where X=2B. `properPairs_mem_iff` proves
this exact membership characterization, and `properPairs_nodup`
preserves distinct factor tags even when their products coincide.
The actual constructor uses quotient-length inner lists,
k=2,...,floor(X/d), rather than an X by X pair rectangle.
`properPairs_length_le` proves at most X*(log2(X)+1)^2 events.
Its mathematical positive-triple envelope is a counting argument,
not an object generated by the source algorithm.

Sorted factor witnesses remain upstream of their scalar product view.
`eventValues_mem_iff` proves that every candidate n>=2 is marked
exactly when n<=X and n is composite. `sortedValues_perm` and
`sortedValues_ordered` preserve the marked products and establish
their order. The literal `firstGap` recurrence then skips products
below the candidate, advances the candidate on equality, and returns
it when the next product is larger. Repeated products are retained
and safely skipped after the first equality advances the candidate.
`firstGap_eq_gapSpec` proves that this merge returns exactly the
first missing candidate in the complete interval specification.
Primality and leastness follow from the exact composite-marking
theorem and the existing public doubled-window prime bound; no
private factor or candidate primality advice enters the constructor.

For positive B, `publicSieve_counts` proves the actual event count
and scan-invocation bounds

\[
 E\le 2B(\log_2(2B)+1)^2,\qquad
 I\le 2B(\log_2(2B)+1)^2+2B+2.
\]

Here log2 is the natural-number floor logarithm, and invocations
include the terminal merge guard. These are event and recurrence
counts, not complete construction or sorting bit clocks. Empty
quotient rows, arithmetic, sorting control, word construction and
the sixth-root computation still require their own bit prices.

The new `ProductComparison` retains both actual Boolean product
reports and the complete Boolean subtraction, including its final
borrow, before projecting the ordering predicate. `compareProductBits`
computes a*b<=c*d by negating the borrow of (c*d)-(a*b), using the
existing multiplication and subtraction bit circuits. There is no
natural-value product or ordering oracle in this predicate's data
path. `compareProductBits_correct` proves its exact numeric meaning.
`compareProductBits_cost` proves primitive clock at most
72*(L+1)^2 when each of the four physical input words has length
at most L. The clock includes the final NOT gate and output cell.
Word encoding and the sorting algorithm are separate obligations;
the native sort below still uses integer comparisons, rather than
this Boolean circuit. No complete bit refinement is inferred from
the existence of the priced comparison component.

`recoverSievedCompanions_sound` proves returned divisors proper.
`control_sieved_modulus` proves that the literal 7303 modulus is 5,
and `control_sieved_recovers` transports the preceding complete
signed repair through the new selector. These are compiled generic
selector and recovery transports, not compiler-trusting execution
certificates for the sieve.

Strict targeted build, strict leaf and root elaboration, all 14
namespace linters and the explicit transitive audit of every module
declaration passed. The checker reports 42 explicit and 87 generated
declarations, 129 in total, with 95 theorem/helper declarations.
Only propext, Classical.choice and Quot.sound occur transitively.
The leaf is registered in the ordinary root and explorer's semiprime
module family. No broad CI, explorer regeneration, commit or push
was performed.

The completed [201-pin replay](semiprime-prime-sieve-audit.json),
seed 202610033218, preserves the entire 197-pin parent and adds
that record plus the new leaf, checker and probe. All 201 hashes
were independently verified after the original native process
terminated successfully. Finite oracles check 70 complete product
windows, 13359 retained factor-pair witnesses, 4093 composite
classifications, 20790 exhaustive small duplicate scan cases and
490 additional sieve scans. The separate Boolean comparator checks
1552 quadruples, including every quadruple in {0,...,5}^4, 256 padded
word inputs and 180 equal-product cases. Its largest physical word
has 28 bits and its largest recorded primitive clock is 7010.
There are 129 complete small public-bound selector checks and 243
sixth-power/neighbor rounding checks. These are native finite checks
supplementing the compiled theorems.

All 47 inherited N-only constructor inputs acquire exactly their
previous public moduli. An additional 90-bit input replays acquisition
only. The native source times the public sixth-root call and rounding,
every quotient row, all proper-product witnesses, stable sorting,
scalar projection and the final merge. Every sorting comparison
recomputes and charges both products; all factor tags and product
multiplicities are retained. Array reads/writes and sorting passes
are native diagnostics, with no implicit random-access bit-machine
credit. Reference primality and full pair rectangles occur only in
the separate finite oracles or checks outside source timers.

| N-only setup | Input bits | Public B / m | Complete product events | Scan invocations | Saved acquisition ms | Complete original packets / saved total ms |
| --- | ---: | --- | ---: | ---: | ---: | --- |
| 369867514421371 | 49 | 268 / 269 | 2384 | 1008 | 130.74982 | 14968 / 667.62801 |
| 2518766418595894637609 | 72 | 3689 / 3691 | 52094 | 23508 | 3679.45350 | 394276 / 17616.32702 |
| 788096216222522769981991129 | 90 | 30393 / 30403 | 557391 | 257732 | 47630.81299 | acquisition only |

The complete 49-bit and 72-bit original constructor replays match
the frozen packet digests exactly. Their source timers include the
new selector and every original intermediate vector, both centers
and public inverses. The companion polynomial and recovery stages
are preserved by the compiled modulus equality and were not retimed
in this acquisition audit. The 90-bit row/companion factorizer was
not replayed. These times are separate saved executions, not paired
benchmarks or a scaling-exponent fit. The new setup performs more
native work than the earlier trial-search setup on these controls;
no measured speedup is claimed.

For the 72-bit setup, 16 sort passes perform 653383 product
comparisons, 1486887 pair reads and 833504 pair writes. The setup
ledger records 1358883 integer products, 736368 additions, 7377
divmods and operand-bit traffic 47915258. Including the complete
original constructor gives 6499194 integer products, 6062745
additions, 1058776 divmods, 3690 public inverses and operand-bit
traffic 719893935, with maximum 93-bit operands/results. The 90-bit
setup alone uses 20 passes and 8777308 product comparisons; its
integer operand-bit traffic is 775981088. None of these diagnostic
integer ledgers is a formal bit clock.

The exact public selector and uniformly bounded event/scan counts
are now compiled, together with a priced Boolean ordering primitive.
A proof connecting a charged sort, control, word materialization
and public root acquisition to the full setup bit clock remains
**OPEN**. Universal useful signed hits, full original construction,
polynomial and recovery bit refinement, arbitrary-ratio recovery
and deterministic every-run construction-inclusive one-sixth
factorization retain their original **OPEN** scope.

## Boolean witness sort with charged payload copies (2026-10-03)

**PROGRESS; full prime acquisition and guaranteed one-sixth factorization
remain OPEN.**
[SemiprimeBitProductSort](../RiemannGaussian/SemiprimeBitProductSort.lean)
proves `sortWords_perm`, `sortWords_ordered` and `sortWords_bounds`
for the actual balanced structural sort. The output preserves every
complete factor-word pair and input occurrence, including high-zero
padding, repeated pairs and different factor pairs with equal products.
Ordering decisions use the preceding proved Boolean multiplication and
subtraction comparator. No natural-value multiplication, ordering
oracle or array index selects a row in the sort data path.

The source carries both physical factor words before decoding their
natural values. `fitBits_self` and `copyPair_row` prove exact word
preservation, including padding. Each payload transfer uses the existing
Boolean copy routine; its reads, writes and tests are counted again on
every transfer. `PairCopy` retains both full primitive copy reports before
projecting the copied pair. The actual merge copies every selected row
and its whole remaining tail. Singleton sort outputs and both alternating
halves are copied too. The declared clocks additionally charge each
factor-pair constructor, list-pattern visit, comparison flag test and
output cons cell specified in the definitions.

`mergeWords_rows` transports the whole copied word output to the standard
merge. `mergeWords_cost` bounds its declared primitive/list clock by
80*(L+1)^2*(n_left+n_right)+3 when every factor word has physical
length at most L. `splitWords_lengths` proves the alternating halves
have exactly ceil(n/2) and floor(n/2) rows. `splitWords_perm` preserves
all factor tags, and `splitWords_cost` bounds the distribution clock
by 12*(L+1)*n+2. Termination lengths are proof data; the recursive
algorithm chooses branches by list structure and Boolean flags.

The compiled `sortWords_bounds_depth` combines those actual subreports
at balanced depth. Its public corollary `sortWords_bounds` proves

\[
 C\le n\lceil\log_2 n\rceil,\qquad
 T\le100(L+1)^2n(\lceil\log_2 n\rceil+1)+1.
\]

Here n is the actual input row count, C counts Boolean comparator calls,
and T is the declared Boolean-gate/payload/list clock. The empty sort
pays its terminal test. All padding contributes to L and every copy
or arithmetic primitive that visits it. The rank n<=2^depth occurs
only in the proof; no depth or sortedness advice enters the algorithm.
These clocks do not yet constitute a complete machine, memory-address,
allocation or report-instrumentation refinement.

The actual event interface is explicit: `wordEvents X` maps every
literal proper pair (d,k) to its two canonical natural bit words.
`bitValue_natBits` and `wordEvents_decoded` prove exact factor-tag
decoding. `wordEvents_bounded` discharges the physical width bound
L=clog2(X+1) for every actual event; that bound is not an assumed
source property. Creating these canonical input words remains an
unpriced interface before the proved sorting stage.

`properPairs_clog_length_le` proves clog2(E)<=3L at the actual event
count E. With Q=log2(X)+1, the compiled `wordEvents_sort_bounds`
therefore gives the complete actual event-sort envelopes

\[
 C\le3XQ^2L,\qquad
 T\le100(L+1)^2XQ^2(3L+1)+1.
\]

The floor and ceiling natural logarithms are exactly those in the Lean
statements. Their count envelope and auxiliary cube inequality are
proof carriers, not generated source lists or paid oracle operations.

`sortedWordValues_eq` proves that the **entire** sorted product list
equals the preceding public sieve list, with every product multiplicity.
Tie order between different factor witnesses can change under the
alternating split, while whole-word permutation remains proved. Only
the downstream scalar list is asserted equal. `wordSortSievePrime_eq`
preserves the previous public prime selector. Its N-only corollary
`wordSortedRowModulus_eq` and `wordSorted_publicPackets_eq` preserve
the original modulus and complete centered row list for every N.
`recoverWordSortedCompanions_eq` preserves the whole shared companion
program, and `recoverWordSortedCompanions_sound` preserves proper
returned divisors. No new signed useful hit is claimed by this transport.
The scalar product projection and gap scan remain ordinary mathematical
components after the priced word sorter, with their Boolean bit prices
still open.

Strict targeted build, strict leaf and ordinary-root elaboration, all
14 namespace linters and the all-declaration transitive audit passed.
The checker reports 74 explicit and 120 generated declarations,
194 in total, including 118 theorem/helper declarations. Only propext,
Classical.choice and Quot.sound occur transitively. The leaf is registered
in the ordinary root and explorer's semiprime module family. No broader
CI, explorer regeneration, commit or push was performed.

The completed [205-pin replay](semiprime-bit-product-sort-audit.json),
seed 202610033220, preserves all 201 parent sources and adds that
record plus the new leaf, checker and probe. Its original process
terminated successfully; every hash was independently verified afterward.
Finite checks cover every word list of length zero through four over
the six-pair alphabet {(0,3),(2,3),(3,2),(1,6),(3,1),(2,2)}, giving
1555 exhaustive lists, plus 256 random padded lists. These include
empty lists, zero products, identical pairs and distinct equal-product
factor witnesses. They check exact word-pair multiplicity, full product
order, actual comparator counts and an independent sum of every declared
clock category. The maximum tested physical word width is 20 bits;
the largest word-list clock is 228302. The word-list oracles execute
19343 comparisons and 67865 complete factor-pair copies.

Separate public-event checks cover 37 complete windows, X=0,...,32
and 97,193,257,511. All 4836 retained events match the earlier sorted
scalar view and satisfy both uniform source bounds. These oracles
execute 40362 Boolean comparisons and total declared sorting clock
20922174. The largest window clock is 12839897. Native finite checks
supplement the generic compiled proof; they are not universal coverage.

Every inherited N-only setup input through 49 bits is replayed, 46 in
total. Each has the frozen modulus, full product-event count and exact
first-gap invocation count. The native source uses linked witness lists
and calls the actual Boolean multiplication/subtraction circuit at every
sorting comparison. The complete root call, rounding, proper-pair
enumeration, word encoding, sorting, scalar projection and gap scan are
inside its setup timer. Ordinary root/event/encoding/projection/scan
integer ledgers remain separate from the proved supplied-word sort clock.
Independent result checks, library sorting, primality checks and final
digest verification occur in oracles outside source timers.

| N-only setup | Public B / m | Complete events | Boolean comparisons | Declared sort clock | Saved sort / acquisition ms | Original packets / saved total ms |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 7303 | 5 / 5 | 8 | 13 | 3255 | 0.48616 / 0.63185 | setup only |
| 369867514421371 | 268 / 269 | 2384 | 23757 | 13813105 | 1424.68214 / 1456.39223 | 14968 / 1970.77563 |

The 49-bit complete original constructor preserves the frozen packet
digest exactly, including all 7484 intermediate vectors, both centers
and 268 public inverses. The word sort makes 56176 complete pair
copies, uses at most nine-bit physical input factors and has balanced
depth 12. Its primitive reports total 5772262 gates, 2177192 input
bit reads, 1671952 bit writes and 3898517 primitive tests. The remaining
clock categories are 47514 comparison NOT/output units, 56176 pair
constructor units and 189492 declared structural list units. Their
sum is exactly 13813105. The public width bound is L=10, giving the
looser proved uniform source clock envelope 20105360001. No timing
or clock is inferred from this envelope alone.

Compared with the saved 201-pin integer sort, the structural Boolean
sort has a different tie schedule and actually performs 23757 versus
22251 product comparisons on this input. Its larger saved native time
is not a measured speedup or an exponent fit. The 72-bit and 90-bit
Boolean setup sources, companion polynomial and factor recovery were
not replayed in this audit. Their source-level equality transports
remain generic compiled theorems, without new native runtime claims.

The declared word-input sorting clock and its actual-event width/count
connection are now **PROVED**. Public root acquisition, proper-event
generation, encoding, the gap scan and complete machine/memory pricing
remain **OPEN** setup obligations. Universal useful signed hits, full
original-row arithmetic, polynomial/recovery bit refinement and
arbitrary-ratio recovery also remain **OPEN**. The active objective
retains every-run deterministic, N-only, construction-inclusive
one-sixth bit factorization, including squares and arbitrary ratios.

## Boolean product construction and least-prime scan (2026-10-03)

**PROGRESS; complete prime acquisition and guaranteed one-sixth factorization
remain OPEN.**
[SemiprimeBitPrimeScan](../RiemannGaussian/SemiprimeBitPrimeScan.lean)
proves `runWordSieve_correct`, `runWordSieve_cost`,
`publicWordSieve_some` and `publicWordSieve_cost`. The actual supplied-word
backend now sorts the complete factor-word witnesses, constructs every
product through Boolean multiplication, and scans for the first missing
candidate using Boolean arithmetic. The preceding scalar product projection
and natural-number gap countdown are removed from this backend's data path.

`WordOrder` retains the complete subtraction and nonzero-scan reports before
its flags. `orderWords_less` and `orderWords_equal` prove exact comparison and
equality, including physically padded words and underflow. Equality uses the
borrow flag and the full difference word; two NOT gates, an AND gate and an
output cell contribute four declared clock units. `orderWords_cost` proves
the full declared comparison clock at most 15W+7 for input widths at most W.

`buildProducts_values`, `buildProducts_length` and `buildProducts_width`
preserve the entire product list, its occurrences and its actual word-width
bound. Every event has a full multiplication report, retained upstream of
the gap result. `buildProducts_cost` proves the declared multiplication/list
clock at most (24(L+1)^2+3)E+1 for E supplied pairs whose factor words have
width at most L. No product is deduplicated.

`scanWordGaps_correct` identifies the actual optional word result with the
preceding `firstGap` result for **every** input product stream, even before
assuming sortedness. The scan first subtracts the candidate from the public
upper limit. On each remaining product it performs the retained word
comparison, copies a missing candidate, or increments an equal candidate
through Boolean addition. `fittedIncrement_value` discharges the no-overflow
condition for its limit-plus-one-bit template. A successful zero-valued word
is distinct from an exhausted window. Every recursive step consumes one
product occurrence; no scalar countdown chooses a branch.

`scanWordGaps_bounds` proves at most E+1 invocations and clock at most
(E+1)(100(L+1)+24), when the limit width is at most L, the candidate width
at most L+1 and every product width at most 3L. Combining all three actual
stage reports, `runWordSieve_cost` proves

\[
 T\le272(L+1)^2(E+1)(\lceil\log_2 E\rceil+1).
\]

`SieveWords` keeps the original candidate and limit words, the full sorted
factor-word report, all product reports and the gap report before the
downstream natural modulus view. Clock arithmetic is instrumentation. The
declared clock charges the existing Boolean primitive reports plus the
specified payload, list, flag and output cells. Complete machine, address,
allocation and report-instrumentation refinement remains **OPEN**.

For the literal public family, put X=2*max(1,B), L=clog2(X+1) and
Q=log2(X)+1. `publicWordSieve_cost` discharges the actual physical-word and
event-count premises and proves

\[
 T\le272(L+1)^2(XQ^2+1)(3L+1).
\]

`firstGap_some_least`, `publicWordSieve_some` and `publicWordSieve_word`
prove that every positive B produces an actual successful word encoding the
literal least public prime at least B, before any default projection.
`wordScanRowModulus_eq`, `wordScan_publicPackets_eq` and
`recoverWordScannedCompanions_eq` preserve the preceding N-only modulus,
entire centered row list and shared companion recovery program for every N.
`recoverWordScannedCompanions_sound` preserves proper returned divisors.
These transports do not establish new useful companion hits.

Strict targeted build, strict leaf and ordinary-root elaboration, all 14
namespace linters and the transitive audit of every module declaration
passed. The new leaf has 61 explicit and 121 generated declarations,
182 total, including 102 theorem/helper declarations. Only propext,
Classical.choice and Quot.sound occur transitively. The module is registered
in the ordinary root and the explorer's semiprime family. Broader CI,
explorer generation, commits and pushes were not run.

The completed [209-pin replay](semiprime-bit-prime-scan-audit.json), seed
202610033222, records an **explicit source-version reconciliation**.
`SemiprimeGeometricRows.lean` changed externally during this slice, from the
historical parent digest
`f2f1d189e922123f2cd266f7818dbaa1ba3a09c49f30a0a3f1f1bf11f66f37d0`
to
`1cb0d7217b18fc2b6f6ef58cf05fbeb1faeaeab730825a11b22c6f3bff0477f3`.
This task did not edit that source. Its current version passed fresh strict
elaboration, root import, all 14 namespace linters and a transitive audit of
all 17 declarations, including 16 theorem/helper declarations. The other
204 parent source pins match exactly; the historical 205-pin manifest
remains unchanged. The new record pins the current source and adds the
parent record, new leaf, checker and probe. It is not an unchanged replay
of the historical snapshot. The original replay process terminated
successfully, and all 209 current hashes were independently verified afterward.

Finite scan oracles cover all sorted product multisets of length zero
through four over 0,...,6, with candidate and upper limit each ranging
over 0,...,8: 26730 cases. These include 12980 exhausted windows and 1890
successful zero-valued results, execute 6446 Boolean increments, and sum
to scan clock 4472394. A further 256 arbitrary padded streams check exact
agreement with the original recurrence without a sortedness assumption.
Prepared product reports in these scan-only oracles are input fixtures,
not a product-construction benchmark.

The complete sort/product/scan backend is also checked on 256 random padded
word-pair lists and on all 69 public bounds B=0,...,64 and 97,127,193,257.
All 16226 events in those complete public windows are retained; every
modulus is the least public prime and all declared backend bounds hold.
The random backends total clock 9939632, with maximum 119937. These finite
oracles supplement the generic compiled theorems.

All 46 inherited N-only setups through 49 bits preserve the exact modulus,
event count, scan invocation count and preceding Boolean sorting clock.
The source timer includes the integer root and its rounding, proper-pair
generation, word encoding, all three Boolean stages and a final decoding
interface. Root, generation and encoding remain unpriced by the proved
backend clock. Independent scalar sorting, result/primality checks,
clock verification and final packet digests occur outside source timers.

| N-only setup | B / m | Events / scan invocations | Sort / products / scan clocks | Complete backend clock | Saved backend / acquisition ms | Original packets / saved total ms |
| --- | --- | --- | --- | ---: | --- | --- |
| 7303 | 5 / 5 | 8 / 2 | 3255 / 425 / 223 | 3908 | 0.57241 / 0.69624 | setup only |
| 369867514421371 | 268 / 269 | 2384 / 1008 | 13813105 / 447651 / 267928 | 14528689 | 1644.73704 / 1662.13003 | 14968 / 2206.11428 |

Five carrier/output units complete each displayed backend sum. The 49-bit
constructor preserves the frozen full packet digest, including every
intermediate vector and both centers. Its backend primitive reports total
6123478 gates, 2276046 input reads, 1738838 writes and 4056058 tests.
Additional charged categories total 334269, giving exactly 14528689.
The least-prime output is physically padded to 11 bits after its increment;
the proved candidate-width allowance includes this padding. Its public
uniform backend envelope is 54687599472, using L=10. The separate integer
prefix/interface ledger records only seven integer products, 2920 additions
and 535 divmods; its operand-bit traffic is 108438. These diagnostics are
not a full bit certificate, a measured speedup or an exponent fit.

The 72-bit and 90-bit Boolean setups, companion polynomials and factor
recovery were not replayed here. The actual Boolean supplied-word backend
and its public width/count connection are now **PROVED** in the declared
model. Root acquisition, complete event generation/encoding and machine
refinement remain **OPEN**. Universal useful signed hits, full original-row
arithmetic, polynomial/recovery bit refinement and arbitrary-ratio recovery
remain **OPEN**. The active target retains deterministic, every-run,
N-only, construction-inclusive one-sixth bit factorization, including
squares and arbitrary ratios.

## Exact companion center spectrum and a complete native signed miss (2026-10-03)

The fixed signed companion family now has a complete native miss on a
balanced 103-bit semiprime. This is evidence against its universal coverage,
not a kernel-checked exhaustion theorem or a general factorization lower
bound. The new compiled module
[`SemiprimeCompanionCenterSpectrum`](../RiemannGaussian/SemiprimeCompanionCenterSpectrum.lean)
retains the actual primitive weighted packet, both public center choices,
both original rows and their signed rounding errors before any projection.
It explains the information surviving the quadratic cancellation and proves
a restriction on one of its collision channels.

For a source pair, write its determinant as `m δ`, where `δ² = 1`, its
original coefficients as `(a_l,b_l,t_l)` and `(a_r,b_r,t_r)`, and its two
midpoint choices as `(A_l,B_l)` and `(A_r,B_r)`. The public choices are
`A_small = floor(sqrt(N/2)) + floor(sqrt(N))` and
`A_large = floor(sqrt(N)) + floor(sqrt(2N))`, with `B` using the opposite
choice. Let `ε = 2m² shift - H` be the signed rounding error for the exact
center numerator `H`. The compiled
`publicPacket_center_spectrum_rankOne` proves the literal primitive
companion center `c` satisfies

```text
2m c = m A_l + δ [t_r ε_l - t_l ε_r
                    - t_l (a_r - t_r) (A_r - A_l)].
```

The minus sign on the mixed term is part of the checked identity.
`publicPacket_center_choices` discharges membership in the actual four
SS/SL/LS/LL choices. `publicPacket_denominators` proves both actual
denominators lie in `[0,m]`, and `packetCenterError_abs_le` proves
`|ε| <= m²`. `publicPacket_weighted_error_bound` bounds the signed error
pair only after retaining its exact cancellation. The complementary midpoint
differences obey `B_r - B_l = -(A_r - A_l)`; the mixed contribution therefore
has one explicit arithmetic direction rather than two unrelated errors.
These are exact source identities, not an independent useful-hit estimate.

For two rows using the same midpoint, the mixed direction vanishes.
`publicPacket_same_center_interval` proves
`|2c - A| <= m(t_l+t_r) <= 2m²` for actual primitive public packets.
`publicPacket_same_center_difference` consequently proves `|c-e| <= 2m²`
for two packets with the same midpoint. Finally,
`publicPacket_same_center_modular_injective` proves that for every modulus
`p > 2m²`, equality of their reductions modulo `p` implies literal integer
equality. Thus this particular channel cannot produce a difference collision
between distinct integer centers above that threshold. The theorem does not
exclude endpoint hits, signed sums, mixed midpoint choices or pairs from
different midpoint bands. The richer original quadratic rows remain available.

The frozen native classifier
[`probe_semiprime_signed_companion_frontier.py`](../scripts/probe_semiprime_signed_companion_frontier.py)
and its [211-pin record](semiprime-signed-companion-frontier-audit.json) use
seed **202610033224**. The requested sample was four cases: `p` is the next
prime after a seeded integer in `[2^50,2^51)`, and `q` is the next prime
after a seeded integer between `p` and `2p`. The run stopped after its third
completed case, at the first signed miss. Each case uses the literal public
ceiling sixth root `B` and the least prime modulus `m >= B`. Every residue,
Euclidean intermediate row, both public centers and all four adjacent-row
weighted choices were enumerated. Both prime-field class sets were computed
independently, including when the first field already found a collision.
The known private factors enter only the reference classification.

| N | B / m | Original / weighted packets | Signed distinct centers | Signed classes mod p / mod q | Result |
| --- | --- | --- | ---: | --- | --- |
| 6932091709815168662574027287759 | 138085 / 138101 | 28586424 / 56620448 | 83922399 | 83922397 / 83922399 | ordinary and signed hit |
| 5476966283366926028364702427427 | 132767 / 132817 | 24932432 / 49333600 | 72893945 | 72893945 / 72893943 | ordinary miss; signed hit |
| 6798061565397654183415201602281 | 137636 / 137639 | 28411164 / 56271776 | 83269309 | 83269309 / 83269309 | complete signed miss |

The last input has
`p = 2245327606949267` and `q = 3027647967431443`.
Its ordinary center set has 41634654 elements and exactly that many classes
in each field. Adding zero and both signs yields 83269309 elements, again
with exactly that many classes in each field. These are whole-family
native injection checks, without constructing a pair matrix. The previously
compiled `recoverRows_none_iff_prime_separation` and
`recoverReflectedRows_none_iff_signed` identify the relevant separation
condition, but the large native class counts have not been transported into
their Lean hypotheses. No full polynomial or factor-recovery computation
was executed on these 103-bit inputs. The saved classification times are
reference diagnostics, not N-only factorizer timings or exponent fits.

`frontier_p_prime` and `frontier_q_prime` certify the two large factors
through kernel-checked Lucas certificates. `frontier_control_arithmetic`
proves their product, balance `p < q <= 2p`, primality of `m`, and
`2m² < p`. `frontier_control_sixthWidth` proves the literal public sixth
width is 137636; `frontier_control_public_modulus` proves the literal least
prime selector is 137639. `frontier_control_modulus_coprime` shows that
the modulus-GCD prefix does not recover this input. These arithmetic proofs
do not certify exhaustion of its 83-million-element signed set.

The separate
[`probe_semiprime_companion_center_spectrum.py`](../scripts/probe_semiprime_companion_center_spectrum.py)
and [215-pin record](semiprime-companion-center-spectrum-audit.json) use
seed **202610033226**. All 46 inherited public setup inputs through 49 bits
and 64 seeded additional `N`/prime-modulus families were checked completely.
The corpus contains 29596 original packets and 54604 primitive weighted
packets, with 13651 in each SS/SL/LS/LL choice; 19 families have no weighted
packets. Every exact signed spectrum, denominator bound, rounding envelope
and same-center interval check passed. This algebra replay inherits the
completed 103-bit miss through the frozen 211-pin record and does not repeat
the large field enumeration. All 211 parent pins, and then all 215 current
pins, were independently verified. The earlier explicit geometric-row
source reconciliation remains part of the inherited audit history.

The final scoped Lean gates passed: targeted build with `--wfail`, strict
leaf and ordinary root elaboration, and the compiled root-plus-leaf checker
[`CheckSemiprimeCompanionCenterSpectrum.lean`](../scripts/CheckSemiprimeCompanionCenterSpectrum.lean).
All 41 module declarations were audited, including 24 explicit and 17
generated declarations; 37 are theorem/helper declarations. All 14 namespace
linters report zero errors, and every transitive axiom is one of
`propext`, `Classical.choice` or `Quot.sound`.

During verification the shared Mathlib checkout was externally replaced
with revision `5514d43f7f6ec1ce8a2f646c24fda8260ed1e534`, which targets Lean
4.35.0-rc3 and prevented the default resolver from selecting the project's
pinned baseline. We preserved the shared checkout and project manifest and
exported the original pinned revision
`0df444a360eaa60ab8c11dca51a86af692955474` into an isolated temporary
dependency. Its cache was restored from 8312 already-local compressed files,
without downloading cache files. The gates passed with the exact command
prefix `/home/dbsanfte/.elan/bin/lake --packages=/tmp/semiprime-center-spectrum-4.33.1/packages.json`.
The shared checkout subsequently returned externally to the original
revision and Lean 4.33.1. All four scoped gates then also passed through the
normal workspace resolver; their suffixes and both command prefixes are
saved in the 215-pin record. No project toolchain or manifest was changed.

The fixed signed family remains a sound conditional detector, but its
universal coverage is **CONTRADICTED BY THE NATIVE REPLAY**. The full signed
failure certificate in Lean remains **OPEN**. A new coverage attempt must
retain useful arithmetic information removed by the linear companion
projection or supply an independently covering amendment; further pricing
of this fixed family cannot establish coverage. The deterministic,
every-run, N-only, construction-inclusive `N^(1/6)` bit factorization target,
including squares and arbitrary ratios, remains **OPEN**.

## Recording future progress

Append dated entries with the exact observable/algorithm, known input,
sample generation and seed, control/baseline, measured results, mathematical
interpretation and remaining obstruction. Distinguish existing Lean
declarations, newly checked proofs, floating-point evidence and conjectures.

Earlier probes ran in memory through Python heredocs; their historical
aggregate results do not all have complete executable reproductions.
The modular decoder's fresh 108-input replay and the October 2 sparse/batch
probes are now saved as source and JSON artifacts linked above.
Preserve the source hash, seed, corpus,
baseline version and timing protocol when comparing future changes.
Do not conflate a historical prototype with a new replay.

## Primary references

- [NIST DLMF: Dirichlet series](https://dlmf.nist.gov/27.4#E12):
  the von Mangoldt logarithmic-derivative series.
- [SymPy number-theory documentation](https://docs.sympy.org/latest/modules/ntheory.html):
  factorization APIs, factor cache and quadratic-sieve implementation.
- [GNU coreutils factor implementation](https://raw.githubusercontent.com/coreutils/coreutils/master/src/factor.c):
  algorithm context; the linked development source is not a pin of the
  locally installed 8.32 executable.
- [CADO-NFS](https://cado-nfs.gitlabpages.inria.fr/):
  a number-field-sieve implementation for future large-input comparisons.
- [Harvey–Hittmeir, A log-log speedup for exponent one-fifth deterministic integer factorisation](https://arxiv.org/abs/2105.11105):
  weighted factor-sum collisions, sparse sieving and proven complexity.
- [Gao–Feng–Hu–Pan, On factoring and power divisor problems via rank-3 lattices and the second vector](https://eprint.iacr.org/2025/1004):
  a further balanced-semiprime lattice framework.
- [Harvey–Hittmeir, Deterministic methods for finding elements of large multiplicative order](https://arxiv.org/abs/2601.11131):
  large-order-or-factor machinery for rigorous collision searches.
- [Brent–Zimmermann, An O(M(n) log n) algorithm for the Jacobi symbol](https://arxiv.org/abs/1004.2091):
  fast colour acquisition does not by itself supply fast factor decoding.
- [Harvey, 2026 Arizona Winter School notes](https://swc-math.github.io/aws/2026/2026HarveyNotes.pdf):
  accumulating remainder trees and fixed-matrix product batching.
- [Montgomery–Kruppa, Improved Stage 2 to P ± 1 Factoring Algorithms](https://antsmath.org/ANTSVIII/files/kruppa.pdf):
  reciprocal Laurent symmetry, geometric evaluation and two-convolution
  quadratic-extension evaluation; precedents for the phase implementation.
- [Brent–Kruppa–Zimmermann, FFT extension for algebraic-group factorization algorithms](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf):
  product/remainder continuation, power and Dickson maps, and ECM.
- [Umans–Wang, 2025 factoring framework](https://arxiv.org/html/2511.10851v1):
  conditional one-sixth factoring requires efficiently prefactored structured
  difference covers; sparse signals alone do not satisfy those hypotheses.
- [He–Sahai, 2026 difference-cover obstruction](https://arxiv.org/html/2608.06681):
  a restriction on the one-dimensional arithmetic-progression variant,
  rather than a no-go for every higher-rank construction.
