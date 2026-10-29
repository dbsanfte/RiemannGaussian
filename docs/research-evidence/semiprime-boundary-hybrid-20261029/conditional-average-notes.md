2026-10-29 rolling checked gain: executed conditional averaging
SemiprimeD1BoundaryConditionalAverage proves localExpectation_average for
arbitrary endpoint factors with endpoint-count at most scale; single_average
and pair_average discharge the actual scale-2/scale-4 calls automatically.
The arbitrary local coordinate is removed/reinserted with exact idxOf/getD
reads and the proof-only BoundaryColourWords.successes_insert catalogue.
potential_average now proves literal executed potential averaging;
selected_potential_le, extend_potential_le and acquire_potential_le discharge
the former averaging premises of BoundaryChoice. Runtime Plan is unchanged.
Strict pinned warningAsError/default-200k compile exit 0; scoped all-linter
and all-generated Std3 audit exit 0 (56 declarations, 55 theorems). Evidence:
/tmp/semiprime-publication-20261029/boundary-conditional-average-verification.json
Initial variance/width and full machine cost remain OPEN.

2026-10-29 rolling checked gain: actual initial covariance accounting
BoundaryInitialVariance exposes the exact proof-only full-catalogue sum of
literal squared measured loads, nonloop initial event-count identity, bucket
mean 2K-1, disjoint pair count=eventCount^2, and universal quarter covariance
bound. BoundaryOverlap proves original ordered overlaps<=2*M*maxDegree,
retaining diagonal and parallel occurrence multiplicity. BoundaryVariance
assembles these into initial_potential_real_bound:
  initialPotential <= K^4 * (2K-1) * M * maxDegree / 2.
Its sole mean-identification premise is equality of the actual per-load
meanNumerator with M*eventCount; bucket equality is proved here and exact
merge equality is parent-owned in BoundaryMergeMean. No covariance or
averaging endpoint is assumed. All three modules strict/default200k exit 0;
scoped all-linter/all-generated Std3 audit exit 0 (67 decl, 62 theorems).
Evidence: /tmp/semiprime-publication-20261029/boundary-variance-verification.json

2026-10-29 rolling checked gain: actual integer K and half-exponent width
BoundaryPartitionRate proves positive actual degree<=M, default-branch
unreachability, successful returned cube test, first-success minimality and
failed immediately preceding test if K>2. BoundaryPartitionWidthRate proves
K<=max(2,ceil(cuberoot(M/Delta))) and actual acquired width
  W<=M/2+3*cuberoot(M^2*Delta).
BoundaryPartitionOriginalRate derives uniformly over all graph instances at
M<=s/sqrt(logarithm s)+1 and Delta<=degreeCap(s), for each eps>0 eventually
  W<=(1/2+eps)*s/sqrt(logarithm s).
The exact empty-graph W=0 branch is included. BoundaryPartitionReachRate joins
actual Reach invariants, original rootReady guards, stopped edge caps and
NetworkDegree.maxDegree_le to the concrete boundary leaf-report width. Both
failed-active-test and scheduled exhausted-fuel leaves are covered. The latter
explicitly requires logarithm(s)+1<=call.depth+0; it makes no assertion about
a caller invoking a large root with arbitrary zero fuel. All four new rate
modules strict pinned/default200k warningAsError exit0 and scoped all-linter/
all-generated Std3 audit exit0 (43 declarations,41 theorems). Evidence:
/tmp/semiprime-publication-20261029/boundary-partition-rate-verification.json
These are actual width/exponent gains, not the still-open complete original
primitive-machine bit-time theorem. Original supplied source-note unchanged.
