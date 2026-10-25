
## Selected-output solver and lattice batching tests, 2026-10-24

Neither tested acquisition route improves the complete soft sqrt(JL)
query. At J=O(k), L=O(k²), the proved clock remains soft k^(3/2).
The all-semiprime deterministic sixth-rate algorithm, unconditional
orientation and executable Lean bit-cost proof remain open. This pass
checks a new primary solver against its actual required input and
executes a concrete batching attempt; it adds no backend theorem or
numerical coverage campaign.

[Khichane–Neiger, March 2026](https://arxiv.org/abs/2603.02425),
Theorem 1 and Theorem 25/Algorithm 3, give deterministic structured
linear solving and nullspace construction over an effective field.
For the nilpotent Stein operator Delta(D)=D-SDS^t, supplied rank-alpha
generators and the right-hand side suffice in
O(alpha^(omega-1)[M(m)log m+M(n)log² n]) field operations.
No generic rank profile or random preconditioner is needed.

There is an exact supported specialization of the old regularized
Bezout readout. Let F be monic degree J, h=G mod F, K=Bez(F,h),
f the lower coefficient vector of F, R reversal, S lower nilpotent shift,
and D=(K+e0e0^t)R. Then

    D-SDS^t=h(e0+SRf)^t-f(SRh)^t+e0 e_last^t.

This is a rank-at-most-three Stein representation; use the displayed
three-column generator for J>=3 and direct fixed-size methods for
J<=2. The first column of the displaced matrix is exactly h for J>1.
Consequently ANY explicit generator for this particular matrix yields
h in O(alpha J), and does not bypass its acquisition. Once h is
supplied, guarded polynomial gcd already recovers the unique common
root in soft J, so the new solver is not a further query advance.
The composite adaptation classifies each coefficient as a unit,
global zero or a source of a proper factor; it does not supply h.

A separate apparent circuit shortcut is not an available theorem:
the [primary ECCC TR25-171 revision notice](https://eccc.weizmann.ac.il/report/2025/171/),
dated 28 January 2026, reports a gap in Theorems 6.2 and 6.4 on which
all the paper's results rely. Its border-composition/GCD claims are
not imported. The original PDF and primary status page are pinned.

For a genuine all-class lattice execution, partition the public full
residue catalog modulo m into groups C of size at most g. In a factor
size bin B<=P<=U and an actual interval block starting at S, acquire
the monic polynomial

    f_(C,S)(Z)=prod_(c in C)(Z+S+[m^-1 c]_N) mod N.

The correct residue gives the root Z=(P-c)/m-S modulo P. May's
unknown-divisor theorem applies with degree delta<=g and epsilon=1/n,
n=ceil log2 N, beta=b/n for B=2^b. Exact integer roots define the
radius X_g=max(1,floor(N^(beta²/g)/16)). For X_g>=2 it lies inside
the theorem's guaranteed radius. The lattice dimensions, coefficient
bits, all integer roots and candidate gcd validation are paid; X_g=1
uses direct bounded enumeration. All wrong candidates are validated,
and coverage is retained by the full catalog and interval schedule.

The scheduled COMPLETE search has
O(ceil(m/g)*(1+B/(m X_g))) lattice calls. In balanced bins its budget,
ignoring logarithms for polylogarithmic g, is

    (m/g)+N^(1/2-1/(4g))/g.

For g=1 this recovers the ordinary soft(m+N^1/4) bound. For fixed
g>=2 the second exponent worsens; polylogarithmic grouping does not
reverse that comparison. This compares the scheduled budget BEFORE
early exit, not an Omega runtime theorem for actual semiprimes. The
native relation c_local=t²/a mod r² supplies no public c_local to
restrict this search. Cross-class translation also needs an integer
height bound on m^-1(c-c') modulo N; it is not supplied by the phase
carries. No uniformly small shared LLL certificate was constructed.

Proofs, primary caches, exact independent reviews and preservation
validation are in /tmp/semiprime-selected-scalar-acquisition-20261024/.
The solver input and the batching radius are now explicit; neither is
an acquired near-linear selector. Preserve all earlier document
prefixes, 270 frozen entries, HEAD and concurrent work, including the
new untracked gated-DeltaNet proposal. No commit or push was requested.
