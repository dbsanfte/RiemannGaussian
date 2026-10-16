# Every scalar stride leaves a linear boundary on the actual quadratic carrier

2026-10-16. **A new arithmetic obstruction to regular homogeneous descent on the supplied carrier, uniform over all scalar strides.** The whole-family softly O(m) collision query remains open; the general softly O(m^(3/2)) acquisition bound is unchanged. Three user-authorized Sol 6.1 agents investigated in parallel, with independent reviews of the final proofs and inspected literature claims.

The [previous packet](../semiprime-descent-query-20261016/README.md) paid the normalized boundary solver but left its forcing unacquired. This packet shows that choosing an input-dependent stride cannot remove the linear boundary. It also checks a minimal pole-bearing gauge and the direct circuit-locator literature. These are classical results, without new Lean declarations or a factoring-exponent claim.

## The actual low digit supplies an all-stride obstruction

The [uniform-boundary proof](reports/uniform-shift-boundary.md) uses the literal offsets, with d=m^2, span [-3d,d], and

    delta_j mod m = N(j^(-2)-2j^(-1)).

Their residue image is exactly A=N(S-1), where S is the set of squares INCLUDING zero in F_m. Thus the deduplicated carrier has (m+1)/2<=J<=m-1 nodes, with at most two nodes above each low residue. The elementary quadratic-character correlation gives, for h!=0,

    |S minus (S+h)|=(m+1-chi(h)-chi(-h))/4.

In either hidden field, assume gamma has order R>8m^2, as on the retained actual family. For EVERY scalar rho!=1, at least ceil((m-1)/4) actual nodes z have rho*z outside the carrier. The bounded integer offsets prevent exponent wraparound. A nonzero low shift uses the exact square-set boundary; a zero low shift stays within fibers of size at most two. Scalars outside the relevant exponent-difference range leave every node dangling. This is simultaneous over all strides, including fully input-dependent or privately advised choices, without a new exceptional-input deletion.

A regular weight w=A_0/B_0, with B_0 unit modulo H=prod(t-z), gives representative-independent descent f -> w(t)f(rho*t) modulo H iff H divides A_0(t)H(rho*t). Hence it must vanish on that entire boundary. On the inherited family with J-o(m) unit rows, it kills Omega(m) unit payloads. Higher homogeneous jets force the same vanishing to higher order. The powered-node compatibility defect has exact rank min(b,|Dang(rho)|) for 1<=b<=J, so balanced dyadic powers have linear defect rank for every such stride.

These statements are fieldwise: gcd(rho-1,N)=1 ensures nonidentity in both fields, a proper gcd already factors N, and identity components need separate handling. They prohibit the stated regular lossless descent and small-rank compatibility contracts. Rank is not an operation lower bound.

## Gauges move the boundary information rather than acquire it

The [minimal q-gauge analysis](reports/minimal-gauge-and-prefix-obstruction.md) constructs G(t)=prod_(i dangling)(t-qz_i), with softly O(J) coefficient setup and unit values at source nodes. Its repaired homogeneous value operator is nilpotent of index at most two. Recovering the actual F/G requires residues F(qz_i)/G'(qz_i) at the newly introduced poles; these are still unacquired long-product payloads. The exclusive P-only and Q-only rows survive in distinct terminal residues. Consequently one common prefix-product/coefficient stream with unit row normalizers cannot represent the entire packet. Multiple streams, sums, different observables and shared computation remain possible.

The [all-stride corollary](reports/all-stride-gauge-corollary.md) proves that a regular gauge assembled from r contiguous product blocks using the SAME base rho as its operator needs

    r >= ceil((m-1)/4)-e,

if the original weight is nonzero at all but e=o(m) source nodes. Origins, horizons and signed integer powers may be arbitrarily advised. Each block supplies at most one numerator endpoint zero, regardless of horizon. Unmatched bases and additive gauge descriptions are outside the theorem. Linear block count could still admit nearlinear shared computation.

The canonical two-endpoint-unit branch is nonvacuous on an actual majority family. For fixed L=2m^2+2, the existing endpoint-band, density and exclusive-row bad-input counts are all measured against the SAME original prime-pair supply; their union remains negligible. Thus both products prod(1-z_i) and prod(1-q^L z_i) are units while the residue obstructions coexist. This does not grant a free menu of arbitrary lengths. Polynomial endpoint-band width is a coverage statement; only the stated polylogarithmic schedules retain a nearlinear probe clock.

## The two acquisition attempts remain unresolved

The [forcing calculation](reports/forcing-attempt.md) gives a short unit-ended q-recurrence for A(x)=F(q^(1-L)x)/prod(1-z_j x). It forbids J+1 consecutive zero coefficients in the relevant prefix. Multiplication by the sparse mask K(x^B) permits cancellations, so that result does not prove a denser pole packet or acquire the quotient forcing. Direct propagation is cubic here and does not compete with the existing query bound.

The [primary-source circuit audit](reports/locator-audit.md) checks output-degree-sensitive SLP factor results, uniform SLP gcd, directed evaluation, shallow coefficient-input gcd circuits and a 2026 prime-power factoring preprint. No inspected theorem uniformly extracts the collision locator in softly O(s+d) from our paid size-s vector circuit. Short output-circuit existence does not acquire its seed or constants. The ECCC border-circuit paper's primary revision notice reports a foundational gap, so its advertised bounds are not used. All inspected primary payloads and exact review scopes are preserved.

The remaining target is a restriction-stable softly O(m) acquisition of the quotient forcing, a channel remainder, the collision locator or another sufficient factor-selective consequence. Enlarged or moving carriers remain open: low-digit structure alone does not exclude an O(m)-size cover with holes, and handling the exact high-digit lift and holes would need a charged algorithm. Fixed-F syzygies, inhomogeneous corrections and implicit diagonal/norm methods also remain possible. Complete bit-complexity and Lean composition are still required after the query advance.

The manifest and source map pin every report, review, primary payload and inherited premise. All ten predecessor packets and their journal entries remain byte-unchanged.
