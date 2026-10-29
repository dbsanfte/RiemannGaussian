# Native coloured finite boundary, with carries and collision ledger

26 October 2026. Packages A/B of the string proposal; scratch only, no tests or repository edits. Result: an explicit soft-k acquired whole-family endpoint boundary is obtained below. It is a mixed difference of shifted collision products. Its factors are not proved to cover the original witness; the cancelled-zero ledger is not acquired. No scalar-query rate improvement is claimed.

Inputs read: [trace-recurrence sections 3–6](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-trace-20261026/trace-recurrence.md:75), [proposal section 2](/home/dbsanfte/riemann/formal/docs/semiprime-string-theory-research-proposal.md:99), and the scratch residue-supplier/multisection.md section 6. The finite identities below are proved algebraically; no infinite vertex or root-of-unity identity is specialized.

## 1. Actual incidence set and unwrapped coordinates

Use the existing output-sensitive soft-k enumeration of coloured incidences. For each unit j modulo k, let R_j be its retained rows v=(a,b), in ALL four signed nonaxis sectors 0<|ab|<k and the specified axes, after the existing public integer-zero row deletion and any legitimately unit-certified pruning. Keep the original metadata and phase for every incidence. Write J_c=sum_j |R_j|=soft O(k).

This is the coverage-preserving stationary-colour family, not a claim that it contains every conic-phase row of the older complete catalogue. Its true-factor colour contains a surviving old witness by the established coverage proof. Multiple colours may supply the same physical row; retaining their multiplicities changes the scalar but not its zero/nonunit predicate. Deduplication is optional and must preserve that metadata. No uncoloured ambient support is substituted.

Let r_j=[Nj^{-2}]_k, u=(k,0), w=(r_j,1), and t_v=(a-r_j b)/k. With j^{-1} its prescribed inverse modulo H, put

    mu_v=-aj-bN j^{-1}, tau_v=floor(mu_v/H),
    lambda_v=mu_v-H tau_v,
    X_j=beta^{k(1-j)},
    Y_j=beta^{(1-j)r_j+N(1-j^{-1})}, Z=q^{-1}.

These are acquired units. Exactly, beta^{a+bN+lambda_v}=X_j^{t_v}Y_j^b Z^{tau_v}. For the original signed clock i=-M,...,M, the comparison normalized by a known unit is therefore

    1-beta^{a+bN+lambda_v}q^{-i}
      =1-X_j^{t_v}Y_j^b Z^{tau_v+i}.                 (1)

Thus canonical carries move the integer clock support, not the coefficients of the character. Formula (1) includes negative rows and axes without further square roots or phase choices.

## 2. Explicit endpoint boundary of the actual coloured support

Initially regard X,Y,Z as independent Laurent indeterminates. Define

    K_j(X,Y,Z)=sum_(v in R_j) X^{t_v}Y^b
                            sum_(i=-M)^M Z^{tau_v+i}.

No long clock is expanded. Its exact finite difference is

    B_j=(1-X)(1-Y)(1-Z)K_j
       =sum_(v in R_j) X^{t_v}Y^b (1-X)(1-Y)
                    [Z^{tau_v-M}-Z^{tau_v+M+1}].   (2)

The factor (1-Z)K_j is the OLD acquired clock-endpoint kernel. Formula (2) applies two further lattice differences (1-X)(1-Y) to that kernel; it is not an independent acquisition of the long query. The credit here is the exact actual-support, carry and deletion integration into this finite boundary. The explicit boundary has at most 8|R_j| signed monomials, including actual tau, deletions, signs and axes. Coincident monomials may be combined by exact integer-coordinate sorting. All colours together require soft O(J_c+k)=soft O(k) bit operations and storage to acquire, including binary powering for specialization. The coordinates t_v,b,tau_v and character exponents have O(log N) bits: |a|,|b|=O(k), |t_v|=O(k), j^{-1}<H, |tau_v|=O(kN), and all these bounds are polynomial in N. The original soft-k acquisition is used rather than a k-by-k scan.

This IS a short finite boundary for the actual phased incidence support. It does not assert the boundary has O(sqrt k) factors. In particular on the positive support D_k, every 0<a<k; translation by u=(k,0) has no overlap with D_k at all. Hence the HNF horizontal difference does not benefit from the uncoloured Young diagram's long horizontal runs. Other lattice bases can be tried, but that observation alone is not a statement about all bases or algorithms.

## 3. Exact cleared product identity and its scope

For any finite signed Laurent sum A=sum c_alpha X^alpha define its formal multiplicative image N_z(A)=product_alpha (1-z X^alpha)^{c_alpha}. This is a rational-function notation only; actual specialization must use the cleared polynomial identity below. Let

    P_j(z)=product_(v in R_j) product_(i=-M)^M
                          (1-z X^{t_v}Y^b Z^{tau_v+i}).

Write N_z(B_j)=B_j^+(z)/B_j^-(z), with the positive/negative multiplicities from (2); both are explicitly acquired products of O(|R_j|) factors. Then

    B_j^-(z) P_j(z) P_j(XYz) P_j(XZz) P_j(YZz)
      =B_j^+(z) P_j(Xz) P_j(Yz) P_j(Zz) P_j(XYZz). (3)

This follows by applying N_z to (2), or expanding the eight translates of K_j. It is valid over the native composite ring after clearing, including every collision. It neither divides by B_j^- nor treats it as a unit.

At z=1, P_j(1) is the desired coloured component. The other seven products have the same finite support but shifted character/clock arguments. They are not supplied values or original covered subfamilies. The acquired ratio of short boundaries determines a relation among EIGHT long products, not P_j(1). Evaluating B_j^± costs soft J_c ring work, but that is not evaluating the products in (3).

Boundary factors specialize to 1-beta^D with explicit integer D of O(log N) bits. Literal D=0 must be detected before any gcd interpretation. Nonliteral nonunits have a legal own-label factor/generic-annihilator route, with once-only T_ext=soft N^{31/192}; they do not need original-row provenance. This supplies a soft-k boundary SCREEN if desired, not a coverage theorem for it. A literal boundary zero is merely a known degeneration of (3); deleting it numerically from (3) without matching regularization is invalid.

## 4. Exactly what happens to a collision

Set z=1-epsilon and work locally at either hidden prime. Every specialized factor 1-(1-epsilon)c, c a unit, has epsilon order one exactly when c=1, and otherwise zero. Therefore (3) gives the alternating relation between the eight shifted collision COUNTS and the signed boundary count. This is valid even when several factors collide; no vanishing leading coefficient is inverted. It is not a way to compute the local valuation in R without additional work.

The clock cancellation can be inspected BEFORE any two-dimensional finite difference. In (1-Z)K_j, every monomial with clock exponent strictly between tau_v-M and tau_v+M+1 cancels coefficientwise. Thus a collision at a strictly interior physical clock position is erased from that boundary ledger. Carries do not repair it: they translate both endpoints by the same exact tau_v. The surviving endpoints are the first included and first excluded clock exponents, not a selection theorem locating an interior witness.

For a one-row clock this is the elementary identity

    P(z)/P(Zz)=(1-z c Z^{-M})/(1-z c Z^{M+1}),

with c=X^{t_v}Y^b Z^{tau_v}. The two endpoints are acquired, while the unknown amplitude remains. Taking gcd flags of every CANCELLED pair would retain the original events, but those flags are not obtained from the two endpoint values. In the whole coloured family their existing complete evaluation is the old shared engine at soft(J_c+sqrt(J_c M)), not a new boundary algorithm. This does NOT prove that a native semiprime's guaranteed witness always misses the boundary; it establishes precisely which implication the cleared identity fails to supply.

Signs, axes and deleted rows do not change the proof: (2) is linear in the actual acquired incidence list. In particular deletion changes its boundary by subtracting the corresponding eight endpoints, and cannot be ignored just because the undeleted ambient region was Young. Replacing actual phase carries by an ambient Young boundary would change (1).

## Outcome and next missing datum

Package A supplies exact coloured-support/carry/deletion integration of two lattice differences applied to the OLD acquired clock-endpoint kernel, at soft-k cost. This is boundary bookkeeping, not independent query acquisition. Package B yields an exact collision ledger and legal boundary nonunit recovery, but no coverage-preserving elimination of the cancelled bulk events. A genuinely new completion would need a theorem selecting a covered nonunit among the acquired boundary factors, or an initialized joint algorithm for the remaining shifted amplitudes/flags. Neither is furnished by finite differencing. The old complete query remains available; there is no new claimed runtime exponent or general algorithmic obstruction.
